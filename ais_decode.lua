-- ais_decode.lua
-- Minimal AIS decoder for message type 1/2/3 + AIVDM fragment reassembly

local M = {}
local bit = bit or bit32

local function nmea_checksum_ok(line)
  local star = line:find("%*")
  if not star then return true end
  local provided = line:sub(star+1, star+2)
  local body = line:sub(2, star-1)
  local c = 0
  for i = 1, #body do
    c = bit.bxor(c, body:byte(i))
  end
  return string.format("%02X", c) == provided:upper()
end

local function split_csv(s)
  local t, field = {}, ""
  for i = 1, #s do
    local ch = s:sub(i,i)
    if ch == "," then
      t[#t+1] = field
      field = ""
    else
      field = field .. ch
    end
  end
  t[#t+1] = field
  return t
end

local function sixbit_val(ch)
  local v = ch:byte() - 48
  if v > 40 then v = v - 8 end
  return v
end

local function payload_to_bits(payload)
  local bits = {}
  for i = 1, #payload do
    local v = payload:byte(i) - 48
    if v > 40 then v = v - 8 end
    for b = 5, 0, -1 do
      bits[#bits+1] = bit.band(bit.rshift(v, b), 1)
    end
  end
  return bits
end

local function bits_to_uint(bits, start_bit, bitlen)
  local v = 0
  for i = 0, bitlen-1 do
    v = bit.bor(bit.lshift(v, 1), bits[start_bit + i] or 0)
  end
  return v
end

local function bits_to_int_signed(bits, start_bit, bitlen)
  local u = bits_to_uint(bits, start_bit, bitlen)
  local sign_bit = bit.lshift(1, bitlen-1)
  if bit.band(u, sign_bit) ~= 0 then
    return u - bit.lshift(1, bitlen)
  end
  return u
end

local function bits_to_text(bits, start_bit, bitlen)
  local chars = {}
  local n = math.floor(bitlen / 6)
  for i = 0, n-1 do
    local v = bits_to_uint(bits, start_bit + i*6, 6)
    local c
    if v < 32 then
      c = string.char(v + 64)
    else
      c = string.char(v)
    end
    chars[#chars+1] = c
  end
  local s = table.concat(chars)
  s = s:gsub("@", ""):gsub("%s+$", "")
  return s
end

local function decode_pos_report(bits)
  local msg_type = bits_to_uint(bits, 1, 6)
  if msg_type ~= 1 and msg_type ~= 2 and msg_type ~= 3 then return nil end

  local mmsi      = bits_to_uint(bits, 9, 30)
  local nav_stat  = bits_to_uint(bits, 39, 4)
  local sog10     = bits_to_uint(bits, 51, 10)
  local lon_raw   = bits_to_int_signed(bits, 62, 28)
  local lat_raw   = bits_to_int_signed(bits, 90, 27)
  local cog10     = bits_to_uint(bits, 117, 12)
  local true_hdg  = bits_to_uint(bits, 129, 9)

  local lon = lon_raw / 600000.0
  local lat = lat_raw / 600000.0

  if lon < -180 or lon > 180 or lat < -90 or lat > 90 then return nil end

  local sog = (sog10 == 1023) and nil or (sog10 / 10.0)
  local cog = (cog10 == 3600) and nil or (cog10 / 10.0)
  local hdg = (true_hdg == 511) and nil or true_hdg

  return {
    type = msg_type,
    mmsi = mmsi,
    nav_status = nav_stat,
    sog = sog,
    cog = cog,
    hdg = hdg,
    lat = lat,
    lon = lon,
    updated_at = os.time(),
  }
end

local function decode_static_voyage(bits)
  local msg_type = bits_to_uint(bits, 1, 6)
  if msg_type ~= 5 then return nil end

  local mmsi = bits_to_uint(bits, 9, 30)
  local name = bits_to_text(bits, 113, 120)   -- Ship name (20 chars)
  local callsign = bits_to_text(bits, 71, 42)
  local shiptype = bits_to_uint(bits, 39, 8)

  return {
    type = 5,
    mmsi = mmsi,
    name = name,
    callsign = callsign,
    shiptype = shiptype,
  }
end

local reasm = {}
local function reasm_key(seq, chan) return tostring(seq or "") .. ":" .. tostring(chan or "") end

local function parse_aivdm(line)
  -- Strip NMEA tag blocks like: \s:...,c:...*hh\   (IEC 61162-1)
  -- There can also be multiple tag blocks; remove all leading \...\ occurrences.
  while line:sub(1,1) == "\\" do
    local endtag = line:find("\\", 2, true)
    if not endtag then break end
    line = line:sub(endtag + 1)
  end

  line = line:gsub("\r$", "")

  if line:sub(1,1) ~= "!" then return nil end
  -- Accept any talker: !AIVDM, !BSVDM, !ABVDM, etc. and also VDO
  if not line:match("^!%w%wVD[MO],") then return nil end

  if not nmea_checksum_ok(line) then return nil end

  local no_chk = line:gsub("%*%x%x$", "")
  local fields = split_csv(no_chk:sub(2)) -- strip leading '!'

  local total    = tonumber(fields[2])
  local num      = tonumber(fields[3])
  local seq      = (fields[4] ~= "" and fields[4]) or nil
  local chan     = (fields[5] ~= "" and fields[5]) or nil
  local payload  = fields[6] or ""
  local fillbits = tonumber(fields[7]) or 0

  if not total or not num then return nil end
  return total, num, seq, chan, payload, fillbits
end


function M.feed_line(line)
  local total, num, seq, chan, payload, fillbits = parse_aivdm(line)
  if not total then return nil end

  if total == 1 then
    local bits = payload_to_bits(payload)
    for _ = 1, fillbits do bits[#bits] = nil end
    local t = decode_pos_report(bits)
    if t then return t end
    return decode_static_voyage(bits)

  end

  local key = reasm_key(seq, chan)
  local slot = reasm[key]
  if not slot or slot.total ~= total then
    slot = { total = total, parts = {}, fillbits = 0, t0 = os.time() }
    reasm[key] = slot
  end

  slot.parts[num] = payload
  slot.fillbits = fillbits

  if os.time() - slot.t0 > 2 then
    reasm[key] = nil
    return nil
  end

  for i = 1, total do
    if not slot.parts[i] then return nil end
  end

  local joined = table.concat(slot.parts, "")
  reasm[key] = nil

  local bits = payload_to_bits(joined)
  for _ = 1, slot.fillbits do bits[#bits] = nil end
  local t = decode_pos_report(bits)
  if t then return t end
  return decode_static_voyage(bits)

end

return M
