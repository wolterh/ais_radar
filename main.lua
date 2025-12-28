local HUD_FONT
local HUD_FONT_MONO


-- =========================
-- Robustness helpers
-- =========================
local function nz(v, d) return (v ~= nil) and v or d end
local function safe_num(v, d) if type(v) == "number" then return v else return d end end
local function safe_str(v, d) if v ~= nil then return tostring(v) else return d end end


-- draw dotted line helper
local function draw_dotted_line(x1, y1, x2, y2, dash, gap)
  dash = dash or 6
  gap  = gap  or 4
  local dx, dy = x2 - x1, y2 - y1
  local len = math.sqrt(dx*dx + dy*dy)
  if len < 1 then return end


local function deg_wrap(d)
  d = d % 360
  if d < 0 then d = d + 360 end
  return d
end

local function deg_diff(a, b)
  -- smallest difference a-b in degrees in [-180, 180]
  local d = (a - b + 180) % 360 - 180
  return d
end

local function rotate_xy(x, y, ang_deg)
  -- rotate (x east, y north) by ang_deg clockwise? Here: positive ang rotates coordinates by +ang about origin.
  local a = math.rad(ang_deg)
  local ca, sa = math.cos(a), math.sin(a)
  return x * ca + y * sa, -x * sa + y * ca
end

  local ux, uy = dx / len, dy / len
  local dist = 0
  while dist < len do
    local d1 = math.min(dash, len - dist)
    local sx = x1 + ux * dist
    local sy = y1 + uy * dist
    local ex = x1 + ux * (dist + d1)
    local ey = y1 + uy * (dist + d1)
    love.graphics.line(sx, sy, ex, ey)
    dist = dist + dash + gap
  end
end

-- main.lua (Love2D)
-- Norway AIS Radar demo with:
-- - AIS decoding (type 1/2/3 + type 5 metadata) via ais_decode.lua
-- - Targets list filtered by (in range) OR (TCPA <= 15 min)
-- - Sorting by smallest CPA
-- - Danger cone + red highlight for dangerous targets
-- - Ownship dead-reckoning with fixed SOG/COG

local socket = require("socket")
local ais = require("ais_decode")
local rm = require("radar_math")

-- =========================
-- Configuration
-- =========================
local HOST, PORT = "153.44.253.27", 5631

local WINDOW_W, WINDOW_H = 1024, 600

local PANEL_W = 440           -- right-side list width
local VISIBLE_ROWS = 22       -- number of list rows shown
local ROW_H = 26
local FONT_UI, font_big

local MAX_AGE_S = 180         -- prune targets older than this
local RANGE_NM_MIN, RANGE_NM_MAX = 1.5, 96.0
local RANGE_NM = 24.0         -- start range (keys adjust)

-- Ownship (demo): fixed speed/course for dead-reckoning
local OWN_SOG_KN = 6.0
local OWN_COG_DEG = 30.0

-- Orientation mode: North-up (false) or Course-up (true)
local COURSE_UP = false

-- Danger cone blinking when TCPA < this threshold (minutes)
local DANGER_BLINK_TCPA_MIN = 5.0
local DANGER_BLINK_PERIOD_S = 0.6  -- blink period (seconds)

-- Fonts (initialized in love.load)
local FONT_UI
local FONT_BIG
local FONT_MED

-- Target styling
local MOVING_SOG_KN = 0.5

-- List filter
local TCPA_FILTER_MIN = 15.0

-- Danger logic (collision cone)
local CPA_CONE_NM = 0.5
local TCPA_CONE_MIN = 15.0

-- Colors (Love2D uses 0..1)
local COL_WHITE = {1, 1, 1, 1}
local COL_MOVING = {0.2, 1.0, 0.2, 1}      -- neon green
local COL_DANGER = {1.0, 0.2, 0.2, 1}      -- red
local COL_DIM = {1, 1, 1, 0.7}

-- =========================
-- State
-- =========================
local conn
local rxbuf = ""

local targets = {}     -- mmsi -> latest dynamic target {lat,lon,sog,cog,...}
local shipinfo = {}    -- mmsi -> {name=..., callsign=...}

local selected_mmsi = nil

local own_lat, own_lon = 60.0, 5.0
local own_valid = false

-- Ownship mode: UNLOCKED (estimate), LOCKED (freeze), FOLLOW (center on selected)
local own_mode = "UNLOCKED"
local lock_after_s = 5.0
local app_t0 = 0
local last_recenter = 0

-- =========================
-- Small math helpers
-- =========================
local function clamp(v, lo, hi)
  if v < lo then return lo end
  if v > hi then return hi end
  return v
end

local function kn_to_ms(kn) return kn * 1852.0 / 3600.0 end
local function m_to_nm(m) return m / 1852.0 end

local function vel_from_cog_sog(cog_deg, sog_kn)
  if cog_deg == nil or sog_kn == nil then return nil end
  local v = kn_to_ms(sog_kn)
  local a = math.rad(cog_deg) -- 0=N, 90=E
  return math.sin(a) * v, math.cos(a) * v -- vx east, vy north
end

local function ang_wrap(a)
  a = a % (2 * math.pi)
  if a < 0 then a = a + 2 * math.pi end
  return a
end

local function ang_diff(a, b)
  -- smallest difference in radians [-pi, pi]
  return (a - b + math.pi) % (2 * math.pi) - math.pi
end

--- Geeft de naam van het schip terug, of het MMSI als de naam ontbreekt.
-- @param name De naam van het schip (string of nil).
-- @param mmsi Het MMSI nummer (string, getal of nil).
-- @return De naam, het MMSI als string, of "Unknown" als beiden missen.
local function get_ship_identity(name, mmsi)
    -- 1. Controleer of de naam bestaat en niet leeg is
    if name and name ~= "" and name ~= "—" then
        return name
    end

    -- 2. Als naam faalt, gebruik MMSI (omgezet naar string voor consistentie)
    -- 3. Als beiden nil zijn, geef "Unknown"
    return tostring(mmsi or "Unknown")
end



--- Formatteert een string naar een vaste lengte.
-- @param str De invoerstring (mag nil zijn).
-- @param len De gewenste doellengte.
-- @param indicator (Optioneel) Teken om inkorting aan te geven, bijv. ".." of "…".
-- @return Een string van exact de opgegeven lengte.
local function format_fixed_length(str, len, indicator)
    str = tostring(str or "") -- Maak robuust voor nil/getallen
    indicator = indicator or ".."
    len = math.max(0, len) -- Voorkom negatieve lengtes

    local str_len = #str

    if str_len > len then
        -- Afkappen: zorg dat de indicator binnen de lengte past
        local suffix_len = #indicator
        if len > suffix_len then
            return str:sub(1, len - suffix_len) .. indicator
        else
            -- Als de gewenste lengte te klein is voor de indicator, 
            -- geef dan gewoon de eerste tekens terug.
            return str:sub(1, len)
        end
    elseif str_len < len then
        -- Opvullen met spaties aan de rechterkant
        return str .. string.rep("_", len - str_len)
    else
        -- Precies goed
        return str
    end
end

-- =========================
-- CPA / TCPA
-- =========================
local function compute_cpa_tcpa(rx, ry, vrelx, vrely)
  local v2 = vrelx * vrelx + vrely * vrely
  if v2 < 1e-6 then
    return m_to_nm(math.sqrt(rx * rx + ry * ry)), nil
  end



local function colregs_classification(brg_true_deg, t_cog_deg, t_sog_kn)
  -- Simple COLREGS-style encounter classification from ownship frame.
  -- Uses relative bearing (target relative to own course) + approximate course relation.
  if not brg_true_deg then return "UNKNOWN" end

  local rb = deg_wrap(brg_true_deg - OWN_COG_DEG)  -- 0=dead ahead, 90=starboard beam, 180=astern, 270=port beam
  local tcog = t_cog_deg
  local tsog = t_sog_kn

  -- Overtaking: target is abaft the beam (>112.5° and <247.5°) and faster than ownship
  if tsog and tsog > (OWN_SOG_KN + 0.5) and rb > 112.5 and rb < 247.5 then
    return "OVERTAKING (YOU ARE STAND-ON)"
  end

  -- Head-on: target nearly ahead and reciprocal-ish course
  if tcog then
    local reciprocal = deg_wrap(OWN_COG_DEG + 180)
    if (rb <= 10 or rb >= 350) and math.abs(deg_diff(tcog, reciprocal)) <= 25 then
      return "HEAD-ON (BOTH ALTER TO STBD)"
    end
  end

  -- Crossing: starboard side vs port side
  if rb > 0 and rb < 112.5 then
    return "CROSSING (TARGET ON STBD: YOU GIVE WAY)"
  elseif rb > 247.5 and rb < 360 then
    return "CROSSING (TARGET ON PORT: YOU STAND ON)"
  end

  return "OTHER / UNDETERMINED"
end

  local dot = rx * vrelx + ry * vrely
  local tcpa_s = -dot / v2
  if tcpa_s < 0 then tcpa_s = 0 end -- future only

  local cx = rx + vrelx * tcpa_s
  local cy = ry + vrely * tcpa_s
  local cpa_m = math.sqrt(cx * cx + cy * cy)

  return m_to_nm(cpa_m), (tcpa_s / 60.0)
end

-- Danger cone (velocity obstacle): is v_rel pointing into the "collision cone"?
local function compute_danger_cone(rx, ry, vrelx, vrely, cpa_nm, tcpa_min)
  local Rm = rm.nm_to_m(CPA_CONE_NM)
  local d = math.sqrt(rx * rx + ry * ry)
  if d < 1e-3 then
    return true, math.pi, 0
  end

  if tcpa_min and tcpa_min > TCPA_CONE_MIN then
    return false, nil, nil
  end
  if cpa_nm and cpa_nm > CPA_CONE_NM then
    return false, nil, nil
  end

  -- must be closing: r·vrel < 0
  if (rx * vrelx + ry * vrely) >= 0 then
    return false, nil, nil
  end

  local alpha
  if d <= Rm then
    alpha = math.pi
  else
    alpha = math.asin(Rm / d)
  end

  -- cone center direction: towards ownship (r + 180°)
  local theta_r = math.atan2(rx, ry) -- 0=N
  local center = ang_wrap(theta_r + math.pi)

  local theta_v = ang_wrap(math.atan2(vrelx, vrely))
  local inside = math.abs(ang_diff(theta_v, center)) <= alpha

  return inside, alpha, center
end

local function draw_cone(cx, cy, radius_px, center_rad, alpha_rad)
  if not center_rad or not alpha_rad then return end
  local L = radius_px

  local a1 = center_rad - alpha_rad
  local a2 = center_rad + alpha_rad

  local x1 = cx + math.sin(a1) * L
  local y1 = cy - math.cos(a1) * L
  local x2 = cx + math.sin(a2) * L
  local y2 = cy - math.cos(a2) * L

  love.graphics.setColor(COL_DANGER)
  love.graphics.setLineWidth(2)
  draw_dotted_line(cx, cy, x1, y1, 8, 6)
  draw_dotted_line(cx, cy, x2, y2, 8, 6)
  love.graphics.setLineWidth(1)
  love.graphics.setColor(COL_WHITE)
end

-- =========================
-- Networking
-- =========================
local function connect()
  conn = assert(socket.tcp())
  conn:settimeout(3)
  assert(conn:connect(HOST, PORT))
  conn:settimeout(0) -- non-blocking
  conn:setoption("tcp-nodelay", true)
  conn:setoption("keepalive", true)
end

local function reconnect()
  pcall(function() if conn then conn:close() end end)
  conn = nil
  rxbuf = ""
  pcall(connect)
end

-- read bytes, split into lines
local function pump_lines(max_chunks)
  if not conn then return end

  for _ = 1, max_chunks do
    local chunk, err, partial = conn:receive(4096)
    local data = chunk or partial

    if data and #data > 0 then
      rxbuf = rxbuf .. data
    end

    if err == "closed" then
      reconnect()
      return
    end

    if err == "timeout" then
      break
    end

    while true do
      local nl = rxbuf:find("\n", 1, true)
      if not nl then break end
      local line = rxbuf:sub(1, nl - 1):gsub("\r$", "")
      rxbuf = rxbuf:sub(nl + 1)

      local msg = ais.feed_line(line)
      if msg and msg.mmsi then
        if msg.type == 5 then
          shipinfo[msg.mmsi] = { name = msg.name, callsign = msg.callsign, shiptype = msg.shiptype }
        elseif msg.lat and msg.lon then
          local info = shipinfo[msg.mmsi]
          if info and info.name then msg.name = info.name end
          msg.updated_at = os.time()
          targets[msg.mmsi] = msg
          if not selected_mmsi then selected_mmsi = msg.mmsi end
        end
      end
    end
  end
end

local function prune_targets()
  local now = os.time()
  for mmsi, t in pairs(targets) do
    if now - (t.updated_at or now) > MAX_AGE_S then
      targets[mmsi] = nil
      if selected_mmsi == mmsi then selected_mmsi = nil end
    end
  end
end

-- =========================
-- Ownship position
-- =========================
local function estimate_ownship_from_targets()
  -- very simple: center of bounding box (OK for demo),
  -- can be replaced by clustering if desired
  local minLat, maxLat =  90, -90
  local minLon, maxLon = 180, -180
  local n = 0

  for _, t in pairs(targets) do
    if t.lat and t.lon then
      minLat = math.min(minLat, t.lat)
      maxLat = math.max(maxLat, t.lat)
      minLon = math.min(minLon, t.lon)
      maxLon = math.max(maxLon, t.lon)
      n = n + 1
    end
  end

  if n >= 3 then
    own_lat = (minLat + maxLat) / 2.0
    own_lon = (minLon + maxLon) / 2.0
    own_valid = true
  end
end

local function advance_ownship_dead_reckoning(dt)
  if not own_valid then return end
  local v_ms = kn_to_ms(OWN_SOG_KN)
  local d_m = v_ms * dt

  local a = math.rad(OWN_COG_DEG)
  local dx = math.sin(a) * d_m
  local dy = math.cos(a) * d_m

  local R = 6371000.0
  local lat0 = math.rad(own_lat)
  local dlat = dy / R
  local dlon = dx / (R * math.cos(lat0))

  own_lat = own_lat + math.deg(dlat)
  own_lon = own_lon + math.deg(dlon)
end


-- =========================
-- Ownship estimation (demo)
-- =========================
local function estimate_ownship_from_targets()
  -- Estimate ownship as center of densest cluster (grid histogram).
  -- This keeps the demo "in the region" of the feed without needing GPS.
  local cell_deg = 0.2     -- ~12 NM in latitude. Tune 0.1..0.3
  local bins = {}
  local n_total = 0

  for _, t in pairs(targets) do
    if t.lat and t.lon then
      local clat = math.floor(t.lat / cell_deg)
      local clon = math.floor(t.lon / cell_deg)
      local key = clat .. ":" .. clon
      local b = bins[key]
      if not b then
        b = { n = 0, sumLat = 0.0, sumLon = 0.0 }
        bins[key] = b
      end
      b.n = b.n + 1
      b.sumLat = b.sumLat + t.lat
      b.sumLon = b.sumLon + t.lon
      n_total = n_total + 1
    end
  end

  if n_total < 10 then return end

  local best = nil
  for _, b in pairs(bins) do
    if (not best) or (b.n > best.n) then best = b end
  end
  if not best or best.n < 5 then return end

  local lat = best.sumLat / best.n
  local lon = best.sumLon / best.n

  if not own_valid then
    own_lat, own_lon = lat, lon
    own_valid = true
  else
    -- Slow smoothing to avoid drift in a stable scene
    own_lat = own_lat * 0.90 + lat * 0.10
    own_lon = own_lon * 0.90 + lon * 0.10
  end
end

-- =========================
-- Target list building
-- =========================
local function build_list()
  local list = {}

  -- Lookup selected item in current list (for details/COLREGS)
  local sel_item = nil
  if selected then
    for _, it in ipairs(list or {}) do
      if it.mmsi == selected then sel_item = it break end
    end
  end
  local sel_t = sel_item and sel_item.t or (selected and targets[selected] or nil)

  local ovx, ovy = vel_from_cog_sog(OWN_COG_DEG, OWN_SOG_KN)

  for mmsi, t in pairs(targets) do
    local x, y = rm.ll_to_xy_m(own_lat, own_lon, t.lat, t.lon)
    local dnm = rm.m_to_nm(math.sqrt(x * x + y * y))
    local brg = (math.deg(math.atan2(x, y)) + 360) % 360

    local cpa_nm, tcpa_min = nil, nil
    local danger, cone_alpha, cone_center = false, nil, nil

    local tvx, tvy = vel_from_cog_sog(t.cog, t.sog)
    if ovx and tvx then
      local vrelx = tvx - ovx
      local vrely = tvy - ovy
      cpa_nm, tcpa_min = compute_cpa_tcpa(x, y, vrelx, vrely)
      danger, cone_alpha, cone_center = compute_danger_cone(x, y, vrelx, vrely, cpa_nm, tcpa_min)
    end
    local in_range = (dnm <= RANGE_NM)
    local tcpa_soon = (tcpa_min ~= nil and tcpa_min <= TCPA_FILTER_MIN)

    list[#list + 1] = {
      mmsi = mmsi,
      t = t,
      x = x, y = y,
      dnm = dnm,
      brg = brg,
      cpa_nm = cpa_nm,
      tcpa_min = tcpa_min,
      danger = danger,
      cone_alpha = cone_alpha,
      cone_center = cone_center,
      in_range = in_range,
      tcpa_soon = tcpa_soon,
    }
  end

  -- Sort by smallest CPA first; unknown CPA at bottom
  table.sort(list, function(a, b)
    if a.cpa_nm and b.cpa_nm then
      if a.cpa_nm ~= b.cpa_nm then return a.cpa_nm < b.cpa_nm end
      if a.tcpa_min and b.tcpa_min and a.tcpa_min ~= b.tcpa_min then return a.tcpa_min < b.tcpa_min end
      return a.dnm < b.dnm
    end
    if a.cpa_nm and not b.cpa_nm then return true end
    if b.cpa_nm and not a.cpa_nm then return false end
    return a.dnm < b.dnm
  end)

  return list
end

-- Ensure selection always stays within top visible rows by resetting to top item
local function clamp_selection_to_visible(list)
  if #list == 0 then
    selected_mmsi = nil
    return
  end
  local visible = math.min(VISIBLE_ROWS, #list)
  local ok = false
  for i = 1, visible do
    if list[i].mmsi == selected_mmsi then ok = true break end
  end
  if not ok then selected_mmsi = list[1].mmsi end
end


local function filter_list_items(list_all)
  local out = {}
  for _, it in ipairs(list_all) do
    if it.in_range or it.tcpa_soon then
      out[#out + 1] = it
    end
  end
  return out
end

local function cycle_selection(dir)
  local list_all = build_list()
  local list = list_all or {}
  local sel_item = nil
  if selected then
    for _, it in ipairs(list) do
      if it and it.mmsi == selected then sel_item = it break end
    end
  end
  local sel_t = sel_item and sel_item.t or nil
  local list = filter_list_items(list_all)
  if #list == 0 then return end

  clamp_selection_to_visible(list)

  local visible = math.min(VISIBLE_ROWS, #list)
  local idx = 1
  for i = 1, visible do
    if list[i].mmsi == selected_mmsi then idx = i break end
  end

  idx = idx + dir
  if idx < 1 or idx > visible then
    selected_mmsi = list[1].mmsi
  else
    selected_mmsi = list[idx].mmsi
  end
end

-- =========================
-- Drawing helpers
-- =========================
local function set_color(c) love.graphics.setColor(c[1], c[2], c[3], c[4] or 1) end

local draw_tickmarks  -- forward declaration

local function draw_rings(cx, cy, radius)
  set_color(COL_DIM)
  love.graphics.circle("line", cx, cy, radius)
  draw_tickmarks(cx, cy, radius)
  love.graphics.circle("line", cx, cy, radius * 0.66)
  love.graphics.circle("line", cx, cy, radius * 0.33)
  love.graphics.line(cx - radius, cy, cx + radius, cy)
  love.graphics.line(cx, cy - radius, cx, cy + radius)
  set_color(COL_WHITE)
end

local function draw_motion_vector_display(cx, cy, radius, x_m, y_m, cog_deg, sog_kn)
  if not cog_deg or not sog_kn then return end



local function draw_motion_vector_display(cx, cy, radius, x_m, y_m, cog_deg, sog_kn)
  if COURSE_UP then
    local xr, yr = rotate_xy(x_m, y_m, -OWN_COG_DEG)
    -- direction should also be rotated by -OWN_COG_DEG to stay consistent on screen
    local cog_r = deg_wrap((cog_deg or 0) - OWN_COG_DEG)
    return draw_motion_vector(cx, cy, radius, xr, yr, cog_r, sog_kn)
  else
    return draw_motion_vector(cx, cy, radius, x_m, y_m, cog_deg, sog_kn)
  end
end

  -- Same scaling as targets: small vector, proportional to SOG
  local len_nm = math.min(2.0, sog_kn / 10.0)
  local len_m = rm.nm_to_m(len_nm)

  local a = math.rad(cog_deg)
  local vx = math.sin(a) * len_m
  local vy = math.cos(a) * len_m

  local sx = cx + (x_m / rm.nm_to_m(RANGE_NM)) * radius
  local sy = cy - (y_m / rm.nm_to_m(RANGE_NM)) * radius
  local ex = cx + ((x_m + vx) / rm.nm_to_m(RANGE_NM)) * radius
  local ey = cy - ((y_m + vy) / rm.nm_to_m(RANGE_NM)) * radius

  love.graphics.line(sx, sy, ex, ey)
end

-- =========================
-- Love2D callbacks
-- =========================
function love.load()
  -- HUD font (prefer mono if available)
  HUD_FONT = love.graphics.newFont(14)
  if love.filesystem.getInfo("DejaVuSansMono.ttf") then
    HUD_FONT_MONO = love.graphics.newFont("DejaVuSansMono.ttf", 14)
  else
    HUD_FONT_MONO = HUD_FONT
  end
  FONT_UI = love.graphics.getFont()
  FONT_BIG = love.graphics.newFont(24)
  FONT_MED = love.graphics.newFont(18)
  love.window.setMode(WINDOW_W, WINDOW_H, { resizable = true, vsync = true })
  love.window.setTitle("AIS Radar (SV Gratie)")
  app_t0 = love.timer.getTime()
  connect()
end

function love.update(dt)
  pump_lines(50)
  prune_targets()

  -- Ownship logic
  if own_mode == "UNLOCKED" then
    local now = love.timer.getTime()
    if (now - last_recenter) > 1.0 then
      estimate_ownship_from_targets()
      last_recenter = now
    end
    if own_valid and (love.timer.getTime() - app_t0) >= lock_after_s then
      own_mode = "LOCKED"
    end
  elseif own_mode == "FOLLOW" then
    local t = selected_mmsi and targets[selected_mmsi]
    if t and t.lat and t.lon then
      own_lat, own_lon = t.lat, t.lon
      own_valid = true
    end
  end

  -- Dead-reckoning unless FOLLOW (FOLLOW means "lock on target")
  if own_mode ~= "FOLLOW" then
    advance_ownship_dead_reckoning(dt)
  end
end

function love.keypressed(key)
  if key == "tab" or key == "right" or key == "down" or key == "j" then
    cycle_selection(1)
  elseif key == "left" or key == "up" or key == "k" then
    cycle_selection(-1)
  elseif key == "m" then
    own_mode = (own_mode == "FOLLOW") and "LOCKED" or "FOLLOW"
  elseif key == "u" then
    own_mode = "UNLOCKED"
    app_t0 = love.timer.getTime()
  elseif key == "pageup" then
    RANGE_NM = clamp(RANGE_NM * 1.5, RANGE_NM_MIN, RANGE_NM_MAX)
  elseif key == "pagedown" then
    RANGE_NM = clamp(RANGE_NM / 1.5, RANGE_NM_MIN, RANGE_NM_MAX)
  elseif key == "f" then
    local fs = love.window.getFullscreen()
    love.window.setFullscreen(not fs, "desktop")
  end
end


local function draw_details_panel(panel_x, y, w, h, sel_item, sel_t)
  -- Background
  set_color(COL_DIM)
  love.graphics.rectangle("line", panel_x + 8, y, w - 16, h)
  set_color(COL_WHITE)

  if not sel_item or not sel_t then
    love.graphics.print("No target selected", panel_x + 16, y + 14)
    return
  end

  local name = (sel_t.name and sel_t.name ~= "") and sel_t.name or "—"
  local mmsi = sel_item.mmsi or sel_t.mmsi or "—"

  local brg = sel_item.brg and string.format("%03.0f°", sel_item.brg) or "---°"
  local rng = sel_item.dnm and string.format("%.1f nm", sel_item.dnm) or "--.- nm"
  local sog = sel_t.sog and string.format("%.1f kn", sel_t.sog) or "--.- kn"
  local cog = sel_t.cog and string.format("%03.0f°", sel_t.cog) or "---°"
  local cpa = sel_item.cpa_nm and string.format("%.2f nm", sel_item.cpa_nm) or "--.-- nm"
  local tcpa = sel_item.tcpa_min and string.format("%.1f min", sel_item.tcpa_min) or "--.- min"

  local colregs = "UNKNOWN"
  if sel_item and sel_t then
    colregs = colregs_classification(sel_item.brg, sel_t.cog, sel_t.sog)
  end

  -- Title line in large font
  love.graphics.setFont(FONT_BIG or love.graphics.getFont())
  if sel_item.danger then
    set_color(COL_DANGER)
  else
    set_color(COL_WHITE)
  end
  love.graphics.print(name, panel_x + 16, y + 10)
  love.graphics.setFont(FONT_UI or love.graphics.getFont())
  set_color(COL_WHITE)

  local yy = y + 44
  love.graphics.print("MMSI: " .. tostring(mmsi), panel_x + 16, yy); yy = yy + 18
  love.graphics.print("BRG/RNG: " .. brg .. "  " .. rng, panel_x + 16, yy); yy = yy + 18
  love.graphics.print("SOG/COG: " .. sog .. "  " .. cog, panel_x + 16, yy); yy = yy + 18
  love.graphics.print("CPA/TCPA: " .. cpa .. "  " .. tcpa, panel_x + 16, yy); yy = yy + 18
  love.graphics.print("COLREGS: " .. colregs, panel_x + 16, yy); yy = yy + 18

  if sel_item.danger then
    set_color(COL_DANGER)
    love.graphics.print("! DANGER", panel_x + 16, y + h - 26)
    set_color(COL_WHITE)
  end
end


-- =========================
-- PACS-style corner overlays
-- =========================
local function draw_text_block(lines, x, y, align, padding, bg)
  padding = padding or 6
  local font = love.graphics.getFont()
  local lh = font:getHeight()
  local wmax = 0
  for _, s in ipairs(lines) do
    wmax = math.max(wmax, font:getWidth(s))
  end
  local h = #lines * lh
  local bx = x
  if align == "right" then
    bx = x - wmax - 2*padding
  end
  local by = y
  if bg then
    love.graphics.setColor(0,0,0,0.35)
    love.graphics.rectangle("fill", bx, by, wmax + 2*padding, h + 2*padding, 6, 6)
    love.graphics.setColor(1,1,1,1)
  end
  for i, s in ipairs(lines) do
    local tx = bx + padding
    if align == "right" then
      tx = bx + padding
    end
    love.graphics.print(s, tx, by + padding + (i-1)*lh)
  end
end

local function draw_corner_overlay(rect_x, rect_y, rect_w, rect_h, corner, lines, opts)
  -- PACS-style overlay block that stays inside the given rectangle.
  opts = opts or {}
  local pad = opts.pad or 8
  local bg_a = opts.bg_a or 0.55
  local fg = opts.fg or {1,1,1,1}
  local bg = opts.bg or {0,0,0,bg_a}
  local font = opts.font or HUD_FONT_MONO or love.graphics.getFont()
  local align = opts.align or "left" -- left|right

  love.graphics.setFont(font)

  local line_h = font:getHeight()
  local max_w = 0
  for i=1,#lines do
    local w = font:getWidth(lines[i] or "")
    if w > max_w then max_w = w end
  end
  local box_w = max_w + pad*2
  local box_h = (#lines * line_h) + pad*2

  local x, y
  if corner == "tl" then
    x = rect_x + 8
    y = rect_y + 8
  elseif corner == "tr" then
    x = rect_x + rect_w - box_w - 8
    y = rect_y + 8
  elseif corner == "bl" then
    x = rect_x + 8
    y = rect_y + rect_h - box_h - 8
  else -- "br"
    x = rect_x + rect_w - box_w - 8
    y = rect_y + rect_h - box_h - 8
  end

  -- clamp inside rectangle
  if x < rect_x + 2 then x = rect_x + 2 end
  if y < rect_y + 2 then y = rect_y + 2 end
  if x + box_w > rect_x + rect_w - 2 then x = rect_x + rect_w - box_w - 2 end
  if y + box_h > rect_y + rect_h - 2 then y = rect_y + rect_h - box_h - 2 end

  love.graphics.setColor(bg[1], bg[2], bg[3], bg[4])
  love.graphics.rectangle("fill", x, y, box_w, box_h, 6, 6)
  love.graphics.setColor(1,1,1,0.25)
  love.graphics.rectangle("line", x, y, box_w, box_h, 6, 6)

  love.graphics.setColor(fg[1], fg[2], fg[3], fg[4])
  for i=1,#lines do
    local s = lines[i] or ""
    local tx
    if align == "right" then
      tx = x + box_w - pad - font:getWidth(s)
    else
      tx = x + pad
    end
    local ty = y + pad + (i-1)*line_h
    love.graphics.print(s, tx, ty)
  end

  love.graphics.setColor(1,1,1,1)
end


local function draw_corner_overlay_test(radar_rect_x, radar_rect_y, radar_rect_w, radar_rect_h, tl_lines, tr_lines, bl_lines, br_lines)
  if tl_lines then draw_corner_overlay(radar_rect_x, radar_rect_y, radar_rect_w, radar_rect_h, "tl", tl_lines, {align="left"}) end
  if tr_lines then draw_corner_overlay(radar_rect_x, radar_rect_y, radar_rect_w, radar_rect_h, "tr", tr_lines, {align="right"}) end
  if bl_lines then draw_corner_overlay(radar_rect_x, radar_rect_y, radar_rect_w, radar_rect_h, "bl", bl_lines, {align="left"}) end
  if br_lines then draw_corner_overlay(radar_rect_x, radar_rect_y, radar_rect_w, radar_rect_h, "br", br_lines, {align="right"}) end
end

local function draw_corner_overlays(w, h, radar_x0, radar_x1)
  local pad = 20
  local radar_w = radar_x1 - radar_x0

  local orient = COURSE_UP and "COURSE-UP" or "NORTH-UP"
  local own_line = own_valid
    and string.format("OWN %.1fkn %03.0f°  %.4f, %.4f", OWN_SOG_KN, OWN_COG_DEG, own_lat, own_lon)
    or  string.format("OWN %.1fkn %03.0f°  (estimating pos…)", OWN_SOG_KN, OWN_COG_DEG)

  -- Top-left: like PACS patient/study header
  draw_text_block({
    string.format("%s", own_mode),
    own_line,
  }, radar_x0 + pad, pad, "left", 6, true)

  -- Top-right: like PACS study/date/tools summary
  draw_text_block({
    string.format("RANGE %.1f nm", RANGE_NM),
    string.format("%s", orient),
    string.format("LIST FILTER: in-range OR TCPA<=%.0f min", TCPA_FILTER_MIN),
  }, radar_x1 - pad, pad, "right", 6, true)

  -- Bottom-left: short controls
  draw_text_block({
    "TAB/←/→ select   PgUp/PgDn range",
    "M mode   U unlock   O orient",
  }, radar_x0 + pad, h - pad - 2*love.graphics.getFont():getHeight() - 12, "left", 6, true)

  -- Bottom-right: status counters
  draw_text_block({
    string.format("Targets %d", nz(target_count, 0)),
    string.format("Selected %s", selected and tostring(selected) or "—"),
  }, radar_x1 - pad, h - pad - 2*love.graphics.getFont():getHeight() - 12, "right", 6, true)
end

function love.draw()
  local w, h = love.graphics.getDimensions()

  local radar_rect_x = 0
  local radar_rect_y = 0
  local radar_rect_w = w - PANEL_W
  local radar_rect_h = h
  local panel_x = w - PANEL_W
  local radar_x0, radar_x1 = 0, panel_x
  local panel_x = w - PANEL_W
  local details_h = math.floor(h * 0.28)
  local details_y = h - details_h - 12
  local panel_w = 440
  local panel_x = nz(panel_x, w - panel_w)

  -- Details panel layout (safe defaults)
  local details_h = math.floor(h * 0.28)
  local details_y = h - details_h - 10
  local panel_x = w - PANEL_W
  local cx = (w - PANEL_W) / 2
  local cy = h / 2
  local radius = math.min((w - PANEL_W) * 0.45, h * 0.42)

  -- Radar frame
  set_color(COL_DIM)
  love.graphics.rectangle("line", 20, 20, w - PANEL_W - 40, h - 40)
  set_color(COL_WHITE)

  draw_rings(cx, cy, radius)

  -- Ownship marker + vector (same scale as targets)
  love.graphics.circle("fill", cx, cy, 4)
  set_color(COL_MOVING)
  draw_motion_vector_display(cx, cy, radius, 0, 0, OWN_COG_DEG, OWN_SOG_KN)
  set_color(COL_WHITE)

  -- Build list once (shared by radar + list)
  local list_all = build_list()
  local list = filter_list_items(list_all)
  clamp_selection_to_visible(list)

  -- Danger cone for selected target (if dangerous)
  do
    local sel
    for _, it in ipairs(list_all) do
      if it.mmsi == selected_mmsi then sel = it break end
    end
    if sel and sel.danger then
      draw_cone(cx, cy, radius, sel.cone_center, sel.cone_alpha)
    end
  end

  -- Draw targets on radar
  for _, it in ipairs(list_all) do
    local t = it.t
    if it.dnm <= RANGE_NM then
      local px = cx + (it.x / rm.nm_to_m(RANGE_NM)) * radius
      local py = cy - (it.y / rm.nm_to_m(RANGE_NM)) * radius

      local is_sel = (it.mmsi == selected_mmsi)
      local moving = (t.sog or 0) > MOVING_SOG_KN

      if it.danger then
        set_color(COL_DANGER)
      elseif moving then
        set_color(COL_MOVING)
      else
        set_color(COL_WHITE)
      end

      if is_sel then
        love.graphics.circle("line", px, py, 8)
      end

      local r = is_sel and 4 or (moving and 3 or 2)
      love.graphics.circle("fill", px, py, r)

      -- Motion vector
      draw_motion_vector_display(cx, cy, radius, it.x, it.y, t.cog, t.sog)

      set_color(COL_WHITE)
    end
  end

  -- Header text
--[[   love.graphics.print(("OWN(%s): %.1fkn %03.0f°  %.4f, %.4f"):format(
    own_mode, OWN_SOG_KN, OWN_COG_DEG, own_lat, own_lon
  ), 20, 5)
  love.graphics.print(("Range: %.1f nm   Filter: in-range OR TCPA<=%.0fmin"):format(RANGE_NM, TCPA_FILTER_MIN), 20, 25)
  local col = "UNKNOWN"
  if sel_item and sel_t then
    col = colregs_classification(sel_item.brg, sel_t.cog, sel_t.sog)
  end
  love.graphics.print("COLREGS: " .. col, panel_x + 10, details_y + 78)
  love.graphics.print("Keys: Tab/←/→ select, PgUp/PgDn range, M mode, U unlock", 20, 45) ]]

  -- Corner overlays (PACS-style)
  -- print(w, h, radar_x0, radar_x1)
  draw_corner_overlays(w, h, radar_x0, radar_x1,"1","2","3","4")

  -- Right list panel
  local panel_x = w - PANEL_W
  set_color(COL_DIM)
  love.graphics.rectangle("line", panel_x, 0, PANEL_W, h)
  love.graphics.line(panel_x, 0, panel_x, h)
  set_color(COL_WHITE)

  local px0 = panel_x + 10
  love.graphics.print("Targets (sorted by CPA)", px0, 10)

  local start_i = 1
  local end_i = math.min(#list, VISIBLE_ROWS)

  local y = 35
  for i = start_i, end_i do
    local it = list[i]
    local t = it.t
    local name = (t.name and t.name ~= "") and t.name or "—"

    local brg = string.format("%03.0f°", it.brg or 0)
    local sog = t.sog and string.format("%.1f", t.sog) or "--.-"
    local cog = t.cog and string.format("%03.0f", t.cog) or "---"
    local cpa = it.cpa_nm and string.format("%.2f", safe_num(it.cpa_nm, 0)) or "--"
    local tcpa = it.tcpa_min and string.format("%.1f", it.tcpa_min) or "--"

    local prefix = (it.mmsi == selected_mmsi) and ">" or "  "
    local line = string.format("%s%s %.1fnm BRG%s S%s C%s CPA%s T%s",
      prefix,
      format_fixed_length(get_ship_identity(name, it.mmsi), 14, ".."),
      it.dnm,
      brg, sog, cog, cpa, tcpa
    )

    if it.danger then
      set_color(COL_DANGER)
    else
      set_color(COL_WHITE)
    end
    love.graphics.print(line, px0, y)
    y = y + ROW_H
  end
  set_color(COL_WHITE)


    -- Selected target details (large, readable)
  local details_y = 35 + (VISIBLE_ROWS * ROW_H) + 12
  local details_h = h - details_y - 12
  if details_h > 80 and selected_mmsi then
    local sel = nil
    for _, it in ipairs(list_all) do
      if it.mmsi == selected_mmsi then sel = it break end
    end
    if sel then
      local t = sel.t
      local name = (t.name and t.name ~= "") and t.name or "—"
      local sog = t.sog and string.format("%.1f kn", t.sog) or "--.- kn"
      local cog = t.cog and string.format("%03.0f°", t.cog) or "---°"
      local brg = sel.brg and string.format("%03.0f°", sel.brg) or "---°"
      local rng = sel.dnm and string.format("%.2f nm", sel.dnm) or "-- nm"
      local cpa = sel.cpa_nm and string.format("%.2f nm", sel.cpa_nm) or "--"
      local tcpa = sel.tcpa_min and string.format("%.1f min", sel.tcpa_min) or "--"
      local pos = (t.lat and t.lon) and string.format("%.4f, %.4f", t.lat, t.lon) or "—"

      set_color(COL_DIM)
      love.graphics.rectangle("line", px0, details_y, PANEL_W - 20, details_h)
      set_color(COL_WHITE)

      love.graphics.setFont(FONT_BIG)
      if sel.danger then set_color(COL_DANGER) end
      love.graphics.print(name:sub(1, 22), px0 + 10, details_y + 8)
      set_color(COL_WHITE)

      love.graphics.setFont(FONT_MED)
      local line1 = string.format("MMSI %s   POS %s", tostring(selected_mmsi), pos)
      local line2 = string.format("RNG %s  BRG %s  SOG %s  COG %s", rng, brg, sog, cog)
      local line3 = string.format("CPA %s  TCPA %s\n%s", cpa, tcpa, sel.danger and "  ⚠ DANGER" or "")
      local line4 = string.format("COLREGS: .. %s", col)
      love.graphics.print(line1,              px0 + 10, details_y + 46)
      love.graphics.print(line2,              px0 + 10, details_y + 68)
      love.graphics.setFont(FONT_BIG)
      love.graphics.print(line3,              px0 + 10, details_y + 90)
      love.graphics.print(line4,              px0 + 10, details_y + 155)
      --love.graphics.print("COLREGS: " .. col, px0 + 10, details_y + 155)
      love.graphics.setFont(FONT_UI)
    end
  end
end

draw_tickmarks = function(cx, cy, radius)
  love.graphics.setColor(0.5, 0.5, 0.5, 0.8)
  for deg = 0, 330, 30 do
    local a = math.rad(deg)
    love.graphics.line(
      cx + math.sin(a) * radius * 0.95, cy - math.cos(a) * radius * 0.95,
      cx + math.sin(a) * radius,        cy - math.cos(a) * radius
    )
  end
  for deg = 0, 315, 45 do
    local a = math.rad(deg)
    love.graphics.line(
      cx + math.sin(a) * radius * 0.90, cy - math.cos(a) * radius * 0.90,
      cx + math.sin(a) * radius,        cy - math.cos(a) * radius
    )
  end
    -- Cardinal course labels
  local font = love.graphics.getFont()
  local function label(txt, ang_deg)
    local a = math.rad(ang_deg)
    local r = radius * 1.05
    local x = cx + math.sin(a) * r
    local y = cy - math.cos(a) * r
    local w = font:getWidth(txt)
    local h = font:getHeight()
    love.graphics.print(txt, x - w/2, y - h/2)
  end
  love.graphics.setColor(0.8, 0.8, 0.8, 0.9)
  label("0°",   0)
  label("90°",  90)
  label("180°", 180)
  label("270°", 270)
  love.graphics.setColor(1,1,1,1)
end
