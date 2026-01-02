-- main.lua (LOVE2D) – AIS Radar (refactored & hardened)

-- =========================
-- Modules
-- =========================
local socket = require("socket")
local ais    = require("ais_decode")
local rm     = require("radar_math")
local utf8   = require("utf8")

-- =========================
-- Global variables
-- =========================
local tp     = 0        -- tijd voor de pulserende dot

-- =========================
-- Robustness helpers
-- =========================
local function nz(v, d)          return (v ~= nil) and v or d end
local function safe_num(v, d)    return (type(v) == "number") and v or d end
local function safe_str(v, d)    return (v ~= nil) and tostring(v) or d end

-- Degrees/radians helpers
local function deg_wrap(d)
  d = d % 360
  if d < 0 then d = d + 360 end
  return d
end

local function deg_diff(a, b)
  -- smallest difference a-b in degrees in [-180, +180]
  return ((a - b + 180) % 360) - 180
end

local function ang_wrap(a)
  a = a % (2 * math.pi)
  if a < 0 then a = a + 2 * math.pi end
  return a
end

local function ang_diff(a, b)
  -- smallest difference in radians [-pi, +pi]
  return ((a - b + math.pi) % (2 * math.pi)) - math.pi
end

local function rotate_xy(x, y, ang_deg)
  -- Rotate (x east, y north) by +ang_deg about origin (screen-aligned)
  local a = math.rad(ang_deg)
  local ca, sa = math.cos(a), math.sin(a)
  return x * ca + y * sa, -x * sa + y * ca
end

-- =========================
-- Drawing helpers
-- =========================
local function draw_dotted_line(x1, y1, x2, y2, dash, gap)
  dash = dash or 6
  gap  = gap  or 4
  local dx, dy = x2 - x1, y2 - y1
  local len = math.sqrt(dx*dx + dy*dy)
  if len < 1 then return end

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

local function set_color(c) love.graphics.setColor(c[1], c[2], c[3], c[4] or 1) end

local MARITIME_THEME = {
    grid         = {0.3 , 0.35, 0.4 , 1.0 },
    bg           = {0.05, 0.07, 0.1 , 1.0 },
    own          = {1.0 , 1.0 , 1.0 , 1.0 },
    moving       = {0.0 , 0.9 , 0.4 , 1.0 },
    stationary   = {0.6 , 0.6 , 0.6 , 1.0 },
    danger       = {1.0 , 0.1 , 0.1 , 1.0 },
    pad_fill     = {1.0 , 0.2 , 0.2 , 0.15},
    default      = {1.0 , 1.0 , 1.0 , 1.0 },
    label_bg     = {0.0 , 0.0 , 0.0 , 0.45},
    label_txt    = {0.7 , 0.7 , 0.7 , 0.6 },
    tickmark     = {0.4 , 0.45, 0.5 , 0.6 }, -- Subtiel blauw-grijs voor de schaalverdeling
    label        = {0.8 , 0.75, 0.6 , 0.7 }, -- Gedimd Amber/Beige voor tekst (zeer rustig voor de ogen)
    panel_border = {0.5 , 0.55, 0.6 , 0.8 }, -- Een neutraal, technisch grijs (Steel Grey). De alpha op 0.8 zorgt dat het paneel subtiel versmelt met de achtergrond
    panel_bg     = {0.1 , 0.12, 0.15, 0.9 }  -- Voor de achtergrond van het paneel zelf (vulling)
}

-- Gebruik in je draw loop:
-- love.graphics.setColor(MARITIME_THEME.moving)
-- of korter nog
-- set_color(MARITIME_THEME.moving)
-- teken target...


-- Forward declaration
local draw_tickmarks

local function draw_ring_labels(cx, cy, radius_px, range_nm)
  if not range_nm or range_nm <= 0 then return end
  local font  = love.graphics.getFont()
  local lineh = font:getHeight()

  local function label_at(x, y, text, align_right)
    local tw, th = font:getWidth(text), lineh
    local pad = 3
    local bx = align_right and (x - tw - pad*2) or x
    local by = y - th/2

    -- set_color(MARITIME_THEME.label_bg)
    -- love.graphics.rectangle("fill", bx, by, tw + pad*2, th, 4, 4)

    set_color(MARITIME_THEME.label)
    love.graphics.print(text, bx + pad, by)
    set_color(MARITIME_THEME.default)
  end

  for _, f in ipairs({1/3, 2/3, 1}) do
    local r = radius_px * f
    local nm = range_nm * f
    local txt = string.format("%.1f nm", nm)
    label_at(cx + 6,    cy - r - 8, txt, false) -- N
    label_at(cx + r+ 8, cy + 11,    txt, false) -- E
    label_at(cx + 6,    cy + r + 8, txt, false) -- S
    label_at(cx - r- 8, cy + 11,    txt, true)  -- W
  end
end

local function draw_rings(cx, cy, radius, range_nm)
  --set_color({1,1,1,0.7})
  set_color(MARITIME_THEME.bg)
  love.graphics.circle("fill", cx, cy, radius)
  set_color(MARITIME_THEME.grid)
  love.graphics.circle("line", cx, cy, radius)
  love.graphics.circle("line", cx, cy, radius * 0.66)
  love.graphics.circle("line", cx, cy, radius * 0.33)
  love.graphics.line(cx - radius, cy, cx + radius, cy)
  love.graphics.line(cx, cy - radius, cx, cy + radius)
  set_color(MARITIME_THEME.default)

  draw_tickmarks(cx, cy, radius)
  draw_ring_labels(cx, cy, radius, range_nm)
end

-- Draw motion vector (in world meters) for a target at (x_m, y_m)
local function draw_motion_vector_display(cx, cy, radius, x_m, y_m, cog_deg, sog_kn, range_nm, course_up, own_cog_deg)
  if not cog_deg or not sog_kn then return end
  local len_nm = math.min(2.0, sog_kn / 10.0)
  local len_m  = rm.nm_to_m(len_nm)

  -- Vector in world meters
  local a  = math.rad(cog_deg)
  local vx = math.sin(a) * len_m
  local vy = math.cos(a) * len_m

  -- Rotate for course-up view (both point and vector)
  if course_up then
    x_m, y_m = rotate_xy(x_m, y_m, -own_cog_deg)
    vx,  vy  = rotate_xy(vx,  vy,  -own_cog_deg)
  end

  local range_m = rm.nm_to_m(range_nm)
  local sx = cx + (x_m / range_m) * radius
  local sy = cy - (y_m / range_m) * radius
  local ex = cx + ((x_m + vx) / range_m) * radius
  local ey = cy - ((y_m + vy) / range_m) * radius

  love.graphics.line(sx, sy, ex, ey)
end

local function draw_cone_oud(cx, cy, radius_px, center_rad, alpha_rad)
  if not center_rad or not alpha_rad then return end
  local L  = radius_px
  local a1 = center_rad - alpha_rad
  local a2 = center_rad + alpha_rad
  local x1 = cx + math.sin(a1) * L
  local y1 = cy - math.cos(a1) * L
  local x2 = cx + math.sin(a2) * L
  local y2 = cy - math.cos(a2) * L
  love.graphics.setColor(1.0, 0.2, 0.2, 1)
  love.graphics.setLineWidth(1)
  draw_dotted_line(cx, cy, x1, y1, 8, 6)
  draw_dotted_line(cx, cy, x2, y2, 8, 6)
  love.graphics.setLineWidth(1)
  love.graphics.setColor(1,1,1,1)
end

local function draw_cone(cx, cy, radius_px, center_rad, alpha_rad)
  if not center_rad or not alpha_rad then return end

  local a1, a2 = center_rad - alpha_rad, center_rad + alpha_rad
  local L      = radius_px

  -- 1. Teken de lichtrode gloed (het vlak)
  -- 'pie' zorgt ervoor dat de vorm sluit in het middelpunt
  -- De -math.pi/2 zorgt dat de arc de sin/cos berekening van de lijnen volgt
  -- love.graphics.setColor(1.0, 0.2, 0.2, 0.15)
  set_color(MARITIME_THEME.pad_fill)
  love.graphics.arc("fill", "pie", cx, cy, L, a1 - math.pi/2, a2 - math.pi/2)

  -- 2. Bereken eindpunten voor de lijnen
  local x1, y1 = cx + math.sin(a1) * L, cy - math.cos(a1) * L
  local x2, y2 = cx + math.sin(a2) * L, cy - math.cos(a2) * L

  -- 3. Teken de rode stippellijnen (de randen)
  -- set_color(MARITIME_THEME.danger)
  love.graphics.setLineWidth(0.5)
  draw_dotted_line(cx, cy, x1, y1, 8, 6)
  draw_dotted_line(cx, cy, x2, y2, 8, 6)

  -- Reset kleur naar standaard wit
  set_color(MARITIME_THEME.default)
end

-- =========================
-- Configuration
-- =========================
-- local HOST, PORT = "153.44.253.27", 5631
local HOST, PORT = "127.0.0.1", 10110

local WINDOW_W, WINDOW_H = 1024, 600
local PANEL_W            = 460
local VISIBLE_ROWS       = 14
local ROW_H              = 26

local MAX_AGE_S          = 180
local RANGE_NM_MIN, RANGE_NM_MAX = 1, 96
local RANGE_NM           = 24.0

-- Ownship demo DR
local OWN_SOG_KN         = 6.0
local OWN_COG_DEG        = 45.0

-- Orientation
local COURSE_UP = false

-- Danger settings
local DANGER_BLINK_TCPA_MIN   = 5.0
local DANGER_BLINK_PERIOD_S   = 0.6

-- Fonts (init in love.load)
local FONT_UI, FONT_BIG, FONT_MED, HUD_FONT, HUD_FONT_MONO

-- Target styling
local MOVING_SOG_KN = 0.5

-- List filter
local TCPA_FILTER_MIN = 15.0

-- Danger cone params
local CPA_CONE_NM   = 0.5
local TCPA_CONE_MIN = 15.0

-- Colors
local COL_WHITE  = {1, 1, 1, 1}
local COL_MOVING = {0.2, 1.0, 0.2, 1}
local COL_DANGER = {1.0, 0.2, 0.2, 1}
local COL_DIM    = {1, 1, 1, 0.7}

-- =========================
-- State
-- =========================
local conn
local rxbuf = ""
local targets   = {}  -- mmsi -> latest dynamic target {lat,lon,sog,cog,...}
local shipinfo  = {}  -- mmsi -> {name=..., callsign=..., ...}
local selected_mmsi = nil
local own_lat, own_lon = 60.0, 5.0
local own_valid = false

-- Ownship mode: UNLOCKED (estimate), LOCKED (freeze), FOLLOW (center on selected)
local own_mode      = "UNLOCKED"
local lock_after_s  = 5.0
local app_t0        = 0
local last_recenter = 0

-- =========================
-- Small math helpers
-- =========================
local function clamp(v, lo, hi)
  if v < lo then return lo end
  if v > hi then return hi end
  return v
end

local function kn_to_ms(kn)   return kn * 1852.0 / 3600.0 end
local function m_to_nm(m)     return m  / 1852.0 end

local function vel_from_cog_sog(cog_deg, sog_kn)
  if cog_deg == nil or sog_kn == nil then return nil end
  local v = kn_to_ms(sog_kn)
  local a = math.rad(cog_deg) -- 0=N, 90=E
  return math.sin(a) * v, math.cos(a) * v -- vx east, vy north
end

-- =========================
-- CPA / TCPA
-- =========================
local function compute_cpa_tcpa(rx, ry, vrelx, vrely)
  local v2 = vrelx*vrelx + vrely*vrely
  if v2 < 1e-6 then
    return m_to_nm(math.sqrt(rx*rx + ry*ry)), nil
  end
  local dot = rx*vrelx + ry*vrely
  local tcpa_s = -dot / v2
  if tcpa_s < 0 then tcpa_s = 0 end -- future only
  local cx = rx + vrelx * tcpa_s
  local cy = ry + vrely * tcpa_s
  local cpa_m = math.sqrt(cx*cx + cy*cy)
  return m_to_nm(cpa_m), (tcpa_s / 60.0)
end

-- ============================================================
-- CPA / TCPA met Passage-indicator (Voor/Achter)
-- rx, ry: Relatieve positie van target (m)
-- vrelx, vrely: Relatieve snelheid (m/s)
-- heading_rad: Koers eigen schip in radialen (0 = Noord, CW+)
-- ============================================================
local function compute_cpa_tcpa_extended(rx, ry, vrelx, vrely, heading_rad)
  local v2 = vrelx*vrelx + vrely*vrely
  
  -- Als relatieve snelheid nul is, is er geen TCPA (statische afstand)
  if v2 < 1e-6 then
    return m_to_nm(math.sqrt(rx*rx + ry*ry)), nil, "n.v.t."
  end

  -- Bereken TCPA (in seconden)
  local dot = rx*vrelx + ry*vrely
  local tcpa_s = -dot / v2
  if tcpa_s < 0 then tcpa_s = 0 end -- Alleen toekomstgericht

  -- Bereken relatieve positie van target op het moment van CPA (cx, cy)
  local cx = rx + vrelx * tcpa_s
  local cy = ry + vrely * tcpa_s
  local cpa_m = math.sqrt(cx*cx + cy*cy)

  -- Bepaal passage: voorlangs of achterlangs
  -- Bereken de absolute hoek naar het target op CPA
  local angle_cpa = math.atan2(cx, cy) 
  
  -- Bereken de relatieve peiling t.o.v. de eigen koers
  local relative_bearing = angle_cpa - heading_rad
  
  -- Normaliseer de hoek naar [-PI, PI]
  while relative_bearing > math.pi do relative_bearing = relative_bearing - 2*math.pi end
  while relative_bearing < -math.pi do relative_bearing = relative_bearing + 2*math.pi end

  -- Interpretatie: -90° tot +90° is de voorzijde (voor de dwarslijn)
  local passage = "achterlangs"
  if math.abs(relative_bearing) < (math.pi / 2) then
    passage = "voorlangs"
  end
  -- print(m_to_nm(cpa_m), (tcpa_s / 60.0), passage)
  -- Resultaten: CPA (nm), TCPA (min), Passage (string)
  return m_to_nm(cpa_m), (tcpa_s / 60.0), passage
end

--[[ Uitleg van de aanpassingen:

    Input heading_rad: De koers van je eigen schip is nodig om te weten wat "voor" en "achter" is.
    Relatieve Positie (cx, cy): We gebruiken de coördinaten van het target op het moment van de CPA.
    Relatieve Peiling: We berekenen het verschil tussen de hoek naar het target en je eigen koers.
    Passage Logica:
        Voorlangs: Als het target zich op het moment van CPA binnen 90 graden van je boeg bevindt (voor de "beam"), passeert het voorlangs.
        Achterlangs: Als de relatieve hoek groter is dan 90 graden, bevindt het target zich achter je dwarslijn op het moment van passeren.  ]]

-- Danger cone (velocity obstacle) : is v_rel pointing into the "collision cone"?
local function compute_danger_cone_v1(rx, ry, vrelx, vrely, cpa_nm, tcpa_min)
  local Rm = rm.nm_to_m(CPA_CONE_NM)
  local d  = math.sqrt(rx*rx + ry*ry)
  if d < 1e-3 then return true, math.pi, 0 end
  if tcpa_min and tcpa_min > TCPA_CONE_MIN then return false end
  if cpa_nm and cpa_nm > CPA_CONE_NM then   return false end
  -- must be closing: r·vrel < 0
  if (rx*vrelx + ry*vrely) >= 0 then return false end

  local alpha = (d <= Rm) and math.pi or math.asin(Rm / d) -- half-angle
  -- cone center direction: towards ownship (r + 180 degrees)
  local theta_r  = math.atan2(rx, ry) -- 0=N
  local center   = ang_wrap(theta_r + math.pi)
  local theta_v  = ang_wrap(math.atan2(vrelx, vrely))
  local inside   = math.abs(ang_diff(theta_v, center)) <= alpha
  return inside, alpha, center
end
-- deze versie van de berekening geeft ook terug op hoeveel NM de CPA ligt
local function compute_danger_cone(rx, ry, vrelx, vrely, cpa_nm, tcpa_min)
  local Rm = rm.nm_to_m(CPA_CONE_NM)
  local d  = math.sqrt(rx*rx + ry*ry)
  
  -- Basis checks
  if d < 1e-3 then return true, math.pi, 0, 0 end
  if tcpa_min and tcpa_min > TCPA_CONE_MIN then return false end
  if cpa_nm and cpa_nm > CPA_CONE_NM then return false end
  if (rx*vrelx + ry*vrely) >= 0 then return false end

  -- Kegel berekening
  local alpha = (d <= Rm) and math.pi or math.asin(Rm / d)
  local theta_r = math.atan2(rx, ry)
  local center = ang_wrap(theta_r + math.pi)
  local theta_v = ang_wrap(math.atan2(vrelx, vrely))
  local inside = math.abs(ang_diff(theta_v, center)) <= alpha

  -- NIEUW: Bereken de lengte van de taartpunt tot aan het CPA-punt
  -- Afstand = relatieve snelheid * tijd tot CPA
  local v_rel_mag = math.sqrt(vrelx*vrelx + vrely*vrely)
  local length_m = v_rel_mag * (tcpa_min * 60) -- v_rel (m/s) * sec
  local length_nm = rm.m_to_nm(length_m)

  return inside, alpha, center, length_nm
end

local function compute_PAD_cone(own_x, own_y, target_x, target_y, target_vx, target_vy, cpa_limit_nm)
    -- Input Parameters 
    -- own_x, own_y: Meters.                                (Dit zijn de cartesiaanse coördinaten van je eigen schip op je lokale grid).
    -- target_x, target_y: Meters.                          (De positie van het andere schip in hetzelfde grid).
    -- target_vx, target_vy: Meters per seconde (\(m/s\)).  (De True Velocity vector van het doelschip).
    -- cpa_limit_nm: Zeemijl (NM).                          (De veiligheidsmarge die je zelf instelt, bijv. 1.0 of 2.0). 
    -- 
    -- Output Parameters 
    -- is_danger: Boolean.                                  (true als je huidige koers de PAD snijdt).
    -- alpha: Radialen.                                     (De halve openingshoek van de kegel).
    -- center: Radialen.                                    (De richting waar de kegel naar wijst, waarbij \(0\) meestal Noord is).
    -- length_nm: Zeemijl (NM).                             (De visuele lengte van de taartpunt).

    -- 1. Relatieve positie van target t.o.v. eigen schip
    local dx = target_x - own_x
    local dy = target_y - own_y
    local dist = math.sqrt(dx*dx + dy*dy)
    
    -- 2. Veiligheidsmarge in meters (CPA limiet)
    local Rm = rm.nm_to_m(cpa_limit_nm)
    
    -- 3. Bereken de openingshoek (alpha) gebaseerd op de veiligheidsstraal
    -- Hoe dichterbij het target, hoe breder de PAD wordt
    local alpha = 0
    if dist > Rm then
        alpha = math.asin(Rm / dist)
    else
        alpha = math.pi -- We zitten al binnen de gevarenzone
    end

    -- 4. Bereken de richting van de PAD
    -- In een PAD-model wijst de center-line van de kegel 
    -- in de richting van de koers van het TARGET (True Motion)
    local target_course = math.atan2(target_vx, target_vy)
    local center = target_course -- De PAD 'stroomt' mee met de beweging van het target
    
    -- 5. Bereken de lengte van de PAD
    -- De PAD moet ver genoeg reiken om jouw eigen vector te kunnen snijden.
    -- Een praktische lengte is 2x de huidige afstand of de radar-range.
    local length_nm = rm.m_to_nm(dist) * 1.5

    -- 6. Check of je eigen koers momenteel in de PAD ligt
    local own_course = math.atan2(OWN_VX, OWN_VY)
    local is_danger = math.abs(ang_diff(own_course, center)) <= alpha

    return is_danger, alpha, center, length_nm
end

-- =========================
-- COLREGS classification (top-level so all can call)
-- =========================
local function colregs_classification(brg_true_deg, t_cog_deg, t_sog_kn)
  if not brg_true_deg then return "UNKNOWN" end
  local rb  = deg_wrap(brg_true_deg - OWN_COG_DEG) -- 0=dead ahead; 90=starboard; 180=astern; 270=port
  local tsog = t_sog_kn
  local tcog = t_cog_deg

  -- Overtaking: target abaft the beam and faster
  if tsog and tsog > (OWN_SOG_KN + 0.5) and rb > 112.5 and rb < 247.5 then
    return "OVERTAKING (YOU ARE STAND-ON)"
  end

  -- Head-on: nearly ahead and reciprocal-ish course
  if tcog then
    local reciprocal = deg_wrap(OWN_COG_DEG + 180)
    if (rb <= 10 or rb >= 350) and math.abs(deg_diff(tcog, reciprocal)) <= 25 then
      return "HEAD-ON (BOTH ALTER TO STBD)"
    end
  end

  -- Crossing
  if rb > 0 and rb < 112.5 then
    return "CROSSING (TARGET ON STBD: YOU GIVE WAY)"
  elseif rb > 247.5 and rb < 360 then
    return "CROSSING (TARGET ON PORT: YOU STAND ON)"
  end

  return "OTHER / UNDETERMINED"
end

-- =========================
-- Networking
-- =========================
local function connect()
  local ok, err
  conn, err = socket.tcp()
  if not conn then return nil, err end
  conn:settimeout(3)
  ok, err = conn:connect(HOST, PORT)
  if not ok then
    conn:close()
    conn = nil
    return nil, err
  end
  conn:settimeout(0) -- non-blocking
  pcall(function() conn:setoption("tcp-nodelay", true) end)
  pcall(function() conn:setoption("keepalive", true)   end)
  return true
end

local function reconnect()
  pcall(function() if conn then conn:close() end end)
  conn  = nil
  rxbuf = ""
  connect()
end

-- Read bytes, split into lines, feed AIS
local function pump_lines(max_chunks)
  if not conn then return end
  for _ = 1, max_chunks do
    local chunk, err, partial = conn:receive(4096)
    -- print(chunk, err, partial)
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
-- Ownship estimation / dead reckoning
-- =========================
local function estimate_ownship_from_targets()
-- 3,0,244690728,5,-128.0,0.0,1,4.5024600,E,52.1912467,N,360.0,511,52,0,0,1
-- 3,0,244690728,5,-128.0,0.0,1,4.5024633,E,52.1912483,N,360.0,511,53,0,0,1
-- 3,0,244690728,5,-128.0,0.0,1,4.5024600,E,52.1912367,N,360.0,511,53,0,0,1
  -- Densest-cluster estimate via grid histogram
  local cell_deg = 0.2
  local bins = {}
  local n_total = 0
  for _, t in pairs(targets) do
    if t.lat and t.lon then
      print("lat/lon: ",t.lat, t.lon)
      local clat = math.floor(t.lat / cell_deg)
      local clon = math.floor(t.lon / cell_deg)
      local key = clat .. ":" .. clon
      local b = bins[key]
      if not b then b = { n = 0, sumLat = 0.0, sumLon = 0.0 } ; bins[key] = b end
      b.n      = b.n + 1
      b.sumLat = b.sumLat + t.lat
      b.sumLon = b.sumLon + t.lon
      n_total  = n_total + 1
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
    own_lat = own_lat * 0.90 + lat * 0.10
    own_lon = own_lon * 0.90 + lon * 0.10
  end
end

local function advance_ownship_dead_reckoning(dt)
  if not own_valid then return end
  local v_ms = kn_to_ms(OWN_SOG_KN)
  local d_m  = v_ms * dt
  local a    = math.rad(OWN_COG_DEG)
  local dx   = math.sin(a) * d_m
  local dy   = math.cos(a) * d_m
  local R    = 6371000.0
  local lat0 = math.rad(own_lat)
  local dlat = dy / R
  local dlon = dx / (R * math.cos(lat0))
  own_lat = own_lat + math.deg(dlat)
  own_lon = own_lon + math.deg(dlon)
end

-- =========================
-- Ship UI helpers
-- =========================
local function get_ship_identity(name, mmsi)
  if name and name ~= "" and name ~= "—" then return name end
  return tostring(mmsi or "Unknown")
end

local function format_fixed_length_oud(str, len, indicator)
  str = tostring(str or "")
  indicator = indicator or ".."
  len = math.max(0, len)
  local str_len = utf8.len(str) or #str
  local ind_len = utf8.len(indicator) or #indicator
  if str_len > len then
    if len > ind_len then
      return str:sub(1, len - ind_len) .. indicator  -- byte-based; acceptable for monospaced UI here
    else
      return str:sub(1, len)
    end
  end
  return string.format("%-" .. len .. "s", str)
end

--- Formatteert een string naar een exact vaste lengte.
local function format_fixed_length(str, len, indicator)
    str = tostring(str or "")
    indicator = indicator or ".."
    len = math.max(0, len)

    -- Gebruik utf8.len voor correcte telling van speciale tekens (zoals '…' of '©')
    -- Als je geen UTF8 library hebt, gebruik dan #str
    local utf8 = require("utf8")
    local str_len = utf8.len(str) or #str
    local ind_len = utf8.len(indicator) or #indicator

    if str_len > len then
        -- Afkappen: Zorg dat indicator past
        if len > ind_len then
            -- Let op: string.sub werkt op bytes, we gebruiken hier een simpele sub 
            -- maar voor 100% veiligheid met UTF8 is een sub-helper beter.
            return str:sub(1, len - ind_len) .. indicator
        else
            return str:sub(1, len)
        end
    end

    -- De 'magie': %-s lijnt links uit, de %*s vult aan met spaties tot de gewenste lengte
    -- Dit vervangt string.rep en is intern sneller.
    return string.format("%-" .. len .. "s", str)
end

local function format_fixed_length_2026(str, len, indicator)
    str = tostring(str or "")
    indicator = indicator or ".."
    len = math.max(0, len)

    local utf8 = require("utf8")
    -- Bereken de werkelijke teken-lengte
    local str_len = utf8.len(str) or #str
    local ind_len = utf8.len(indicator) or #indicator

    if str_len > len then
        -- Gebruik een loop om veilig UTF-8 karakters te tellen bij het afkappen
        local stop_pos = 0
        local current_char = 0
        local target_chars = math.max(0, len - ind_len)
        
        for p, _ in utf8.codes(str) do
            if current_char == target_chars then break end
            stop_pos = p
            current_char = current_char + 1
        end
        return str:sub(1, stop_pos) .. indicator
    end

    -- Handmatige padding: string.format werkt niet met UTF-8 tekens
    local padding = len - str_len
    return str .. string.rep(" ", padding)
end


-- =========================
-- List & selection
-- =========================
local function build_list()
  local list = {}
  local ovx, ovy = vel_from_cog_sog(OWN_COG_DEG, OWN_SOG_KN)

  for mmsi, t in pairs(targets) do
    local x, y = rm.ll_to_xy_m(own_lat, own_lon, t.lat, t.lon)
    local dnm  = rm.m_to_nm(math.sqrt(x*x + y*y))
    local brg  = (math.deg(math.atan2(x, y)) + 360) % 360

    local cpa_nm, tcpa_min = nil, nil
    local danger, cone_alpha, cone_center = false, nil, nil
    local cone_radius = 0
    local passage_txt = "onbekend"

    local tvx, tvy = vel_from_cog_sog(t.cog, t.sog)
    if ovx and tvx then
      local vrelx = tvx - ovx
      local vrely = tvy - ovy
      -- bereken cpa en tcpa
      -- cpa_nm, tcpa_min = compute_cpa_tcpa(x, y, vrelx, vrely)
      -- bereken cpa, tcpa en passage (in tekst)
      cpa_nm, tcpa_min, passage_txt = compute_cpa_tcpa_extended(x, y, vrelx, vrely, math.rad(OWN_COG_DEG))
      danger, cone_alpha, cone_center, cone_radius = compute_danger_cone(x, y, vrelx, vrely, cpa_nm, tcpa_min)
      -- let op dat deze functie andere input parameters vraagt
      -- danger, cone_alpha, cone_center, cone_radius = compute_PAD_cone(x, y, vrelx, vrely, cpa_nm, tcpa_min)
    end

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
      cone_radius = cone_radius,
      in_range = (dnm <= RANGE_NM),
      tcpa_soon = (tcpa_min ~= nil and tcpa_min <= TCPA_FILTER_MIN),
      passage = passage_txt
    }
  end

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

local function clamp_selection_to_visible(list)
  if #list == 0 then
    selected_mmsi = nil
    return
  end
  local visible = math.min(VISIBLE_ROWS, #list)
  for i = 1, visible do
    if list[i].mmsi == selected_mmsi then return end
  end
  selected_mmsi = list[1].mmsi
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
-- UI blocks
-- =========================
local function draw_text_block(lines, x, y, align, padding, bg)
  padding = padding or 6
  local font = love.graphics.getFont()
  local lh   = font:getHeight()
  local wmax = 0
  for _, s in ipairs(lines) do
    wmax = math.max(wmax, font:getWidth(s))
  end
  local h = #lines * lh
  local bx = x
  if align == "right" then bx = x - wmax - 2*padding end
  local by = y
  if bg then
    --love.graphics.setColor(0,0,0,0.35)
    set_color(MARITIME_THEME.label_bg)
    love.graphics.rectangle("fill", bx, by, wmax + 2*padding, h + 2*padding, 6, 6)
    set_color(MARITIME_THEME.default)
    --love.graphics.setColor(1,1,1,1)
  end
  for i, s in ipairs(lines) do
    local tx = bx + padding
    love.graphics.print(s, tx, by + padding + (i-1)*lh)
  end
end

function decimalToDMSLat(decimalLat)
    -- 1. Controleer op nil of ongeldige types (bijv. strings)
    local val = tonumber(decimalLat)
    if not val then 
        return "0° 00' 0.00\" N" -- Return een veilige default waarde
    end

    -- 2. Bepaal halfrond (0 wordt als Noord behandeld)
    local hemisphere = "N"
    if val < 0 then
        hemisphere = "S"
        val = math.abs(val)
    end

    -- 3. Bereken graden, minuten en seconden
    local degrees = math.floor(val)
    local minutesDecimal = (val - degrees) * 60
    local minutes = math.floor(minutesDecimal)
    local seconds = (minutesDecimal - minutes) * 60

    -- 4. Formatteer resultaat 
    -- %.2f rondt automatisch af naar 2 decimalen in de string
    return string.format("%d° %02d' %.1f\" %s", degrees, minutes, seconds, hemisphere)
end

-- Function to convert decimal longitude to Degrees, Minutes, Seconds (DMS) format
function decimalLonToDMS(decimalLon)
    -- 1. Controleer op nil of ongeldige types (bijv. strings die geen getal zijn)
    local val = tonumber(decimalLon)
    
    -- 2. Als de waarde ongeldig is of exact 0, geef een veilige default terug
    if not val or val == 0 then
        return "0° 00' 0.00\" E"
    end

    -- 3. Bepaal de richting (E of W)
    local direction = (val >= 0) and "E" or "W"
    local absLon = math.abs(val)

    -- 4. Bereken graden (geheel getal)
    local degrees = math.floor(absLon)

    -- 5. Bereken minuten
    local minutesDecimal = (absLon - degrees) * 60
    local minutes = math.floor(minutesDecimal)

    -- 6. Bereken seconden
    local seconds = (minutesDecimal - minutes) * 60
    
    -- 7. Formatteer resultaat
    -- %.2f zorgt voor automatische afronding naar 2 decimalen
    return string.format("%d° %02d' %.1f\" %s", degrees, minutes, seconds, direction)
end

local function draw_corner_overlays(w, h, radar_x0, radar_x1)
  local pad      = 20
  local orient   = COURSE_UP and "COURSE-UP" or "NORTH-UP"

  -- TL
  -- 1. Bepaal de positie-regel (Robuust en overzichtelijk)
  local pos_info = "OWN POS: (estimating...)"
  if own_valid then
      pos_info = string.format("OWN POS: %s  %s", decimalToDMSLat(own_lat), decimalLonToDMS(own_lon))
  end

  -- 2. Stel het tekstblok samen (Gegroepeerd per categorie)
  -- Gebruik hoofdletters voor labels voor een professionele ARPA-look
  local text_lines = {
      string.format("%s (%s)", own_mode, orient), -- Modus en oriëntatie op één regel
      "",                                          -- Witregel voor rust
      string.format("SOG: %5.1f kn", OWN_SOG_KN),  -- Uitgelijnde cijfers
      string.format("COG: %05.1f°",  OWN_COG_DEG),
      "",                                          -- Witregel voor rust
      pos_info                                     -- Positie onderaan
  }

  -- 3. Teken het blok
  draw_text_block(text_lines, radar_x0 + pad, pad, "left", 6, true)


  -- TR
  local pad = 20
  local right_x = radar_x1 - pad

  -- Gebruik een consistente opbouw: Status -> Instelling -> Filter
  local radar_status = {
      string.format("RANGE: %.1f NM", RANGE_NM),
      orient, -- Bijv. "NORTH-UP" of "COURSE-UP"
      "",     -- Subtiele witregel voor scheiding
      string.format("FILTER: TCPA < %.0f'", TCPA_FILTER_MIN),
  }

  draw_text_block(radar_status, right_x, pad, "right", 6, true)


  -- BL
  local fh = love.graphics.getFont():getHeight()
  local y_pos = h - pad - 3*fh - 12

  -- Gebruik een overzichtelijke indeling met duidelijke groepering
  local hotkeys = {
      "TAB/←/→: Select Target  •  PgUp/Dn: Range",
      "L: Mode  U: Unlock  O: Orient  F: Fullscreen",
      "J:-COG K:+COG I:+SOG M:-SOG"
  }

  -- Teken het blok met iets meer witruimte tussen de regels (line height = 1.2)
  draw_text_block(hotkeys, radar_x0 + pad, y_pos, "left", 6, true)


  -- BR
  -- 1. Efficiënte target telling
  local target_count = 0
  for _ in pairs(targets) do target_count = target_count + 1 end

  -- 2. Bepaal de geselecteerde waarde (gebruik 'NONE' of '—' voor rust)
  local target_id = selected_mmsi and tostring(selected_mmsi) or "—"

  -- 3. Teken het blok (Rechts uitgelijnd)
  local footer_y = h - pad - (2 * fh) - 12
  draw_text_block({
      string.format("TGT COUNT: %d", target_count),
      string.format("SELECTED: %s", target_id),
  }, radar_x1 - pad, footer_y, "right", 6, true)

end

local function draw_details_panel(panel_x, y, w, h, sel_item, sel_t)
  
  set_color(MARITIME_THEME.panel_border)
  love.graphics.rectangle("line", panel_x + 8, y, w - 16, h)
  set_color(MARITIME_THEME.default)

  if not sel_item or not sel_t then
    love.graphics.print("No target selected", panel_x + 16, y + 14)
    return
  end

--[[   local function format_line(label, val1, val2)
      -- Gebruik string.format met een vaste breedte voor labels (bijv. 9 tekens)
      return string.format("%-9s %-9s %s", label, val1, val2 or "")
  end ]]

  local name = (sel_t.name and sel_t.name ~= "") and sel_t.name or "—"
  local mmsi = tostring(sel_item.mmsi or sel_t.mmsi or "—")

--[[   local brg  = sel_item.brg  and string.format("%03.0f°", sel_item.brg) or "---°"
  local rng  = sel_item.dnm  and string.format("%.1f nm", sel_item.dnm) or "--.- nm"
  local sog  = sel_t.sog     and string.format("%.1f kn", sel_t.sog)    or "--.- kn"
  local cog  = sel_t.cog     and string.format("%03.0f°", sel_t.cog)    or "---°"
  local cpa  = sel_item.cpa_nm   and string.format("%.2f nm", sel_item.cpa_nm)  or "--.-- nm"
  local tcpa = sel_item.tcpa_min  and string.format("%.1f min", sel_item.tcpa_min) or "--.- min" ]]

  -- Gebruik vaste formaten voor getallen zodat ze niet 'dansen' bij updates
  local brg  = string.format("%03.0f°", sel_item.brg or 0)
  local rng  = string.format("%4.1f nm", sel_item.dnm or 0)
  local sog  = string.format("%4.1f kn", sel_t.sog or 0)
  local cog  = string.format("%03.0f°", sel_t.cog or 0)
  local cpa  = string.format("%4.2f nm", sel_item.cpa_nm or 0)
  local tcpa = string.format("%4.1f min", sel_item.tcpa_min or 0)

  local colregs = colregs_classification(sel_item.brg, sel_t.cog, sel_t.sog)

  love.graphics.setFont(FONT_BIG or love.graphics.getFont())
  if sel_item.danger then set_color(MARITIME_THEME.danger) else set_color(MARITIME_THEME.default) end
  love.graphics.print(get_ship_identity(name, mmsi), panel_x + 16, y + 10)

  love.graphics.setFont(FONT_UI or love.graphics.getFont())
  set_color(MARITIME_THEME.default)
  local yy = y + 44
  local line_h = 20 -- Iets meer witruimte tussen de regels voor 2026 UX

  -- UX Goud: Splits labels en waarden in kleur
  local function draw_data_row(label, value, y_pos)
      set_color(MARITIME_THEME.label_txt)  -- Gedimd grijs/amber
      love.graphics.print(label, panel_x + 16, y_pos)
      set_color(MARITIME_THEME.label)     -- Helder off-white
      love.graphics.print(value, panel_x + 100, y_pos)   -- Vaste inspringing voor waarden
  end

  draw_data_row("MMSI",   mmsi                  , yy); yy = yy + line_h
  draw_data_row("BRG/RNG", brg .. " / " .. rng  , yy); yy = yy + line_h
  draw_data_row("SOG/COG", sog .. " / " .. cog  , yy); yy = yy + line_h
  draw_data_row("CPA/TCPA", cpa .. " / " .. tcpa, yy); yy = yy + line_h
  draw_data_row("COLREGS", colregs              , yy); yy = yy + line_h
  draw_data_row("passeert", sel_item.passage    , yy); yy = yy + line_h
  
  

  if sel_item.danger then
    set_color(MARITIME_THEME.danger)
    love.graphics.print("! DANGER !", panel_x + 16, yy)
    set_color(MARITIME_THEME.default)
  end
end

-- =========================
-- LOVE callbacks
-- =========================
function love.load()
  -- Fonts
  HUD_FONT = love.graphics.newFont(14)
  if love.filesystem.getInfo("DejaVuSansMono.ttf") then
    HUD_FONT_MONO = love.graphics.newFont("DejaVuSansMono.ttf", 14)
    FONT_BIG      = love.graphics.newFont("DejaVuSansMono.ttf", 24)
    FONT_MED      = love.graphics.newFont("DejaVuSansMono.ttf", 18)
  else
    HUD_FONT_MONO = HUD_FONT
    FONT_BIG      = love.graphics.newFont(24)
    FONT_MED      = love.graphics.newFont(18)
  end
  FONT_UI = HUD_FONT_MONO

  love.window.setMode(WINDOW_W, WINDOW_H, { resizable = true, vsync = true })
  love.window.setTitle("AIS Radar (SV Gratie)")
  app_t0 = love.timer.getTime()
  connect()
end

function love.update(dt)
  pump_lines(50)
  prune_targets()

  tp = tp + dt

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

  -- Dead-reckoning unless FOLLOW
  if own_mode ~= "FOLLOW" then
    advance_ownship_dead_reckoning(dt)
  end

  -- Definieer de snelheid van de verandering (bijv. 30 graden per seconde)
  local turn_speed = 20 

  -- Controleer of de toets fysiek ingedrukt wordt gehouden
  if love.keyboard.isDown("j") then
      OWN_COG_DEG = OWN_COG_DEG - turn_speed * dt
  elseif love.keyboard.isDown("k") then
      OWN_COG_DEG = OWN_COG_DEG + turn_speed * dt
  end

  -- Houd de koers tussen 0 en 360 graden (UX: voorkom negatieve getallen)
  OWN_COG_DEG = (OWN_COG_DEG + 360) % 360
end

function love.keypressed(key)
  if key == "tab" or key == "right" or key == "down"  then
    cycle_selection(1)

  elseif key == "left" or key == "up"  then
    cycle_selection(-1)

  elseif key == "j" then          -- 2 graden naar bakboord
    OWN_COG_DEG = OWN_COG_DEG - 2
    if OWN_COG_DEG < 0 then OWN_COG_DEG = OWN_COG_DEG + 360 end

  elseif key == "k" then          -- 2 graden naar stuurboord
    OWN_COG_DEG = OWN_COG_DEG + 2
    if OWN_COG_DEG > 360 then OWN_COG_DEG = OWN_COG_DEG - 360 end
  elseif key == "i" then          -- 1 knoop sneller
    OWN_SOG_KN = OWN_SOG_KN + 0.5

  elseif key == "m" then          -- 1 knoop langzamer
    OWN_SOG_KN = OWN_SOG_KN - 0.5
    if OWN_SOG_KN < 0 then OWN_SOG_KN = 0 end

  elseif key == "l" then
    own_mode = (own_mode == "FOLLOW") and "LOCKED" or "FOLLOW"

  elseif key == "u" then
    own_mode = "UNLOCKED"
    app_t0   = love.timer.getTime()

  elseif key == "o" then
    COURSE_UP = not COURSE_UP

  elseif key == "pageup" then
    RANGE_NM = math.floor(clamp(RANGE_NM * 1.5, RANGE_NM_MIN, RANGE_NM_MAX) / 3 + 0.5) * 3

  elseif key == "pagedown" then
    -- Uitzondering: als we onder de 3 zakken, dwing dan de 1.5 af
    if RANGE_NM == 3 then
      RANGE_NM = 1.5
    elseif RANGE_NM == 1.5 then
      RANGE_NM = 1.5
    else
      -- Bereken de verkleinde range
      local nieuwe_range = clamp(RANGE_NM / 1.5, RANGE_NM_MIN, RANGE_NM_MAX)
      -- Pas de "snap-naar-3" logica toe
      RANGE_NM = math.floor(nieuwe_range / 3 + 0.5) * 3
    end

  elseif key == "f" then
    local fs = love.window.getFullscreen()
    love.window.setFullscreen(not fs, "desktop")
  end
end
--[[
    Converteert zeemijl naar pixels gebaseerd op de huidige radarinstellingen.
    @param dist_nm: De afstand in zeemijl die getekend moet worden.
    @param range_nm: De huidige schaalinstelling van de radar (bijv. 1.5, 3, 6 NM).
    @param radar_radius_px: De straal van het radarbeeld op je scherm in pixels.
    @return De afstand in pixels.
]]
local function nm_to_px(dist_nm, range_nm, radar_radius_px)
    -- Voorkom delen door nul
    if not range_nm or range_nm <= 0 then return 0 end
    
    -- Bereken hoeveel pixels één zeemijl waard is (pixels per NM)
    local px_per_nm = radar_radius_px / range_nm
    
    return dist_nm * px_per_nm
end

function love.draw()
  local w, h = love.graphics.getDimensions()

  -- Geometry
  local panel_x  = w - PANEL_W
  local radar_x0 = 0
  local radar_x1 = panel_x
  local cx = (w - PANEL_W) / 2
  local cy = h / 2
  local radius = math.min((w - PANEL_W) * 0.45, h * 0.42)

  -- Radar frame
  set_color(MARITIME_THEME.panel_border)
  love.graphics.rectangle("line", 20, 20, w - PANEL_W - 40, h - 40)
  set_color(MARITIME_THEME.default)
  draw_rings(cx, cy, radius, RANGE_NM)



  -- Build lists once (shared)
  local list_all = build_list()
  local list     = filter_list_items(list_all)
  clamp_selection_to_visible(list)

--[[   -- Danger cone for selected target
  do
    local sel
    for _, it in ipairs(list_all) do
      if it.mmsi == selected_mmsi then sel = it break end 
    end
    if sel and sel.danger then      -- alleen als geselecteerd en gevaarlijk
    --if  sel.danger then                -- alleen als gevaarlijk
      -- teken cone vanuit center (is ownship)
      -- draw_cone(cx, cy, radius, sel.cone_center, sel.cone_alpha)

      -- teken cone vanuit selected target
      local x_t, y_t = sel.x, sel.y
      local range_m = rm.nm_to_m(RANGE_NM)
      -- range_m, cx, x_m)
      local px = cx + (x_t / range_m) * radius
      local py = cy - (y_t / range_m) * radius

      
      -- Voorbeeld gebruik in je draw loop:
      -- Stel je radarbeeld is 600x600 pixels, dan is de straal 300.
      local radius_px = nm_to_px(sel.cone_radius, RANGE_NM, radius)
      draw_cone(px, py, radius_px, sel.cone_center, sel.cone_alpha)
    end
  end ]]

  -- Danger cone for all dangerous  targeta
  do
    local sel
    for _, it in ipairs(list_all) do
      if it.danger then      -- alleen als geselecteerd en gevaarlijk
        -- teken cone vanuit  target
        local x_t, y_t = it.x, it.y
        local range_m = rm.nm_to_m(RANGE_NM)
        local px = cx + (x_t / range_m) * radius
        local py = cy - (y_t / range_m) * radius
        local radius_px = nm_to_px(it.cone_radius, RANGE_NM, radius)
        draw_cone(px, py, radius_px, it.cone_center, it.cone_alpha)
      end
    end
  end

  -- Draw targets
  local range_m = rm.nm_to_m(RANGE_NM)
  for _, it in ipairs(list_all) do
    if it.dnm <= RANGE_NM then
      local x_m, y_m = it.x, it.y
      if COURSE_UP then
        x_m, y_m = rotate_xy(x_m, y_m, -OWN_COG_DEG)
      end
      local px = cx + (x_m / range_m) * radius
      local py = cy - (y_m / range_m) * radius

      local t = it.t
      local is_sel = (it.mmsi == selected_mmsi)
      local moving = (t.sog or 0) > MOVING_SOG_KN

      if it.danger then
        -- set_color(MARITIME_THEME.danger)
        local name = (t.name and t.name ~= "") and t.name or "—"
        love.graphics.print(get_ship_identity(name, it.mmsi), px + 10, py + 10)
        -- maak een rood pulserende punt
        local pulse = 0.65 + math.sin(tp * 4) * 0.35
        love.graphics.setColor(1, 0, 0, pulse)
      elseif moving then
        set_color(MARITIME_THEME.moving)
      else
        set_color(MARITIME_THEME.stationary)
      end

      if is_sel then love.graphics.circle("line", px, py, 8) end
      local r = is_sel and 4 or (moving and 3 or 2)
      love.graphics.circle("fill", px, py, r)
      

      -- Motion vector (world coords)
      draw_motion_vector_display(cx, cy, radius, it.x, it.y, t.cog, t.sog, RANGE_NM, COURSE_UP, OWN_COG_DEG)
      set_color(MARITIME_THEME.default)
    end
  end

    -- Ownship marker + vector
  love.graphics.circle("fill", cx, cy, 4)
  
  set_color(MARITIME_THEME.moving)
  draw_motion_vector_display(cx, cy, radius, 0, 0, OWN_COG_DEG, OWN_SOG_KN, RANGE_NM, COURSE_UP, OWN_COG_DEG)
  set_color(MARITIME_THEME.default)

  -- Corner overlays
  draw_corner_overlays(w, h, radar_x0, radar_x1)

  -- Right list panel
  set_color(MARITIME_THEME.panel_border)
  love.graphics.rectangle("line", panel_x, 0, PANEL_W, h)
  love.graphics.line(panel_x, 0, panel_x, h)
  set_color(MARITIME_THEME.default)
  local px0 = panel_x + 5
  love.graphics.print("Targets (sorted by CPA)", px0, 10)

  -- lijst met targets
  local start_i = 1
  local end_i   = math.min(#list, VISIBLE_ROWS)
  local y = 35
  for i = start_i, end_i do
    local it = list[i]
    local t  = it.t
    local name = (t.name and t.name ~= "") and t.name or "—"

    local dist = string.format("%.1fnm", it.dnm or 0)
    local brg  = string.format("%03.0f°", it.brg or 0)
    local sog  = t.sog and string.format("%.1f", t.sog) or "--.-"
    local cog  = t.cog and string.format("%03.0f", t.cog) or "---"
    local cpa  = it.cpa_nm and string.format("%.1f", safe_num(it.cpa_nm, 0)) or "--"
    local tcpa = it.tcpa_min and string.format("%.1f", it.tcpa_min) or "--"
    local prefix   = (it.mmsi == selected_mmsi) and ">" or " "
    local identity = format_fixed_length(get_ship_identity(name, it.mmsi), 11, "..")

    local line = string.format(
      "%s %-11s %6s B:%-4s S:%-4s C:%-3s CPA:%-4s T:%-4s",
      prefix, identity, dist, brg, sog, cog, cpa, tcpa
    )
    local moving = (t.sog or 0) > MOVING_SOG_KN
    if it.danger then 
      set_color(MARITIME_THEME.danger) 
    elseif moving then
      set_color(MARITIME_THEME.moving)
    else
      set_color(MARITIME_THEME.stationary) 
    end
    love.graphics.print(line, px0, y)
    y = y + ROW_H
  end
  set_color(MARITIME_THEME.default)

  -- Selected target big details
  local height = love.graphics.getHeight()
  if height > 768 then VISIBLE_ROWS = 20 end

  local details_y = 35 + (VISIBLE_ROWS * ROW_H) + 12
  local details_h = h - details_y - 12
  if details_h > 80 and selected_mmsi then
    local sel
    for _, it in ipairs(list_all) do if it.mmsi == selected_mmsi then sel = it break end end
    if sel then
      draw_details_panel(px0, details_y, PANEL_W - 20, details_h, sel, sel.t)
    end
  end
end

draw_tickmarks = function(cx, cy, radius)
  set_color(MARITIME_THEME.tickmark)
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
  -- Cardinal labels (true)
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
  
  set_color(MARITIME_THEME.label)
  label("0° N",   0)
  label("90° O",  90)
  label("180° S", 180)
  label("270° W", 270)
  set_color(MARITIME_THEME.default)
end
