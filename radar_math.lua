-- radar_math.lua
local M = {}

local R = 6371000.0

function M.ll_to_xy_m(lat0, lon0, lat, lon)
  -- equirectangular; prima voor 0-100 km rond ownship
  local phi0 = math.rad(lat0)
  local dlat = math.rad(lat - lat0)
  local dlon = math.rad(lon - lon0)
  local x = dlon * math.cos(phi0) * R
  local y = dlat * R
  return x, y -- x oost+, y noord+
end

function M.m_to_nm(m) return m / 1852.0 end
function M.nm_to_m(nm) return nm * 1852.0 end

return M
