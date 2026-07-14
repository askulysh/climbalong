#!/usr/bin/python3

import requests
from shapely.geometry import LineString, Point
from shapely.ops import substring, transform
import pyproj
import folium
from folium.plugins import LocateControl
import urllib.parse
import xml.etree.ElementTree as ET
import re
import csv
import os
import argparse
import time
import unicodedata
import math
import json

# === CONFIGURATION ===
buffer_km = 10  # default distance around route to search for crags (km)
max_distance_m = 10


def _load_car_config(path=None):
    if path is None:
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "car.json")
    with open(path, encoding="utf-8") as f:
        data = json.load(f)
    return float(data["consumption"]), float(data["fuel_cost"])


consumption, fuel_cost = _load_car_config()

CRAG_SEGMENT_KM = 250
OVERPASS_URLS = [
    "https://overpass-api.de/api/interpreter",
    "https://overpass.kumi.systems/api/interpreter",
]
OVERPASS_HEADERS = {"User-Agent": "route-climbing-fetcher"}
A8_BASE = "https://www.8a.nu"
A8_MATCH_RADIUS_KM = 10
TOILET_SEARCH_RADIUS_KM = 10
P4N_BASE = "https://guest.park4night.com/services/V4.1"
P4N_WEB_BASE = "https://park4night.com/en"
P4N_SEARCH_RADIUS_KM = 10
P4N_PARKING_CODES = frozenset({"P", "A"})
P4N_HEADERS = {"User-Agent": "route-climbing-fetcher"}
A8_LINK_RE = re.compile(
    r'<a href="(/crags/sportclimbing/[^"]+/routes(?:\?[^"]*)?)"[^>]*>([^<]+)</a>',
    re.I)
A8_PAYLOAD_RE = re.compile(
    r'"([^"]+)","([a-z0-9][a-z0-9-]*)","([^"]+)","([a-z0-9][a-z0-9-]*)",'
    r'(?:(?!"\{)[\s\S]){0,600}?\{"latitude":\d+,"longitude":\d+\},([\d.]+),([\d.]+)')
A8_ROUTE_ROW_RE = re.compile(r'<tr[^>]*data-v[^>]*>(.*?)</tr>', re.S)
A8_GRADE_RE = re.compile(r'^[56789][abc]?\+?$')
FRENCH_GRADES = [
    "5", "5a", "5a+", "5b", "5b+", "5c", "5c+",
    "6a", "6a+", "6b", "6b+", "6c", "6c+",
    "7a", "7a+", "7b", "7b+", "7c", "7c+",
    "8a", "8a+", "8b", "8b+", "8c", "8c+",
    "9a", "9a+", "9b", "9b+",
]
OSM_GRADE_SYSTEMS = ("french", "uiaa", "saxon", "norwegian", "yds_class")
A8_CACHE_FIELDS = [
    "name", "country", "lat", "lon", "url",
    "routes_total", "grade_min", "grade_max",
    "routes_6a_6b", "routes_7a_7b", "routes_7c_8a",
]
A8_COUNTRY_SLUG = {
    "DE": "germany",
    "AT": "austria",
    "IT": "italy",
    "FR": "france",
    "ES": "spain",
    "GR": "greece",
    "CH": "switzerland",
    "PL": "poland",
    "CZ": "czechia",
    "SK": "slovakia",
    "SI": "slovenia",
    "HR": "croatia",
    "HU": "hungary",
    "RO": "romania",
    "BG": "bulgaria",
    "UA": "ukraine",
    "GB": "united-kingdom",
    "US": "united-states",
    "NO": "norway",
    "SE": "sweden",
    "FI": "finland",
    "PT": "portugal",
    "BE": "belgium",
    "NL": "netherlands",
    "LU": "luxembourg",
    "TR": "turkey",
}

#routes = 3

# === STEP 1: Geocode cities (Nominatim) ===
def _city_cache_key(city_name):
    return re.sub(r"\s+", " ", city_name.strip()).casefold()


def city_cache_load(csv_filename):
    """Load forward-geocode cache keyed by normalized city name."""
    cache = {}
    if not os.path.exists(csv_filename):
        return cache
    with open(csv_filename, newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            try:
                city = (row.get("city") or "").strip()
                if not city:
                    continue
                lon = float(row["lon"])
                lat = float(row["lat"])
                cache[_city_cache_key(city)] = (lon, lat, city)
            except (ValueError, KeyError):
                continue
    print(f"📂 Loaded {len(cache)} city locations from {csv_filename}")
    return cache


def city_cache_save(cache, csv_filename):
    """Persist forward-geocode city locations to CSV."""
    with open(csv_filename, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=["city", "lon", "lat"])
        writer.writeheader()
        for key in sorted(cache):
            lon, lat, city = cache[key]
            writer.writerow({"city": city, "lon": lon, "lat": lat})
    print(f"💾 City location cache saved: {csv_filename}")


def geocode(city_name, city_cache=None):
    """Forward-geocode a city name to (lon, lat). Uses city_cache when provided."""
    key = _city_cache_key(city_name)
    if city_cache is not None and key in city_cache:
        lon, lat, _ = city_cache[key]
        print(f"City cache hit: {city_name} → {lat:.4f},{lon:.4f}")
        return lon, lat
    url = "https://nominatim.openstreetmap.org/search"
    params = {"q": city_name, "format": "json", "limit": 1}
    resp = requests.get(url, params=params,
                        headers={"User-Agent": "route-climbing-fetcher"})
    resp.raise_for_status()
    data = resp.json()
    if not data:
        raise ValueError(f"City not found: {city_name}")
    lon = float(data[0]["lon"])
    lat = float(data[0]["lat"])
    if city_cache is not None:
        city_cache[key] = (lon, lat, city_name.strip())
    return lon, lat


def is_indoor_gym(tags):
    return (
        "building" in tags
        or tags.get("leisure") in ("sports_centre", "playground", "pitch")
        or tags.get("fee") == "yes"
        or "opening_hours" in tags
    )


def website_from_tags(tags):
    url = tags.get("website") or tags.get("contact:website")
    if not url:
        return None
    url = url.strip()
    if url and not url.startswith(("http://", "https://")):
        url = "https://" + url
    return url


def _sanitize_city_token(city_name):
    token = city_name.split(",")[0].strip()
    token = re.sub(r"[^A-Za-z0-9]+", "_", token)
    return token.strip("_") or "city"


def route_basename(start_city, end_city):
    return f"{_sanitize_city_token(start_city)}_{_sanitize_city_token(end_city)}"


def is_known_crag(tags):
    for key, value in tags.items():
        if not value or not str(value).strip():
            continue
        if key == "climbing:url" or key.startswith("climbing:url:"):
            return True
    if is_indoor_gym(tags):
        return False
    if tags.get("url") or tags.get("climbing:grade"):
        return True
    return bool(website_from_tags(tags))


def filter_locations(in_buffer, variant):
    if variant == "crags":
        return [el for el in in_buffer
                if not is_indoor_gym(el.get("tags", {}))]
    if variant == "gym":
        return in_buffer
    if variant == "known":
        return [el for el in in_buffer
                if is_known_crag(el.get("tags", {}))]
    raise ValueError(f"Unknown variant: {variant}")


def create_base_map(center_lat, center_lon):
    m = folium.Map(location=[center_lat, center_lon], zoom_start=6, tiles=None)
    folium.TileLayer(
        tiles="https://{s}.basemaps.cartocdn.com/light_all/{z}/{x}/{y}{r}.png",
        name="CartoDB Positron (Local File Compatible)",
        attr='&copy; <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a> contributors &copy; <a href="https://carto.com/attributions">CARTO</a>'
    ).add_to(m)
    folium.TileLayer(
        tiles="https://tile.openstreetmap.org/{z}/{x}/{y}.png",
        name="OpenStreetMap (Requires Web Server)",
        attr='&copy; <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a> contributors',
        referrerPolicy="no-referrer-when-downgrade"
    ).add_to(m)
    LocateControl(
        auto_start=False,
        position="topleft",
        strings={"title": "My location", "popup": "You are here"},
        locateOptions={"enableHighAccuracy": True, "maxZoom": 16},
    ).add_to(m)
    return m


def add_route_layers(m, routes, route_buffer, search_buffer_km, route_colors,
                     start_lat, start_lon, end_lat, end_lon,
                     city_start, city_end):
    for i, r in enumerate(routes):
        route_coords = r["geometry"]["coordinates"]
        route_ = [(lat, lon) for lon, lat in route_coords]
        color = route_colors[i % len(route_colors)]
        folium.PolyLine(route_, color=color, weight=3, opacity=0.8,
                        tooltip=f"Route {i + 1}").add_to(m)

    buffer_coords = list(route_buffer.exterior.coords)
    folium.Polygon([(lat, lon) for lon, lat in buffer_coords],
                   color="green", weight=1, fill=True, fill_opacity=0.1,
                   tooltip=f"Search area ±{search_buffer_km} km").add_to(m)

    start_popup = (
        f"<b>Start: {city_start}</b><br>"
        f"{_nav_links_html(start_lat, start_lon, city_start)}"
    )
    end_popup = (
        f"<b>End: {city_end}</b><br>"
        f"{_nav_links_html(end_lat, end_lon, city_end)}"
    )
    folium.Marker(
        [start_lat, start_lon],
        popup=folium.Popup(start_popup, max_width=320),
        icon=folium.Icon(color="green"),
    ).add_to(m)
    folium.Marker(
        [end_lat, end_lon],
        popup=folium.Popup(end_popup, max_width=320),
        icon=folium.Icon(color="blue"),
    ).add_to(m)


def _nav_links_html(lat, lon, name=None):
    dest = f"{lat},{lon}"
    gmaps = f"https://www.google.com/maps/dir/?api=1&destination={dest}"
    label = urllib.parse.quote(name) if name else dest
    geo = f"geo:{lat},{lon}?q={lat},{lon}({label})"
    return (
        f'<a href="{gmaps}" target="_blank">Google Maps</a> | '
        f'<a href="{geo}">Android nav</a>'
    )


def add_toll_markers(fmap, nearby_tolls):
    for t in nearby_tolls:
        osm_link = f"https://www.openstreetmap.org/node/{t['id']}"
        popup_html = f"""
        <b>{t['name']}</b><br>
        Fee: {t['fee']} {t['currency']}<br>
        <a href="{osm_link}" target="_blank">OpenStreetMap</a><br>
        {_nav_links_html(t['lat'], t['lon'], t['name'])}
        """
        folium.Marker(
            [t["lat"], t["lon"]],
            popup=folium.Popup(popup_html, max_width=320),
            tooltip=f"{t['name']} ({t['fee']} {t['currency']})",
            icon=folium.Icon(color="blue", icon="road", prefix="fa")
        ).add_to(fmap)


def _crag_name_from_tags(tags):
    return tags.get("int_name", tags.get("name:en", tags.get("name")))


def _norm_crag_name(name):
    s = unicodedata.normalize("NFKD", name)
    s = "".join(c for c in s if not unicodedata.combining(c))
    return re.sub(r"\s+", " ", s).strip().casefold()


def _a8_search_name(name):
    """Strip OSM 'sector ' prefix before 8a.nu search/match."""
    if not name:
        return name
    s = name.strip()
    if re.match(r"^sector\s+", s, re.I):
        return re.sub(r"^sector\s+", "", s, count=1, flags=re.I).strip()
    return s


def _slugify(name):
    s = unicodedata.normalize("NFKD", name)
    s = "".join(c for c in s if not unicodedata.combining(c))
    s = s.casefold()
    return re.sub(r"[^a-z0-9]+", "-", s).strip("-")


def _a8_cache_key(name, country_slug=None, lat=None, lon=None):
    lat_k = round(lat, GEOCODE_CACHE_DECIMALS) if lat is not None else ""
    lon_k = round(lon, GEOCODE_CACHE_DECIMALS) if lon is not None else ""
    return (_norm_crag_name(name), country_slug or "", lat_k, lon_k)


def _a8_cache_key_parts(key):
    """Unpack cache key as (name, country, lat_k, lon_k); legacy keys are 2-tuples."""
    if len(key) == 2:
        name, country = key
        return name, country, "", ""
    name, country, lat_k, lon_k = key
    return name, country, lat_k, lon_k


def _a8_normalize_entry(val):
    if isinstance(val, dict):
        return val
    return {"url": val}


def _a8_lookup_entry(name, cache, country_slug=None, lat=None, lon=None):
    """Return cached 8a entry dict if unambiguous; else None."""
    norm = _norm_crag_name(name)
    key = _a8_cache_key(name, country_slug, lat, lon)
    if key in cache:
        return _a8_normalize_entry(cache[key])
    if country_slug is not None or (lat is not None and lon is not None):
        key2 = (norm, country_slug or "", "", "")
        if key2 in cache:
            return _a8_normalize_entry(cache[key2])
    by_name = [
        _a8_normalize_entry(v) for k, v in cache.items()
        if _a8_cache_key_parts(k)[0] == norm]
    if len(by_name) == 1:
        return by_name[0]
    return None


def _a8_find_cache_key(name, cache, country_slug=None, lat=None, lon=None):
    norm = _norm_crag_name(name)
    key = _a8_cache_key(name, country_slug, lat, lon)
    if key in cache:
        return key
    key2 = (norm, country_slug or "", "", "")
    if key2 in cache:
        return key2
    matches = [k for k in cache if _a8_cache_key_parts(k)[0] == norm]
    if len(matches) == 1:
        return matches[0]
    return None

def _a8_lookup_cached(name, cache, country_slug=None, lat=None, lon=None):
    entry = _a8_lookup_entry(name, cache, country_slug, lat, lon)
    return entry["url"] if entry else None


def _haversine_km(lat1, lon1, lat2, lon2):
    r = 6371.0
    p = math.pi / 180
    dlat = (lat2 - lat1) * p
    dlon = (lon2 - lon1) * p
    a = (math.sin(dlat / 2) ** 2
         + math.cos(lat1 * p) * math.cos(lat2 * p) * math.sin(dlon / 2) ** 2)
    return 2 * r * math.asin(math.sqrt(a))


def _entry_within_radius(entry, lat, lon, radius_km=A8_MATCH_RADIUS_KM):
    elat = entry.get("lat")
    elon = entry.get("lon")
    if elat is None or elon is None:
        return False
    return _haversine_km(lat, lon, elat, elon) <= radius_km


def _french_grade_index(grade):
    g = grade.strip().lower()
    try:
        return FRENCH_GRADES.index(g)
    except ValueError:
        return None


def _grade_in_range(grade, low, high):
    i = _french_grade_index(grade)
    if i is None:
        return False
    return _french_grade_index(low) <= i <= _french_grade_index(high)


def _summarize_route_grades(grades):
    valid = [g for g in grades if _french_grade_index(g) is not None]
    if not valid:
        return None
    indices = [_french_grade_index(g) for g in valid]
    return {
        "routes_total": len(valid),
        "grade_min": FRENCH_GRADES[min(indices)],
        "grade_max": FRENCH_GRADES[max(indices)],
        "routes_6a_6b": sum(1 for g in valid if _grade_in_range(g, "6a", "6b+")),
        "routes_7a_7b": sum(1 for g in valid if _grade_in_range(g, "7a", "7b+")),
        "routes_7c_8a": sum(1 for g in valid if _grade_in_range(g, "7c", "8a")),
    }


def _parse_8a_routes_grades(html):
    grades = []
    for row in A8_ROUTE_ROW_RE.findall(html):
        cells = re.findall(r'>([^<]{1,20})<', row)
        if cells and A8_GRADE_RE.match(cells[0]):
            grades.append(cells[0])
    return grades


def fetch_8a_route_stats(direct_url):
    base = direct_url.rstrip("/")
    path = base.split("?", 1)[0]
    if path.endswith("/routes"):
        routes_url = base
    else:
        routes_url = base + "/routes"
    all_grades = []
    page = 1
    while True:
        if page == 1:
            url = routes_url
        else:
            sep = "&" if "?" in routes_url else "?"
            url = f"{routes_url}{sep}page={page}"
        try:
            resp = requests.get(url, headers=OVERPASS_HEADERS, timeout=30)
            resp.raise_for_status()
        except requests.RequestException:
            break
        grades = _parse_8a_routes_grades(resp.text)
        if not grades:
            break
        all_grades.extend(grades)
        page += 1
        time.sleep(0.3)
    return _summarize_route_grades(all_grades)


def _osm_crag_stats(tags):
    routes_total = None
    raw = tags.get("climbing:routes", "").strip()
    if raw.isdigit():
        routes_total = int(raw)
    grade_min = grade_max = grade_system = None
    for system in OSM_GRADE_SYSTEMS:
        lo = tags.get(f"climbing:grade:{system}:min", "").strip()
        hi = tags.get(f"climbing:grade:{system}:max", "").strip()
        if lo and hi:
            grade_min, grade_max, grade_system = lo, hi, system
            break
    if not grade_min:
        mins, maxs = {}, {}
        for key, val in tags.items():
            m = re.match(r"climbing:grade:([^:]+):min$", key)
            if m and val.strip():
                mins[m.group(1)] = val.strip()
            m = re.match(r"climbing:grade:([^:]+):max$", key)
            if m and val.strip():
                maxs[m.group(1)] = val.strip()
        for system in sorted(set(mins) & set(maxs)):
            grade_min = mins[system]
            grade_max = maxs[system]
            grade_system = system
            break
    if routes_total is None and grade_min is None:
        return None
    return {
        "routes_total": routes_total,
        "grade_min": grade_min,
        "grade_max": grade_max,
        "grade_system": grade_system,
    }


def _format_osm_stats_line(stats):
    if not stats:
        return None
    parts = []
    if stats.get("routes_total") is not None:
        parts.append(f"{stats['routes_total']} routes")
    if stats.get("grade_min") and stats.get("grade_max"):
        g = f"{stats['grade_min']}–{stats['grade_max']}"
        if stats.get("grade_system") and stats["grade_system"] != "french":
            g += f", {stats['grade_system']}"
        parts.append(f"({g})")
    if not parts:
        return None
    if len(parts) == 1:
        return f"OSM: {parts[0]}"
    return f"OSM: {parts[0]} {parts[1]}"


def _format_a8_stats_lines(entry):
    if not entry or not _is_a8_direct(entry.get("url", "")):
        return []
    lines = []
    rt = entry.get("routes_total")
    gmin = entry.get("grade_min")
    gmax = entry.get("grade_max")
    if rt is not None and gmin and gmax:
        lines.append(f"8a.nu: {rt} routes ({gmin}–{gmax})")
    elif rt is not None:
        lines.append(f"8a.nu: {rt} routes")
    b1 = entry.get("routes_6a_6b")
    b2 = entry.get("routes_7a_7b")
    b3 = entry.get("routes_7c_8a")
    bands = []
    if b1:
        bands.append(f"6a–6b+: {b1}")
    if b2:
        bands.append(f"7a–7b+: {b2}")
    if b3:
        bands.append(f"7c–8a: {b3}")
    if bands:
        lines.append(" | ".join(bands))
    return lines


def _a8_search_url(name):
    return f"{A8_BASE}/search/crags?query={urllib.parse.quote(_a8_search_name(name))}"


def _is_thecrag_direct(url):
    return bool(url and "thecrag.com" in url and "/search" not in url)


def _is_a8_direct(url):
    return bool(url and "8a.nu" in url and "/crags/sportclimbing/" in url)


def _a8_highlight_bands(entry):
    """True when 8a stats show >=3 routes in both 6a–6b+ and 7a–7b+ bands."""
    if not entry:
        return False
    b1 = entry.get("routes_6a_6b")
    b2 = entry.get("routes_7a_7b")
    return b1 is not None and b1 >= 3 and b2 is not None and b2 >= 3


def _crag_icon_color(name, thecrag_url, a8nu_url, a8_entry=None):
    if not name:
        return "gray"
    if _a8_highlight_bands(a8_entry):
        return "beige"
    if _is_thecrag_direct(thecrag_url) or _is_a8_direct(a8nu_url):
        return "green"
    return "red"


def _crag_marker_icon(name, thecrag_url, a8nu_url, a8_entry=None):
    color = _crag_icon_color(name, thecrag_url, a8nu_url, a8_entry)
  
    return folium.Icon(color=color, icon="flag")


def thecrag_url_from_tags(tags):
    url = tags.get("climbing:url:thecrag")
    if url:
        return url.strip()
    crag_url = tags.get("climbing:url")
    if crag_url and "thecrag.com" in crag_url:
        return crag_url.strip()
    return None


def _outdoor_crag_urls(name, tags, a8_cache, lon=None, lat=None,
                      geocode_cache=None):
    """Return (thecrag_url, a8nu_url, a8_entry) for popup links."""
    thecrag_url = thecrag_url_from_tags(tags)
    if name and not thecrag_url:
        query_name = urllib.parse.quote(name)
        thecrag_url = f"https://www.thecrag.com/search?S={query_name}#crags"
    a8nu_url = None
    a8_entry = None
    if name:
        if a8_cache is not None:
            a8_entry = _a8_lookup_entry(name, a8_cache, lat=lat, lon=lon)
            country_slug = None
            if a8_entry is None:
                country_slug = _crag_country_slug(
                    tags, lon, lat, geocode_cache)
                a8_entry = _a8_lookup_entry(
                    name, a8_cache, country_slug, lat, lon)
            if a8_entry is None:
                if country_slug is None:
                    country_slug = _crag_country_slug(
                        tags, lon, lat, geocode_cache)
                a8_entry = resolve_8a_nu_url(
                    name, a8_cache, country_slug=country_slug,
                    lat=lat, lon=lon)
            a8nu_url = a8_entry["url"]
        else:
            a8nu_url = _a8_search_url(name)
    return thecrag_url, a8nu_url, a8_entry


def _a8_direct_url(country, slug):
    return f"{A8_BASE}/crags/sportclimbing/{country}/{slug}"


def _country_from_payload_window(window):
    matches = re.findall(r'"([a-z0-9-]+)","([^"]+)"', window)
    for slug, label in reversed(matches):
        if slug in ("yes", "no", "limited", "null"):
            continue
        if re.match(r"^[A-Z][a-zA-Z /'-]+$", label) and slug != label.lower().replace(" ", "-"):
            return slug
        if label in ("Italy", "France", "Germany", "Greece", "Austria", "Switzerland",
                     "Spain", "Poland", "United Kingdom", "United States", "Brazil",
                     "Unknown", "Netherlands", "Belgium", "Norway", "Sweden", "Finland",
                     "Portugal", "Czechia", "Slovakia", "Slovenia", "Croatia", "Hungary",
                     "Romania", "Bulgaria", "Ukraine", "Turkey", "Luxembourg"):
            return slug
    return None


def _parse_8a_search_entries(html):
    entries = []
    seen = set()
    coord_by_slug = {}
    for m in A8_PAYLOAD_RE.finditer(html):
        area, area_slug, crag, crag_slug, lat_s, lon_s = m.groups()
        lat, lon = float(lat_s), float(lon_s)
        country = _country_from_payload_window(m.group(0))
        if not country:
            continue
        coord_by_slug[(country, area_slug)] = (lat, lon)
        coord_by_slug[(country, crag_slug)] = (lat, lon)
        for kind, display, slug in (
            ("area", area, area_slug),
            ("crag", crag, crag_slug),
        ):
            key = (kind, display, country, slug)
            if key in seen:
                continue
            seen.add(key)
            entries.append({
                "kind": kind,
                "name": display,
                "country": country,
                "slug": slug,
                "lat": lat,
                "lon": lon,
            })
    for path, link_name in A8_LINK_RE.findall(html):
        parts = path.strip("/").split("/")
        if len(parts) < 4:
            continue
        country, slug = parts[2], parts[3]
        sector_slug = None
        if "?sector=" in path:
            kind = "sector"
            sector_slug = path.split("?sector=", 1)[1].split("&", 1)[0]
            key = ("sector", link_name, country, slug, sector_slug)
        else:
            kind = "crag"
            key = ("crag", link_name, country, slug)
        if key in seen:
            continue
        seen.add(key)
        lat, lon = coord_by_slug.get((country, slug), (None, None))
        entry = {
            "kind": kind,
            "name": link_name,
            "country": country,
            "slug": slug,
            "lat": lat,
            "lon": lon,
            "url_path": path,
        }
        if sector_slug:
            entry["sector_slug"] = sector_slug
        entries.append(entry)
    return entries


def _dedupe_8a_entries(entries):
    seen = set()
    deduped = []
    for entry in entries:
        key = entry.get("url_path") or (
            entry["kind"], entry["country"], entry["slug"],
            entry.get("sector_slug"))
        if key in seen:
            continue
        seen.add(key)
        deduped.append(entry)
    return deduped


def _a8_entry_url(entry):
    url_path = entry.get("url_path")
    if url_path:
        return A8_BASE + url_path
    return _a8_direct_url(entry["country"], entry["slug"])


def _match_8a_url(name, entries, country_slug=None, lat=None, lon=None):
    target = _norm_crag_name(name)
    name_slug = _slugify(name)

    exact_named = [e for e in entries if _norm_crag_name(e["name"]) == target]
    if country_slug:
        exact_named = [e for e in exact_named if e["country"] == country_slug]

    if exact_named:
        for kind in ("sector", "crag", "area"):
            for entry in exact_named:
                if entry["kind"] == kind:
                    return _a8_entry_url(entry)

    if lat is not None and lon is not None:
        with_coords = [
            e for e in entries
            if e.get("lat") is not None and _entry_within_radius(e, lat, lon)]
        if with_coords:
            pool = with_coords
        else:
            pool = [e for e in entries if e.get("lat") is None]
            if not pool:
                return None
    else:
        pool = entries

    if country_slug:
        pool = [e for e in pool if e["country"] == country_slug]
        if not pool:
            return None
        for kind in ("sector", "crag", "area"):
            for entry in pool:
                if entry["kind"] != kind:
                    continue
                slug = entry["slug"]
                if slug == name_slug or slug.endswith("-" + name_slug):
                    return _a8_entry_url(entry)
                sector_slug = entry.get("sector_slug")
                if sector_slug and (
                        sector_slug == name_slug
                        or sector_slug.endswith("-" + name_slug)):
                    return _a8_entry_url(entry)
        return None

    for kind in ("sector", "crag", "area"):
        for entry in pool:
            if entry["kind"] == kind and _norm_crag_name(entry["name"]) == target:
                return _a8_entry_url(entry)
    return None


def _fetch_8a_search_matches(name, country_slug=None, lat=None, lon=None):
    search_name = _a8_search_name(name)
    entries = []
    for endpoint in ("crags", "sectors"):
        try:
            resp = requests.get(
                f"{A8_BASE}/search/{endpoint}",
                params={"query": search_name},
                headers=OVERPASS_HEADERS,
                timeout=30,
            )
            resp.raise_for_status()
            entries.extend(_parse_8a_search_entries(resp.text))
        except requests.RequestException:
            continue
    return _match_8a_url(
        search_name, _dedupe_8a_entries(entries), country_slug, lat, lon)


def resolve_8a_nu_url(name, cache, country_slug=None, lat=None, lon=None):
    """Resolve 8a.nu URL via search page; return cache entry dict."""
    cached = _a8_lookup_entry(name, cache, country_slug, lat, lon)
    if cached is not None :
        return cached
    key = _a8_find_cache_key(name, cache, country_slug, lat, lon)
    if key is None:
        key = _a8_cache_key(name, country_slug, lat, lon)
    if cached is not None:
        url = cached["url"]
        stats = {}
        if _is_a8_direct(url):
            fetched = fetch_8a_route_stats(url)
            if fetched:
                stats = fetched
        entry = {**cached, **stats}
        cache[key] = entry
        time.sleep(0.3)
        return entry
    search_url = _a8_search_url(name)
    url = search_url
    stats = {}
    matched = _fetch_8a_search_matches(
        name, country_slug=country_slug, lat=lat, lon=lon)
    if matched:
        url = matched
    if _is_a8_direct(url):
        fetched = fetch_8a_route_stats(url)
        if fetched:
            stats = fetched
    entry = {"url": url, **stats}
    cache[key] = entry
    time.sleep(0.3)
    return entry


def a8_cache_load(csv_filename):
    cache = {}
    if not os.path.exists(csv_filename):
        return cache
    with open(csv_filename, newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            name = row.get("name", "").strip()
            url = row.get("url", "").strip()
            if not name or not url:
                continue
            country = row.get("country", "").strip()
            lat_s = row.get("lat", "").strip()
            lon_s = row.get("lon", "").strip()
            lat_k = float(lat_s) if lat_s else ""
            lon_k = float(lon_s) if lon_s else ""
            key = (name, country, lat_k, lon_k)
            entry = {"url": url}
            for field in ("routes_total", "routes_6a_6b", "routes_7a_7b",
                          "routes_7c_8a"):
                val = row.get(field, "").strip()
                if val.isdigit():
                    entry[field] = int(val)
            for field in ("grade_min", "grade_max"):
                val = row.get(field, "").strip()
                if val:
                    entry[field] = val
            cache[key] = entry
    print(f"📂 Loaded {len(cache)} 8a.nu entries from {csv_filename}")
    return cache


def a8_cache_save(cache, csv_filename):
    with open(csv_filename, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=A8_CACHE_FIELDS)
        writer.writeheader()
        for key, entry in sorted(cache.items()):
            entry = _a8_normalize_entry(entry)
            name, country, lat_k, lon_k = _a8_cache_key_parts(key)
            row = {
                "name": name,
                "country": country,
                "lat": lat_k if lat_k != "" else "",
                "lon": lon_k if lon_k != "" else "",
                "url": entry.get("url", ""),
                "routes_total": entry.get("routes_total", ""),
                "grade_min": entry.get("grade_min", ""),
                "grade_max": entry.get("grade_max", ""),
                "routes_6a_6b": entry.get("routes_6a_6b", ""),
                "routes_7a_7b": entry.get("routes_7a_7b", ""),
                "routes_7c_8a": entry.get("routes_7c_8a", ""),
            }
            writer.writerow(row)
    print(f"💾 8a.nu cache saved: {csv_filename}")


def add_crag_legend(m):
    legend_html = """
    <div style="position: fixed; bottom: 24px; left: 24px; z-index: 9999;
                background: white; padding: 8px 12px; border: 1px solid #ccc;
                border-radius: 4px; font-size: 13px; line-height: 1.5;">
      <b>Crags</b><br>
      <span style="color:#2ecc71;">&#9679;</span> direct TheCrag / 8a.nu link<br>
      <span style="color:#f1c40f;">&#9679;</span> 6a–6b+ &amp; 7a–7b+ &ge;3 routes each<br>
      <span style="color:#e74c3c;">&#9679;</span> named (search links only)<br>
      <span style="color:#7f8c8d;">&#9679;</span> unnamed<br>
      <span style="color:#e67e22;">&#9679;</span> indoor gym<br>
      <span style="color:#5f9ea0;">&#9679;</span> nearest toilet (within 10 km)<br>
      <span style="color:#663399;">&#9679;</span> nearest parking (beige or toilet-shown crags)
    </div>
    """
    m.get_root().html.add_child(folium.Element(legend_html))


def _format_toilet_line(nearest_info):
    if not nearest_info:
        return None
    toilet = nearest_info["toilet"]
    name = toilet["name"] or "Unnamed toilet"
    dist = nearest_info["distance_km"]
    osm_url = f"https://www.openstreetmap.org/{toilet['type']}/{toilet['id']}"
    return (
        f'Nearest toilet: <a href="{osm_url}" target="_blank">{name}</a>, '
        f"{dist:.1f} km"
    )


def _format_parking_line(nearest_info):
    if not nearest_info:
        return None
    place = nearest_info["place"]
    name = place["name"] or place.get("titre") or "Unnamed parking"
    dist = nearest_info["distance_km"]
    url = _p4n_place_url(place["id"])
    return (
        f'Nearest parking: <a href="{url}" target="_blank">{name}</a>, '
        f"{dist:.1f} km"
    )


def add_crag_markers(m, locations, a8_cache=None, geocode_cache=None,
                     nearest_toilets=None, nearest_parking=None):
    for el in locations:
        tags = el.get("tags", {})
        name = _crag_name_from_tags(tags)
        lat = el.get("lat") or el.get("center", {}).get("lat")
        lon = el.get("lon") or el.get("center", {}).get("lon")

        osm_url = f"https://www.openstreetmap.org/{el['type']}/{el['id']}"

        if is_indoor_gym(tags):
            website = website_from_tags(tags)
            links = f'<a href="{osm_url}" target="_blank">OpenStreetMap</a>'
            if website:
                links += f' | <a href="{website}" target="_blank">Website</a>'
            popup_html = f"""
            <b>{name}</b><br>
            📍 {lat:.4f}, {lon:.4f}<br>
            {links}<br>
            {_nav_links_html(lat, lon, name)}
            """
            icon = folium.Icon(color="orange", icon="home", prefix="fa")
        else:
            thecrag_url, a8nu_url, a8_entry = _outdoor_crag_urls(
                name, tags, a8_cache, lon=lon, lat=lat,
                geocode_cache=geocode_cache)
            stats_lines = []
            osm_line = _format_osm_stats_line(_osm_crag_stats(tags))
            if osm_line:
                stats_lines.append(osm_line)
            stats_lines.extend(_format_a8_stats_lines(a8_entry))
            toilet_line = _format_toilet_line(
                nearest_toilets.get((el["type"], el["id"]))
                if nearest_toilets else None)
            if toilet_line:
                stats_lines.append(toilet_line)
            parking_line = _format_parking_line(
                nearest_parking.get((el["type"], el["id"]))
                if nearest_parking else None)
            if parking_line:
                stats_lines.append(parking_line)
            stats_html = ""
            if stats_lines:
                stats_html = "<br>" + "<br>".join(stats_lines)
            if name:
                popup_html = f"""
                <b>{name}</b><br>
                <br>
                📍 {lat:.4f}, {lon:.4f}<br>
                <a href="{osm_url}" target="_blank">OpenStreetMap</a> |
                <a href="{thecrag_url}" target="_blank">TheCrag</a> |
                <a href="{a8nu_url}" target="_blank">8a.nu</a>{stats_html}<br>
                {_nav_links_html(lat, lon, name)}
                """
            else:
                popup_html = f"""
                <b>Unnamed crag</b><br>
                <br>
                📍 {lat:.4f}, {lon:.4f}<br>
                <a href="{osm_url}" target="_blank">OpenStreetMap</a><br>
                {_nav_links_html(lat, lon)}
                """
            icon = _crag_marker_icon(
                name, thecrag_url, a8nu_url, a8_entry=a8_entry)

        folium.Marker(
            [lat, lon],
            popup=folium.Popup(popup_html, max_width=320),
            icon=icon
        ).add_to(m)


def add_toilet_markers(m, nearest_toilets):
    if not nearest_toilets:
        return
    by_toilet = {}
    for info in nearest_toilets.values():
        toilet = info["toilet"]
        key = (toilet["type"], toilet["id"])
        if key not in by_toilet:
            by_toilet[key] = {"toilet": toilet, "crags": []}
        by_toilet[key]["crags"].append(info["crag_name"])

    group = folium.FeatureGroup(name="Toilets", show=True)
    for data in by_toilet.values():
        toilet = data["toilet"]
        name = toilet["name"] or "Unnamed toilet"
        osm_url = (
            f"https://www.openstreetmap.org/{toilet['type']}/{toilet['id']}")
        crags = sorted(set(data["crags"]))
        crags_html = f"<br>Nearest for: {', '.join(crags)}"
        popup_html = f"""
        <b>{name}</b><br>
        <a href="{osm_url}" target="_blank">OpenStreetMap</a>{crags_html}<br>
        {_nav_links_html(toilet["lat"], toilet["lon"], name)}
        """
        folium.Marker(
            [toilet["lat"], toilet["lon"]],
            popup=folium.Popup(popup_html, max_width=320),
            icon=folium.Icon(color="cadetblue", icon="info-sign"),
        ).add_to(group)
    group.add_to(m)


def add_parking_markers(m, nearest_parking):
    if not nearest_parking:
        return
    by_place = {}
    for info in nearest_parking.values():
        place = info["place"]
        key = place["id"]
        if key not in by_place:
            by_place[key] = {"place": place, "crags": []}
        by_place[key]["crags"].append(info["crag_name"])

    group = folium.FeatureGroup(name="Parking", show=True)
    for data in by_place.values():
        place = data["place"]
        name = place["name"] or place.get("titre") or "Unnamed parking"
        url = _p4n_place_url(place["id"])
        crags = sorted(set(data["crags"]))
        crags_html = f"<br>Nearest for: {', '.join(crags)}"
        popup_html = f"""
        <b>{name}</b><br>
        <a href="{url}" target="_blank">park4night</a>{crags_html}<br>
        {_nav_links_html(place["lat"], place["lon"], name)}
        """
        folium.Marker(
            [place["lat"], place["lon"]],
            popup=folium.Popup(popup_html, max_width=320),
            icon=folium.Icon(color="darkpurple", icon="car", prefix="fa"),
        ).add_to(group)
    group.add_to(m)


def build_and_save_map(m, locations, path, a8_cache=None, geocode_cache=None,
                       nearest_toilets=None, nearest_parking=None):
    add_crag_markers(
        m, locations, a8_cache=a8_cache, geocode_cache=geocode_cache,
        nearest_toilets=nearest_toilets, nearest_parking=nearest_parking)
    add_toilet_markers(m, nearest_toilets)
    add_parking_markers(m, nearest_parking)
    add_crag_legend(m)
    folium.LayerControl().add_to(m)
    m.save(path)
    print(f"Map saved: {path} ({len(locations)} locations)")


def save_crags_to_gpx(crags, filename):
    gpx = ET.Element("gpx", version="1.1", creator="ClimbingRouteFinder",
                     xmlns="http://www.topografix.com/GPX/1/1")
    for el in crags:
        name = el.get("tags", {}).get("name", f"crag_{el['id']}")
        lat = el.get("lat") or el.get("center", {}).get("lat")
        lon = el.get("lon") or el.get("center", {}).get("lon")
        if lat is None or lon is None:
            continue
        wpt = ET.SubElement(gpx, "wpt", lat=str(lat), lon=str(lon))
        ET.SubElement(wpt, "name").text = name
        tags = el.get("tags", {})
        if is_indoor_gym(tags):
            desc = website_from_tags(tags) or (
                f"https://www.openstreetmap.org/{el['type']}/{el['id']}")
        else:
            desc = f"https://www.openstreetmap.org/{el['type']}/{el['id']}"
        ET.SubElement(wpt, "desc").text = desc
    tree = ET.ElementTree(gpx)
    tree.write(filename, encoding="utf-8", xml_declaration=True)
    print(f"✅ GPX file saved: {filename}")


def toll_save(details, csv_filename) :
    with open(csv_filename, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=["id", "name", "lat", "lon",
                                               "fee", "currency"])
        writer.writeheader()
#        writer.writerows(details)
        for t in details.values():
            writer.writerow({
                "id": t["id"],
                "name": t["name"],
                "lat": t["lat"],
                "lon": t["lon"],
                "fee": t["fee"],
                "currency": "EUR"
                })

def toll_load(csv_filename):
    known_tolls = {}
    if os.path.exists(csv_filename):
        with open(csv_filename, newline='', encoding='utf-8') as f:
            reader = csv.DictReader(f)
            for row in reader:
                try:
                    node_id = int(row["id"])
                    fee_val = float(row["fee"])
                    known_tolls[node_id] = fee_val
                except (ValueError, KeyError):
                    continue
        print(f"📂 Loaded {len(known_tolls)} tolls from {csv_filename}")
    return known_tolls

def toll_update(nearby_tolls) :
    # Merge known_tolls with newly found
    updated = {t["id"]: t for t in nearby_tolls}
    # Load old data if exists
    csv_filename = "jumper_tolls.csv"
    if os.path.exists(csv_filename):
        with open(csv_filename, newline='', encoding='utf-8') as f:
            reader = csv.DictReader(f)
            for row in reader:
                node_id = int(row["id"])
                if node_id not in updated:
                    updated[node_id] = row

        # Save updated data
        csv_filename = "tolls.csv"
        with open(csv_filename, "w", newline='', encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=["id", "name", "lat", "lon",
                                                   "fee", "currency"])
            writer.writeheader()
            for t in updated.values():
                writer.writerow({
                    "id": t["id"],
                    "name": t["name"],
                    "lat": t["lat"],
                    "lon": t["lon"],
                    "fee": t["fee"],
                    "currency" : "EUR"
                })
        print(f"💾 CSV updated: {csv_filename}")


def overpass_post(query, timeout=90, max_retries=3):
    """POST to Overpass with retries and mirror fallback."""
    if "[timeout:" in query:
        query = re.sub(r"\[timeout:\d+\]", f"[timeout:{timeout}]", query)
    elif query.lstrip().startswith("[out:json]"):
        query = re.sub(r"\[out:json\]", f"[out:json][timeout:{timeout}]", query, count=1)
    else:
        query = f"[out:json][timeout:{timeout}];\n{query}"

    last_error = None
    for url in OVERPASS_URLS:
        for attempt in range(max_retries):
            try:
                resp = requests.post(
                    url, data={"data": query}, headers=OVERPASS_HEADERS,
                    timeout=timeout + 30)
                if resp.status_code in (429, 503, 504):
                    resp.raise_for_status()
                resp.raise_for_status()
                return resp.json().get("elements", [])
            except requests.RequestException as exc:
                last_error = exc
                if attempt < max_retries - 1:
                    time.sleep(2 ** attempt)
        time.sleep(1)

    raise RuntimeError(
        f"Overpass query failed after {len(OVERPASS_URLS)} mirrors: {last_error}"
    ) from last_error


def iter_route_segments(route_coords, segment_km=CRAG_SEGMENT_KM):
    """Yield route coordinate lists for each ~segment_km slice."""
    route_line = LineString(route_coords)
    if route_line.is_empty:
        return

    project = pyproj.Transformer.from_crs("epsg:4326", "epsg:3857",
                                          always_xy=True).transform
    unproject = pyproj.Transformer.from_crs("epsg:3857", "epsg:4326",
                                            always_xy=True).transform
    route_proj = transform(project, route_line)
    length_m = route_proj.length
    if length_m == 0:
        yield route_coords
        return

    segment_m = segment_km * 1000
    start = 0.0
    while start < length_m:
        end = min(start + segment_m, length_m)
        seg_proj = substring(route_proj, start, end)
        seg_wgs = transform(unproject, seg_proj)
        coords = list(seg_wgs.coords)
        if coords:
            yield coords
        start = end


def _crag_bbox_query(min_lat, min_lon, max_lat, max_lon, timeout=90):
    return f"""
    [out:json][timeout:{timeout}];
    (
      node["climbing"="crag"]({min_lat},{min_lon},{max_lat},{max_lon});
      node["sport"="climbing"]({min_lat},{min_lon},{max_lat},{max_lon});
      way["climbing"="crag"]({min_lat},{min_lon},{max_lat},{max_lon});
      way["sport"="climbing"]({min_lat},{min_lon},{max_lat},{max_lon});
      relation["climbing"="crag"]({min_lat},{min_lon},{max_lat},{max_lon});
    );
    out center;
    """


def fetch_crags_along_route(route_coords, buffer_km, segment_km=CRAG_SEGMENT_KM):
    """Fetch climbing features along route using chunked Overpass bbox queries."""
    project = pyproj.Transformer.from_crs("epsg:4326", "epsg:3857",
                                          always_xy=True).transform
    unproject = pyproj.Transformer.from_crs("epsg:3857", "epsg:4326",
                                            always_xy=True).transform
    merged = {}
    segments = list(iter_route_segments(route_coords, segment_km))
    total = len(segments)

    for i, seg_coords in enumerate(segments):
        print(f"Crag segment {i + 1}/{total}...")
        seg_line = LineString(seg_coords)
        seg_buffer = transform(
            unproject, transform(project, seg_line).buffer(buffer_km * 1000))
        min_lon, min_lat, max_lon, max_lat = seg_buffer.bounds
        query = _crag_bbox_query(min_lat, min_lon, max_lat, max_lon)
        elements = overpass_post(query)
        for el in elements:
            merged[(el["type"], el["id"])] = el

    return list(merged.values())


def _element_latlon(el):
    lat = el.get("lat") or el.get("center", {}).get("lat")
    lon = el.get("lon") or el.get("center", {}).get("lon")
    if lat is None or lon is None:
        return None, None
    return lat, lon


def _toilet_access_ok(tags):
    access = tags.get("access", "").strip().lower()
    return not access or access == "yes"


def _normalize_toilet(el):
    lat, lon = _element_latlon(el)
    if lat is None:
        return None
    tags = el.get("tags", {})
    if not _toilet_access_ok(tags):
        return None
    return {
        "id": el["id"],
        "type": el["type"],
        "lat": lat,
        "lon": lon,
        "name": tags.get("name", "").strip(),
        "tags": tags,
    }


def _toilet_bbox_query(min_lat, min_lon, max_lat, max_lon, timeout=90):
    b = f"{min_lat},{min_lon},{max_lat},{max_lon}"
    return f"""
    [out:json][timeout:{timeout}];
    (
      node["amenity"="toilets"]["access"="yes"]({b});
      node["amenity"="toilets"][!"access"]({b});
      node["amenity"="toilet"]["access"="yes"]({b});
      node["amenity"="toilet"][!"access"]({b});
      way["amenity"="toilets"]["access"="yes"]({b});
      way["amenity"="toilets"][!"access"]({b});
      way["amenity"="toilet"]["access"="yes"]({b});
      way["amenity"="toilet"][!"access"]({b});
    );
    out center;
    """


def fetch_toilets_along_route(route_coords, buffer_km,
                              toilet_radius_km=TOILET_SEARCH_RADIUS_KM,
                              segment_km=CRAG_SEGMENT_KM):
    """Fetch amenity=toilets/toilet along route with expanded search bbox."""
    expand_km = buffer_km + toilet_radius_km
    project = pyproj.Transformer.from_crs("epsg:4326", "epsg:3857",
                                          always_xy=True).transform
    unproject = pyproj.Transformer.from_crs("epsg:3857", "epsg:4326",
                                            always_xy=True).transform
    merged = {}
    segments = list(iter_route_segments(route_coords, segment_km))
    total = len(segments)

    for i, seg_coords in enumerate(segments):
        print(f"Toilet segment {i + 1}/{total}...")
        seg_line = LineString(seg_coords)
        seg_buffer = transform(
            unproject, transform(project, seg_line).buffer(expand_km * 1000))
        min_lon, min_lat, max_lon, max_lat = seg_buffer.bounds
        query = _toilet_bbox_query(min_lat, min_lon, max_lat, max_lon)
        elements = overpass_post(query)
        for el in elements:
            merged[(el["type"], el["id"])] = el

    toilets = []
    for el in merged.values():
        normalized = _normalize_toilet(el)
        if normalized:
            toilets.append(normalized)
    print(f"Found {len(toilets)} toilets in search area")
    return toilets


def nearest_toilets_for_crags(outdoor_crags, toilets,
                               radius_km=TOILET_SEARCH_RADIUS_KM):
    """Map crag (type, id) -> {toilet, distance_km, crag_name}."""
    result = {}
    if not toilets:
        return result
    for el in outdoor_crags:
        if is_indoor_gym(el.get("tags", {})):
            continue
        lat, lon = _element_latlon(el)
        if lat is None:
            continue
        best = None
        best_dist = None
        for toilet in toilets:
            dist = _haversine_km(lat, lon, toilet["lat"], toilet["lon"])
            if dist <= radius_km and (best_dist is None or dist < best_dist):
                best_dist = dist
                best = toilet
        if best is not None:
            crag_name = _crag_name_from_tags(el.get("tags", {})) or "Unnamed crag"
            result[(el["type"], el["id"])] = {
                "toilet": best,
                "distance_km": best_dist,
                "crag_name": crag_name,
            }
    return result


def _p4n_place_url(place_id):
    return f"{P4N_WEB_BASE}/place/{place_id}"


def _is_p4n_parking(place):
    return place.get("code") in P4N_PARKING_CODES


def _normalize_p4n_place(raw):
    try:
        lat = float(raw["latitude"])
        lon = float(raw["longitude"])
    except (KeyError, TypeError, ValueError):
        return None
    name = (raw.get("name") or raw.get("titre") or "").strip()
    dist_s = raw.get("distance", "")
    try:
        distance_km = float(dist_s) if dist_s not in ("", None) else None
    except ValueError:
        distance_km = None
    return {
        "id": str(raw["id"]),
        "lat": lat,
        "lon": lon,
        "name": name,
        "code": raw.get("code", ""),
        "distance_km": distance_km,
        "titre": (raw.get("titre") or "").strip(),
    }


def fetch_park4night_places(lat, lon):
    resp = requests.get(
        f"{P4N_BASE}/lieuxGetFilter.php",
        params={"latitude": lat, "longitude": lon},
        headers=P4N_HEADERS,
        timeout=30,
    )
    resp.raise_for_status()
    lieux = resp.json().get("lieux") or []
    places = []
    for raw in lieux:
        place = _normalize_p4n_place(raw)
        if place and _is_p4n_parking(place):
            places.append(place)
    return places


def highlighted_outdoor_crags(outdoor_crags, a8_cache, geocode_cache):
    highlighted = []
    for el in outdoor_crags:
        if is_indoor_gym(el.get("tags", {})):
            continue
        tags = el.get("tags", {})
        name = _crag_name_from_tags(tags)
        lat = el.get("lat") or el.get("center", {}).get("lat")
        lon = el.get("lon") or el.get("center", {}).get("lon")
        if not name or lat is None or lon is None:
            continue
        a8_entry = _a8_lookup_entry(name, a8_cache, lat=lat, lon=lon)
        if a8_entry is None:
            country_slug = _crag_country_slug(tags, lon, lat, geocode_cache)
            a8_entry = _a8_lookup_entry(
                name, a8_cache, country_slug, lat, lon)
        if _a8_highlight_bands(a8_entry):
            highlighted.append(el)
    return highlighted


def outdoor_crags_for_p4n_parking(outdoor_crags, a8_cache, geocode_cache,
                                  nearest_toilets):
    """Beige outdoor crags plus crags with a nearest OSM toilet, deduped."""
    by_key = {}
    for el in highlighted_outdoor_crags(outdoor_crags, a8_cache, geocode_cache):
        by_key[(el["type"], el["id"])] = el
    toilet_keys = set(nearest_toilets or {})
    for el in outdoor_crags:
        key = (el["type"], el["id"])
        if key in toilet_keys and key not in by_key:
            if not is_indoor_gym(el.get("tags", {})):
                by_key[key] = el
    return list(by_key.values())


def nearest_parking_for_crags(crags, radius_km=P4N_SEARCH_RADIUS_KM):
    """Map crag (type, id) -> {place, distance_km, crag_name}."""
    result = {}
    places_cache = {}
    for el in crags:
        lat, lon = _element_latlon(el)
        if lat is None:
            continue
        cache_key = _geocode_cache_key(lat, lon)
        if cache_key not in places_cache:
            places_cache[cache_key] = fetch_park4night_places(lat, lon)
            time.sleep(0.3)
        places = places_cache[cache_key]
        best = None
        best_dist = None
        for place in places:
            dist = place.get("distance_km")
            if dist is None:
                dist = _haversine_km(lat, lon, place["lat"], place["lon"])
            if dist <= radius_km and (best_dist is None or dist < best_dist):
                best_dist = dist
                best = place
        if best is not None:
            crag_name = _crag_name_from_tags(el.get("tags", {})) or "Unnamed crag"
            result[(el["type"], el["id"])] = {
                "place": best,
                "distance_km": best_dist,
                "crag_name": crag_name,
            }
    return result


def _toll_around_coords(route_coords):
    """Build capped lat,lon list for Overpass around filter."""
    route_line = LineString(route_coords)
    project = pyproj.Transformer.from_crs("epsg:4326", "epsg:3857",
                                          always_xy=True).transform
    route_proj = transform(project, route_line)
    length_km = route_proj.length / 1000
    tolerance = 0.0015
    simplified = route_line.simplify(tolerance, preserve_topology=False)
    coords = list(simplified.coords)
    return coords


def _fetch_toll_elements(route_coords):
    """Query toll booths along route; segment on failure."""
    coords = _toll_around_coords(route_coords)
    coords_str = ",".join(f"{lat:.6f},{lon:.6f}" for lon, lat in coords)
    query = f"""
    [out:json][timeout:90];
    node["barrier"="toll_booth"](around:150,{coords_str});
    out body;
    """
    try:
        return overpass_post(query)
    except RuntimeError:
        merged = {}
        segments = list(iter_route_segments(route_coords))
        print(f"Toll query split into {len(segments)} segments...")
        for seg_coords in segments:
            seg_coords_list = _toll_around_coords(seg_coords)
            seg_str = ",".join(f"{lat:.6f},{lon:.6f}" for lon, lat in seg_coords_list)
            seg_query = f"""
            [out:json][timeout:90];
            node["barrier"="toll_booth"](around:150,{seg_str});
            out body;
            """
            for el in overpass_post(seg_query):
                merged[el["id"]] = el
        return list(merged.values())


NOMINATIM_HEADERS = {"User-Agent": "route-climbing-fetcher"}
GEOCODE_CACHE_DECIMALS = 1  # ~10 km grid for reverse-geocode cache keys
VIGNETTE_SAMPLE_KM = 40
VIGNETTE_MAX_SAMPLES = 25


def _geocode_cache_key(lat, lon):
    return (round(lat, GEOCODE_CACHE_DECIMALS),
            round(lon, GEOCODE_CACHE_DECIMALS))


def vignette_load(csv_filename):
    """Load vignette fees keyed by ISO country code."""
    vignettes = {}
    if not os.path.exists(csv_filename):
        return vignettes
    with open(csv_filename, newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            try:
                code = row["country_code"].strip().upper()
                fee = float(row["fee"])
                name = row.get("country", code)
                currency = row.get("currency", "EUR")
                vignettes[code] = {"fee": fee, "country": name, "currency": currency}
            except (ValueError, KeyError):
                continue
    print(f"📂 Loaded {len(vignettes)} vignette prices from {csv_filename}")
    return vignettes


def geocode_cache_load(csv_filename):
    """Load reverse-geocode cache keyed by (lat, lon) rounded to ~10 km."""
    cache = {}
    if not os.path.exists(csv_filename):
        return cache
    with open(csv_filename, newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            try:
                lat, lon = _geocode_cache_key(
                    float(row["lat"]), float(row["lon"]))
                code = row.get("country_code", "").strip().upper()
                name = row.get("country", "").strip()
                if code:
                    cache[(lat, lon)] = (code, name or code)
                else:
                    cache[(lat, lon)] = None
            except (ValueError, KeyError):
                continue
    print(f"📂 Loaded {len(cache)} geocode entries from {csv_filename}")
    return cache


def geocode_cache_save(cache, csv_filename):
    """Persist reverse-geocode cache to CSV."""
    with open(csv_filename, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(
            f, fieldnames=["lat", "lon", "country_code", "country"])
        writer.writeheader()
        for (lat, lon), result in sorted(cache.items()):
            if result:
                code, name = result
                writer.writerow({
                    "lat": lat,
                    "lon": lon,
                    "country_code": code,
                    "country": name,
                })
            else:
                writer.writerow({
                    "lat": lat,
                    "lon": lon,
                    "country_code": "",
                    "country": "",
                })
    print(f"💾 Geocode cache saved: {csv_filename}")


def reverse_country(lon, lat, cache):
    """Reverse-geocode a point; return (country_code, country_name) or None."""
    key = _geocode_cache_key(lat, lon)
    if key in cache:
        return cache[key]
    url = "https://nominatim.openstreetmap.org/reverse"
    params = {"lat": lat, "lon": lon, "format": "json"}
    resp = requests.get(url, params=params, headers=NOMINATIM_HEADERS)
    resp.raise_for_status()
    data = resp.json()
    address = data.get("address", {})
    code = address.get("country_code", "").upper()
    name = address.get("country", code)
    result = (code, name) if code else None
    cache[key] = result
    return result


def _crag_country_slug(tags, lon, lat, geocode_cache):
    """Map crag location to 8a.nu country slug (e.g. germany, austria)."""
    for key in ("ISO3166-1:alpha2", "addr:country"):
        val = tags.get(key, "").strip().upper()
        if len(val) == 2:
            slug = A8_COUNTRY_SLUG.get(val)
            if slug:
                return slug
    if geocode_cache is not None and lon is not None and lat is not None:
        result = reverse_country(lon, lat, geocode_cache)
        if result:
            return A8_COUNTRY_SLUG.get(result[0])
    return None


def sample_route_points(route_coords, interval_km=VIGNETTE_SAMPLE_KM,
                        max_samples=VIGNETTE_MAX_SAMPLES):
    """Return (lon, lat) sample points along the route polyline."""
    route_line = LineString(route_coords)
    project = pyproj.Transformer.from_crs("epsg:4326", "epsg:3857",
                                          always_xy=True).transform
    unproject = pyproj.Transformer.from_crs("epsg:3857", "epsg:4326",
                                          always_xy=True).transform
    route_proj = transform(project, route_line)
    length_m = route_proj.length
    if length_m == 0:
        lon, lat = route_coords[0]
        return [(lon, lat)]

    interval_m = interval_km * 1000
    distances = [0.0]
    d = interval_m
    while d < length_m:
        distances.append(d)
        d += interval_m
    if distances[-1] < length_m:
        distances.append(length_m)

    if len(distances) > max_samples:
        step = max(1, len(distances) // max_samples)
        distances = distances[::step]
        if distances[-1] != length_m:
            distances.append(length_m)

    points = []
    for dist in distances:
        pt = route_proj.interpolate(dist)
        lon, lat = transform(unproject, pt).coords[0]
        points.append((lon, lat))
    return points


def countries_on_route(route_coords, geocode_cache=None):
    """Detect unique countries crossed by sampling the route."""
    samples = sample_route_points(route_coords)
    cache = geocode_cache if geocode_cache is not None else {}
    countries = {}
    for i, (lon, lat) in enumerate(samples):
        result = reverse_country(lon, lat, cache)
        if result:
            code, name = result
            countries[code] = name
    return countries


def calc_vignette_cost(route_coords, csv_path="vignettes.csv", vignettes=None,
                       geocode_cache=None, label=None):
    """Compute vignette cost for countries crossed (one fee per country)."""
    if vignettes is None:
        vignettes = vignette_load(csv_path)
    if not vignettes:
        print(f"⚠ No vignette data in {csv_path}")
        return 0.0

    if label is not None:
        print(f"\n--- Route {label}: vignettes ---")
    print("Detecting countries along route (Nominatim)...")
    countries = countries_on_route(route_coords, geocode_cache)
    if not countries:
        print("No countries detected on route.")
        return 0.0

    codes_sorted = sorted(countries.keys())
    print(f"Countries on route: {', '.join(codes_sorted)}")
    print("(Vignette prices are editable in vignettes.csv)")

    total = 0.0
    currency = "EUR"
    charged = []
    for code in codes_sorted:
        name = countries[code]
        if code in vignettes:
            entry = vignettes[code]
            fee = entry["fee"]
            currency = entry.get("currency", "EUR")
            if fee > 0:
                charged.append((name, code, fee, currency))
                total += fee
        else:
            print(f"  ⚠ crossed {name} ({code}) — no vignette price in {csv_path}")

    if charged:
        print("Vignettes:")
        for name, code, fee, cur in charged:
            print(f"  • {name} ({code}) — {fee:.2f} {cur}")
    print(f"Total vignette cost: {total:.2f} {currency}")
    return total


def calc_fuel_cost(distance_km, consumption_l_per_100km=consumption,
                   price_per_liter=fuel_cost, label=None):
    liters = (distance_km / 100) * consumption_l_per_100km
    total = liters * price_per_liter
    if label is not None:
        print(f"\n--- Route {label}: fuel ---")
    print(f"Distance: {distance_km:.1f} km, "
          f"consumption: {consumption_l_per_100km} L/100km @ "
          f"{price_per_liter:.2f} EUR/L")
    print(f"Fuel used: {liters:.1f} L")
    print(f"Fuel cost: {total:.2f} EUR")
    return total


def print_route_cost_summary(route_costs):
    print("\n=== Route cost summary ===")
    for r in route_costs:
        print(f"\nRoute {r['label']}: {r['dist_km']:.1f} km, {r['dur_h']:.2f} h")
        print(f"  Tolls:     {r['tolls']:8.2f} EUR")
        print(f"  Vignettes: {r['vignettes']:8.2f} EUR")
        print(f"  Fuel:      {r['fuel']:8.2f} EUR ({r['fuel_liters']:.1f} L)")
        print(f"  Total:     {r['total']:8.2f} EUR")


def calc_toll_cost(route, fmap=None, known_tolls=None, label=None):
    elements = _fetch_toll_elements(route)

    project = pyproj.Transformer.from_crs("epsg:4326", "epsg:3857",
                                          always_xy=True).transform
    route_proj = transform(project,  LineString(route))

    def distance_m(lon, lat):
        p = transform(project, Point(lon, lat))
        return route_proj.distance(p)  # distance in meters (because EPSG:3857)

    # === Step 6: Parse fee values ===
    def parse_fee(tags):
        """Extract numeric fee or interpret 'yes'."""
        name = tags.get("name")
        fee = tags.get("fee")
        currency = tags.get("fee:currency", "EUR")
        charge = tags.get("charge")
        if charge :
            match = re.search(r"(\d+(\.\d+)?)", charge)
            if match:
                return float(match.group(1)), currency
        if fee:
            # Extract numeric part
            match = re.search(r"(\d+(\.\d+)?)", fee)
            if match:
                return float(match.group(1)), currency
        if name :
            match = re.search(r"(\d+(\.\d+)?)", name.replace(',', '.'))
            if match:
                return float(match.group(1)), currency
        return 0, currency

    if known_tolls is None:
        known_tolls = toll_load("jumper_tolls.csv")
    nearby_tolls = []
    total_cost = 0.0
    for el in elements:
        lon, lat = el["lon"], el["lat"]
        node_id = int(el["id"])
        if distance_m(lon, lat) > max_distance_m:
            continue

        tags = el.get("tags", {})
        name = tags.get("name", "(unnamed)")

        if node_id in known_tolls:
            fee = known_tolls[node_id]
            currency = "EUR"
            source = "CSV"
        else:
            fee, currency = parse_fee(tags)
            source = "OSM"

        nearby_tolls.append({
            "id": node_id,
            "name": name,
            "lat": lat,
            "lon": lon,
            "fee": fee,
            "source": source,
            "currency": currency
        })
        total_cost += fee

    toll_update(nearby_tolls)
    if label is not None:
        print(f"\n--- Route {label}: tolls ---")
    print(f"Toll booths found: {len(nearby_tolls)}")
    for t in nearby_tolls:
        print(f"  • {t['name']} ({t['lat']:.4f},{t['lon']:.4f}) — {t['fee']} {t['currency']}")
    print(f"Total toll cost: {total_cost:.2f}" )


    if fmap:
        add_toll_markers(fmap, nearby_tolls)

    return total_cost, nearby_tolls


def run_route(start_city, end_city, *, buffer_km=10, vignettes_csv="vignettes.csv",
              geocode_cache_path="geocode_cache.csv", city_cache_path="city_cache.csv",
              a8_cache_path="8a_cache.csv",
              no_map=False, no_8a_resolve=False, no_toilets=False, no_parking=False):
    """Generate crag maps and GPX for a driving route between two cities.

    Returns a dict with ``base`` (filename basename) and ``paths`` (written files).
    """
    city_start = start_city
    city_end = end_city
    search_buffer_km = buffer_km

    geocode_cache = geocode_cache_load(geocode_cache_path)
    city_cache = city_cache_load(city_cache_path)
    a8_cache = None
    paths = []
    base = route_basename(city_start, city_end)
    try:
        start_lon, start_lat = geocode(city_start, city_cache)
        end_lon, end_lat = geocode(city_end, city_cache)
        print(f"Route: {city_start} → {city_end}")

        # === STEP 2: Get route polyline via OSRM ===
        osrm_url = f"https://router.project-osrm.org/route/v1/driving/{start_lon},{start_lat};{end_lon},{end_lat}"
        resp = requests.get(osrm_url, params={"overview": "full", "geometries":
                                          "geojson", "alternatives": "3" },
                            headers={"User-Agent": "route-climbing-fetcher"})
        resp.raise_for_status()
        route = resp.json()["routes"][0]["geometry"]["coordinates"]
        route_line = LineString([(lon, lat) for lon, lat in route])
        routes = resp.json()["routes"]

        # === STEP 3: Create buffer around route ===
        project = pyproj.Transformer.from_crs("epsg:4326", "epsg:3857",
                                              always_xy=True).transform
        route_buffer = transform(project, route_line).buffer(search_buffer_km * 1000)
        unproject = pyproj.Transformer.from_crs("epsg:3857", "epsg:4326",
                                                always_xy=True).transform
        route_buffer = transform(unproject, route_buffer)

        # === STEP 4: Query Overpass API (chunked along route) ===
        elements = fetch_crags_along_route(route, search_buffer_km)

        # === STEP 5: Filter to only those inside buffer ===
        def is_in_buffer(el):
            lat = el.get("lat") or el.get("center", {}).get("lat")
            lon = el.get("lon") or el.get("center", {}).get("lon")
            if lat is None or lon is None:
                return False
            return route_buffer.contains(Point(lon, lat))

        in_buffer = [el for el in elements if is_in_buffer(el)]
        outdoor_crags = filter_locations(in_buffer, "crags")
        all_with_gyms = filter_locations(in_buffer, "gym")
        known_crags = filter_locations(in_buffer, "known")
        gym_count = len(all_with_gyms) - len(outdoor_crags)
        print(f"Found {len(in_buffer)} in buffer: {len(outdoor_crags)} outdoor, "
              f"{gym_count} gyms; known={len(known_crags)}")

        nearest_toilets = {}
        if not no_map and not no_toilets:
            try:
                toilets = fetch_toilets_along_route(route, search_buffer_km)
                nearest_toilets = nearest_toilets_for_crags(outdoor_crags, toilets)
                print(f"Nearest toilets found for {len(nearest_toilets)} outdoor crags")
            except RuntimeError as exc:
                print(f"Warning: toilet lookup failed: {exc}")

        known_tolls = toll_load("jumper_tolls.csv")
        vignettes = vignette_load(vignettes_csv)
        route_colors = ["blue", "orange", "purple", "red"]

        primary_tolls = None
        route_costs = []
        for i, r in enumerate(routes):
            route_coords = r["geometry"]["coordinates"]
            label = i + 1
            dist_km = r["distance"] / 1000
            dur_h = r["duration"] / 60 / 60
            print(f"\n=== Route {label} ===")
            print(f"distance: {dist_km:.1f} km, duration: {dur_h:.2f} h")

            toll_total, route_tolls = calc_toll_cost(
                route_coords, fmap=None, known_tolls=known_tolls, label=label)
            if i == 0:
                primary_tolls = route_tolls
            vignette_total = calc_vignette_cost(
                route_coords, vignettes=vignettes,
                geocode_cache=geocode_cache, label=label)
            fuel_total = calc_fuel_cost(dist_km, label=label)
            fuel_liters = (dist_km / 100) * consumption
            total_cost = toll_total + vignette_total + fuel_total
            route_costs.append({
                "label": label,
                "dist_km": dist_km,
                "dur_h": dur_h,
                "tolls": toll_total,
                "vignettes": vignette_total,
                "fuel": fuel_total,
                "fuel_liters": fuel_liters,
                "total": total_cost,
            })
            print(f"Total travel cost (tolls + vignettes + fuel): "
                  f"{total_cost:.2f} EUR")

        print_route_cost_summary(route_costs)

        if not no_map and not no_8a_resolve:
            a8_cache = a8_cache_load(a8_cache_path)
            variants_for_names = [
                outdoor_crags,
                all_with_gyms,
                known_crags,
            ]
            to_resolve = set()
            for locations in variants_for_names:
                for el in locations:
                    tags = el.get("tags", {})
                    if is_indoor_gym(tags):
                        continue
                    name = _crag_name_from_tags(tags)
                    if not name:
                        continue
                    lat = el.get("lat") or el.get("center", {}).get("lat")
                    lon = el.get("lon") or el.get("center", {}).get("lon")
                    if _a8_lookup_entry(name, a8_cache, lat=lat, lon=lon):
                        continue
                    country_slug = _crag_country_slug(
                        tags, lon, lat, geocode_cache)
                    key = _a8_cache_key(name, country_slug, lat, lon)
                    if key not in a8_cache:
                        to_resolve.add((name, country_slug, lat, lon))
            for name, country_slug, lat, lon in sorted(to_resolve):
                resolve_8a_nu_url(
                    name, a8_cache, country_slug=country_slug, lat=lat, lon=lon)

        nearest_parking = {}
        if not no_map and not no_parking:
            if a8_cache is None:
                a8_cache = a8_cache_load(a8_cache_path)
            try:
                highlighted = highlighted_outdoor_crags(
                    outdoor_crags, a8_cache, geocode_cache)
                p4n_crags = outdoor_crags_for_p4n_parking(
                    outdoor_crags, a8_cache, geocode_cache, nearest_toilets)
                n_toilet = len(nearest_toilets or {})
                print(f"Beige crags: {len(highlighted)}, with OSM toilet: "
                      f"{n_toilet}, unique for p4n lookup: {len(p4n_crags)}")
                nearest_parking = nearest_parking_for_crags(p4n_crags)
                print(f"Nearest parking found for {len(nearest_parking)} crags")
            except requests.RequestException as exc:
                print(f"Warning: park4night lookup failed: {exc}")

        if not no_map:
            center_lat = (start_lat + end_lat) / 2
            center_lon = (start_lon + end_lon) / 2
            variants = [
                ("crags", outdoor_crags),
                ("crags_gym", all_with_gyms),
                ("crags_known", known_crags),
            ]
            for idx, (suffix, locations) in enumerate(variants):
                m = create_base_map(center_lat, center_lon)
                add_route_layers(
                    m, routes, route_buffer, search_buffer_km, route_colors,
                    start_lat, start_lon, end_lat, end_lon, city_start, city_end)
                if idx == 0 and primary_tolls:
                    add_toll_markers(m, primary_tolls)
                out_path = f"{base}_{suffix}.html"
                build_and_save_map(
                    m, locations, out_path,
                    a8_cache=a8_cache, geocode_cache=geocode_cache,
                    nearest_toilets=nearest_toilets,
                    nearest_parking=nearest_parking)
                paths.append(out_path)

        gpx_path = f"{base}_crags.gpx"
        save_crags_to_gpx(outdoor_crags, gpx_path)
        paths.append(gpx_path)
    finally:
        geocode_cache_save(geocode_cache, geocode_cache_path)
        city_cache_save(city_cache, city_cache_path)
        if a8_cache is not None:
            a8_cache_save(a8_cache, a8_cache_path)

    return {"base": base, "paths": paths}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Calculate toll cost between two cities using OSM data.")
    parser.add_argument("start_city", help="Name of the start city")
    parser.add_argument("end_city", help="Name of the end city")
    parser.add_argument("--buffer", type=float, default=10,
                        help="Buffer distance (km) around route for crag search")
    parser.add_argument("--csv", default="tolls.csv",
                        help="CSV file to store toll data")
    parser.add_argument("--no-map", action="store_true",
                        help="Disable map output")
    parser.add_argument("--vignettes-csv", default="vignettes.csv",
                        help="CSV file with per-country vignette prices")
    parser.add_argument("--geocode-cache", default="geocode_cache.csv",
                        help="CSV file to cache Nominatim reverse-geocode results")
    parser.add_argument("--city-cache", default="city_cache.csv",
                        help="CSV file to cache Nominatim city location lookups")
    parser.add_argument("--8a-cache", dest="a8_cache", default="8a_cache.csv",
                        help="CSV file to cache 8a.nu URL lookups")
    parser.add_argument("--no-8a-resolve", action="store_true",
                        help="Skip 8a.nu search resolution; use search URLs only")
    parser.add_argument("--no-toilets", action="store_true",
                        help="Skip nearest-toilet lookup and map markers")
    parser.add_argument("--no-parking", action="store_true",
                        help="Skip park4night parking lookup")
    args = parser.parse_args()

    run_route(
        args.start_city, args.end_city,
        buffer_km=args.buffer,
        vignettes_csv=args.vignettes_csv,
        geocode_cache_path=args.geocode_cache,
        city_cache_path=args.city_cache,
        a8_cache_path=args.a8_cache,
        no_map=args.no_map,
        no_8a_resolve=args.no_8a_resolve,
        no_toilets=args.no_toilets,
        no_parking=args.no_parking,
    )
