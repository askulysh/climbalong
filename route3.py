#!/usr/bin/python3

import requests
from shapely.geometry import LineString, Point
from shapely.ops import substring, transform
import pyproj
import folium
import urllib.parse
import xml.etree.ElementTree as ET
import re
import csv
import os
import argparse
import time

# === CONFIGURATION ===
#city_start = "Chernivtsi, Ukraine"
city_start = "Giurgiu"
#city_start = "Arta, Greece"
#city_start ="Athens, Greece"
#city_end = "Paradisos, Greece"
#city_start = "Paradisos, Greece"
city_end = "Leonidio, Greece"
#city_end = "Antalya"
#city_end = "Arco"
#city_end = "Giurgiu"
#city_end = "Chernivtsi, Ukraine"
buffer_km = 10  # default distance around route to search for crags (km)
max_distance_m = 10
consumption = 7.5
fuel_cost = 1.4

CRAG_SEGMENT_KM = 250
OVERPASS_URLS = [
    "https://overpass-api.de/api/interpreter",
    "https://overpass.kumi.systems/api/interpreter",
]
OVERPASS_HEADERS = {"User-Agent": "route-climbing-fetcher"}

#routes = 3

# === STEP 1: Geocode cities (Nominatim) ===
def geocode(city_name):
    url = "https://nominatim.openstreetmap.org/search"
    params = {"q": city_name, "format": "json", "limit": 1}
    resp = requests.get(url, params=params,
                        headers={"User-Agent": "route-climbing-fetcher"})
    resp.raise_for_status()
    data = resp.json()
    if not data:
        raise ValueError(f"City not found: {city_name}")
    return float(data[0]["lon"]), float(data[0]["lat"])

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
        ET.SubElement(wpt, "desc").text = f"https://www.openstreetmap.org/{el['type']}/{el['id']}"
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
VIGNETTE_SAMPLE_KM = 40
VIGNETTE_MAX_SAMPLES = 25


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


def reverse_country(lon, lat, cache):
    """Reverse-geocode a point; return (country_code, country_name) or None."""
    key = (round(lat, 3), round(lon, 3))
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
        if i > 0:
            time.sleep(1.1)
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


    if fmap :
        for t in nearby_tolls:
            osm_link = f"https://www.openstreetmap.org/node/{t['id']}"
            popup_html = f"""
            <b>{t['name']}</b><br>
            Fee: {t['fee']} {t['currency']}<br>
            <a href="{osm_link}" target="_blank">OpenStreetMap</a>
            """
            folium.Marker(
                [t["lat"], t["lon"]],
                popup=popup_html,
                tooltip=f"{t['name']} ({t['fee']} {t['currency']})",
                icon=folium.Icon(color="blue", icon="road", prefix="fa")
            ).add_to(fmap)

    return total_cost


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
    args = parser.parse_args()

    city_start = args.start_city
    city_end = args.end_city
    search_buffer_km = args.buffer

    start_lon, start_lat = geocode(city_start)
    end_lon, end_lat = geocode(city_end)
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


    crags = [el for el in elements if is_in_buffer(el)]
    print(f"Found {len(crags)} climbing crags along the route.")


    # === STEP 6: Create map ===
    center_lat = (start_lat + end_lat) / 2
    center_lon = (start_lon + end_lon) / 2
    m = folium.Map(location=[center_lat, center_lon], zoom_start=6,
                   tiles=None)
    
    # CartoDB Positron: Beautiful, fast, and fully compatible with local file (file://) protocol viewing
    folium.TileLayer(
        tiles="https://{s}.basemaps.cartocdn.com/light_all/{z}/{x}/{y}{r}.png",
        name="CartoDB Positron (Local File Compatible)",
        attr='&copy; <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a> contributors &copy; <a href="https://carto.com/attributions">CARTO</a>'
    ).add_to(m)
    
    # Standard OpenStreetMap: Requires a local web server (e.g. python -m http.server) to satisfy Referer checks
    folium.TileLayer(
        tiles="https://tile.openstreetmap.org/{z}/{x}/{y}.png",
        name="OpenStreetMap (Requires Web Server)",
        attr='&copy; <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a> contributors',
        referrerPolicy="no-referrer-when-downgrade"
    ).add_to(m)

    fmap = None if args.no_map else m
    known_tolls = toll_load("jumper_tolls.csv")
    vignettes = vignette_load(args.vignettes_csv)
    geocode_cache = {}
    route_colors = ["blue", "orange", "purple", "red"]

    for i, r in enumerate(routes):
        route_coords = r["geometry"]["coordinates"]
        label = i + 1
        dist_km = r["distance"] / 1000
        dur_h = r["duration"] / 60 / 60
        print(f"\n=== Route {label} ===")
        print(f"distance: {dist_km:.1f} km, duration: {dur_h:.2f} h")

        route_fmap = fmap if i == 0 else None
        toll_total = calc_toll_cost(route_coords, route_fmap, known_tolls, label)
        vignette_total = calc_vignette_cost(
            route_coords, vignettes=vignettes,
            geocode_cache=geocode_cache, label=label)
        print(f"Total travel cost (tolls + vignettes): "
              f"{toll_total + vignette_total:.2f} EUR")

        route_ = [(lat, lon) for lon, lat in route_coords]
        color = route_colors[i % len(route_colors)]
        folium.PolyLine(route_, color=color, weight=3, opacity=0.8,
                        tooltip=f"Route {label}").add_to(m)

    # Buffer polygon (approximate)
    buffer_coords = list(route_buffer.exterior.coords)
    folium.Polygon([(lat, lon) for lon, lat in buffer_coords],
               color="green", weight=1, fill=True, fill_opacity=0.1,
               tooltip=f"Search area ±{search_buffer_km} km").add_to(m)

    # === STEP 7: Add markers for crags ===
    for el in crags:
        tags = el.get("tags", {})
        name = tags.get("int_name", tags.get("name:en", tags.get("name",
                                                             "Unnamed crag")))
        lat = el.get("lat") or el.get("center", {}).get("lat")
        lon = el.get("lon") or el.get("center", {}).get("lon")

        osm_url = f"https://www.openstreetmap.org/{el['type']}/{el['id']}"
        query_name = urllib.parse.quote(name)
        thecrag_url = tags.get("climbing:url:thecrag",
                    f"https://www.thecrag.com/search?S={query_name}#crags")
        a8nu_url = f"https://www.8a.nu/search/crags?query={query_name}"

        popup_html = f"""
        <b>{name}</b><br>
        📍 {lat:.4f}, {lon:.4f}<br>
        <a href="{osm_url}" target="_blank">OpenStreetMap</a> |
        <a href="{thecrag_url}" target="_blank">TheCrag</a> |
        <a href="{a8nu_url}" target="_blank">8a.nu</a>
        """
        folium.Marker(
            [lat, lon],
            popup=folium.Popup(popup_html, max_width=300),
            icon=folium.Icon(color="red", icon="flag")
        ).add_to(m)

    # Start & end markers
    folium.Marker([start_lat, start_lon], popup=f"Start: {city_start}",
                  icon=folium.Icon(color="green")).add_to(m)
    folium.Marker([end_lat, end_lon], popup=f"End: {city_end}",
                  icon=folium.Icon(color="blue")).add_to(m)

    # === STEP 8: Save map ===
    folium.LayerControl().add_to(m)
    m.save("climbing_crags_route.html")
    print("✅ Map saved to climbing_crags_route.html")

    save_crags_to_gpx(crags, "crags.gpx")
