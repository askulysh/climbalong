#!/usr/bin/python3
"""HTTP server for browsing and generating climbing route map pages."""

import argparse
import html
import os
import re
import socket
import ssl
import subprocess
import sys
import threading
import traceback
from http.server import ThreadingHTTPServer, SimpleHTTPRequestHandler
from urllib.parse import parse_qs, quote

from route3 import run_route

ROOT = os.path.dirname(os.path.abspath(__file__))
CRAGS_HTML_RE = re.compile(r"^(.+)_crags\.html$")
GENERATE_LOCK = threading.Lock()
CERT_PATH = os.path.join(ROOT, "cert.pem")
KEY_PATH = os.path.join(ROOT, "key.pem")


def discover_routes(directory=ROOT):
    """Return sorted list of prepared route basenames from *_crags.html files."""
    routes = []
    for name in os.listdir(directory):
        match = CRAGS_HTML_RE.match(name)
        if not match:
            continue
        # Exclude gym/known variants (they end in _crags_gym / _crags_known)
        if name.endswith("_crags_gym.html") or name.endswith("_crags_known.html"):
            continue
        base = match.group(1)
        routes.append(base)
    return sorted(set(routes))


def route_labels(base):
    """Split basename into start/end display labels."""
    parts = base.split("_", 1)
    if len(parts) == 2:
        return parts[0].replace("_", " "), parts[1].replace("_", " ")
    return base, ""


def index_html(routes, error=None, busy=False):
    rows = []
    for base in routes:
        start, end = route_labels(base)
        outdoor = f"{base}_crags.html"
        gym = f"{base}_crags_gym.html"
        known = f"{base}_crags_known.html"
        gpx = f"{base}_crags.gpx"
        links = []
        if os.path.isfile(os.path.join(ROOT, outdoor)):
            links.append(f'<a href="/{quote(outdoor)}">outdoor</a>')
        if os.path.isfile(os.path.join(ROOT, gym)):
            links.append(f'<a href="/{quote(gym)}">gym</a>')
        if os.path.isfile(os.path.join(ROOT, known)):
            links.append(f'<a href="/{quote(known)}">known</a>')
        if os.path.isfile(os.path.join(ROOT, gpx)):
            links.append(f'<a href="/{quote(gpx)}">gpx</a>')
        label = html.escape(f"{start} → {end}" if end else start)
        rows.append(
            f"<tr><td>{label}</td><td>{' · '.join(links)}</td></tr>"
        )

    empty_row = '<tr><td colspan="2">No prepared routes yet.</td></tr>'
    body_rows = "".join(rows) if rows else empty_row
    routes_section = (
        "<table><thead><tr><th>Route</th><th>Maps</th></tr></thead>"
        f"<tbody>{body_rows}</tbody></table>"
    )

    notices = []
    if busy:
        notices.append(
            '<p class="busy">A route generation is already running. '
            "Try again when it finishes.</p>"
        )
    if error:
        notices.append(f'<pre class="error">{html.escape(error)}</pre>')

    return f"""<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <title>Climbing route maps</title>
  <style>
    body {{ font-family: system-ui, sans-serif; max-width: 52rem; margin: 2rem auto; padding: 0 1rem; }}
    h1 {{ font-size: 1.5rem; }}
    h2 {{ font-size: 1.15rem; margin-top: 2rem; }}
    table {{ border-collapse: collapse; width: 100%; }}
    th, td {{ text-align: left; padding: 0.4rem 0.6rem; border-bottom: 1px solid #ddd; }}
    form {{ display: grid; gap: 0.75rem; max-width: 24rem; }}
    label {{ display: flex; flex-direction: column; gap: 0.25rem; font-size: 0.9rem; }}
    label.check {{ flex-direction: row; align-items: center; gap: 0.5rem; }}
    input[type="text"], input[type="number"] {{ padding: 0.35rem 0.5rem; font-size: 1rem; }}
    button {{ width: fit-content; padding: 0.45rem 1rem; font-size: 1rem; cursor: pointer; }}
    .error {{ background: #fde8e8; padding: 0.75rem; overflow-x: auto; }}
    .busy {{ color: #a30; font-weight: 600; }}
    .hint {{ color: #555; font-size: 0.85rem; }}
  </style>
</head>
<body>
  <h1>Climbing route maps</h1>
  {''.join(notices)}

  <h2>Prepared routes</h2>
  {routes_section}

  <h2>Generate a new route</h2>
  <p class="hint">Generation may take several minutes (OSRM, Overpass, optional 8a/toilets/parking).</p>
  <form method="post" action="/generate">
    <label>Start city
      <input type="text" name="start" required placeholder="e.g. Lviv">
    </label>
    <label>End city
      <input type="text" name="end" required placeholder="e.g. Chamonix">
    </label>
    <label>Buffer (km)
      <input type="number" name="buffer" value="10" min="1" max="100" step="1">
    </label>
    <label class="check">
      <input type="checkbox" name="no_8a_resolve" value="1">
      Skip 8a.nu resolution
    </label>
    <label class="check">
      <input type="checkbox" name="no_toilets" value="1">
      Skip toilet lookup
    </label>
    <label class="check">
      <input type="checkbox" name="no_parking" value="1">
      Skip park4night parking
    </label>
    <button type="submit">Generate</button>
  </form>
</body>
</html>
"""


class RouteHandler(SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=ROOT, **kwargs)

    def do_GET(self):
        if self.path in ("/", "/index.html"):
            body = index_html(discover_routes()).encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return
        return super().do_GET()

    def do_POST(self):
        if self.path.rstrip("/") != "/generate":
            self.send_error(404, "Not found")
            return

        length = int(self.headers.get("Content-Length", 0))
        raw = self.rfile.read(length).decode("utf-8", errors="replace")
        form = parse_qs(raw)

        start = (form.get("start") or [""])[0].strip()
        end = (form.get("end") or [""])[0].strip()
        try:
            buffer_km = float((form.get("buffer") or ["10"])[0] or 10)
        except ValueError:
            buffer_km = 10.0
        no_8a = "no_8a_resolve" in form
        no_toilets = "no_toilets" in form
        no_parking = "no_parking" in form

        if not start or not end:
            body = index_html(
                discover_routes(), error="Start and end cities are required."
            ).encode("utf-8")
            self.send_response(400)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return

        if not GENERATE_LOCK.acquire(blocking=False):
            body = index_html(discover_routes(), busy=True).encode("utf-8")
            self.send_response(503)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return

        try:
            result = run_route(
                start, end,
                buffer_km=buffer_km,
                no_8a_resolve=no_8a,
                no_toilets=no_toilets,
                no_parking=no_parking,
            )
            target = f"/{result['base']}_crags.html"
            self.send_response(302)
            self.send_header("Location", target)
            self.end_headers()
        except Exception:
            err = traceback.format_exc()
            print(err, file=sys.stderr)
            body = index_html(discover_routes(), error=err).encode("utf-8")
            self.send_response(500)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
        finally:
            GENERATE_LOCK.release()

    def log_message(self, fmt, *args):
        sys.stderr.write("%s - %s\n" % (self.address_string(), fmt % args))


def ensure_tls_certs(cert_path=CERT_PATH, key_path=KEY_PATH):
    """Ensure cert.pem / key.pem exist; create a self-signed pair via openssl if missing."""
    if os.path.isfile(cert_path) and os.path.isfile(key_path):
        return cert_path, key_path
    print(f"Generating self-signed TLS cert → {cert_path}, {key_path}")
    try:
        subprocess.run(
            [
                "openssl", "req", "-x509", "-newkey", "rsa:2048",
                "-keyout", key_path, "-out", cert_path,
                "-days", "825", "-nodes",
                "-subj", "/CN=climbing-route-maps",
            ],
            check=True,
            capture_output=True,
        )
    except FileNotFoundError:
        raise SystemExit(
            "openssl not found; install it or create cert.pem and key.pem manually"
        )
    except subprocess.CalledProcessError as exc:
        err = (exc.stderr or b"").decode("utf-8", errors="replace")
        raise SystemExit(f"Failed to generate TLS cert: {err}")
    return cert_path, key_path


def lan_ip():
    """Best-effort LAN IPv4 for display (not used for binding)."""
    try:
        with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as s:
            s.connect(("8.8.8.8", 80))
            return s.getsockname()[0]
    except OSError:
        return None


def main():
    parser = argparse.ArgumentParser(description="Serve climbing route map pages")
    parser.add_argument("--port", type=int, default=8000,
                        help="Port to listen on (default: 8000)")
    parser.add_argument("--bind", default="0.0.0.0",
                        help="Address to bind (default: 0.0.0.0)")
    parser.add_argument(
        "--https", action="store_true",
        help="Serve HTTPS (needed for GPS locate on Android Chrome over LAN). "
             "Uses cert.pem/key.pem; generates them with openssl if missing.",
    )
    args = parser.parse_args()

    os.chdir(ROOT)
    server = ThreadingHTTPServer((args.bind, args.port), RouteHandler)
    scheme = "http"
    if args.https:
        cert, key = ensure_tls_certs()
        ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        ctx.load_cert_chain(certfile=cert, keyfile=key)
        server.socket = ctx.wrap_socket(server.socket, server_side=True)
        scheme = "https"

    host_hint = lan_ip() if args.bind in ("0.0.0.0", "::") else args.bind
    print(f"Serving route maps at {scheme}://{args.bind}:{args.port}/")
    if host_hint and host_hint != args.bind:
        print(f"  On phone (same Wi-Fi): {scheme}://{host_hint}:{args.port}/")
        if args.https:
            print("  Accept the self-signed certificate warning once for GPS locate.")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nShutting down")
        server.shutdown()


if __name__ == "__main__":
    main()
