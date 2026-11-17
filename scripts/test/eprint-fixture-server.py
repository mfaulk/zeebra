#!/usr/bin/env python3
"""Local stand-in for the ePrint mirror, so fetch-eprint-test.sh never touches the network.

Each paper number selects a behaviour (see ROUTES). Every request path is appended to --log, which
is how the tests count network hits. The bound port is written to --port-file.
"""
import argparse
import http.server
import os
import threading
import time


def fixture_pdf(text: str) -> bytes:
    """A minimal one-page PDF with real xref offsets, so pdftotext can extract `text`."""
    content = f"BT /F1 12 Tf 72 720 Td ({text}) Tj ET".encode()
    objects = [
        b"<< /Type /Catalog /Pages 2 0 R >>",
        b"<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
        b"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792] "
        b"/Resources << /Font << /F1 4 0 R >> >> /Contents 5 0 R >>",
        b"<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica >>",
        b"<< /Length %d >>\nstream\n%s\nendstream" % (len(content), content),
    ]
    out = bytearray(b"%PDF-1.4\n")
    offsets = []
    for i, body in enumerate(objects, start=1):
        offsets.append(len(out))
        out += b"%d 0 obj\n%s\nendobj\n" % (i, body)
    xref = len(out)
    out += b"xref\n0 %d\n0000000000 65535 f \n" % (len(objects) + 1)
    for off in offsets:
        out += b"%010d 00000 n \n" % off
    out += b"trailer\n<< /Size %d /Root 1 0 R >>\nstartxref\n%d\n%%%%EOF\n" % (len(objects) + 1, xref)
    return bytes(out)


PDF = fixture_pdf("Fixture paper for fetch-eprint")
HTML = b"<!DOCTYPE html><html><head><title>Just a moment...</title></head><body>challenge</body></html>"
counts: dict = {}
lock = threading.Lock()


class Handler(http.server.BaseHTTPRequestHandler):
    log_path = ""

    def log_message(self, *args):  # silence stderr
        pass

    def send(self, code, body, ctype):
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        with lock:
            with open(self.log_path, "a") as log:
                log.write(self.path + "\n")
            counts[self.path] = counts.get(self.path, 0) + 1
            n = counts[self.path]
        route = self.path.rsplit("/", 1)[-1]
        if route in ("2340.pdf", "001.pdf"):
            self.send(200, PDF, "application/pdf")
        elif route == "403.pdf":
            self.send(403, HTML, "text/html")
        elif route == "404.pdf":
            self.send(404, b"not found", "text/plain")
        elif route == "200.pdf":
            self.send(200, HTML, "text/html")
        elif route == "100.pdf":
            self.send(200, PDF[: len(PDF) // 2], "application/pdf")
        elif route == "503.pdf":
            if n <= 2:
                self.send(503, b"busy", "text/plain")
            else:
                self.send(200, PDF, "application/pdf")
        elif route == "500.pdf":
            self.send(500, b"error", "text/plain")
        elif route == "777.pdf":
            time.sleep(1.0)
            self.send(200, PDF, "application/pdf")
        else:
            self.send(404, b"no route", "text/plain")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--port-file", required=True)
    ap.add_argument("--log", required=True)
    args = ap.parse_args()
    Handler.log_path = args.log
    server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Handler)
    with open(args.port_file + ".tmp", "w") as f:
        f.write(str(server.server_address[1]))
    os.replace(args.port_file + ".tmp", args.port_file)
    server.serve_forever()


if __name__ == "__main__":
    main()
