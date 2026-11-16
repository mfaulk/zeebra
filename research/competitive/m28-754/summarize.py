#!/usr/bin/env python3
"""Pair #754's serial and 16-worker Zeebra rows by cell, against the previous Zeebra row and the
fastest complete comparand row for the same cell. Reads history.json; writes Markdown to stdout.

    python3 research/competitive/m28-754/summarize.py <commit> [history.json]
"""
import json
import sys

commit = sys.argv[1]
path = sys.argv[2] if len(sys.argv) > 2 else "research/competitive/results/history.json"
rows = json.load(open(path))["rows"]


def key(r):
    return (r["problem"], r["task"], r["field"]["characteristic"])


def outcome(r):
    o = r["outcome"]
    return o if isinstance(o, str) else next(iter(o))


def cell(r):
    if r is None:
        return "—"
    if outcome(r) != "complete":
        return outcome(r)
    return f"{r['wall_nanos'] / 1e6:.1f}"


def mib(r):
    b = r and r.get("peak_rss_bytes")
    return f"{b / 2**20:.1f}" if b else "—"


ours = {}
previous = {}
comparand = {}
for r in rows:
    k = key(r)
    if r["library"] == "zeebra":
        if r["environment"]["commit"] == commit:
            ours[(k, r["environment"]["concurrency"])] = r
        elif r["environment"]["concurrency"] == 1:
            previous[k] = r  # last serial Zeebra row before this cohort
    elif outcome(r) == "complete" and r["library"] != "sagebrush":
        best = comparand.get(k)
        if best is None or r["wall_nanos"] < best["wall_nanos"]:
            comparand[k] = r

cells = sorted({k for k, _ in ours}, key=lambda k: (str(k[2]), k[0], k[1]))
print("| problem | task | p | previous serial ms | serial ms | 16w ms | 16w speedup | serial MiB | 16w MiB | fastest comparand ms (engine, workers) |")
print("|---|---|---|---:|---:|---:|---:|---:|---:|---|")
for k in cells:
    s, w = ours.get((k, 1)), ours.get((k, 16))
    speed = "—"
    if s and w and outcome(s) == outcome(w) == "complete":
        speed = f"{s['wall_nanos'] / w['wall_nanos']:.2f}x"
    c = comparand.get(k)
    best = f"{cell(c)} ({c['library']}, {c['environment']['concurrency']})" if c else "—"
    task = "RGB" if k[1] == "reduced-grobner-basis" else ("lex" if k[1].startswith("lex") else k[1])
    p = {2147483647: "M31", 18446744073709551263: "2^64-353"}.get(k[2], str(k[2]))
    print(f"| {k[0]} | {task} | {p} | {cell(previous.get(k))} | {cell(s)} | {cell(w)} | {speed} | {mib(s)} | {mib(w)} | {best} |")
