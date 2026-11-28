"""Tables for docs/research/m5gb-paper-reference.md from the #1165 run records.

    python3 research/1165-m5gb-paper-reference/summarize.py [verdicts|fields|dense|probe]
"""

import collections
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def load(variant):
    path = os.path.join(HERE, f"runs-{variant}.jsonl")
    with open(path) as f:
        lines = [json.loads(line) for line in f]
    return lines[0], lines[1:]


def verdicts():
    for variant in ("upstream", "repair-interreduce", "hash-probe", "hash-narrow"):
        try:
            _, rows = load(variant)
        except FileNotFoundError:
            continue
        table = collections.defaultdict(collections.Counter)
        for r in rows:
            table[r["family"]][r["verdict"]] += 1
        print(f"\n{variant}: {len(rows)} rows")
        print("| family | rows | " + " | ".join(["verdicts"]) + " |")
        print("|---|---|---|")
        for family, counts in sorted(table.items()):
            text = ", ".join(f"{v} {n}" for v, n in counts.most_common())
            print(f"| {family} | {sum(counts.values())} | {text} |")


def fields():
    _, rows = load("upstream")
    table = collections.defaultdict(collections.Counter)
    for r in rows:
        if r["family"] in ("control", "dense-mq"):
            table[r["modulus"]][r["verdict"]] += 1
    print("| p | rows | verdicts |")
    print("|---|---|---|")
    for p, counts in sorted(table.items()):
        text = ", ".join(f"{v} {n}" for v, n in counts.most_common())
        print(f"| {p} | {sum(counts.values())} | {text} |")


def dense():
    _, rows = load("upstream")
    print("| row | M5GB s | Zeebra s | peak RSS MiB | raw elements | raw terms | canon s | verdict |")
    print("|---|---|---|---|---|---|---|---|")
    for r in rows:
        if r["family"] != "scale" and not (r["family"] == "dense-mq" and r["n"] == 10
                                           and r["modulus"] == 101 and "d1000-s116501" in r["row"]):
            continue
        raw = r.get("raw", {})
        z = r.get("zeebra_wall_s")
        print(f"| {r['row']} | {r['m5gb']['wall_s']:.2f} | "
              f"{z:.2f} | {r['m5gb']['peak_rss_bytes'] >> 20} | {raw.get('elements')} | "
              f"{raw.get('terms')} | {r.get('canonical', {}).get('seconds')} | {r['verdict']} |")


def probe():
    _, rows = load("hash-probe")
    lookups = sum(r["counters"].get("probe_reducer_map_lookups", 0) for r in rows)
    print(f"rows {len(rows)}, reducer-map lookups {lookups}")
    for r in rows:
        c = r["counters"]
        if c.get("probe_poly_append_collisions") or c.get("probe_reducer_map_collisions"):
            print(r["row"], r["verdict"], c.get("probe_poly_append_collisions"),
                  c.get("probe_reducer_map_collisions"))
    biggest = max(rows, key=lambda r: r["counters"].get("probe_reducer_map_lookups", 0))
    print("largest:", biggest["row"], biggest["counters"].get("probe_reducer_map_lookups"))


if __name__ == "__main__":
    {"verdicts": verdicts, "fields": fields, "dense": dense, "probe": probe}[
        sys.argv[1] if len(sys.argv) > 1 else "verdicts"]()
