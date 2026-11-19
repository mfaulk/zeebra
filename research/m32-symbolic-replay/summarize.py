#!/usr/bin/env python3
"""Tables for #933's symbolic replay (docs/research/m32-parallel-symbolic.md §4).

    python3 research/m32-symbolic-replay/summarize.py research/m32-symbolic-replay/replay.jsonl.gz

Each input line is one fresh `sig_f4_study --symbolic-replay` process. Per row and engine worker
count, every figure is the median over processes of a per-process sum over batches; a speedup is
the median of the per-process ratios (the engine's own closure ÷ the prototype, same process).
"""
import gzip
import json
import statistics
import sys

WORKERS = [1, 4, 8, 16]
# M31 reference, f4_signature cascade at 16 workers (research/m31-final/tables.md, plan §2.2).
M31 = {"eco-12": (552.0, 1752.0), "mq-random-10": (232.0, 380.0)}


def load(path):
    opener = gzip.open if path.endswith(".gz") else open
    with opener(path, "rt") as f:
        return [json.loads(line) for line in f if line.strip()]


def med(xs):
    return statistics.median(xs)


def main(path):
    runs = [r for r in load(path) if not r.get("failed")]
    keys = sorted({(r["name"], r["engine_workers"]) for r in runs})
    print("| Row | Engine w | n | Engine closure ms | Lookup share | Levels (max width) | "
          + " | ".join(f"S{w}" for w in WORKERS) + " | S16, parallel sort | Merge share at 16 |")
    print("|---|---:|---:|---:|---:|---:|" + "---:|" * len(WORKERS) + "---:|---:|")
    projections = {}
    for name, ew in keys:
        group = [r for r in runs if (r["name"], r["engine_workers"]) == (name, ew)]
        serial = [sum(b["serial_ns"] for b in r["batches"]) for r in group]
        lookup = [r["lookup_ns"] / s for r, s in zip(group, serial)]
        levels = [sum(len(b["levels"]) for b in r["batches"]) for r in group]
        width = max(max(b["levels"]) for b in group[0]["batches"])
        speedups, sorted16, merge16 = [], [], []
        for k, w in enumerate(WORKERS):
            ratio = []
            for r, s in zip(group, serial):
                total = sum(b["runs"][k]["total_ns"] for b in r["batches"])
                ratio.append(s / total)
                if w == 16:
                    sort = sum(b["runs"][k]["sort_ns"] for b in r["batches"])
                    merge = sum(b["runs"][k]["merge_ns"] for b in r["batches"])
                    sorted16.append(s / (total - sort + sort / w))
                    merge16.append(merge / total)
            speedups.append(med(ratio))
        print(f"| {name} | {ew} | {len(group)} | {med(serial) / 1e6:.1f} | {med(lookup):.1%} | "
              f"{med(levels)} ({width}) | " + " | ".join(f"{s:.2f}" for s in speedups)
              + f" | {med(sorted16):.2f} | {med(merge16):.1%} |")
        if ew == 16:
            projections[name] = (speedups[-1], med(sorted16))
    print()
    print("| Row | M31 symbolic ms | M31 wall ms | S16 | Projected symbolic ms | Projected wall ms "
          "| ÷ M31 wall |")
    print("|---|---:|---:|---:|---:|---:|---:|")
    for name, (s16, s16_sorted) in sorted(projections.items()):
        if name not in M31:
            continue
        sym, wall = M31[name]
        for label, s in (("as run", s16), ("parallel sort", s16_sorted)):
            projected = wall - sym + sym / s
            print(f"| {name} ({label}) | {sym:.0f} | {wall:.0f} | {s:.2f} | {sym / s:.0f} | "
                  f"{projected:.0f} | {projected / wall:.3f} |")


if __name__ == "__main__":
    main(sys.argv[1])
