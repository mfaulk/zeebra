#!/usr/bin/env python3
"""Markdown tables for docs/research/m31-parallel-signature-elimination.md §6 from the
`sig_f4_study --replay` records in this directory (one JSON object per file)."""
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROWS = sys.argv[1:] or [p.stem for p in sorted(HERE.glob("*.json"))]


def load(stem):
    return json.loads((HERE / f"{stem}.json").read_text())


def total(batches, key):
    return sum(b[key] for b in batches)


print("| Row | Batches | Targets (zero) | d1 products | d2 ÷ d1 | Max width | Max depth "
      "| Dependent targets | CP share dag / frontier / claim | Shadowed | Would displace (suffix ÷ d1) |")
print("|---|---:|---:|---:|---:|---:|---:|---:|---|---:|---:|")
for stem in ROWS:
    d = load(stem)
    b1, b2 = d["design1_batches"], d["design2_batches"]
    w1 = total(b1, "phase_a") + total(b1, "cascade")
    w2 = total(b2, "phase_a") + total(b2, "cascade")
    share = " / ".join(f"{total(b1, k) / w1:.3f}" for k in ("cp_dag", "cp_frontier", "cp_claim"))
    print(f"| {d['name']} / {d['field']} | {len(b1)} | {total(b1, 'targets'):,} "
          f"({total(b1, 'zero_targets'):,}) | {w1 / 1e9:.3f} G | {w2 / w1:.3f} "
          f"| {max(b['width'] for b in b1)} | {max(b['depth'] for b in b1)} "
          f"| {total(b1, 'dependent_targets'):,} | {share} | {total(b1, 'shadowed'):,} "
          f"| {total(b1, 'would_displace'):,} ({total(b1, 'displaced_suffix') / w1:.3f}) |")

print()
print("| Row | Arm / schedule | Products ÷ d1 | 4 | 8 | 16 | 16 (greedy) |")
print("|---|---|---:|---:|---:|---:|---:|")
for stem in ROWS:
    d = load(stem)
    cells = {}
    for c in d["ceilings"]:
        cells.setdefault((c["arm"], c["schedule"]), {})[c["workers"]] = c
    for (arm, schedule), by in cells.items():
        print(f"| {d['name']} / {d['field']} | {arm} / {schedule} | {by[16]['products_ratio']} "
              f"| {by[4]['ceiling']} | {by[8]['ceiling']} | {by[16]['ceiling']} "
              f"| {by[16]['greedy']} |")
