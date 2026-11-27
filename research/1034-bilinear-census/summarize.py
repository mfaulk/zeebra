#!/usr/bin/env python3
"""Summarize #1034's bidegree census (counts.tsv) under the criteria pre-declared on the issue.

S     = largest built F4 matrix / largest regrouped bidegree block (rows x columns).
D     = perturbed control's largest matrix / bilinear's largest matrix.
share = ln D / (ln D + ln S), 0 when D <= 1: the part of the gain over the control that
        total-degree F4 already has through its lower solving degree.

Usage: summarize.py counts.tsv > tables.md
"""

import csv
import math
import statistics
import sys
from collections import Counter, defaultdict

BALANCED = {("5", "5"), ("6", "6"), ("7", "7"), ("8", "8")}


def fmt(xs, spec="{:.2f}"):
    if not xs:
        return "—"
    return (spec + " [" + spec + ", " + spec + "]").format(
        statistics.median(xs), min(xs), max(xs)
    )


def main(path):
    rows = list(csv.DictReader(open(path), delimiter="\t"))
    groups = defaultdict(list)
    status = Counter()
    for r in rows:
        key = (r["kind"], r["k"], r["n_y"])
        status[key + (r["status"],)] += 1
        if r["status"] != "done":
            continue
        s = float(r["reduction"])
        area = int(r["largest_matrix"])
        d = share = None
        if r["control_largest_matrix"].isdigit():
            d = int(r["control_largest_matrix"]) / area
            share = 0.0 if d <= 1 else math.log(d) / (math.log(d) + math.log(s))
        sig = None
        if r["sig_max_rows"].isdigit():
            sig = int(r["sig_max_rows"]) * int(r["sig_max_columns"])
        groups[key].append(
            dict(
                s=s,
                d=d,
                share=share,
                degree=int(r["degree"]),
                control_degree=r["control_degree"],
                dup=int(r["regrouped_columns"]) / int(r["columns"]),
                area=area,
                block=int(r["largest_block"]),
                sig=sig,
                control=r["control_degree"] if not r["control_degree"].isdigit() else "done",
            )
        )

    print("| kind | k × n_y | done / failed / censored / skipped | F4 degree | control degree "
          "| largest matrix (median) | S median [min, max] | D median [min, max] "
          "| share median [min, max] | column duplication | sig extents ÷ largest block (median) "
          "| controls |")
    print("|---|---|---|---|---|---:|---:|---:|---:|---:|---:|---|")
    keys = sorted({k[:3] for k in status}, key=lambda k: (k[0], int(k[1]) + int(k[2]), k[1]))
    for key in keys:
        v = groups.get(key, [])
        counts = "/".join(
            str(status[key + (s,)]) for s in ("done", "failed", "censored", "skipped")
        )
        if not v:
            print(f"| {key[0]} | {key[1]} × {key[2]} | {counts} | — | — | — | — | — | — | — | — | — |")
            continue
        degrees = ",".join(map(str, sorted({x["degree"] for x in v})))
        cdeg = sorted({int(x["control_degree"]) for x in v if x["control_degree"].isdigit()})
        cdeg = ",".join(map(str, cdeg)) or "—"
        area = int(statistics.median(x["area"] for x in v))
        sig = [x["sig"] / x["block"] for x in v if x["sig"]]
        sig = f"{statistics.median(sig):.1f}" if sig else "—"
        # failed:<F4 error> is a shipping-budget refusal; keep only its kind.
        controls = Counter(x["control"].split(":")[0] for x in v)
        controls = ", ".join(f"{n} {c}" for c, n in sorted(controls.items()))
        print(
            f"| {key[0]} | {key[1]} × {key[2]} | {counts} | {degrees} | {cdeg} | {area:,} "
            f"| {fmt([x['s'] for x in v])} "
            f"| {fmt([x['d'] for x in v if x['d']], '{:.0f}')} "
            f"| {fmt([x['share'] for x in v if x['share'] is not None], '{:.3f}')} "
            f"| {statistics.median(x['dup'] for x in v):.2f} | {sig} | {controls} |"
        )

    decided = [x for k, v in groups.items() if k[0] == "affine" and k[1:] in BALANCED for x in v]
    shapes = sorted({k[1:] for k, v in groups.items() if k[0] == "affine" and k[1:] in BALANCED and v})
    s = [x["s"] for x in decided]
    share = [x["share"] for x in decided if x["share"] is not None]
    print()
    print("**Pre-declared decision (balanced affine).**")
    print(f"- Shapes completed: {', '.join('×'.join(t) for t in shapes)}; instances: {len(decided)}.")
    print(f"- Median S = {statistics.median(s):.2f} (needs ≥ 2; disproved below 1.5).")
    print(f"- Median share = {statistics.median(share):.3f} over {len(share)} instances with a "
          f"completed control (needs < 0.75).")
    for shape in shapes:
        v = [x["share"] for x in groups[("affine",) + shape] if x["share"] is not None]
        if v:
            print(f"  - {'×'.join(shape)}: median {statistics.median(v):.4f} over {len(v)}, "
                  f"{sum(x >= 0.75 for x in v)} at or above 0.75.")


if __name__ == "__main__":
    main(sys.argv[1])
