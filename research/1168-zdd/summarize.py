#!/usr/bin/env python3
"""Tables for docs/research/boolean-zdd-normal-forms.md from #1168's results.csv.

python3 research/1168-zdd/summarize.py [results.csv] > research/1168-zdd/tables.md

One row per family and size: the natural order's figures, then the median ratio over the scrambled
orders. For the MQ control, the median over its three seeds of each.
"""
import csv
import statistics
import sys
from collections import defaultdict
from pathlib import Path


def num(x):
    return float(x) if x not in ("", None) else None


def med(xs):
    xs = [x for x in xs if x is not None]
    return statistics.median(xs) if xs else None


def fmt(x, spec):
    return "—" if x is None else format(x, spec)


def main():
    path = Path(sys.argv[1] if len(sys.argv) > 1 else Path(__file__).with_name("results.csv"))
    rows = list(csv.DictReader(path.open()))
    groups = defaultdict(list)
    for r in rows:
        groups[(r["family"], int(r["size"]))].append(r)
    print("| family | size | vars | ZDD ms | ZDD out ms | ANF ms | R | R_out | scrambled R (median) "
          "| alloc nodes | result nodes | result terms | ZDD heap KiB | ANF peak terms | ANF KiB (lb) "
          "| refusals (natural) |")
    print("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|")
    for (family, size), rs in groups.items():
        nat = [r for r in rs if r["order"] == "natural"]
        scr = [r for r in rs if r["order"] != "natural"]

        def m(col, scale=1.0, src=nat):
            v = med([num(r[col]) for r in src])
            return None if v is None else v * scale

        refusals = sorted(
            {f"{route} {r[col]}" for r in nat for route, col in
             (("ZDD", "zdd_status"), ("ZDD out", "zdd_out_status"), ("ANF", "anf_status"))
             if r[col] not in ("ok", "")}
        )
        anf_ms = m("anf_s", 1e3)
        print(
            f"| {family} | {size} | {nat[0]['vars']} | {fmt(m('zdd_s', 1e3), '.3f')} "
            f"| {fmt(m('zdd_out_s', 1e3), '.3f')} "
            f"| {fmt(anf_ms, '.3f') if anf_ms is not None else 'refused'} "
            f"| {fmt(m('ratio'), '.1f')} | {fmt(m('ratio_out'), '.2f')} | {fmt(m('ratio', src=scr), '.1f')} "
            f"| {fmt(m('allocated_nodes'), '.0f')} | {fmt(m('result_nodes'), '.0f')} "
            f"| {fmt(m('result_terms'), '.0f')} | {fmt(m('zdd_heap_bytes', 1 / 1024), '.1f')} "
            f"| {fmt(m('anf_peak_terms'), '.0f')} | {fmt(m('anf_bytes_lb', 1 / 1024), '.1f')} |"
            + f" {'; '.join(refusals) or '—'} |"
        )


if __name__ == "__main__":
    main()
