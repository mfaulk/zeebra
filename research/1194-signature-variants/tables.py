#!/usr/bin/env python3
"""#1194: tables.md from runs.jsonl.gz (run.sh) and extra.jsonl.gz (README). Counts only; the
clocks are for scale.

    python3 research/1194-signature-variants/tables.py > research/1194-signature-variants/tables.md
"""
import gzip
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROWS = ["eco-12", "katsura-11", "mq-random-11", "cyclic-7", "sd-hairer-2@p31"]
CELLS = [
    "schreyer / ratio",
    "schreyer / newest",
    "dpot / ratio",
    "dpot / newest",
    "pot / ratio",
    "pot / newest",
    "pot / ratio / reversed",
]


def cell(r):
    name = f"{r['module']} / {r['rewrite']}"
    return name + (" / reversed" if r.get("reverse") else "")


def load(path):
    if not path.exists():
        return []
    with gzip.open(path, "rt") as f:
        return [json.loads(line) for line in f if line.strip()]


def fmt(n):
    return f"{n:,}"


def complete(r):
    return r is not None and r.get("status") == "complete"


def records():
    """Each (row, cell)'s record; an extra.jsonl.gz record (a larger live budget) replaces a
    stopped one. Returns {row: (f4, {cell: (record, from_extra)})}."""
    runs, extra = load(HERE / "runs.jsonl.gz"), load(HERE / "extra.jsonl.gz")
    table = {}
    for row in ROWS:
        f4 = next((r for r in runs if r["name"] == row and r["engine"] == "f4"), None)
        cells = {}
        for r in runs:
            if r["name"] == row and r["engine"] == "sigf4":
                cells[cell(r)] = (r, False)
        for r in extra:
            if r["name"] == row and r["engine"] == "sigf4" and complete(r):
                if not complete(cells.get(cell(r), (None, False))[0]):
                    cells[cell(r)] = (r, True)
        table[row] = (f4, cells)
    return table


def ratio(r, base):
    if not (complete(r) and complete(base)):
        return None
    return r["statistics"]["coefficient_products"] / base["statistics"]["coefficient_products"]


def summary(table):
    print("## Summary: coefficient products against Schreyer / ratio")
    print()
    print("`stopped` means the live-entry budget stopped the run (6 GiB; † a 14 GiB rerun, "
          "`extra.jsonl.gz`).")
    print()
    print("| row | " + " | ".join(CELLS) + " |")
    print("|---|" + "---:|" * len(CELLS))
    for row in ROWS:
        f4, cells = table[row]
        base = cells.get("schreyer / ratio", (None, False))[0]
        out = []
        for c in CELLS:
            r, extra = cells.get(c, (None, False))
            q = ratio(r, base)
            out.append("—" if r is None else
                       ("stopped" if q is None else f"{q:.3f}{' †' if extra else ''}"))
        print(f"| {row} | " + " | ".join(out) + " |")
    print()


def detail(table):
    print("## Pairs, rows and products per row and variant")
    print()
    print("Products are batch-elimination multiply-accumulates (`coefficient_products`); "
          "`× base` is against Schreyer / ratio on the same row. `basis` is `ok` when the "
          "`m33-basis-v1` digest equals conventional F4's.")
    for row in ROWS:
        f4, cells = table[row]
        base = cells.get("schreyer / ratio", (None, False))[0]
        print()
        print(f"### {row}")
        print()
        if f4:
            print(f"Conventional F4: {f4['status']}, {fmt(f4['basis_elements'] or 0)} elements, "
                  f"{f4['call_ns'] / 1e6:,.0f} ms.")
            print()
        print("| variant | status | basis | elements | dominated at birth | pairs | product "
              "| Koszul | zero-row | rewrite | duplicate | targets | reducer rows | to zero "
              "| singular | products | × base | on zero rows | ms |")
        print("|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:"
              "|---:|---:|---:|")
        for c in CELLS:
            if c not in cells:
                continue
            r, extra = cells[c]
            name = c + (" †" if extra else "")
            if not complete(r):
                status = "stopped" if str(r.get("status", "")).startswith("stopped") else r.get("status")
                print(f"| {name} | {status} | — |" + " |" * 16)
                continue
            s = r["statistics"]
            ok = f4 is not None and r.get("basis_m33") == f4.get("basis_m33")
            print(
                f"| {name} | complete | {'ok' if ok else 'DIFFERS'} | {fmt(s['elements_added'])} "
                f"| {fmt(s['dominated_at_birth'])} | {fmt(s['pairs_created'])} "
                f"| {fmt(s['rejected_product'])} | {fmt(s['rejected_koszul'])} "
                f"| {fmt(s['rejected_zero_row'])} | {fmt(s['rejected_rewrite'])} "
                f"| {fmt(s['rejected_duplicate'])} | {fmt(s['targets'])} "
                f"| {fmt(s['reducer_rows'])} | {fmt(s['reductions_to_zero'])} "
                f"| {fmt(s['singular_rows'])} | {fmt(s['coefficient_products'])} "
                f"| {ratio(r, base):.3f} | {fmt(s['products_on_zero_rows'])} "
                f"| {r['call_ns'] / 1e6:,.0f} |"
            )


def main():
    table = records()
    print("<!-- generated by tables.py from runs.jsonl.gz and extra.jsonl.gz; do not edit -->")
    print()
    summary(table)
    detail(table)


if __name__ == "__main__":
    sys.exit(main())
