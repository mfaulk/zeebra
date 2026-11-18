#!/usr/bin/env python3
"""#86: stage shares and logical arithmetic intensity from committed records.

Inputs (all committed): research/m30-final/{stages,census}.jsonl.gz (e4826153 via 5515c412),
research/gpu-kernels/f4-*.jsonl and ceilings-*.json (this issue's runs). Prints Markdown.

Logical bytes per kernel follow the shipped dense-accumulator step (src/linalg/dense/accumulator.rs):
each coefficient product reads one `(usize, F)` pivot entry and reads and writes one cell; loads,
scans and gathers add their own entry or cell traffic. Physical DRAM traffic is not measured.
"""
import gzip
import json
import statistics as st
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = ROOT / "research/gpu-kernels"
STAGES = ["symbolic_ns", "construction_ns", "forward_ns", "backward_ns",
          "extraction_ns", "interreduction_ns", "other_ns"]
CELL = {"PrimeFieldElement32": 4, "PrimeFieldElement64": 8, "PrimeFieldElement256": 32,
        "BinaryFieldElement": 8}


def cell_bytes(field_type):
    for key, size in CELL.items():
        if key in field_type:
            return size
    raise ValueError(field_type)


def logical_bytes(phase, entry, cell):
    return (phase["coefficient_products"] * (entry + 2 * cell)
            + phase["dense_load_entries"] * (entry + cell)
            + phase["dense_scan_cells"] * cell
            + phase["dense_gather_cells"] * cell
            + phase["dense_gather_entries"] * entry)


def jsonl(path):
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt") as f:
        return [json.loads(line) for line in f if line.strip()]


def m30_rows():
    """(target, workers) -> list of reports from the final build, plus census per target."""
    stages = defaultdict(list)
    for r in jsonl(ROOT / "research/m30-final/stages.jsonl.gz"):
        if r["build"] == "final" and r["report"]["status"] == "complete":
            rep = dict(r["report"])
            rep["process_wall_ns"] = r["process_wall_ns"]
            rep["load"] = r["before"]["load1"]
            stages[(r["target"], r["workers"])].append(rep)
    census = {}
    for r in jsonl(ROOT / "research/m30-final/census.jsonl.gz"):
        if r["build"] == "final" and r["arm"] == "final-work":
            census[r["target"]] = r["report"]
    return stages, census


def new_rows():
    stages = defaultdict(list)
    census = {}
    for path in sorted(HERE.glob("f4-*.jsonl")):
        for r in jsonl(path):
            if r["status"] != "complete":
                continue
            key = f'{r["system"]}/{r["field"]}'
            if r.get("work"):
                if r["work"]["forward"]["coefficient_products"] > 0:
                    census[key] = r
            else:
                stats = dict(r["statistics"])
                rep = {"statistics": stats, "f4_call_ns": r["f4_call_ns"],
                       "process_wall_ns": r.get("process_wall_ns", r["f4_call_ns"]),
                       "field_type": r["field_type"], "load": r.get("load1")}
                stages[(key, r["workers"])].append(rep)
    return stages, census


def med(rows, f):
    return st.median(f(r) for r in rows)


def share_table(stages):
    print("| target | workers | n | process wall ms | " +
          " | ".join(s[:-3] for s in STAGES) + " | outside F4 |")
    print("|---|---:|---:|---:|" + "---:|" * (len(STAGES) + 1))
    for (target, workers), rows in sorted(stages.items()):
        wall = med(rows, lambda r: r["process_wall_ns"])
        f4 = med(rows, lambda r: r["f4_call_ns"])
        cells = [100 * med(rows, lambda r, s=s: r["statistics"][s]) / wall for s in STAGES]
        print(f"| {target} | {workers} | {len(rows)} | {wall / 1e6:.1f} | " +
              " | ".join(f"{c:.1f}%" for c in cells) + f" | {100 * (wall - f4) / wall:.1f}% |")


def intensity_table(stages, census, cell_of):
    print("| target | cell B | forward products | logical B / product | products / logical B | "
          "1w forward G products/s | 1w logical GB/s | 16w logical GB/s | backward products |")
    print("|---|---:|---:|---:|---:|---:|---:|---:|---:|")
    for target, rep in sorted(census.items()):
        work = rep["work"]
        entry = work.get("sparse_entry_bytes") or rep["statistics"]["bytes_per_entry"]
        cell = cell_of(rep)
        fwd = work["forward"]
        products = fwd["coefficient_products"]
        b = logical_bytes(fwd, entry, cell)
        one = stages.get((target, 1))
        sixteen = stages.get((target, 16))
        r1 = products / (med(one, lambda r: r["statistics"]["forward_ns"]) / 1e9) if one else None
        g1 = b / (med(one, lambda r: r["statistics"]["forward_ns"])) if one else None
        g16 = b / (med(sixteen, lambda r: r["statistics"]["forward_ns"])) if sixteen else None
        fmt = lambda x, p=2: "—" if x is None else f"{x:.{p}f}"
        print(f"| {target} | {cell} | {products:,} | {b / products:.1f} | {products / b:.4f} | "
              f"{fmt(r1 / 1e9 if r1 else None, 3)} | {fmt(g1, 1)} | {fmt(g16, 1)} | "
              f"{work['backward']['coefficient_products']:,} |")


def main():
    stages, census = m30_rows()
    print("## M30 final cohort (e4826153), stage share of clocked process wall\n")
    share_table(stages)
    print("\n## Forward elimination, logical intensity (M30 census)\n")
    intensity_table(stages, census, lambda rep: cell_bytes(rep["field_type"]))
    ns, nc = new_rows()
    if ns:
        print("\n## This issue's runs, stage share of F4 call\n")
        share_table(ns)
    if nc:
        print("\n## This issue's runs, forward elimination logical intensity\n")
        intensity_table(ns, nc, lambda rep: rep["cell_bytes"])
    for path in sorted(HERE.glob("ceilings-*.json")):
        c = json.loads(path.read_text())
        print(f"\n## Ceilings ({path.name}); stream read {c['stream_read_gbs_1t']} GB/s, one core\n")
        print("| field | cell B | B / product | L1 contiguous M/s | L2 scatter M/s | L3 scatter M/s | "
              "DRAM scatter M/s | DRAM scatter logical GB/s |")
        print("|---|---:|---:|---:|---:|---:|---:|---:|")
        for f in c["fields"]:
            a = f["arms"]
            print(f"| {f['field']} | {f['cell_bytes']} | {f['bytes_per_product']} | "
                  f"{float(a['L1 contiguous']['mops']):.1f} | {float(a['L2 scatter']['mops']):.1f} | "
                  f"{float(a['L3 scatter']['mops']):.1f} | {float(a['DRAM scatter']['mops']):.1f} | "
                  f"{float(a['DRAM scatter']['logical_gbs']):.2f} |")
    return 0


if __name__ == "__main__":
    sys.exit(main())
