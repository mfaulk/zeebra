#!/usr/bin/env python3
"""#1136: the attribution tables from results.jsonl, as Markdown on stdout.

  python3 research/1136-hairer2-attribution/tables.py > research/1136-hairer2-attribution/tables.md
"""
import gzip
import json
import pathlib
import statistics

HERE = pathlib.Path(__file__).resolve().parent


def load(name="results.jsonl.gz"):
    with gzip.open(HERE / name, "rt") as f:
        rows = [json.loads(line) for line in f if line.strip()]
    cells = {}
    for r in rows:
        cells[(r["name"], r["engine"])] = r
    return cells


def median_ms(r):
    return statistics.median(r["calls_ns"]) / 1e6


def main():
    cells = load()
    ids = list(dict.fromkeys(name for name, _ in cells))
    print("## Cells (Apple M-series laptop, 1 worker, median of 5 solves in one process)\n")
    print("| record | F4 ms | F4 max pair degree | F4 elements added | sig ms | sig ÷ F4 "
          "| sig max signature degree | sig batches | sig elements added | dominated at birth "
          "| reducer rows | coefficient products | symbolic ms | elimination ms | same basis |")
    print("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|")
    for i in ids:
        f, s = cells[(i, "f4")], cells[(i, "sigf4")]
        assert f["status"] == s["status"] == "complete", i
        fs, ss = f["statistics"], s["statistics"]
        u = ss["usage"]
        print(
            f"| `{i}` | {median_ms(f):,.1f} | {fs['max_pair_degree']} | {fs['elements_added']:,} "
            f"| {median_ms(s):,.0f} | {median_ms(s) / median_ms(f):,.0f} "
            f"| {max(b['degree'] for b in u['batches'])} | {ss['batches']} "
            f"| {ss['elements_added']:,} | {u['dominated_at_birth']:,} | {ss['reducer_rows']:,} "
            f"| {ss['coefficient_products']:,} | {ss['symbolic_ns'] / 1e6:,.0f} "
            f"| {ss['elimination_ns'] / 1e6:,.0f} | {f['basis_sha256'] == s['basis_sha256']} |"
        )
    print("\n## Decomposition: sig(affine) ÷ F4(affine) = [F4(homog) ÷ F4(affine)] × "
          "[sig(homog) ÷ F4(homog)] × [sig(affine) ÷ sig(homog)]\n")
    print("| source | sig ÷ F4 | F4 homog ÷ F4 affine | sig homog ÷ F4 homog "
          "| sig affine ÷ sig homog | products affine ÷ homog (sig) |")
    print("|---|---:|---:|---:|---:|---:|")
    for prefix in ("h2", "h2-sub", "bu", "bu-sub"):
        a = f"{prefix}-orig" if not prefix.endswith("-sub") else f"{prefix[:-4]}-substituted"
        h = f"{prefix}-homogenized"
        if (a, "f4") not in cells or (h, "f4") not in cells:
            continue
        fa, fh = median_ms(cells[(a, "f4")]), median_ms(cells[(h, "f4")])
        sa, sh = median_ms(cells[(a, "sigf4")]), median_ms(cells[(h, "sigf4")])
        pa = cells[(a, "sigf4")]["statistics"]["coefficient_products"]
        ph = cells[(h, "sigf4")]["statistics"]["coefficient_products"]
        print(f"| `{a}` | {sa / fa:,.0f} | {fh / fa:.1f} | {sh / fh:.1f} | {sa / sh:.2f} "
              f"| {pa / ph:.4f} |")
    print("\n## sd-hairer-2 (`h2-orig`): signature engine work by signature degree\n")
    print("| signature degree | batches | targets | elements added | essential | ms |")
    print("|---:|---:|---:|---:|---:|---:|")
    per = {}
    for b in cells[("h2-orig", "sigf4")]["statistics"]["usage"]["batches"]:
        row = per.setdefault(b["degree"], [0, 0, 0, 0, 0])
        ns = b["select_ns"] + b["insert_ns"] + b["symbolic_ns"] + b["elimination_ns"]
        for k, v in enumerate((1, b["targets"], b["elements_added"], b["essential_added"], ns)):
            row[k] += v
    for d in sorted(per):
        n, t, a, e, ns = per[d]
        print(f"| {d} | {n} | {t} | {a} | {e} | {ns / 1e6:,.0f} |")
    print("\nF4's batch degrees on `h2-orig`:",
          cells[("h2-orig", "f4")]["statistics"]["step_degrees"])
    development()


def development():
    """T1 (README): signature-engine products on each development record against its
    homogenization, with F4 beside it for the degree-fall factor."""
    cells = load("development.jsonl.gz")
    ids = [i for i, e in cells if e == "sigf4" and not i.endswith("#h")]
    print("\n## T1: development records, affine against homogenized (1 worker, one solve, 60 s wall)\n")
    print("| record | sig products, affine | sig products, homogenized | ratio | in [0.99, 1.01] "
          "| sig ms | F4 ms | sig ÷ F4 | F4 homog ÷ F4 affine | F4 max pair degree, affine / homog |")
    print("|---|---:|---:|---:|---|---:|---:|---:|---:|---|")
    held = failed = undecided = 0
    for i in sorted(ids):
        sa, sh = cells[(i, "sigf4")], cells[(f"{i}#h", "sigf4")]
        fa, fh = cells.get((i, "f4"), {}), cells.get((f"{i}#h", "f4"), {})
        done = lambda r: r.get("status") == "complete"
        ms = lambda r: f"{r['call_ns'] / 1e6:,.1f}" if done(r) else r.get("status", "missing")
        deg = lambda r: str(r["statistics"]["max_pair_degree"]) if done(r) else "–"
        if done(sa) and done(sh):
            pa = sa["statistics"]["coefficient_products"]
            ph = sh["statistics"]["coefficient_products"]
            ratio = pa / ph if ph else float("nan") if pa else 1.0
            ok = 0.99 <= ratio <= 1.01
            held += ok
            failed += not ok
            cols = [f"{pa:,}", f"{ph:,}", f"{ratio:.4f}", "yes" if ok else "**no**"]
        else:
            undecided += 1
            cols = ["–", "–", "–", f"undecided ({sa.get('status')} / {sh.get('status')})"]
        both = done(sa) and done(fa)
        ratio_sf = f"{sa['call_ns'] / fa['call_ns']:,.1f}" if both else "–"
        fall = f"{fh['call_ns'] / fa['call_ns']:,.1f}" if done(fa) and done(fh) else "–"
        print(f"| `{i}` | " + " | ".join(cols) + f" | {ms(sa)} | {ms(fa)} | {ratio_sf} | {fall} "
              f"| {deg(fa)} / {deg(fh)} |")
    print(f"\nT1: {held} in the band, {failed} outside it, {undecided} undecided.")


if __name__ == "__main__":
    main()
