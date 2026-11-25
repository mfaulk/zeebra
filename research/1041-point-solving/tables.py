#!/usr/bin/env python3
"""#1041: the comparison table and the predeclared decision, as Markdown.

  python3 research/1041-point-solving/tables.py > research/1041-point-solving/tables.md

Zeebra's pipeline and the hybrid arm are measured walls (measured.jsonl). Crossbred and XL + block
Wiedemann are counted (counted.json) and converted at the calibrated rate r: one counted operation
costs one GF(31) multiply-add, or one 64-bit word operation over GF(2). That prices crossbred's
bit-level enumeration terms as whole word operations, which is conservative for it. The rate is the
slower of the two calibration runs. The hybrid total for k extra fixed variables is
(q^k − 1)·wrong + correct, charged in full. Seeds are combined by their median.
"""
import json
import pathlib
import statistics

HERE = pathlib.Path(__file__).resolve().parent


def load():
    measured, rates = [], []
    for line in (HERE / "measured.jsonl").read_text().splitlines():
        r = json.loads(line)
        (rates if r.get("mode") == "calibrate" else measured).append(r)
    counted = {(r["family"], r["n"], r["m"]): r for r in json.loads((HERE / "counted.json").read_text())}
    rate = {31: min(r["gf31_multiply_adds_per_s"] for r in rates),
            2: min(r["gf2_word_ops_per_s"] for r in rates)}
    return measured, counted, rate


def seconds(ns):
    return ns / 1e9


def fmt(s):
    if s is None:
        return "—"
    if s >= 1:
        return f"{s:,.2f} s"
    if s >= 1e-3:
        return f"{s * 1e3:,.1f} ms"
    return f"{s * 1e6:,.1f} µs"


def completed(r):
    return r["status"] == "point" or (r["status"] == "attempts" and r["last"]["status"] == "point")


def main():
    measured, counted, rate = load()
    print(f"Rates (slower of two calibration runs, one core): GF(31) {rate[31]:.3g} multiply-adds/s, "
          f"GF(2) {rate[2]:.3g} word operations/s.\n")
    print("| family | n | m | Zeebra pipeline | attempts | hybrid best (k) | crossbred (k, D, d) "
          "| XL + BW (D) | best alternative | Zeebra ÷ best |")
    print("|---|---:|---:|---|---:|---|---|---|---|---:|")
    largest = {}
    for (family, n, m), c in counted.items():
        q = c["q"]
        runs = [r for r in measured if r["family"] == family and r["n"] == n and r["m"] == m
                and r["mode"] == "pipeline"]
        done = [r for r in runs if completed(r)]
        if not runs:
            continue
        if len(done) < len(runs):
            print(f"| {family} | {n} | {m} | did not complete ({len(runs) - len(done)}/{len(runs)}) "
                  f"| — | — | — | — | — | — |")
            continue
        zeebra = statistics.median(seconds(r["call_ns"]) for r in done)
        attempts = statistics.median(r.get("attempts") or 1 for r in done)
        hybrid = None
        for k in sorted({r["k"] for r in measured if r.get("k") and r["family"] == family
                         and r["n"] == n and r["m"] == m}):
            totals = []
            for seed in (1, 2):
                br = {r["branch"]: r for r in measured if r.get("k") == k and r["family"] == family
                      and r["n"] == n and r["m"] == m and r["seed"] == seed}
                if set(br) == {"correct", "wrong"} and all(
                        b["status"] in ("point", "inconsistent", "no-base-field-point")
                        for b in br.values()):
                    totals.append((q ** k - 1) * seconds(br["wrong"]["call_ns"])
                                  + seconds(br["correct"]["call_ns"]))
            if len(totals) == 2:
                t = statistics.median(totals)
                if hybrid is None or t < hybrid[0]:
                    hybrid = (t, k)
        cb, xl = c["crossbred"], c["xl_wiedemann"]
        cb_s = cb and 2 ** cb["log2_total"] / rate[q]
        xl_s = xl and 2 ** xl["log2_total"] / rate[q]
        options = [("hybrid", hybrid and hybrid[0]), ("crossbred", cb_s), ("XL + BW", xl_s)]
        name, best = min(((a, b) for a, b in options if b), key=lambda x: x[1])
        ratio = zeebra / best
        largest[family] = dict(n=n, m=m, zeebra=zeebra, best=best, name=name,
                               counted=name != "hybrid")
        hybrid_text = f"{fmt(hybrid[0])} ({hybrid[1]})" if hybrid else "—"
        cb_text = f"{fmt(cb_s)} ({cb['k']}, {cb['D']}, {cb['d']})" if cb else "—"
        xl_text = f"{fmt(xl_s)} ({xl['D']})" if xl else "—"
        print(f"| {family} | {n} | {m} | {fmt(zeebra)} | {attempts:g} | {hybrid_text} | {cb_text} "
              f"| {xl_text} | {name} | {ratio:.2f} |")
    print("\n## Predeclared decision\n")
    print("At the largest size each family completes. A counted alternative is re-priced at r/4; "
          "the hybrid arm is measured and does not move with r.\n")
    print("| family | n | m | best alternative | Zeebra ÷ best at r | at r/4 |")
    print("|---|---:|---:|---|---:|---:|")
    proceed, defer = [], []
    for family, f in largest.items():
        at_r = f["zeebra"] / f["best"]
        at_quarter = at_r / 4 if f["counted"] else at_r
        print(f"| {family} | {f['n']} | {f['m']} | {f['name']} | {at_r:.2f} | {at_quarter:.2f} |")
        if at_r >= 3 and at_quarter >= 3:
            proceed.append(family)
        elif at_r >= 3:
            defer.append(family)
    if proceed:
        verdict = f"proceed: a bounded prototype proposal (families {', '.join(proceed)})"
    elif defer:
        verdict = f"defer to the bench host (families {', '.join(defer)} hold at r only)"
    else:
        verdict = "close: #75 and #76 reaffirmed"
    print(f"\n**Predeclared decision:** {verdict}.")


if __name__ == "__main__":
    main()
