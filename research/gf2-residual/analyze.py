"""Summarize `gf2_residual_replay batches` output (#1077).

    python3 -I research/gf2-residual/analyze.py research/gf2-residual/batches-dev.tsv [...]

Prints, per file: arm totals against the per-batch oracle, the batches where the residual arm
beats the shipped full-width packed route by at least 10% and those where it loses by as much,
and the same split by residual fraction (residual columns over columns).
"""

import csv
import sys

ARMS = ["packed", "fl", "lazy", "eager"]


def rows(path):
    with open(path, newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def number(row, key):
    return float(row[key])


def summarize(path):
    data = rows(path)
    print(f"## {path}: {len(data)} batches\n")
    totals = {arm: sum(number(r, f"{arm}_us") for r in data) for arm in ARMS}
    oracle_two = sum(min(number(r, "packed_us"), number(r, "fl_us")) for r in data)
    oracle_three = sum(
        min(number(r, "packed_us"), number(r, "fl_us"), number(r, "lazy_us")) for r in data
    )
    print("| arm | total ms | over packed+fl oracle |")
    print("| --- | ---: | ---: |")
    for arm in ARMS:
        print(f"| {arm} | {totals[arm] / 1e3:.2f} | {100 * (totals[arm] / oracle_two - 1):+.1f}% |")
    print(f"| oracle(packed, fl) | {oracle_two / 1e3:.2f} | +0.0% |")
    print(
        f"| oracle(packed, fl, lazy) | {oracle_three / 1e3:.2f} | "
        f"{100 * (oracle_three / oracle_two - 1):+.1f}% |\n"
    )

    words = sum(number(r, "packed_words") for r in data)
    lazy_words = sum(number(r, "lazy_words") for r in data)
    eager_words = sum(number(r, "eager_words") for r in data)
    tails = sum(number(r, "lazy_tails") for r in data)
    eager_tails = sum(number(r, "eager_tails") for r in data)
    uses = sum(number(r, "tail_uses") for r in data)
    print(
        f"xor words: packed {words:.0f}, lazy {lazy_words:.0f} ({lazy_words / max(words, 1):.2f}x),"
        f" eager {eager_words:.0f} ({eager_words / max(words, 1):.2f}x); tails built: lazy"
        f" {tails:.0f} of {eager_tails:.0f} ({tails / max(eager_tails, 1):.1%}); tail uses per"
        f" built tail {uses / max(tails, 1):.2f}\n"
    )

    def banded(title, key, bands):
        print(
            f"| {title} | batches | packed ms | fl ms | lazy ms | eager ms | packed/lazy |"
            " lazy wins >=10% | lazy loses >=10% |"
        )
        print("| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |")
        for low, high in bands:
            band = [r for r in data if low <= key(r) < high]
            if not band:
                continue
            packed = sum(number(r, "packed_us") for r in band)
            fl = sum(number(r, "fl_us") for r in band)
            lazy = sum(number(r, "lazy_us") for r in band)
            eager = sum(number(r, "eager_us") for r in band)
            wins = sum(number(r, "lazy_us") * 1.1 <= number(r, "packed_us") for r in band)
            losses = sum(number(r, "lazy_us") >= 1.1 * number(r, "packed_us") for r in band)
            upper = "inf" if high == float("inf") else f"{high:g}"
            print(
                f"| {low:g}-{upper} | {len(band)} | {packed / 1e3:.2f} | {fl / 1e3:.2f} |"
                f" {lazy / 1e3:.2f} | {eager / 1e3:.2f} | {packed / max(lazy, 1e-9):.2f}x |"
                f" {wins} | {losses} |"
            )
        print()

    banded(
        "residual fraction",
        lambda r: number(r, "residual_columns") / max(number(r, "columns"), 1),
        [(0.0, 0.25), (0.25, 0.5), (0.5, 0.75), (0.75, 1.01)],
    )
    banded(
        "reducers per pair row",
        lambda r: number(r, "reducers") / max(number(r, "pair_rows"), 1),
        [(0.0, 0.25), (0.25, 1.0), (1.0, 4.0), (4.0, float("inf"))],
    )
    banded(
        "packed us (batch cost)",
        lambda r: number(r, "packed_us"),
        [(0.0, 100.0), (100.0, 1000.0), (1000.0, float("inf"))],
    )

    expensive = sorted(data, key=lambda r: -number(r, "packed_us"))[:12]
    print(
        "| instance | batch | pair rows | columns | residual | reducers | D ppm | reduced ppm |"
        " referenced / lazy / eager tails | tail fill | uses per tail | packed words | lazy words |"
        " tail bytes | packed us | fl us | lazy us | eager us | packed/lazy |"
    )
    print("| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |")
    for r in expensive:
        fill = number(r, "lazy_tail_entries") / max(number(r, "B_entries"), 1)
        reuse = number(r, "tail_uses") / max(number(r, "lazy_tails"), 1)
        print(
            f"| {r['instance']} | {r['batch']} | {r['pair_rows']} | {r['columns']} |"
            f" {r['residual_columns']} | {r['reducers']} | {r['D_ppm']} | {r['reduced_ppm']} |"
            f" {r['referenced_tails']} / {r['lazy_tails']} / {r['eager_tails']} | {fill:.1f} |"
            f" {reuse:.1f} | {r['packed_words']} | {r['lazy_words']} | {r['lazy_tail_bytes']} |"
            f" {r['packed_us']} | {r['fl_us']} | {r['lazy_us']} | {r['eager_us']} |"
            f" {number(r, 'packed_us') / max(number(r, 'lazy_us'), 1e-3):.2f}x |"
        )
    print()

    phases = ["pack", "tails", "multiply", "echelon", "write_back"]
    sums = {p: sum(number(r, f"lazy_{p}_us") for r in data) for p in phases}
    whole = sum(sums.values())
    print(
        "lazy phases: "
        + ", ".join(f"{p} {sums[p] / 1e3:.2f} ms ({sums[p] / max(whole, 1e-9):.0%})" for p in phases)
        + "\n"
    )


for argument in sys.argv[1:]:
    summarize(argument)
