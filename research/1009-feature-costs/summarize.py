#!/usr/bin/env python3
"""#1009's extraction-cost table, pilot-panel coverage summary and stop-condition verdicts.

Reads the records `run.sh` writes (`examples/feature_costs.rs`, one JSON line per catalog record)
and prints `tables.md`. The rules were declared on #1009 before the timed run:

- A feature's cost on a record is its median per-call time; its ratio is that cost divided by the
  cheapest arm's median solve on the same record, the faster of `entry` and `f4`.
- **Small inputs** are the records whose cheapest arm completes within SMALL_NS.
- A feature **passes** when its worst ratio over the small inputs is at most FEATURE_FRACTION. The
  whole set (the sum over FEATURES) is held to SET_FRACTION the same way.
- A record where no arm completed is not small. Its ratio is reported as an upper bound against the
  wall budget and decides nothing.

The cold first call and a second, repeat session are reported beside the verdicts and decide nothing.

    python3 summarize.py records.jsonl.gz records-repeat.jsonl.gz > tables.md
    python3 summarize.py --check          # tables.md is what the two record files give
"""

import gzip
import json
import statistics
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
FEATURES = [
    "system_shape",
    "is_homogeneous",
    "incidence",
    "linear_subsystem",
    "scalar_substitutions",
    "support_profile",
    "leading_profile",
]
FEATURE_FRACTION = 0.01
SET_FRACTION = 0.02
SMALL_NS = 1_000_000_000


def load(path):
    opener = gzip.open if str(path).endswith(".gz") else open
    with opener(path, "rt") as f:
        return [json.loads(line) for line in f if line.strip()]


def cost_ns(record, feature):
    return record["feature_costs"][feature]["median_ns"]


def set_cost_ns(record):
    return sum(cost_ns(record, f) for f in FEATURES)


def cold_set_ns(record):
    return sum(record["feature_costs"][f]["cold_ns"] for f in FEATURES)


def stopped_after_ns(record):
    """The shortest call of an arm that did not complete: a lower bound on that arm's solve."""
    calls = [
        min(record[arm]["calls_ns"])
        for arm in ("entry", "f4")
        if record[arm]["calls_ns"] and record[arm]["status"] != "complete"
    ]
    return min(calls, default=None)


def is_small(record):
    c = record.get("cheapest_ns")
    return c is not None and c <= SMALL_NS


def ratio(record, ns):
    """Cost over the cheapest arm's solve; None when no arm completed."""
    c = record.get("cheapest_ns")
    return None if c is None else ns / c


def verdict(worst, fraction):
    if worst is None:
        return "no small input"
    return "pass" if worst <= fraction else "FAIL"


def feature_rows(records):
    """Per feature (and the whole set): absolute cost and its ratio to the cheapest solve."""
    small = [r for r in records if is_small(r)]
    rows = []
    for name, cost, fraction in [(f, None, FEATURE_FRACTION) for f in FEATURES] + [
        ("all seven", set_cost_ns, SET_FRACTION)
    ]:
        get = cost or (lambda r, f=name: cost_ns(r, f))
        cold = cold_set_ns if cost else (lambda r, f=name: r["feature_costs"][f]["cold_ns"])
        absolute = [get(r) for r in records]
        ratios = [ratio(r, get(r)) for r in small]
        worst = max(ratios) if ratios else None
        worst_id = max(small, key=lambda r: ratio(r, get(r)))["id"] if small else None
        failing = [r["cheapest_ns"] for r in small if ratio(r, get(r)) > fraction]
        rows.append(
            {
                "feature": name,
                "median_ns": statistics.median(absolute),
                "max_ns": max(absolute),
                "median_ratio": statistics.median(ratios) if ratios else None,
                "worst_ratio": worst,
                "worst_cold_ratio": max((ratio(r, cold(r)) for r in small), default=None),
                "worst_id": worst_id,
                "failing_below_ns": max(failing, default=None),
                "over": sum(1 for x in ratios if x > fraction),
                "small": len(ratios),
                "fraction": fraction,
                "verdict": verdict(worst, fraction),
            }
        )
    return rows


def coverage(records):
    """Counts over the panel's feature space, one entry per question the summary answers."""
    v = [r["features"] for r in records]

    def count(pred):
        return sum(1 for x in v if pred(x))

    def span(key):
        values = [x[key] for x in v if x[key] is not None]
        return (min(values), max(values)) if values else (None, None)

    density = [
        x["top_degree_terms"] / x["homogeneous_capacity"]
        for x in v
        if x["homogeneous_capacity"]
    ]
    return {
        "records": len(v),
        "variables": span("variables"),
        "generators": span("generators"),
        "max_degree": span("max_degree"),
        "terms": span("terms"),
        "over_determined": count(lambda x: x["nonzero_generators"] > x["variables"]),
        "square": count(lambda x: x["nonzero_generators"] == x["variables"]),
        "under_determined": count(lambda x: x["nonzero_generators"] < x["variables"]),
        "homogeneous": count(lambda x: x["homogeneous"]),
        "quadratic_only": count(
            lambda x: x["max_degree"] == 2 and x["linear_generators"] == 0
        ),
        "split_components": count(lambda x: x["components"] > 1),
        "unused_variables": count(lambda x: x["unused_variables"] > 0),
        "constant_generator": count(lambda x: x["constant_generators"] > 0),
        "elimination_width": span("elimination_width"),
        "width_capped": count(lambda x: x["elimination_width"] is None),
        "linear_part": count(lambda x: x["linear_rank"] > 0),
        "linear_inconsistent": count(lambda x: not x["linear_consistent"]),
        "substitutions": count(lambda x: x["scalar_substitutions"] > 0),
        "univariate": count(lambda x: x["univariate_generators"] > 0),
        "binomial_majority": count(
            lambda x: 2 * x["binomial_generators"] > x["nonzero_generators"]
        ),
        "monomial_generator": count(lambda x: x["monomial_generators"] > 0),
        "duplicates": count(lambda x: x["duplicate_generators"] > 0),
        "divisible_leading": count(lambda x: x["divisible_leading"] > 0),
        "all_pairs_coprime": count(
            lambda x: x["sampled_pairs"] > 0 and x["coprime_pairs"] == x["sampled_pairs"]
        ),
        "overlap_capped": count(lambda x: x["overlapping_pairs"] is None),
        "top_degree_density": (min(density), max(density)) if density else (None, None),
        "solved": sum(1 for r in records if r.get("cheapest_ns") is not None),
        "small": sum(1 for r in records if is_small(r)),
    }


def fmt_ns(ns):
    if ns is None:
        return "—"
    if ns < 1_000:
        return f"{ns:.0f} ns"
    if ns < 1_000_000:
        return f"{ns / 1e3:.1f} µs"
    if ns < 1_000_000_000:
        return f"{ns / 1e6:.1f} ms"
    return f"{ns / 1e9:.2f} s"


def fmt_ratio(x):
    return "—" if x is None else f"{100 * x:.3f}%"


def fmt_span(pair):
    lo, hi = pair
    if lo is None:
        return "—"
    if isinstance(lo, float):
        return f"{lo:.2g}–{hi:.2g}"
    return f"{lo}–{hi}"


def render(records, repeat=None):
    failed = sorted(r["id"] for r in records if "feature_costs" not in r)
    records = [r for r in records if "feature_costs" in r]
    out = []
    w = out.append
    rows = feature_rows(records)
    cov = coverage(records)
    w(f"# #1009 feature extraction costs ({len(records)} records)\n")
    w(
        f"Small inputs: the cheapest arm completes within {fmt_ns(SMALL_NS)} "
        f"({cov['small']} of {len(records)} records). Threshold: "
        f"{fmt_ratio(FEATURE_FRACTION)} per feature, {fmt_ratio(SET_FRACTION)} for the set.\n"
    )
    if failed:
        w(f"Failed processes, excluded: {', '.join(f'`{i}`' for i in failed)}.\n")
    w("## Extraction cost\n")
    w(
        "| feature | median cost | max cost | median ratio, small | worst ratio, small "
        "| worst record | small inputs over threshold | failing solves at most | verdict "
        "| worst cold ratio, small |"
    )
    w("|---|---:|---:|---:|---:|---|---:|---:|---|---:|")
    for r in rows:
        w(
            f"| `{r['feature']}` | {fmt_ns(r['median_ns'])} | {fmt_ns(r['max_ns'])} "
            f"| {fmt_ratio(r['median_ratio'])} | {fmt_ratio(r['worst_ratio'])} "
            f"| `{r['worst_id']}` | {r['over']} / {r['small']} "
            f"| {fmt_ns(r['failing_below_ns'])} | {r['verdict']} "
            f"| {fmt_ratio(r['worst_cold_ratio'])} |"
        )
    w("")
    if repeat is not None:
        w("## Repeat session\n")
        w("| feature | worst ratio, small | small inputs over threshold | verdict |")
        w("|---|---:|---:|---|")
        for r in feature_rows([x for x in repeat if "feature_costs" in x]):
            w(
                f"| `{r['feature']}` | {fmt_ratio(r['worst_ratio'])} "
                f"| {r['over']} / {r['small']} | {r['verdict']} |"
            )
        w("")
    w("## Per record\n")
    w(
        "| record | n | m | cheapest arm | cheapest solve | entry route | all seven "
        "| ratio | costliest feature |"
    )
    w("|---|---:|---:|---|---:|---|---:|---:|---|")
    for r in sorted(records, key=lambda r: r["id"]):
        v = r["features"]
        total = set_cost_ns(r)
        top = max(FEATURES, key=lambda f: cost_ns(r, f))
        cheapest = r.get("cheapest_ns")
        stopped = stopped_after_ns(r)
        bound = ratio(r, total)
        if cheapest is not None:
            shown, bound_text = fmt_ns(cheapest), fmt_ratio(bound)
        elif stopped:
            shown = f"stopped ≥ {fmt_ns(stopped)}"
            bound_text = f"< {fmt_ratio(total / stopped)}"
        else:
            shown, bound_text = "—", "—"
        w(
            f"| `{r['id']}` | {v['variables']} | {v['nonzero_generators']} "
            f"| {r.get('cheapest_arm', '—')} | {shown} | {r['entry'].get('route') or '—'} "
            f"| {fmt_ns(total)} | {bound_text} | `{top}` |"
        )
    w("")
    w("## Coverage\n")
    w("| question | records |")
    w("|---|---:|")
    labels = [
        ("variables", "variables n (range)"),
        ("generators", "generators m (range)"),
        ("max_degree", "max degree (range)"),
        ("terms", "terms (range)"),
        ("over_determined", "m > n"),
        ("square", "m = n"),
        ("under_determined", "m < n"),
        ("homogeneous", "every generator homogeneous"),
        ("quadratic_only", "degree 2, no linear generator"),
        ("split_components", "incidence graph splits (> 1 component)"),
        ("unused_variables", "a declared variable unused"),
        ("constant_generator", "a nonzero constant generator"),
        ("elimination_width", "greedy elimination width (range)"),
        ("width_capped", "width work cap reached"),
        ("linear_part", "affine-linear rank > 0"),
        ("linear_inconsistent", "inconsistent linear part"),
        ("substitutions", "a scalar substitution"),
        ("univariate", "a univariate generator"),
        ("binomial_majority", "binomials > half the generators"),
        ("monomial_generator", "a monomial generator"),
        ("duplicates", "a duplicate generator"),
        ("divisible_leading", "a leading monomial divisible by another"),
        ("all_pairs_coprime", "every initial pair coprime"),
        ("overlap_capped", "overlap work cap reached"),
        ("top_degree_density", "top-degree density (range)"),
        ("solved", "an arm completed within the wall"),
        ("small", "small (cheapest ≤ 1 s)"),
    ]
    for key, label in labels:
        value = cov[key]
        w(f"| {label} | {fmt_span(value) if isinstance(value, tuple) else value} |")
    return "\n".join(out) + "\n"


def main(argv):
    if argv[:1] == ["--check"]:
        expected = render(
            load(HERE / "records.jsonl.gz"), load(HERE / "records-repeat.jsonl.gz")
        )
        actual = (HERE / "tables.md").read_text()
        if expected != actual:
            print("tables.md is stale: rerun summarize.py", file=sys.stderr)
            return 1
        return 0
    if len(argv) not in (1, 2):
        print(__doc__, file=sys.stderr)
        return 64
    sys.stdout.write(render(load(argv[0]), load(argv[1]) if len(argv) == 2 else None))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
