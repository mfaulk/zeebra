#!/usr/bin/env python3
"""#945's gate tables from `records.jsonl` (written by run.sh), as Markdown on stdout.

Pairs the k-th lane attempt of a row with its k-th field (or accumulator) attempt, the order
run.sh interleaves them in, and reports the paired lane/field ratio of process wall with
`tools/bench_stats.paired_ratio`, seeded by the row label. A row whose two arms disagree on the
basis or echelon digest, or that has a failed attempt, is reported as such and gets no ratio.
"""
import json
import pathlib
import statistics
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / "tools"))
import bench_stats  # noqa: E402

COMPLETE_BOUND = 0.87
CONTROL_BOUND = 1.05
MATRIX_BOUND = 0.5


def main(path):
    records = [json.loads(line) for line in open(path) if line.strip()]
    rows = {}
    for r in records:
        rows.setdefault(r["label"], {}).setdefault(r["arm"], []).append(r)

    print("| Row | Field / accumulator median | Lane median | Lane ÷ field [95% CI], n | Bound | "
          "Peak RSS lane ÷ field | Digests agree | Verdict |")
    print("|---|---|---|---|---|---|---|---|")
    for label, arms in rows.items():
        base_arm = "accumulator" if "accumulator" in arms else "field"
        base, lane = arms.get(base_arm, []), arms.get("lane", [])
        failed = [r for r in base + lane if r["rc"] != 0 or r.get("status", "complete") != "complete"]
        digest = "output_digest" if base_arm == "accumulator" else "basis_m33"
        digests = {r.get(digest) for r in base + lane + arms.get("entry", [])}
        wall = "forward_seconds" if base_arm == "accumulator" else "wall_s"
        bound = (MATRIX_BOUND if base_arm == "accumulator"
                 else COMPLETE_BOUND if "dense" in label else CONTROL_BOUND)
        k = min(len(base), len(lane))
        if failed or k == 0:
            print(f"| {label} | | | | ≤ {bound} | | | INCOMPLETE ({len(failed)} failed) |")
            continue
        ratios = [lane[i][wall] / base[i][wall] for i in range(k)]
        ci = bench_stats.paired_ratio(ratios, seed=label)
        rss = statistics.median(lane[i]["max_rss_kib"] / base[i]["max_rss_kib"] for i in range(k))
        agree = len(digests) == 1
        verdict = "PASS" if agree and ci.hi <= bound else "FAIL"
        entry = arms.get("entry")
        note = f" (entry {statistics.median(r['wall_s'] for r in entry):.2f} s)" if entry else ""
        print(f"| {label} | {statistics.median(r[wall] for r in base[:k]):.2f} s{note} | "
              f"{statistics.median(r[wall] for r in lane[:k]):.2f} s | "
              f"{ci.median:.3f} [{ci.lo:.3f}, {ci.hi:.3f}], {k} | ≤ {bound} | {rss:.2f} | "
              f"{'yes' if agree else 'NO'} | {verdict} |")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else pathlib.Path(__file__).parent / "records.jsonl")
