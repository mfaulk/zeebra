#!/usr/bin/env python3
"""Fold split_run.py's per-arm runs into counts.tsv, keeping its schema.

A bilinear-arm run replaces the instance's bilinear columns (and its status); a control or
signature run replaces only that arm's columns. A run stopped by the watchdog writes `censored`
or `refused:rss` into the arm's columns; a skipped one writes `skipped`. A stopped or skipped
bilinear arm makes the instance's status `censored` or `skipped` (an RSS refusal is `failed`,
like F4's own budget refusals).

Usage: merge.py counts.tsv runs.tsv [runs.tsv ...] > merged.tsv
"""

import csv
import sys

KEY = ("k", "n_y", "kind", "field", "support", "seed")
BILINEAR = [
    "status", "basis", "matrices", "degree", "largest_matrix", "largest_block", "reduction",
    "total_area", "total_block_area", "columns", "regrouped_columns",
]
ARM_COLUMNS = {
    "control": ["control_degree", "control_largest_matrix"],
    "signature": ["sig_max_rows", "sig_max_columns"],
}


def main(counts, runs):
    with open(counts) as f:
        reader = csv.DictReader(f, delimiter="\t")
        header = reader.fieldnames
        rows = list(reader)
    index = {tuple(r[k] for k in KEY): r for r in rows}
    for path in runs:
        for line in open(path):
            arm, outcome, rest = line.rstrip("\n").split("\t", 2)
            values = rest.split("\t")
            run = dict(zip(header, values))
            row = index[tuple(run[k] for k in KEY)]
            stopped = {"censored": "censored", "refused-rss": "refused:rss", "skipped": "skipped"}
            if arm == "bilinear":
                if outcome == "ran":
                    for c in BILINEAR:
                        row[c] = run.get(c, "")
                else:
                    row["status"] = {"refused-rss": "failed"}.get(outcome, outcome)
                    for c in BILINEAR[1:]:
                        row[c] = "refused:rss" if outcome == "refused-rss" else ""
                    for c in ARM_COLUMNS["control"] + ARM_COLUMNS["signature"]:
                        row[c] = ""
            else:
                for c in ARM_COLUMNS[arm]:
                    row[c] = run[c] if outcome == "ran" else stopped[outcome]
    w = csv.DictWriter(sys.stdout, header, delimiter="\t", lineterminator="\n")
    w.writeheader()
    for r in rows:
        # A row that was never `done` carries no trailing columns, as in the original file.
        if r["status"] != "done":
            print("\t".join([r[c] for c in header[:9]] + ([r["basis"]] if r["status"] == "failed" and r["basis"] else [])))
            continue
        w.writerow(r)


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2:])
