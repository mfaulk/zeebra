"""#1077 fresh-process whole solves: per-set arm totals, per-instance ratio ranges and peak RSS.

    python3 -I research/gf2-residual/analyze_fresh.py <solve-fresh-*.tsv>...

Each cell is the median over a process's repetitions. Ratios pair arms per instance, then report
the range; totals are sums of per-instance medians.
"""

import csv
import statistics
import sys
from collections import defaultdict

PAIRS = [("packed", "eager"), ("auto", "auto-eager")]


def load(paths):
    cells = defaultdict(list)
    for path in paths:
        with open(path, newline="") as handle:
            for row in csv.DictReader(handle, delimiter="\t"):
                key = (row["set"], row["instance"], row["arm"], int(row["workers"]))
                cells[key].append(row)
    return cells


def median(rows, field):
    return statistics.median(float(row[field]) for row in rows)


def main(paths):
    cells = load(paths)
    groups = defaultdict(dict)
    for (set_name, instance, arm, workers), rows in cells.items():
        groups[(set_name, workers)].setdefault(instance, {})[arm] = rows
    for (set_name, workers), instances in sorted(groups.items()):
        for slow, fast in PAIRS:
            paired = {
                name: arms for name, arms in instances.items() if slow in arms and fast in arms
            }
            if not paired:
                continue
            for name, arms in paired.items():
                bases = {row["basis"] for rows in arms.values() for row in rows}
                assert len(bases) == 1, f"{name}: basis sizes differ {bases}"
            totals = {
                arm: sum(median(arms[arm], "wall_ms") for arms in paired.values())
                for arm in (slow, fast)
            }
            elim = {
                arm: sum(median(arms[arm], "elim_ms") for arms in paired.values())
                for arm in (slow, fast)
            }
            ratios = [
                median(arms[slow], "wall_ms") / median(arms[fast], "wall_ms")
                for arms in paired.values()
            ]
            elim_ratios = [
                median(arms[slow], "elim_ms") / median(arms[fast], "elim_ms")
                for arms in paired.values()
                if median(arms[fast], "elim_ms") > 0
            ]
            rss = [
                median(arms[fast], "peak_rss_kib") / median(arms[slow], "peak_rss_kib")
                for arms in paired.values()
            ]
            print(
                f"{set_name}\tworkers={workers}\t{slow}/{fast}\tn={len(paired)}"
                f"\t{slow}={totals[slow]:.1f}ms\t{fast}={totals[fast]:.1f}ms"
                f"\ttotal={totals[slow] / totals[fast]:.3f}x"
                f"\tper-instance={min(ratios):.3f}x-{max(ratios):.3f}x"
                f"\telim-total={elim[slow] / elim[fast]:.3f}x"
                f"\telim-per-instance={min(elim_ratios):.3f}x-{max(elim_ratios):.3f}x"
                f"\trss {fast}/{slow}={min(rss):.3f}x-{max(rss):.3f}x"
            )
        if set_name in ("heldout", "big"):
            arms_present = sorted({arm for arms in instances.values() for arm in arms})
            print("instance\t" + "\t".join(f"{a}_ms\t{a}_elim\t{a}_rss" for a in arms_present))
            for name, arms in sorted(instances.items()):
                fields = [name]
                for arm in arms_present:
                    rows = arms.get(arm, [])
                    fields += (
                        [
                            f"{median(rows, 'wall_ms'):.2f}",
                            f"{median(rows, 'elim_ms'):.2f}",
                            f"{median(rows, 'peak_rss_kib') / 1024:.1f}",
                        ]
                        if rows
                        else ["-", "-", "-"]
                    )
                print("\t".join(fields))


if __name__ == "__main__":
    main(sys.argv[1:])
