#!/usr/bin/env python3
"""#927 Gate R tables from `campaign.py` records: per row and worker count, the new entry point
(`en`) against its reference (`f4` conventional F4, or `m31` M31's entry point), paired per
repetition, median with a 95% bootstrap interval of the median (20,000 draws); the route, team and
dispatch cost; and plan §10.3's precision rule (half-width ≤ half the distance from the threshold
to 1.0). Rows of the `small` suite use the median warm in-process call per process.

    python3 research/m32-adaptive-dispatch/summarize.py mq10.jsonl[.gz] fav.jsonl[.gz] ...
"""
import gzip
import json
import random
import statistics
import sys
from collections import defaultdict

DRAWS = 20000
# Plan §8.2 Gate R: (reference arm, threshold on the 95% upper bound).
BOUNDS = {'mq10': ('f4', 1.05), 'fav': ('m31', 1.03), 'ctrl': ('f4', 1.05)}
SMALL_BOUNDS = {'wide64/katsura-9': ('m31', 1.03)}
SMALL_DEFAULT = ('f4', 1.05)
T9_NS = 50_000


def interval(values, seed=927):
    rng = random.Random(seed)
    medians = sorted(statistics.median(rng.choices(values, k=len(values))) for _ in range(DRAWS))
    return medians[int(0.025 * DRAWS)], medians[int(0.975 * DRAWS) - 1]


def load(paths):
    records = []
    for path in paths:
        opener = gzip.open if path.endswith('.gz') else open
        with opener(path, 'rt') as handle:
            records.extend(json.loads(line) for line in handle if line.strip())
    return records


def complete(r):
    return r['returncode'] == 0 and (r.get('report') or {}).get('status') == 'complete'


def metric(r):
    """Milliseconds: process wall, or the median warm call for the small suite."""
    warm = r['report'].get('warm_ns') or []
    if r['suite'] == 'small':
        return statistics.median(warm) / 1e6
    return r['process_wall_ns'] / 1e6


def bound(suite, row):
    if suite == 'small':
        return SMALL_BOUNDS.get(row, SMALL_DEFAULT)
    return BOUNDS[suite]


def main(paths):
    records = load(paths)
    cells = defaultdict(lambda: defaultdict(dict))  # (suite, row, workers) -> rep -> label -> record
    digests = defaultdict(set)
    failures = []
    dispatch = []  # (row, workers, dispatch ns, wall ms)
    for r in records:
        if not complete(r):
            failures.append((r['suite'], r['row'], r['arm'], r['rep'], r['returncode']))
            continue
        label, workers = r['arm'].split(':')
        cells[(r['suite'], r['row'], int(workers))][r['rep']][label] = r
        digests[r['row']].add(r['report']['basis_sha256'])
        if label == 'en':
            stats = r['report']['statistics']
            dispatch.append((r['row'], int(workers), stats['dispatch_ns'], r['process_wall_ns'] / 1e6))
    print('| suite | row | w | n | reference ms | en ms | en ÷ ref [95%] | half-width | bound | read |'
          ' route | team |')
    print('|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|---:|')
    verdicts = []
    for (suite, row, workers) in sorted(cells, key=lambda k: (k[0], k[1], k[2])):
        ref, threshold = bound(suite, row)
        reps = cells[(suite, row, workers)]
        pairs = [(reps[k]['en'], reps[k][ref]) for k in sorted(reps) if 'en' in reps[k] and ref in reps[k]]
        ratios = [metric(e) / metric(b) for e, b in pairs]
        lo, hi = interval(ratios)
        med = statistics.median(ratios)
        half = (hi - lo) / 2 / med
        readable = half <= (threshold - 1.0) / 2
        passed = hi <= threshold
        read = ('pass' if passed else 'FAIL') + ('' if readable else ' (imprecise)')
        verdicts.append((suite, row, workers, passed, readable))
        stats = pairs[0][0]['report']['statistics']
        print(f"| {suite} | {row} | {workers} | {len(ratios)} | "
              f"{statistics.median(metric(b) for _, b in pairs):.2f} | "
              f"{statistics.median(metric(e) for e, _ in pairs):.2f} | "
              f"{med:.3f} [{lo:.3f}, {hi:.3f}] | {100 * half:.1f}% | {threshold} | {read} | "
              f"{stats['route']} | {stats.get('team', '—')} |")
    print()
    worst = max(dispatch, key=lambda d: d[2])
    worst_share = max((d[2] / 1e6 / d[3] for d in dispatch if d[3] >= 50), default=0.0)
    t9 = worst[2] <= T9_NS and worst_share <= 0.001
    print(f"T9 dispatch cost: max {worst[2] / 1e3:.1f} µs ({worst[0]}, {worst[1]} w); "
          f"median {statistics.median(d[2] for d in dispatch) / 1e3:.1f} µs; "
          f"worst share of wall on rows ≥ 50 ms {100 * worst_share:.4f}% — {'pass' if t9 else 'FAIL'}")
    print(f"Basis digests: {sum(len(v) == 1 for v in digests.values())} of {len(digests)} rows "
          f"have one digest across every arm and repetition")
    print(f"Incomplete children: {len(failures)} {failures[:5]}")
    imprecise = [v[:3] for v in verdicts if not v[4]]
    print(f"Imprecise cells (extension candidates): {imprecise}")
    gate = all(v[3] for v in verdicts) and t9 and not failures and all(len(v) == 1 for v in digests.values())
    print(f"Gate R: {'PASS' if gate else 'FAIL'}")


if __name__ == '__main__':
    main(sys.argv[1:])
