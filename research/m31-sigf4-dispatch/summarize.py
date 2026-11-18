#!/usr/bin/env python3
"""#905 Gate C tables from `campaign.py` records: per row and worker count, medians of process wall
and peak RSS for the shipping F4 (`f4`) and the entry point (`en`), ratios paired per repetition
with a 95% bootstrap interval of the median (20,000 draws, #904's method), the route and the
in-process dispatch cost; the §6.2 criteria read mechanically. Thresholds are the plan's.

    python3 research/m31-sigf4-dispatch/summarize.py w16.jsonl[.gz] w1.jsonl[.gz] certify.jsonl[.gz]
"""
import gzip
import json
import random
import statistics
import sys
from collections import defaultdict

DRAWS = 20000
GATING_16 = {'wide64/eco-12': ('median', 0.75, 0.80), 'goldilocks/katsura-11': ('excl', 0.90, 1.0)}
CONTROLS = ['goldilocks/katsura-4', 'wide64/katsura-4', 'goldilocks/noon-7', 'goldilocks/cyclic-7']
HELD_OUT = ['wide64/katsura-9', 'wide64/noon-8']


def interval(values, seed=905):
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


def wall(r):
    return r['process_wall_ns'] / 1e6


def rss(r):
    return r['report']['peak_rss_bytes'] / 2**20


def paired(reps, f):
    ratios = [f(reps[k]['en']) / f(reps[k]['f4']) for k in sorted(reps)
              if 'en' in reps[k] and 'f4' in reps[k]]
    lo, hi = interval(ratios)
    return statistics.median(ratios), lo, hi, len(ratios)


def main(paths):
    records = load(paths)
    timed = defaultdict(lambda: defaultdict(dict))  # (row, workers) -> rep -> label -> record
    digests = defaultdict(set)
    failures = []
    certified = {}
    for r in records:
        label, workers = r['arm'].split(':')
        if not complete(r):
            failures.append((r['row'], r['arm'], r['rep'], r['returncode']))
            continue
        digests[r['row']].add(r['report']['basis_sha256'])
        if label == 'ec':
            cert = r['report'].get('certification') or {}
            certified[r['row']] = cert
            continue
        timed[(r['row'], int(workers))][r['rep']][label] = r

    print('| Row | Workers | n | F4 ms | Entry ms | Entry ÷ F4 [95%] | RSS ÷ F4 [95%] | Route | Dispatch µs |')
    print('|---|---:|---:|---:|---:|---:|---:|---|---:|')
    results = {}
    for (row, workers), reps in sorted(timed.items(), key=lambda kv: (kv[0][1] != 16, kv[0][0])):
        t = paired(reps, wall)
        m = paired(reps, rss)
        results[(row, workers)] = (t, m)
        en = [reps[k]['en'] for k in reps if 'en' in reps[k]]
        f4 = [reps[k]['f4'] for k in reps if 'f4' in reps[k]]
        routes = sorted({e['report']['statistics']['route'] for e in en})
        dispatch = statistics.median(e['report']['statistics']['dispatch_ns'] for e in en) / 1e3
        print(f"| {row}{' (held out)' if row in HELD_OUT else ''} | {workers} | {t[3]} "
              f"| {statistics.median(map(wall, f4)):,.1f} | {statistics.median(map(wall, en)):,.1f} "
              f"| {t[0]:.3f} [{t[1]:.3f}, {t[2]:.3f}] | {m[0]:.3f} [{m[1]:.3f}, {m[2]:.3f}] "
              f"| {', '.join(routes)} | {dispatch:.1f} |")

    print('\n## Gate C (plan §6.2), read mechanically\n')
    verdicts = []

    def verdict(name, ok, value):
        verdicts.append(ok)
        print(f"- {name}: {value} — **{'pass' if ok else 'FAIL'}**")

    for row, (kind, a, b) in GATING_16.items():
        t = results[(row, 16)][0]
        ok = t[0] <= a and (t[2] <= b if kind == 'median' else t[2] < b)
        verdict(f'{row} at 16 workers', ok, f'{t[0]:.3f} [{t[1]:.3f}, {t[2]:.3f}]')
    for row in CONTROLS:
        for workers in (1, 16):
            t = results[(row, workers)][0]
            verdict(f'{row} at {workers} worker(s), upper ≤ 1.05', t[2] <= 1.05,
                    f'{t[0]:.3f} [{t[1]:.3f}, {t[2]:.3f}]')
    corpus16 = [k for k in results if k[1] == 16 and k[0] not in HELD_OUT]
    worst = max(corpus16, key=lambda k: results[k][1][0])
    verdict('peak RSS ≤ 1.25× on every corpus row (median paired ratio)',
            all(results[k][1][0] <= 1.25 for k in results if k[0] not in HELD_OUT),
            f'worst {worst[0]} {results[worst][1][0]:.3f}')
    equal = all(len(d) == 1 for d in digests.values())
    verdict('one basis digest per row across arms and repetitions', equal,
            f'{sum(len(d) == 1 for d in digests.values())}/{len(digests)} rows')
    passed = [row for row, c in certified.items() if c.get('checks_passed') and c.get('complete')]
    verdict('certification of every row (entry arm, certify_f4_output)',
            len(passed) == len(certified) and certified, f'{len(passed)}/{len(certified)} rows')
    verdict('every child completed', not failures, f'{len(failures)} failures {failures[:5]}')
    print(f"\nAll measured criteria: **{'pass' if all(verdicts) else 'FAIL'}**")


if __name__ == '__main__':
    main(sys.argv[1:])
