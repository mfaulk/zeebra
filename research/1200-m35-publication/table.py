#!/usr/bin/env python3
"""#1200: the publication gap table and the declared regimes' scores from extracted records.

    table.py records.jsonl [records.jsonl ...] [--panel panel.json]

Timing is library-call time (`call_ns`), as in #1162. A row's Zeebra figure is the faster median of
`f4` and `adaptive` (a per-row choice, labelled as such); `adaptive` alone is shown beside it. `R` is
Zeebra ÷ default grobx, medians of clean completed attempts, with an independent percentile bootstrap.
A regime's score aggregates by lineage (base problem): the geometric mean of its rows' `R` within a
lineage, then across lineages (plan §3).
"""
import argparse
import collections
import json
import math
import random
import statistics
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'tools'))
import bench_stats  # noqa: E402

ZEEBRA = ('f4', 'adaptive')
DRAWS = 5000


def load(paths):
    rows = collections.defaultdict(lambda: collections.defaultdict(list))
    for path in paths:
        for line in open(path):
            r = json.loads(line)
            rows[r['id']][r['arm']].append(r)
    return rows


def clean(attempts):
    return [a for a in attempts if not a['contaminated']]


def seconds(attempts):
    return [a['call_ns'] / 1e9 for a in clean(attempts) if a['status'] == 'complete' and a['call_ns']]


def median(xs):
    return statistics.median(xs) if xs else None


def best_arm(arms):
    timed = [(median(seconds(arms.get(k, []))), k) for k in ZEEBRA]
    timed = [(s, k) for s, k in timed if s is not None]
    return min(timed)[1] if timed else None


def lineage(rid):
    row = rid.split('@')[0]
    row = row[4:] if row.startswith('gen-') else row
    return row.rsplit('-', 1)[0]


def outcome(attempts):
    statuses = collections.Counter(a['status'] for a in clean(attempts))
    return 'complete' if statuses.get('complete') else (statuses.most_common(1)[0][0] if statuses else '-')


def fmt(s):
    return '-' if s is None else (f'{s:.3f}' if s < 1 else f'{s:.2f}')


def row_table(rows):
    print('| Row | n | f4 (s) | adaptive (s) | grobx (s) | Zeebra arm | R | 95% interval | '
          'adaptive R | Peak RSS Zeebra / grobx (MiB) | Digests | Contaminated |')
    print('|---|---:|---:|---:|---:|---|---:|---|---:|---|---|---:|')
    for rid in sorted(rows):
        arms = rows[rid]
        g = seconds(arms.get('grobx', []))
        arm = best_arm(arms)
        cells = []
        for k in ZEEBRA:
            s = median(seconds(arms.get(k, [])))
            cells.append(fmt(s) if s is not None else (outcome(arms[k]) if k in arms else '-'))
        r = ci = ra = '-'
        if arm and g:
            iv = bench_stats.independent_ratio(seconds(arms[arm]), g, seed=rid)
            r, ci = f'{iv.median:.2f}', f'{iv.lo:.2f}–{iv.hi:.2f}'
        if seconds(arms.get('adaptive', [])) and g:
            ra = f"{median(seconds(arms['adaptive'])) / median(g):.2f}"
        rss = lambda k: median([a['peak_rss_bytes'] / 2**20 for a in clean(arms.get(k, []))  # noqa: E731
                                if a['status'] == 'complete' and a['peak_rss_bytes']])
        zr, gr = rss(arm) if arm else None, rss('grobx')
        digests = {a['basis_sha256'] for v in arms.values() for a in v if a.get('basis_sha256')}
        agree = 'agree' if len(digests) == 1 else ('-' if not digests else f'DIFFER ({len(digests)})')
        dirty = sum(a['contaminated'] for v in arms.values() for a in v)
        n = len(g) if g else 0
        print(f"| `{rid}` | {n} | {cells[0]} | {cells[1]} | {fmt(median(g)) if g else outcome(arms.get('grobx', []))} | {arm or '-'} | {r} | {ci} | "
              f"{ra} | {fmt(zr) if zr else '-'} / {fmt(gr) if gr else '-'} | {agree} | {dirty} |")


def regime_score(rows, ids, rng):
    """Point estimate and a bootstrap interval for the lineage-nested geometric mean of R."""
    samples = {}
    for rid in ids:
        arms = rows.get(rid, {})
        arm, g = best_arm(arms), seconds(arms.get('grobx', []))
        if not arm or not g:
            return None
        samples[rid] = (seconds(arms[arm]), g)

    def score(pick):
        by_lineage = collections.defaultdict(list)
        for rid, (z, g) in samples.items():
            by_lineage[lineage(rid)].append(math.log(median(pick(z)) / median(pick(g))))
        return math.exp(statistics.mean(statistics.mean(v) for v in by_lineage.values()))

    point = score(lambda xs: xs)
    draws = sorted(score(lambda xs: rng.choices(xs, k=len(xs))) for _ in range(DRAWS))
    worst = max(median(z) / median(g) for z, g in samples.values())
    return point, draws[int(0.025 * DRAWS)], draws[int(0.975 * DRAWS) - 1], worst


def regimes(rows, panel):
    print('| Regime | Rows | Lineages | Geometric-mean R | 95% interval | Largest row median R |')
    print('|---|---:|---|---:|---|---:|')
    for name, reg in panel['regimes'].items():
        if not isinstance(reg, dict) or 'rows' not in reg:
            continue
        res = regime_score(rows, reg['rows'], random.Random(name))
        lin = ', '.join(sorted({lineage(r) for r in reg['rows']}))
        if res is None:
            print(f"| {name} | {len(reg['rows'])} | {lin} | incomplete | - | - |")
            continue
        p, lo, hi, worst = res
        print(f"| {name} | {len(reg['rows'])} | {lin} | {p:.2f} | {lo:.2f}–{hi:.2f} | {worst:.2f} |")


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('records', nargs='+')
    p.add_argument('--panel', default=str(Path(__file__).resolve().parents[1] / '1162-m35-baseline' / 'panel.json'))
    a = p.parse_args()
    rows = load(a.records)
    panel = json.load(open(a.panel))
    print('### Regimes\n')
    regimes(rows, panel)
    print('\n### Rows\n')
    row_table(rows)


if __name__ == '__main__':
    main()
