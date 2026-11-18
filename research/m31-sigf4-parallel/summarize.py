"""#904 tables from `campaign.py` records: per row and arm, medians of process wall, elimination,
products and peak RSS; ratios paired per repetition with a 95% bootstrap interval of the median
(#903's method, 20,000 draws); Gate B (plan §8.2) and #905's Target criterion 1 read mechanically.

    python3 research/m31-sigf4-parallel/summarize.py gate.jsonl[.gz] [reported.jsonl ...]
"""
import gzip
import json
import random
import statistics
import sys
from collections import defaultdict

DRAWS = 20000


def interval(values, seed=904):
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


def metric(r, name):
    report = r['report']
    st = report.get('statistics') or {}
    return {
        'wall': r['process_wall_ns'] / 1e6,
        'elim': st.get('elimination_ns', 0) / 1e6,
        'products': st.get('coefficient_products'),
        'rss': report['peak_rss_bytes'] / 2**20,
    }[name]


def fmt(x, digits=1):
    return '—' if x is None else f'{x:,.{digits}f}'


def paired(by_rep, num, den, name):
    ratios = [metric(by_rep[r][num], name) / metric(by_rep[r][den], name)
              for r in sorted(by_rep) if num in by_rep[r] and den in by_rep[r]]
    if not ratios:
        return None
    lo, hi = interval(ratios)
    return statistics.median(ratios), lo, hi, len(ratios)


def main(paths):
    records = load(paths)
    failed = [r for r in records if not complete(r)]
    rows = defaultdict(lambda: defaultdict(dict))
    digests = defaultdict(set)
    for r in records:
        if complete(r):
            rows[r['row']][r['rep']][r['arm']] = r
            digests[r['row']].add(r['report']['basis_sha256'])
    print(f'records {len(records)}, incomplete {len(failed)}')
    for row, by_rep in rows.items():
        arms = sorted({a for rep in by_rep.values() for a in rep})
        print(f'\n## {row}  (basis digests: {len(digests[row])})\n')
        print('| Arm | n | Process wall ms | Elimination ms | Products | Peak RSS MiB |')
        print('|---|---:|---:|---:|---:|---:|')
        for arm in arms:
            rs = [rep[arm] for rep in by_rep.values() if arm in rep]
            def med(n):
                values = [metric(r, n) for r in rs]
                return None if None in values else statistics.median(values)
            sig = not arm.startswith('f4')
            print(f'| {arm} | {len(rs)} | {fmt(med("wall"))} | {fmt(med("elim")) if sig else "—"} | '
                  f'{fmt(med("products"), 0) if sig else "—"} | {fmt(med("rss"))} |')
        print()
        for num in arms:
            for den in ('d1:1', 'f4:16'):
                if num == den or den not in arms:
                    continue
                for name in ('wall', 'elim', 'products', 'rss'):
                    if (den == 'f4:16' or num.startswith('f4')) and name != 'wall':
                        continue
                    got = paired(by_rep, num, den, name)
                    if got:
                        m, lo, hi, n = got
                        print(f'- {num} ÷ {den} {name}: {m:.3f} [{lo:.3f}, {hi:.3f}] (n={n})')
        if row == 'wide64/eco-12' and 's2:16' in arms and 'd1:1' in arms:
            elim = paired(by_rep, 'd1:1', 's2:16', 'elim')
            wall = paired(by_rep, 's2:16', 'd1:1', 'wall')
            prod = paired(by_rep, 's2:16', 'd1:1', 'products')
            rss = paired(by_rep, 's2:16', 'd1:1', 'rss')
            print('\nGate B (plan §8.2):')
            print(f'- elimination speedup d1 ÷ s2 median {elim[0]:.3f} [{elim[1]:.3f}, {elim[2]:.3f}]'
                  f' ≥ 2.5: {"pass" if elim[0] >= 2.5 else "FAIL"}')
            print(f'- wall s2 ÷ d1 median {wall[0]:.3f} ≤ 0.75 and upper {wall[2]:.3f} ≤ 0.80: '
                  f'{"pass" if wall[0] <= 0.75 and wall[2] <= 0.80 else "FAIL"}')
            print(f'- products {prod[0]:.3f} ≤ 1.25: {"pass" if prod[0] <= 1.25 else "FAIL"}')
            print(f'- peak RSS {rss[0]:.3f} ≤ 1.25: {"pass" if rss[0] <= 1.25 else "FAIL"}')
        if row == 'wide64/eco-12' and 's2:16' in arms and 'f4:16' in arms:
            t = paired(by_rep, 's2:16', 'f4:16', 'wall')
            print(f'\nvs F4-16: s2 ÷ f4 median {t[0]:.3f} [{t[1]:.3f}, {t[2]:.3f}]; Target 1 (Eco-12: median ≤ 0.75, '
                  f'upper ≤ 0.80): {"pass" if t[0] <= 0.75 and t[2] <= 0.80 else "FAIL"}')


if __name__ == '__main__':
    main(sys.argv[1:])
