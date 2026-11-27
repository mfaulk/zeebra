#!/usr/bin/env python3
"""Tabulate M4GB's iteration counters per cell (seeds folded; a range means they disagree).

`basis` is the verified basis length. Selection share is of M4GB's own phase totals, which the
unit-ideal exit never prints, so unplanted rows have none.

usage: summarize.py <runs.jsonl>...
"""
import gzip
import json
import sys
from collections import defaultdict

KEYS = ['rounds', 'max_lcm_degree', 'peak_basis', 'peak_pairs', 'peak_store',
        'peak_dense_columns', 'polynomials_added']
HEAD = ['rounds', 'max lcm deg', 'peak #b', 'peak #cp', 'peak store #mr', 'peak dense #mc',
        'polys added', 'basis']


def span(values):
    lo, hi = min(values), max(values)
    return str(lo) if lo == hi else f'{lo}–{hi}'


def main(paths):
    cells = defaultdict(list)
    for path in paths:
        for line in (gzip.open(path, "rt") if path.endswith(".gz") else open(path)):
            r = json.loads(line)
            if r['engine'] != 'm4gb':
                continue
            key = (r['modulus'], r['n'], r['m'], r['density'], r['planted'])
            cells[key].append(r)
    print('| p | n | m | density | planted | ' + ' | '.join(HEAD)
          + ' | selection share | status |')
    print('|' + '---|' * (len(HEAD) + 7))
    for key in sorted(cells):
        rows = cells[key]
        counted = [r['counters'] for r in rows if r.get('counters')]
        cols = [span([c[k] for c in counted]) if counted else '—' for k in KEYS]
        cols.append(span([r['basis_len'] for r in rows if r.get('basis_len') is not None] or [0]))
        shares = []
        for r in rows:
            s = r['stages']
            phases = sum(s.get(f'engine-{k}', 0) for k in ('update', 'matrix', 'selection'))
            if phases:
                shares.append(round(100 * s['engine-selection'] / phases))
        share = f'{span(shares)}%' if shares else '—'
        status = ', '.join(sorted({r['status'][:20] for r in rows}))
        p, n, m, d, planted = key
        print(f'| {p} | {n} | {m} | {d} | {"yes" if planted else "no"} | '
              + ' | '.join(cols) + f' | {share} | {status} |')


if __name__ == '__main__':
    main(sys.argv[1:])
