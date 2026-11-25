#!/usr/bin/env python3
"""#1030's pre-declared rule over the bench host's held-out run (issue comments 7145421369, 7150169799,
7150986750): per field, the median over planted cells whose faster arm takes at least 0.3 s of the
speedup M4GB / X, for X = the best Zeebra arm and X = grobx. Proceed needs >= 1.5x against both, at
GF(31) and GF(65521). Unplanted cells are reported, not decided."""
import gzip
import json
import statistics
import sys
from collections import defaultdict

FLOOR_S, GATE = 0.3, 1.5


def main(path):
    opener = gzip.open if path.endswith('.gz') else open
    cells = defaultdict(lambda: defaultdict(list))
    statuses = defaultdict(lambda: defaultdict(set))
    for line in opener(path, 'rt'):
        r = json.loads(line)
        key = (r['modulus'], r['n'], r['density'], r['seed'], r['planted'])
        statuses[key][r['engine']].add(r['status'])
        ok = ('verified',) if r['engine'] in ('m4gb', 'grobx') else ('complete', 'verified')
        if r['status'] in ok:
            cells[key][r['engine']].append(r['wall_ns'] / 1e9)
    verdict = {}
    for planted in (True, False):
        print(f'## {"Planted (decides)" if planted else "Unplanted (reported)"}\n')
        print('| p | n | density | seed | reps | best Zeebra s | M4GB s | grobx s | best Zeebra ÷ M4GB '
              '| grobx ÷ M4GB | counted |')
        print('|---|---|---|---|---|---|---|---|---|---|---|')
        per_field = defaultdict(lambda: ([], []))
        for key in sorted(k for k in cells if k[4] == planted):
            p, n, d, s, _ = key
            med = {e: statistics.median(v) for e, v in cells[key].items() if v}
            best = min(med[e] for e in ('zeebra', 'zeebra-adaptive') if e in med)
            m4gb, grobx = med.get('m4gb'), med.get('grobx')
            counted = m4gb is not None and grobx is not None and min(best, m4gb, grobx) >= FLOOR_S
            if counted:
                per_field[p][0].append(best / m4gb)
                per_field[p][1].append(grobx / m4gb)
            reps = min(len(v) for v in cells[key].values())
            f = (lambda v: f'{v:.3f}' if v is not None else 'failed')
            print(f'| {p} | {n} | {d} | {s} | {reps} | {best:.3f} | {f(m4gb)} | {f(grobx)} '
                  f'| {best / m4gb:.2f}x | {grobx / m4gb:.2f}x | {"yes" if counted else "no (floor)"} |'
                  if m4gb and grobx else f'| {p} | {n} | {d} | {s} | {reps} | {best:.3f} | {f(m4gb)} '
                  f'| {f(grobx)} | — | — | no |')
        print()
        for p, (vz, vg) in sorted(per_field.items()):
            mz, mg = statistics.median(vz), statistics.median(vg)
            print(f'- GF({p}), {len(vz)} counted cells: M4GB vs best Zeebra **{mz:.2f}x**, '
                  f'M4GB vs grobx **{mg:.2f}x**')
            if planted:
                verdict[p] = (mz >= GATE, mg >= GATE)
        print()
    failed = [(k, e, st) for k, v in statuses.items() for e, st in v.items()
              if st - {'complete', 'verified'}]
    print(f'Non-answered rows: {failed if failed else "none"}\n')
    zeebra = all(v[0] for v in verdict.values()) and {31, 65521} <= verdict.keys()
    both = zeebra and all(v[1] for v in verdict.values())
    print(f'Against best Zeebra: {"holds" if zeebra else "fails"}. Against grobx: '
          f'{"holds" if all(v[1] for v in verdict.values()) else "fails"}. '
          f'**Decision: {"PROCEED" if both else "REJECT"}** (the hypothesis needs both).')


if __name__ == '__main__':
    main(sys.argv[1])
