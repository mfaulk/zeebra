#!/usr/bin/env python3
"""#1162: band, ratio and phase-share tables from the development probe's records.

    summarize.py probe.jsonl [--phases | --signature]

Every figure here is development mode (`probe.py`): it places rows in time bands and attributes
phases. None of it is a deciding timing.
"""
import argparse
import collections
import json
import sys
from pathlib import Path

ZEEBRA = ('f4', 'adaptive')
F4_PHASES = ('symbolic_ns', 'construction_ns', 'forward_ns', 'fl_sweep_ns', 'fl_echelon_ns',
             'backward_ns', 'extraction_ns', 'interreduction_ns')


def load(path):
    rows = collections.defaultdict(dict)
    for line in open(path):
        r = json.loads(line)
        rows[r['id']][r['arm']] = r
    return rows


def seconds(r):
    return r['call_ns'] / 1e9 if r and r['status'] == 'complete' and r['call_ns'] else None


def cell(r):
    if not r:
        return '-'
    s = seconds(r)
    return f'{s:.2f}' if s is not None else r['status']


def band(s):
    if s is None:
        return 'frontier'
    return '<1 s' if s < 1 else ('1-300 s' if s <= 300 else '>300 s')


def table(rows):
    print('| Record | Role | f4 (s) | adaptive (s) | grobx (s) | best Zeebra / grobx | Zeebra band | '
          'Digests | adaptive route | grobx runs |')
    print('|---|---|---|---|---|---|---|---|---|---|')
    for i in sorted(rows):
        a = rows[i]
        best = min((s for s in (seconds(a.get(k)) for k in ZEEBRA) if s is not None), default=None)
        g = seconds(a.get('grobx'))
        ratio = f'{best / g:.1f}' if best and g else '-'
        digests = {r['basis_sha256'] for r in a.values() if r.get('basis_sha256')}
        agree = 'agree' if len(digests) == 1 else ('-' if not digests else 'DIFFER')
        runs = (a.get('grobx') or {}).get('report', {}).get('runs', [])
        chain = ' → '.join(f"{r['engine']}/{r['reduce']}" for r in runs) or '-'
        role = next(iter(a.values())).get('role') or ''
        print(f"| `{i}` | {role.split(' ')[0]} | {cell(a.get('f4'))} | {cell(a.get('adaptive'))} | "
              f"{cell(a.get('grobx'))} | {ratio} | {band(best)} | {agree} | "
              f"{(a.get('adaptive') or {}).get('route') or '-'} | {chain} |")


def phases(rows):
    print('| Record | f4-stages total (s) | ' + ' | '.join(p[:-3] for p in F4_PHASES) +
          ' | zero rows / rows | grobx reduce share | grobx symbolic+encode+decode share |')
    print('|---|---|' + '---|' * len(F4_PHASES) + '---|---|---|')
    for i in sorted(rows):
        z = rows[i].get('f4-stages')
        if not z or z['status'] != 'complete' or not z.get('stages'):
            continue
        st, c = z['stages'], z.get('counters') or {}
        total = st['total_ns'] or 1
        shares = ' | '.join(f'{100 * st[p] / total:.0f}%' for p in F4_PHASES)
        zr = f"{c.get('zero_rows', 0)}/{c.get('pairs_reduced', 0)}"
        g = rows[i].get('grobx')
        gs = '-'
        gm = '-'
        if g and g['status'] == 'complete':
            rs = g['report']['round_stage_s']
            gt = sum(rs.values()) + sum(g['report']['inter_s'].values()) or 1
            gs = f"{100 * rs['reduce'] / gt:.0f}%"
            gm = f"{100 * (rs['symbolic'] + rs['encode'] + rs['decode']) / gt:.0f}%"
        print(f'| `{i}` | {total / 1e9:.2f} | {shares} | {zr} | {gs} | {gm} |')


SIG_PHASES = ('bookkeeping_ns', 'element_hashing_ns', 'symbolic_ns', 'elimination_ns', 'interreduction_ns')


def signature(rows):
    print('| Record | sig total (s) | ' + ' | '.join(p[:-3] for p in SIG_PHASES) +
          ' | products on zero rows | reductions to zero / targets |')
    print('|---|---|' + '---|' * len(SIG_PHASES) + '---|---|')
    for i in sorted(rows):
        z = rows[i].get('sig-stages')
        if not z or z['status'] != 'complete' or not z.get('counters'):
            continue
        c = z['counters']
        total = c['total_ns'] or 1
        shares = ' | '.join(f'{100 * c[p] / total:.0f}%' for p in SIG_PHASES)
        zero = f"{100 * c['products_on_zero_rows'] / (c['coefficient_products'] or 1):.0f}%"
        print(f"| `{i}` | {total / 1e9:.2f} | {shares} | {zero} | "
              f"{c['reductions_to_zero']}/{c['targets']} |")


OVERHEAD_S = 1.9  # upper end of #1158's measured 1.4-1.9 s per attempt
PRIMARY_ARMS = ('f4', 'adaptive', 'grobx')
EXACT_ROWS = ('mq-dense-15-s15@m31', 'gen-chandrasekhar-h-11@p31', 'eco-12@w59', 'katsura-9@m31',
              'katsura-9@w59', 'eco-8@m31', 'cyclic-7@m31', 'gen-chandrasekhar-h-11@p64')


def repetitions(s):
    return 9 if s < 60 else 3


def attempt_seconds(r, cap):
    """A completed or limit-stopped attempt costs its measured call; only a timeout costs the cap."""
    if r and r.get('call_ns') and r['status'] in ('complete', 'stopped'):
        return min(r['call_ns'] / 1e9, cap)
    return cap


def price(rows, panel_path, cap):
    sys_path = str(Path(__file__).resolve().parent)
    if sys_path not in sys.path:
        sys.path.insert(0, sys_path)
    import catalog
    panel = json.loads(Path(panel_path).read_text())
    groups = collections.defaultdict(list)
    for family, row, field in catalog.panel_rows(panel):
        frontier = row in family.get('frontier', [])
        groups['frontier' if frontier else family['role'].split(' ')[0]].append(f'{row}@{field}')
    print('| Group | Rows | Arms | Attempts | Solve (h) | Harness (h) | Total (h) |')
    print('|---|---:|---:|---:|---:|---:|---:|')
    grand = 0.0
    for group in ('target', 'control', 'frontier'):
        attempts = solve = 0.0
        ids = groups[group]
        for i in ids:
            for arm in PRIMARY_ARMS:
                s = attempt_seconds(rows.get(i, {}).get(arm), cap)
                n = 1 if group == 'frontier' else repetitions(s)
                attempts += n
                solve += n * s
        harness = attempts * OVERHEAD_S
        grand += solve + harness
        print(f'| {group} | {len(ids)} | {len(PRIMARY_ARMS)} | {attempts:.0f} | {solve / 3600:.2f} | '
              f'{harness / 3600:.2f} | {(solve + harness) / 3600:.2f} |')
    print(f'| **primary total** | | | | | | **{grand / 3600:.2f}** |')
    attempts = solve = 0.0
    for i in EXACT_ROWS:
        s = attempt_seconds(rows.get(i, {}).get('grobx-certified') or None, cap)
        if not rows.get(i, {}).get('grobx-certified'):
            s = 60 * max(seconds(rows.get(i, {}).get('grobx')) or 1, 1)  # unmeasured: 60x raw
        n = 3
        attempts += n
        solve += n * min(s, cap)
    harness = attempts * OVERHEAD_S
    print(f'| secondary: grobx exact checker | {len(EXACT_ROWS)} | 1 | {attempts:.0f} | '
          f'{solve / 3600:.2f} | {harness / 3600:.2f} | {(solve + harness) / 3600:.2f} |')


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('records')
    p.add_argument('--phases', action='store_true')
    p.add_argument('--signature', action='store_true')
    p.add_argument('--price', metavar='PANEL', help='price the manifest for this panel.json')
    p.add_argument('--cap-s', type=float, default=300.0)
    args = p.parse_args()
    rows = load(args.records)
    if args.price:
        price(rows, args.price, args.cap_s)
    else:
        (signature if args.signature else phases if args.phases else table)(rows)


if __name__ == '__main__':
    main()
