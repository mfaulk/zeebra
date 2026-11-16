#!/usr/bin/env python3
"""#821: the current-code Zeebra wide-ladder cohorts against the retained #738 comparand rows.

    python3 research/wide-corpus/current-821/summarize.py [--check]

Every new Zeebra completion is compared coefficient for coefficient with every complete answer
for the same input (the #738 Zeebra answer included) using the board's own `verify_bases`, and
ratios use the board's own startup gate: both operands at least 2x their engine's Katsura-4
control. With --check, fails unless every new completion agrees with at least one other answer.
"""
import importlib.util
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
spec = importlib.util.spec_from_file_location('wide', ROOT / 'tools/external/wide-corpus.py')
wide = importlib.util.module_from_spec(spec)
spec.loader.exec_module(wide)

archive = wide.load(ROOT / 'research/wide-corpus/campaign.json.gz')
cohorts = {w: wide.load(HERE / f'workers-{w}.json.gz') for w in (1, 16)}
COMPARANDS = wide.ENGINES[1:]


def by_cell(attempts):
    out = {}
    for a in attempts:
        out.setdefault((a['field'], a['name']), {})[a['engine']] = a
    return out


old = by_cell(archive['attempts'])
new = {w: by_cell(c['attempts']) for w, c in cohorts.items()}


def floor(cells, field, engine):
    a = cells.get((field, 'katsura-4'), {}).get(engine)
    return wide.seconds(a) if a and wide.completed(a) else 0


def cell(a):
    if a is None:
        return 'not run'
    if wide.completed(a):
        return f'{wide.seconds(a):.3f}'
    r = a.get('report', {})
    status = a.get('stop') or r.get('status', 'runner-failure')
    if status == 'stopped-by-limit':
        detail = r.get('detail', 'unspecified limit')
        status = 'wall-60s' if 'WallClock' in detail else 'limit: ' + detail.split(' were needed')[0].split(' needed')[0][:40]
    return status


unchecked = []
print('| Field | Row | Zeebra #738 s | Zeebra 1w s | Zeebra 16w s | 16w/1w | best comparand s (engine) | Z1w/best | Z16w/best |')
print('|---|---|---:|---:|---:|---:|---:|---:|---:|')
for key in old:
    field, name = key
    z0 = old[key].get('zeebra')
    z1, z16 = (new[w].get(key, {}).get('zeebra') for w in (1, 16))
    others = [old[key][e] for e in COMPARANDS if e in old[key] and wide.completed(old[key][e])]
    for z in (z1, z16):
        if z and wide.completed(z) and field != 'bn254':
            pool = [z] + others + ([z0] if z0 and wide.completed(z0) else [])
            if len(pool) < 2:
                unchecked.append(f'{field}/{name}')
            else:
                wide.verify_bases(pool)  # raises on any coefficient disagreement
    best = min(others, key=wide.seconds) if others else None
    def ratio(z):
        if not (z and best and wide.completed(z)):
            return '—'
        r = wide.wall_ratio(wide.seconds(z), wide.seconds(best), floor(old, field, 'zeebra'), floor(old, field, best['engine']))
        return '—' if r is None else f'{r:.2f}x'
    speed = (f'{wide.seconds(z1) / wide.seconds(z16):.2f}x'
             if z1 and z16 and wide.completed(z1) and wide.completed(z16) else '—')
    print(f"| {field} | {name} | {cell(z0)} | {cell(z1)} | {cell(z16)} | {speed} | "
          + (f"{wide.seconds(best):.3f} ({best['engine']})" if best else '—') + f" | {ratio(z1)} | {ratio(z16)} |")
print()
print('Every new 64-bit Zeebra completion agrees coefficient for coefficient with every other complete '
      'answer for its input. 64-bit completions with no other answer: ' + (', '.join(sorted(set(unchecked))) or 'none')
      + '. BN254 has no external oracle; its completions are unchecked.')
if '--check' in sys.argv and unchecked:
    sys.exit(1)
