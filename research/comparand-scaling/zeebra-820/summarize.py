#!/usr/bin/env python3
"""#820: Zeebra's fresh-process cohort against the retained #739 comparand cohort, one boundary.

    python3 research/comparand-scaling/zeebra-820/summarize.py ZEEBRA.json.gz [COMPARANDS.json.gz]

Process wall (fresh process, input/output included) medians per field/input, engine and worker
count. A Zeebra completion without an exact reference is also compared, coefficient for
coefficient, with every complete comparand answer for the same input; that is agreement between
engines, not independent verification, and it is reported separately.
"""
import importlib.util
import statistics
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('scaling', ROOT / 'tools/external/comparand-scaling.py')
scaling = importlib.util.module_from_spec(spec)
spec.loader.exec_module(scaling)

ours = scaling.load_cohort(Path(sys.argv[1]))
theirs = scaling.load_cohort(Path(sys.argv[2] if len(sys.argv) > 2 else ROOT / 'research/comparand-scaling/native-resume-v1.json.gz'))
cases = {c['digest']: scaling.canonical_case(c) for c in ours['cases'] + theirs['cases']}
DONE = ('verified', 'complete')


def groups(cohort):
    out = {}
    for a in cohort['attempts']:
        if a['status'] in DONE and not a.get('diagnostic') and a.get('process_wall_ns'):
            out.setdefault((a['digest'], a['engine'], a['workers']), []).append(a)
    return out


z, c = groups(ours), groups(theirs)
agree = disagree = unchecked = 0
for (digest, engine, p), rows in z.items():
    for a in rows:
        if a['status'] == 'verified':
            continue
        others = [b for (d, _, _), bs in c.items() if d == digest for b in bs if b.get('basis')]
        if not others:
            unchecked += 1
            continue
        try:
            scaling.verify_basis(a['basis'], others[0]['basis'], cases[digest])
            agree += 1
        except ValueError:
            disagree += 1

med = lambda rows: statistics.median(a['process_wall_ns'] for a in rows) / 1e9
print('| Field/input | p | Zeebra s (n, status) | best comparand at p s (engine) | Zeebra / best | best comparand at ≤p s (engine, p) | Zeebra / best ≤p |')
print('|---|---:|---:|---:|---:|---:|---:|')
digests = sorted({d for d, _, _ in z}, key=lambda d: (str(cases[d]['field']), cases[d]['name']))
for d in digests:
    label = f"{cases[d]['field']}/{cases[d]['name']}"
    for p in sorted({p for dd, _, p in z if dd == d}):
        rows = z[(d, 'zeebra', p)]
        status = 'verified' if all(a['status'] == 'verified' for a in rows) else 'complete'
        mine = med(rows)
        same = [(med(v), e) for (dd, e, pp), v in c.items() if dd == d and pp == p]
        upto = [(med(v), e, pp) for (dd, e, pp), v in c.items() if dd == d and pp <= p]
        best = min(same) if same else None
        best_upto = min(upto) if upto else None
        print(f"| {label} | {p} | {mine:.4f} ({len(rows)}, {status}) | "
              + (f"{best[0]:.4f} ({best[1]}) | {mine / best[0]:.2f}x" if best else '— | —') + ' | '
              + (f"{best_upto[0]:.4f} ({best_upto[1]}, {best_upto[2]}) | {mine / best_upto[0]:.2f}x" if best_upto else '— | —') + ' |')
print()
print(f'Unreferenced Zeebra completions: {agree} agree with a complete comparand answer coefficient for '
      f'coefficient, {disagree} disagree, {unchecked} have no comparand answer to compare.')
