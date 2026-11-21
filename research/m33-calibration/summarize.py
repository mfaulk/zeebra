#!/usr/bin/env python3
"""Calibration table from bench-job journals (#968): per condition and cell, the A/A and 5%-arm
paired ratios with bootstrap 95% intervals of the median, absolute drift against idle, and the
§11.2 contamination rate.

    research/m33-calibration/summarize.py <condition>=<job-dir> ...   > table.md
"""
import collections
import importlib.util
import random
import statistics
import sys
from pathlib import Path

TOOLS = Path(__file__).resolve().parents[2] / 'tools'


def _module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


aj = _module('attempt_journal', TOOLS / 'external' / 'attempt_journal.py')
bc = _module('bench_contamination', TOOLS / 'bench_contamination.py')


def median_ci(xs, reps=10000, seed=968):
    """Median and a percentile-bootstrap 95% interval of the median."""
    rng = random.Random(seed)
    boot = sorted(statistics.median(rng.choices(xs, k=len(xs))) for _ in range(reps))
    return statistics.median(xs), boot[int(0.025 * reps)], boot[int(0.975 * reps) - 1]


def load(job_dir):
    """{(instance, workers): {rep: {arm: wall_s}}} and the attempts' contamination records."""
    walls = collections.defaultdict(lambda: collections.defaultdict(dict))
    records = []
    for a in aj.load(Path(job_dir) / 'journal')['attempts']:
        if a['status'] != 'ok':
            continue
        c, md = a['cell'], a['metadata']
        walls[(c['instance'], c['workers'])][c['rep']][c['arm']] = md['wall_seconds']
        records.append((c, md.get('contamination') or {}))
    return walls, records


def _rule(reason):
    for key in ('sibling', 'bench foreign', 'bench clock', 'rest load', 'compiler', 'Runner', 'benchlock'):
        if key in reason:
            return key
    return reason


def contamination_rate(records, mode='dev'):
    """The session verdict with the clock rule per cell, flags per cell, and counts per rule."""
    judged = [(c, r['metrics']) for c, r in records if r.get('metrics')]
    s = bc.session_verdict([m for _, m in judged], mode, [f"{c['instance']}@{c['workers']}" for c, _ in judged])
    by_cell, reasons = collections.Counter(), collections.Counter()
    for (c, _), v in zip(judged, s['attempts']):
        if v['contaminated']:
            by_cell[(c['instance'], c['workers'])] += 1
            reasons.update({_rule(r) for r in v['reasons']})
    return s, by_cell, reasons, [m for _, m in judged]


def quantile(xs, q):
    xs = sorted(x for x in xs if x is not None)
    return xs[min(len(xs) - 1, int(q * len(xs)))] if xs else float('nan')


def export(conds, out):
    """One JSON line per attempt: what the table is computed from, without the journals' blobs."""
    import json
    with open(out, 'w') as f:
        for name, d in conds:
            for a in aj.load(Path(d) / 'journal')['attempts']:
                md, c = a['metadata'], (a['metadata'].get('contamination') or {})
                m = c.get('metrics') or {}
                f.write(json.dumps(dict(
                    condition=name, job=Path(d).name, attempt=md['attempt_id'], cell=a['cell'],
                    status=a['status'], wall_seconds=md['wall_seconds'], cpu_seconds=md['cpu_seconds'],
                    harness_cpu_seconds=md.get('harness_cpu_seconds'), metrics=m), sort_keys=True) + '\n')


def main(argv):
    if argv and argv[0].startswith('--jsonl='):
        out, argv = argv[0].split('=', 1)[1], argv[1:]
        export([arg.split('=', 1) for arg in argv], out)
    conds = [arg.split('=', 1) for arg in argv]
    data = {name: load(d) for name, d in conds}
    base = data[conds[0][0]][0]
    print('| condition | cell | n | A median s | abs drift vs idle | A/A median [95% CI] | within ±2.5% '
          '| 5% arm median [95% CI] | detected | contaminated (dev) |')
    print('|---|---|---:|---:|---:|---|---|---|---|---:|')
    notes = []
    for name, _ in conds:
        walls, records = data[name]
        s, by_cell, reasons, ms = contamination_rate(records)
        for cell in sorted(walls):
            reps = walls[cell]
            a = [r['a'] for r in reps.values() if 'a' in r]
            aa = [r['a2'] / r['a'] for r in reps.values() if {'a', 'a2'} <= r.keys()]
            ab = [r['s5'] / r['a'] for r in reps.values() if {'a', 's5'} <= r.keys()]
            m_a = statistics.median(a)
            drift = m_a / statistics.median(r['a'] for r in base[cell].values() if 'a' in r)
            aa_m, aa_lo, aa_hi = median_ci(aa)
            ab_m, ab_lo, ab_hi = median_ci(ab)
            within = 'yes' if 0.975 <= aa_lo and aa_hi <= 1.025 else 'no'
            print(f'| {name} | {cell[0]} {cell[1]}w | {len(aa)} | {m_a:.3f} | {drift:.3f}x '
                  f'| {aa_m:.3f} [{aa_lo:.3f}, {aa_hi:.3f}] | {within} '
                  f'| {ab_m:.3f} [{ab_lo:.3f}, {ab_hi:.3f}] | {"yes" if ab_lo > 1.0 else "no"} '
                  f'| {by_cell[cell]}/{3 * len(reps)} |')
        notes.append(f'- {name}: {s["contaminated"]}/{s["total"]} attempts contaminated '
                     f'({100 * s["contaminated"] / max(1, s["total"]):.0f}%), session void: '
                     f'{"yes" if s["void"] else "no"}; reasons: '
                     + (', '.join(f'{k} x{v}' for k, v in reasons.most_common()) or 'none'))
        notes.append(f'  - observed: max sibling busy {100 * max((max(m["sibling_busy"].values(), default=0) for m in ms), default=0):.2f}%, '
                     f'p90 bench foreign {100 * quantile([m["bench_foreign"] for m in ms], 0.9):.2f}%, '
                     f'median rest load {quantile([m["rest_load"] for m in ms], 0.5):.1f}, '
                     f'max compilers {max(m["compilers"] for m in ms)}')
    print()
    print('\n'.join(notes))


if __name__ == '__main__':
    main(sys.argv[1:])
