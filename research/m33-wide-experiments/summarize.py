#!/usr/bin/env python3
"""Regenerate tables.md from this directory's retained records alone (#971, M33-G2).

    summarize.py [--check]      # --check: exit 1 if tables.md differs from what the records give

Inputs: records-*.jsonl.gz with their *.session.json (`campaign.py extract`). Every interval is
over ok attempts, paired per repetition for head ÷ base; the bench-job contamination verdict is
reported beside them and regrouped per arm, as #966 and #970 did.
"""
import argparse
import gzip
import importlib.util
import json
import sys
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import bench_stats as bs  # noqa: E402

_spec = importlib.util.spec_from_file_location('m33_g1_summarize', ROOT / 'research/m33-grobx-attribution/summarize.py')
g1 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(g1)

LABEL = {'wide64/eco-12': 'Eco-12 / 2⁶⁴−353', 'wide64/katsura-11': 'Katsura-11 / 2⁶⁴−353',
         'goldilocks/mq-random-11': 'MQ11 / Goldilocks', 'wide64/noon-8': 'Noon-8 / 2⁶⁴−353',
         'wide64/noon-7': 'Noon-7 / 2⁶⁴−353', 'wide64/cyclic-7': 'Cyclic-7 / 2⁶⁴−353',
         'wide64/katsura-9': 'Katsura-9 / 2⁶⁴−353', 'goldilocks/katsura-11': 'Katsura-11 / Goldilocks'}
ORDER = list(LABEL)
MS = 1e6
STAGES = ('bookkeeping', 'symbolic', 'elimination', 'interreduction')
QUANTITIES = ('wall', 'call') + STAGES + ('rss',)
# Gate A record and plan §13, posted on #971 before measuring.
GATE_B = dict(eco_wall_hi=0.95, eco_symbolic=0.45, katsura_wall_hi=1.00, stage_drift=0.03, rss=1.25,
              eco_half_width=0.025)


def load():
    recs, sessions = [], []
    for path in sorted(HERE.glob('records-*.jsonl.gz')):
        recs += [json.loads(line) for line in gzip.decompress(path.read_bytes()).decode().splitlines()]
        sessions.append(json.loads(Path(str(path).replace('.jsonl.gz', '.session.json')).read_text()))
    return recs, sessions


def value(r, q):
    if q == 'wall':
        return r['wall_ns'] / MS
    if q == 'rss':
        return r['peak_rss_bytes'] / 2**20
    if q == 'call':
        return r['zeebra']['call_ns'] / MS
    return r['zeebra']['statistics'][f'{q}_ns'] / MS


def cells(recs):
    """(job, row, workers) -> arm -> rep -> record, ok attempts only."""
    out = defaultdict(lambda: defaultdict(dict))
    for r in recs:
        if r['status'] == 'ok':
            out[r['job'], f"{r['field']}/{r['name']}", r.get('workers', 1)][r['arm']][r['rep']] = r
    return out


def paired(arms, q, seed):
    a = {k: value(r, q) for k, r in arms['head'].items()}
    b = {k: value(r, q) for k, r in arms['base'].items()}
    ratios = bs.paired_ratios(a, b)
    return bs.paired_ratio(ratios, seed=seed) if ratios else None


def ab_table(recs):
    out = ['## 2. Paired head ÷ base', '',
           'Per row and worker count: each arm\'s median (ms; RSS in MiB) and the paired per-repetition ratio '
           'head ÷ base with its 95% percentile bootstrap (20,000 draws). `call` is the in-process solve; the four '
           'stages are the engine\'s own clocks.', '',
           '| Job | Row | w | Quantity | base | head | head ÷ base [95%] | n |',
           '|---|---|---:|---|---:|---:|---:|---:|']
    for (job, row, w), arms in sorted(cells(recs).items(), key=lambda kv: (kv[0][0], ORDER.index(kv[0][1]), kv[0][2])):
        if 'head' not in arms or 'base' not in arms:
            continue
        for q in QUANTITIES:
            c = paired(arms, q, f'{job}{row}{w}{q}')
            mb = g1.med([value(r, q) for r in arms['base'].values()])
            mh = g1.med([value(r, q) for r in arms['head'].values()])
            first = q == 'wall'
            out.append(f"| {f'`{job}`' if first else ''} | {LABEL[row] if first else ''} | {w if first else ''} | {q} | "
                       f"{g1.fmt(mb)} | {g1.fmt(mh)} | {g1.fci(c)} | {c.n if c else 0} |")
    return out + ['']


def gate_b(recs):
    """Gate B's criteria over the 1-w cells of every job holding them, pooled per row."""
    pooled = defaultdict(lambda: defaultdict(dict))
    for (job, row, w), arms in cells(recs).items():
        if w != 1:
            continue
        for arm, reps in arms.items():
            for rep, r in reps.items():
                pooled[row][arm][(job, rep)] = r
    out = ['## 3. Gate B verdicts (thresholds posted on #971 before measuring)', '',
           '| Criterion | Threshold | Measured | Verdict |', '|---|---|---|---|']

    def line(name, threshold, c, ok):
        out.append(f"| {name} | {threshold} | {g1.fci(c) if hasattr(c, 'median') else c} | {'pass' if ok else '**FAIL**'} |")

    eco, kat = pooled.get('wide64/eco-12'), pooled.get('wide64/katsura-11')
    if eco and 'head' in eco:
        w = paired(eco, 'wall', 'gateB-eco-wall')
        line('Eco-12 paired wall, upper bound', f"≤ {GATE_B['eco_wall_hi']}", w, w.hi <= GATE_B['eco_wall_hi'])
        hw = (w.hi - w.lo) / 2
        line('Eco-12 wall interval half-width (precision rule)', f"≤ {GATE_B['eco_half_width']}", f'{hw:.4f}',
             hw <= GATE_B['eco_half_width'])
        s = paired(eco, 'symbolic', 'gateB-eco-symbolic')
        line('Eco-12 paired symbolic ratio (Gate A falsifier)', f"≤ {GATE_B['eco_symbolic']}", s,
             s.median <= GATE_B['eco_symbolic'])
        for q in ('elimination', 'interreduction'):
            c = paired(eco, q, f'gateB-eco-{q}')
            line(f'Eco-12 {q} moves ≤ 3%', f"|median − 1| ≤ {GATE_B['stage_drift']}", c,
                 abs(c.median - 1) <= GATE_B['stage_drift'])
    if kat and 'head' in kat:
        k = paired(kat, 'wall', 'gateB-kat-wall')
        line('Katsura-11 paired wall, upper bound (Gate A falsifier)', f"≤ {GATE_B['katsura_wall_hi']}", k,
             k.hi <= GATE_B['katsura_wall_hi'])
        for q in ('elimination', 'interreduction'):
            c = paired(kat, q, f'gateB-kat-{q}')
            line(f'Katsura-11 {q} moves ≤ 3%', f"|median − 1| ≤ {GATE_B['stage_drift']}", c,
                 abs(c.median - 1) <= GATE_B['stage_drift'])
    for row in ORDER:
        if row in pooled and 'head' in pooled[row]:
            c = paired(pooled[row], 'rss', f'gateB-{row}-rss')
            line(f'{LABEL[row]} peak RSS', f"≤ {GATE_B['rss']}×", c, c.median <= GATE_B['rss'])
    d = g1.digests(recs)
    same = all(len(v) == 1 for v in d.values())
    out.append(f"| `m33-basis-v1` digests, every ok attempt and arm | one per row | "
               f"{', '.join(f'{len(v)}' for v in d.values())} distinct | {'pass' if same else '**FAIL**'} |")
    return out + ['']


def grobx_table(recs):
    out = ['## 4. Exploratory: Zeebra ÷ grobx 0.155.1 at 1 w (dev mode, same session)', '',
           'Process wall, independent bootstrap. Dev-mode figures are never a competitive result (plan §11.2); '
           'confirmation is #975\'s.', '',
           '| Job | Row | base ms | head ms | grobx ms | base ÷ grobx [95%] | head ÷ grobx [95%] |',
           '|---|---|---:|---:|---:|---:|---:|']
    for (job, row, w), arms in sorted(cells(recs).items(), key=lambda kv: (kv[0][0], ORDER.index(kv[0][1]), kv[0][2])):
        if w != 1 or 'grobx155' not in arms:
            continue
        walls = {a: [value(r, 'wall') for r in arms[a].values()] for a in ('base', 'head', 'grobx155')}
        cb = bs.independent_ratio(walls['base'], walls['grobx155'], seed=f'{job}{row}base-grobx')
        ch = bs.independent_ratio(walls['head'], walls['grobx155'], seed=f'{job}{row}head-grobx')
        out.append(f"| `{job}` | {LABEL[row]} | {g1.fmt(g1.med(walls['base']))} | {g1.fmt(g1.med(walls['head']))} | "
                   f"{g1.fmt(g1.med(walls['grobx155']))} | {g1.fci(cb)} | {g1.fci(ch)} |")
    return out + ['']


def render():
    recs, sessions = load()
    lines = ['# #971 M33-G2 tables', '', 'Generated by `summarize.py` from the records in this directory; do not edit.', '']
    lines += g1.session_table(recs, sessions)
    lines += ab_table(recs) + gate_b(recs) + grobx_table(recs)
    return '\n'.join(lines).rstrip() + '\n'


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--check', action='store_true')
    args = p.parse_args()
    text, path = render(), HERE / 'tables.md'
    if args.check:
        if not path.exists() or path.read_text() != text:
            print('tables.md is stale: run research/m33-wide-experiments/summarize.py', file=sys.stderr)
            sys.exit(1)
        return
    path.write_text(text)
    print(path)


if __name__ == '__main__':
    main()
