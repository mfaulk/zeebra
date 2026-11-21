#!/usr/bin/env python3
"""Regenerate tables.md from this directory's retained records alone (#970, M33-G1).

    summarize.py [--check]      # --check: exit 1 if tables.md differs from what the records give

Inputs: records-*.jsonl.gz with their *.session.json (`campaign.py extract`) and work.json
(`campaign.py work`). Every interval is over ok attempts; the bench-job contamination verdict is
reported beside them and, as in #966, regrouped per arm (§1).
"""
import argparse
import gzip
import json
import statistics
import sys
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import bench_contamination as bc  # noqa: E402
import bench_stats as bs  # noqa: E402

ROWS = [('wide64', 'eco-12'), ('wide64', 'katsura-11'), ('goldilocks', 'mq-random-11')]
LABEL = {'wide64/eco-12': 'Eco-12 / 2⁶⁴−353', 'wide64/katsura-11': 'Katsura-11 / 2⁶⁴−353',
         'goldilocks/mq-random-11': 'MQ11 / Goldilocks'}
MS = 1e6
# Zeebra's four stage clocks and grobx's report clocks mapped onto them. grobx's encode/decode move
# rows between its monomial ids and matrix columns, so they are counted with symbolic/elimination.
STAGES = ('bookkeeping', 'symbolic', 'elimination', 'interreduction')
GROBX_ROUND = {'bookkeeping': ('select', 'update', 'record'), 'symbolic': ('symbolic', 'encode'),
               'elimination': ('reduce', 'backsub', 'decode')}


def load():
    recs, sessions = [], []
    for path in sorted(HERE.glob('records-*.jsonl.gz')):
        recs += [json.loads(line) for line in gzip.decompress(path.read_bytes()).decode().splitlines()]
        sessions.append(json.loads(Path(str(path).replace('.jsonl.gz', '.session.json')).read_text()))
    work = json.loads((HERE / 'work.json').read_text()) if (HERE / 'work.json').exists() else None
    return recs, sessions, work


def ok(recs, row, arm):
    return [r for r in recs if (r['field'], r['name']) == row and r['arm'] == arm and r['status'] == 'ok']


def med(xs):
    return statistics.median(xs) if xs else None


def ci(xs, seed):
    """The median of one arm's per-attempt values with its bootstrap interval (`independent_ratio` over 1)."""
    return bs.independent_ratio(xs, [1.0], seed=seed) if xs else None


def fmt(x, digits=1):
    return '—' if x is None else f'{x:,.{digits}f}'


def fci(c, digits=3):
    return '—' if c is None else f'{c.median:.{digits}f} [{c.lo:.{digits}f}, {c.hi:.{digits}f}]'


def zeebra_parts(r):
    """One Zeebra attempt's process wall split into the four stages and what lies outside them, in ms."""
    z, s = r['zeebra'], r['zeebra']['statistics']
    stages = {k: s[f'{k}_ns'] / MS for k in STAGES}
    return dict(stages, wall=r['wall_ns'] / MS, digest=z['basis_m33_ns'] / MS,
                in_call=(z['call_ns'] - sum(s[f'{k}_ns'] for k in STAGES)) / MS,
                harness=(r['wall_ns'] - z['call_ns'] - z['basis_m33_ns']) / MS)


def grobx_parts(r):
    """One grobx attempt's process wall on the same split, from its stock report."""
    g = r['grobx']
    parts = {k: sum(run[f'{c}_ns'] for run in g['runs'] for c in cs) / MS for k, cs in GROBX_ROUND.items()}
    parts['interreduction'] = sum(v for k, v in g['inter'].items() if k.endswith('_ns')) / MS
    parts.update(wall=r['wall_ns'] / MS, digest=g['text_ns'] / MS,
                 in_call=g['call_ns'] / MS - sum(parts[k] for k in STAGES) - g['text_ns'] / MS,
                 harness=(r['wall_ns'] - g['call_ns']) / MS)
    return parts


PARTS = ('wall', 'harness', 'digest', 'in_call') + STAGES
PART_LABEL = dict(wall='process wall', harness='exec, parse, exit', digest='digest / basis text',
                  in_call='in call, outside stages', bookkeeping='bookkeeping', symbolic='symbolic',
                  elimination='elimination', interreduction='interreduction')


def session_table(recs, sessions):
    out = ['## 1. Session and contamination', '',
           '| Job | Attempts | ok | Contaminated (bench-job, per cell) | Void | One session median | Per arm and cell | Reasons |',
           '|---|---:|---:|---:|---|---|---|---|']
    for s in sessions:
        job = s['job']['job_id']
        mine = [r for r in recs if r['job'] == job]
        judged = [r for r in mine if r.get('metrics')]
        c = (s['stop'] or {}).get('contamination') or {}
        alt = []
        for groups in (None, [f"{r['field']}/{r['name']}@{r['arm']}" for r in judged]):
            v = bc.session_verdict([r['metrics'] for r in judged], 'dev', groups)
            alt.append(f"{v['contaminated']}/{v['total']}{' void' if v['void'] else ''}")
        why = defaultdict(int)
        for r in mine:
            for x in r['reasons']:
                why[' '.join(x.split(' ')[:2])] += 1
        out.append(f"| `{job}` | {len(mine)} | {sum(r['status'] == 'ok' for r in mine)} | "
                   f"{c.get('contaminated')}/{c.get('total')} | {c.get('void')} | {alt[0]} | {alt[1]} | "
                   f"{', '.join(f'{k} {v}' for k, v in sorted(why.items())) or '—'} |")
    foreign = [r['metrics']['bench_foreign'] for r in recs if r.get('metrics')]
    out += ['', f'Thresholds unchanged. Largest foreign share on the bench CPU: {max(foreign):.1%}. '
            'Intervals below use every ok attempt, as #966 did, pending the owner\'s clock-rule decision on #965.', '']
    return out


def digests(recs):
    out = defaultdict(set)
    for r in recs:
        if r['status'] == 'ok':
            out[r['field'], r['name']].add(r.get('basis_m33'))
    return out


def stage_table(recs):
    out = ['## 2. Process wall by stage, Zeebra signature route vs grobx 0.155.1, 1 worker', '',
           'Medians in ms over ok attempts (`sig` and `grobx155` arms). grobx\'s clocks are its stock report\'s: '
           'bookkeeping = select + update + record, symbolic = symbolic + encode, elimination = reduce + backsub '
           '+ decode, interreduction = its final `inter` matrix; "digest / basis text" is Zeebra\'s `basis_m33` '
           'against grobx building its basis text. Ratio = Zeebra ÷ grobx, independent bootstrap; share = the '
           'part\'s difference over the wall difference.', '',
           '| Row | Part | Zeebra | grobx | Δ ms | share of gap | Zeebra ÷ grobx [95%] |',
           '|---|---|---:|---:|---:|---:|---:|']
    for row in ROWS:
        z = [zeebra_parts(r) for r in ok(recs, row, 'sig')]
        g = [grobx_parts(r) for r in ok(recs, row, 'grobx155')]
        if not z or not g:
            continue
        gap = med([p['wall'] for p in z]) - med([p['wall'] for p in g])
        for part in PARTS:
            zs, gs = [p[part] for p in z], [p[part] for p in g]
            d = med(zs) - med(gs)
            c = bs.independent_ratio(zs, gs, seed=f'{row}{part}') if min(gs) > 0 else None
            label = LABEL['/'.join(row)] if part == 'wall' else ''
            out.append(f'| {label} | {PART_LABEL[part]} | {fmt(med(zs))} | {fmt(med(gs))} | {fmt(d)} | '
                       f"{'—' if part == 'wall' else f'{d / gap:.0%}'} | {fci(c, 2)} |")
    return out + ['']


def first_stats(recs, row, arm):
    stats = [r['zeebra']['statistics'] for r in ok(recs, row, arm)]
    return stats[0] if stats else None


def work_table(recs, work):
    out = ['## 3. Work counters (deterministic; one attempt per row shown, all attempts agree)', '',
           '| Quantity | ' + ' | '.join(f'{LABEL["/".join(r)]} Zeebra sig | grobx' for r in ROWS) + ' |',
           '|---|' + '---:|---:|' * len(ROWS)]
    lines = defaultdict(list)
    for row in ROWS:
        s = first_stats(recs, row, 'split')
        g = ok(recs, row, 'grobx155')
        if not s or not g:
            continue
        g = g[0]['grobx']
        rounds = lambda k: sum(run[k] for run in g['runs'])  # noqa: E731
        sp = s['split']
        entries = sum(b['entries'] for b in sp['batches'])
        cells = [
            ('Route', 'signature, 1 run', ' → '.join(run['engine'] for run in g['runs'])),
            ('Batches / rounds', s['batches'], rounds('rounds')),
            ('Pairs created', s['pairs_created'], '—'),
            ('Rows reduced (targets / reductions)', s['targets'], rounds('reductions')),
            ('Reducer rows', s['reducer_rows'], '—'),
            ('Reductions to zero', s['reductions_to_zero'], rounds('zero')),
            ('Rows ruled zero by randomized tests', '—', rounds('zero_rows')),
            ('Elements added (pivots)', s['elements_added'], rounds('pivots')),
            ('Reduced basis', s['reduced_basis_elements'], g['inter']['elements']),
            ('Redundant elements (pivots − reduced basis)', sp['redundant_elements'],
             max(rounds('pivots') - g['inter']['elements'], 0)),
            ('Max matrix rows × columns', f"{s['max_matrix_rows']:,} × {s['max_matrix_columns']:,}",
             f"{max(run['max_rows'] for run in g['runs']):,} × {max(run['max_columns'] for run in g['runs']):,}"),
            ('Matrix entries, total (M)', fmt(entries / 1e6), fmt(rounds('entries') / 1e6)),
            ('Elimination products / charges (M)', fmt(s['coefficient_products'] / 1e6), fmt(rounds('subtracted') / 1e6)),
            ('… on rows reduced to zero (M)', fmt(s['products_on_zero_rows'] / 1e6), '—'),
            ('… on redundant elements (M)', fmt(sp['products_on_redundant_elements'] / 1e6), '—'),
            ('… on kept elements (M)', fmt(sp['products_on_kept_elements'] / 1e6), '—'),
            ('Interreduction matrix columns', s['interreduction_columns'], g['inter']['columns']),
            ('Interreduction nonzeros (M)', fmt(s['interreduction_nonzeros'] / 1e6, 2), fmt(g['inter']['entries'] / 1e6, 2)),
            ('Interreduction charges (M)', '—', fmt(g['inter']['subtracted'] / 1e6, 1)),
        ]
        for name, zv, gv in cells:
            lines[name] += [zv if isinstance(zv, str) else f'{zv:,}', gv if isinstance(gv, str) else f'{gv:,}']
    for name, vals in lines.items():
        out.append(f'| {name} | ' + ' | '.join(vals) + ' |')
    out += ['', "grobx's charges are its stock budget's `subtracted`, one per entry of each row operation; #713 found "
            'them within 2% of executed products at GF(2³¹−1). At these primes (p ≥ 2⁶³) its row update takes one '
            '`u128` remainder per product. Its reductions exclude rows its signature run ruled zero by randomized '
            'tests (`zero-rows`).', '']
    if work:
        out += ['Conventional F4 at one worker (`--engine f4 --discovery`, untimed, `work.json`):', '',
                '| Row | Forward products (M) | Backward (M) | Zero rows | Products on zero rows (M) | share |',
                '|---|---:|---:|---:|---:|---:|']
        for row in ROWS:
            w = (work['rows'].get('/'.join(row)) or {}).get('work')
            if w:
                total = w['forward_products'] + w['backward_products']
                out.append(f"| {LABEL['/'.join(row)]} | {fmt(w['forward_products'] / 1e6)} | "
                           f"{fmt(w['backward_products'] / 1e6)} | {w['zero_rows']:,} | "
                           f"{fmt(w['products_on_zero_rows'] / 1e6)} | {w['products_on_zero_rows'] / total:.1%} |")
        out.append('')
    return out


def cost_table(recs):
    out = ['## 4. Per-product cost (ns), 1 worker', '',
           'Zeebra: elimination clock ÷ coefficient products (`sig`). grobx: round reduce + backsub ÷ round '
           'charges; interreduction: its `inter` reduce ÷ `inter` charges. Median [95%] over attempts; the ratio '
           'is independent.', '',
           '| Row | Zeebra elimination | grobx rounds | Zeebra ÷ grobx | grobx interreduction | '
           'Zeebra products ÷ grobx charges |',
           '|---|---:|---:|---:|---:|---:|']
    for row in ROWS:
        z = [r['zeebra']['statistics']['elimination_ns'] / r['zeebra']['statistics']['coefficient_products']
             for r in ok(recs, row, 'sig')]
        gs = ok(recs, row, 'grobx155')
        g = [sum(run['reduce_ns'] + run['backsub_ns'] for run in r['grobx']['runs']) /
             sum(run['subtracted'] for run in r['grobx']['runs']) for r in gs]
        gi = [r['grobx']['inter']['reduce_ns'] / r['grobx']['inter']['subtracted'] for r in gs]
        if not z or not g:
            continue
        s = first_stats(recs, row, 'sig')
        work = s['coefficient_products'] / sum(run['subtracted'] for run in gs[0]['grobx']['runs'])
        out.append(f"| {LABEL['/'.join(row)]} | {fci(ci(z, f'{row}z'), 2)} | {fci(ci(g, f'{row}g'), 2)} | "
                   f"{fci(bs.independent_ratio(z, g, seed=f'{row}zg'), 2)} | {fci(ci(gi, f'{row}gi'), 2)} | {work:.2f} |")
    return out + ['']


def paired(recs, row, num, den, value):
    a = {r['rep']: value(r) for r in ok(recs, row, num)}
    b = {r['rep']: value(r) for r in ok(recs, row, den)}
    ratios = bs.paired_ratios(a, b)
    return bs.paired_ratio(ratios, seed=f'{row}{num}{den}') if ratios else None


def stage(name):
    return lambda r: r['zeebra']['statistics'][f'{name}_ns']


def hg2_table(recs):
    out = ['## 5. Fused vs unfused symbolic (HG2) and the components of the stage', '',
           '`split` ÷ `sig`, paired per repetition. The split build unfuses multiply from intern and clocks every '
           'reducer lookup, so its symbolic stage is the unfused design plus its own clocks.', '',
           '| Row | symbolic | elimination | interreduction | process wall |', '|---|---:|---:|---:|---:|']
    for row in ROWS:
        cells = [paired(recs, row, 'split', 'sig', stage(k)) for k in ('symbolic', 'elimination', 'interreduction')]
        cells.append(paired(recs, row, 'split', 'sig', lambda r: r['wall_ns']))
        out.append(f"| {LABEL['/'.join(row)]} | " + ' | '.join(fci(c) for c in cells) + ' |')
    out += ['', 'Symbolic components in the split build (medians, ms; per term in ns):', '',
            '| Row | total | reducer search | multiply | interning | column sort | terms (M) | interning ns/term | '
            'searches (k) |', '|---|---:|---:|---:|---:|---:|---:|---:|---:|']
    for row in ROWS:
        sy = [r['zeebra']['statistics']['split']['symbolic'] for r in ok(recs, row, 'split')]
        if not sy:
            continue
        m = {k: med([s[k] for s in sy]) for k in sy[0] if k.endswith('_ns')}
        terms = sy[0]['terms']
        out.append(f"| {LABEL['/'.join(row)]} | {fmt(m['total_ns'] / MS)} | {fmt(m['reducer_search_ns'] / MS)} | "
                   f"{fmt(m['multiply_ns'] / MS)} | {fmt(m['interning_ns'] / MS)} | {fmt(m['column_sort_ns'] / MS)} | "
                   f"{terms / 1e6:.2f} | {m['interning_ns'] / terms:.1f} | {sy[0]['searches'] / 1e3:,.0f} |")
    out += ['', 'Hardware counters, user mode, whole process (`hwcount.py`; medians over attempts). The two builds '
            'differ only in the symbolic stage\'s loop and the split build\'s clocks, so the difference is that '
            'stage\'s.', '',
            '| Row | arm | instructions (G) | cycles (G) | IPC | L1d reads (G) | L1d miss rate | DRAM fills (M) | '
            'cycles ÷ main (GHz) |',
            '|---|---|---:|---:|---:|---:|---:|---:|---:|']
    for row in ROWS:
        for arm in ('sig-hw', 'split-hw'):
            hw = [r['hwcount'] for r in ok(recs, row, arm) if r.get('hwcount')]
            if not hw:
                continue
            c = {k: med([h['counts'][k] for h in hw]) for k in hw[0]['counts']}
            ghz = med([r['hwcount']['counts']['cycles'] / r['zeebra']['main_ns'] for r in ok(recs, row, arm)])
            out.append(f"| {LABEL['/'.join(row)] if arm == 'sig-hw' else ''} | {arm} | {c['instructions'] / 1e9:.2f} | "
                       f"{c['cycles'] / 1e9:.2f} | {c['instructions'] / c['cycles']:.2f} | {c['l1d_reads'] / 1e9:.2f} | "
                       f"{c['l1d_read_misses'] / c['l1d_reads']:.2%} | {c['fills_dram'] / 1e6:.1f} | {ghz:.2f} |")
        sig = {r['rep']: r['hwcount']['counts'] for r in ok(recs, row, 'sig-hw') if r.get('hwcount')}
        spl = {r['rep']: r['hwcount']['counts'] for r in ok(recs, row, 'split-hw') if r.get('hwcount')}
        reps = sorted(set(sig) & set(spl))
        if reps:
            d = {k: med([spl[i][k] - sig[i][k] for i in reps]) for k in sig[reps[0]]}
            out.append(f"| | split − sig, paired | {d['instructions'] / 1e9:+.2f} | {d['cycles'] / 1e9:+.2f} | — | "
                       f"{d['l1d_reads'] / 1e9:+.2f} | {d['l1d_read_misses'] / 1e6:+.1f} M misses | "
                       f"{d['fills_dram'] / 1e6:+.1f} | — |")
    return out + ['']


def outside_table(recs):
    out = ['## 6. Outside the four stages (HG3) and inside interreduction', '',
           'Medians, ms. Exec/parse/exit and digest from `sig`; the split build names materialization (signature '
           'basis to polynomials), the engine drop and input normalization, and times the minimal selection on a copy.',
           '', '| Row | process wall | outside four stages | share | exec, parse, exit | digest | in call | '
           'of which materialize | drop | inputs | interreduction | of which minimal selection |',
           '|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|']
    for row in ROWS:
        z = [zeebra_parts(r) for r in ok(recs, row, 'sig')]
        sp = [r['zeebra']['statistics'] for r in ok(recs, row, 'split')]
        if not z or not sp:
            continue
        wall = med([p['wall'] for p in z])
        outside = med([p['harness'] + p['digest'] + p['in_call'] for p in z])
        m = lambda k: med([s['split'][k] / MS for s in sp])  # noqa: E731
        out.append(f"| {LABEL['/'.join(row)]} | {fmt(wall)} | {fmt(outside)} | {outside / wall:.1%} | "
                   f"{fmt(med([p['harness'] for p in z]))} | {fmt(med([p['digest'] for p in z]))} | "
                   f"{fmt(med([p['in_call'] for p in z]))} | {fmt(m('materialize_ns'))} | {fmt(m('drop_ns'))} | "
                   f"{fmt(m('inputs_ns'))} | {fmt(med([s['interreduction_ns'] / MS for s in sp]))} | "
                   f"{fmt(m('minimal_selection_ns'))} |")
    return out + ['']


def workers_table(recs):
    out = ['## 7. Design 2 at one CPU (#894\'s question on this route)', '',
           '`sig-w4` ÷ `sig`, paired: the timed build asked for four workers on the one CPU, so every target is first '
           'reduced against the reducer block in a pass of its own, then finished in signature order.', '',
           '| Row | elimination | process wall |', '|---|---:|---:|']
    for row in ROWS:
        out.append(f"| {LABEL['/'.join(row)]} | {fci(paired(recs, row, 'sig-w4', 'sig', stage('elimination')))} | "
                   f"{fci(paired(recs, row, 'sig-w4', 'sig', lambda r: r['wall_ns']))} |")
    return out + ['']


def correctness(recs):
    out = ['## 8. Correctness', '', '| Row | ok attempts | distinct `m33-basis-v1` digests |', '|---|---:|---:|']
    d = digests(recs)
    for row in ROWS:
        n = sum(1 for r in recs if (r['field'], r['name']) == row and r['status'] == 'ok')
        out.append(f"| {LABEL['/'.join(row)]} | {n} | {len(d[row])} |")
    return out + ['']


def render():
    recs, sessions, work = load()
    lines = ['# M33-G1 generated tables (#970)', '',
             'Generated by `summarize.py` from the retained records; do not edit by hand.', '']
    for part in (session_table(recs, sessions), stage_table(recs), work_table(recs, work), cost_table(recs),
                 hg2_table(recs), outside_table(recs), workers_table(recs), correctness(recs)):
        lines += part
    return '\n'.join(lines).rstrip() + '\n'


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--check', action='store_true')
    args = p.parse_args()
    text = render()
    path = HERE / 'tables.md'
    if args.check:
        if not path.exists() or path.read_text() != text:
            print('tables.md is stale; run summarize.py', file=sys.stderr)
            return 1
        return 0
    path.write_text(text)
    return 0


if __name__ == '__main__':
    sys.exit(main())
