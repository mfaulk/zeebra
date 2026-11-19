#!/usr/bin/env python3
"""#939 tables from the committed records: the baseline cohort, the M31 ratio check, stage clocks,
the symbolic-stage split and frequency, the attribution outside the stages, the re-derived plan
§6.3 ceilings, #934's small-control method and #935's groebner-rs sweep.

    python3 research/m32-baseline/summarize.py research/m32-baseline > research/m32-baseline/tables.md
    python3 research/m32-baseline/summarize.py --extract-rs OUT research/m32-baseline   # writes rs.jsonl.gz
"""
import gzip
import hashlib
import importlib.util
import json
import statistics
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def _module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


M1 = _module('m31final_summary', ROOT / 'research/m31-final/summarize.py')
M0 = M1.M0
fmt, ms, interval = M1.fmt, M1.ms, M1.interval
STAGES = M1.STAGES
SUBSTANTIAL_S = 0.050          # plan §10.3: rows under 50 ms are #934's
REPRODUCE = 0.03               # #939 acceptance: within 3% of M31 §15.2
# Quoted, not measured here: grobx raw on Eco-12 in M31's and M30's final sessions (plan §6.3).
GROBX_ECO12_MS = {'M31 session': 1746.5, 'M30 session': 1613.7}
COMPONENTS = ('reducer_search', 'multiply', 'interning', 'column_sort')


def med(values):
    return statistics.median(values) if values else None


def cohort(directory, name):
    return M1.Final(M1.load(directory, name))


def reports(c, row, arm):
    return list(c.reports[(row, arm)].values())


def stat(c, row, arm, key):
    return med([r['statistics'][key] / 1e9 for r in reports(c, row, arm)])


def walls(c, out):
    M1.walls_table(c, out)


def headline(c, m31, out):
    out.append('## Entry point against shipping F4, and the M31 reference beside the baseline (paired, median [95%])\n')
    out.append('`en` is `grobner::f4_signature` with its dispatch, `f4` shipping F4, both from the baseline '
               '`7b25a1ee`; `r` arms are the M31 reference `8715c8ed` (identical code).\n')
    out.append('| row | route | en ÷ f4, 1w | 4w | 8w | 16w | en:16 base ÷ ref | f4:16 base ÷ ref |')
    out.append('|---|---|---:|---:|---:|---:|---:|---:|')
    for row in c.rows:
        routes = sorted({r['statistics']['route'] for r in reports(c, row, 'en:16')})
        cells = ' | '.join(fmt(c.ratio(row, f'en:{w}', f'f4:{w}')) for w in (1, 4, 8, 16))
        out.append(f"| {row} | {', '.join(routes)} | {cells} | {fmt(c.ratio(row, 'en:16', 'ren:16'))} | "
                   f"{fmt(c.ratio(row, 'f4:16', 'rf4:16'))} |")
    out.append('')
    out.append('### M31 §15.2 reproduced? (en:16 ÷ f4:16, paired medians; M31 from `research/m31-final/walls.jsonl.gz`)\n')
    out.append(f'Substantial rows: both arms at or above {SUBSTANTIAL_S * 1e3:.0f} ms process wall (plan §10.3). '
               f'Criterion: the M32 median within {REPRODUCE:.0%} of M31\'s.\n')
    out.append('| row | M31 | M32 baseline | M32 ÷ M31 | substantial | within 3% |')
    out.append('|---|---:|---:|---:|---|---|')
    for row in c.rows:
        old, new = m31.ratio(row, 'en:16', 'f4:16'), c.ratio(row, 'en:16', 'f4:16')
        if old is None or new is None:
            continue
        walls_s = [med(list(c.wall[(row, a)].values())) for a in ('en:16', 'f4:16')]
        substantial = min(walls_s) >= SUBSTANTIAL_S
        drift = new[0] / old[0]
        ok = abs(drift - 1) <= REPRODUCE
        out.append(f"| {row} | {old[0]:.3f} | {new[0]:.3f} | {drift:.3f} | {'yes' if substantial else 'no'} | "
                   f"{('yes' if ok else '**no**') if substantial else '(not gated)'} |")
    out.append('')


def stages(c, out):
    out.append('## Stage clocks of the signature route (medians, ms; timed baseline build)\n')
    out.append('| row | arm | wall | in-process call | symbolic | elimination | bookkeeping | interreduction | '
               'four stages | engine total |')
    out.append('|---|---|---:|---:|---:|---:|---:|---:|---:|---:|')
    for row in c.rows:
        for arm in ('d1:1', 'cl:4', 'cl:8', 'cl:16'):
            rs = reports(c, row, arm)
            if not rs:
                continue
            wall = med(list(c.wall[(row, arm)].values()))
            st = [stat(c, row, arm, f'{n}_ns') for n in STAGES]
            four = med([sum(r['statistics'][f'{n}_ns'] for n in STAGES) / 1e9 for r in rs])
            out.append(f"| {row} | {arm} | {wall * 1e3:,.0f} | {med([r['call_ns'] / 1e9 for r in rs]) * 1e3:,.0f} | "
                       + ' | '.join(f'{v * 1e3:,.0f}' for v in st)
                       + f" | {four * 1e3:,.0f} | {stat(c, row, arm, 'total_ns') * 1e3:,.0f} |")
    out.append('')


def attribution(c, split, out):
    out.append('## Where the process wall goes outside the four stages (medians, ms)\n')
    out.append('Per child: exec + exit = process wall − `main_ns`; harness = `main_ns` − call − render '
               '(argument parsing, input parse, report); engine glue = call − engine total; untimed in '
               'engine = engine total − four stages. The split build names the untimed part: input '
               'normalization, basis materialization and the engine drop.\n')
    out.append('| row | arm | wall | four stages | untimed in engine | engine glue | render | harness | exec + exit |')
    out.append('|---|---|---:|---:|---:|---:|---:|---:|---:|')
    for row in ('wide64/eco-12', 'goldilocks/katsura-11', 'goldilocks/mq-random-11', 'gf32003/mq-random-10',
                'm31/mq-random-10'):
        for arm in ('d1:1', 'cl:16'):
            parts = []
            for rep, r in c.reports[(row, arm)].items():
                s = r['statistics']
                four = sum(s[f'{n}_ns'] for n in STAGES)
                wall = c.wall[(row, arm)][rep] * 1e9
                parts.append((wall, four, s['total_ns'] - four, r['call_ns'] - s['total_ns'], r['render_ns'],
                              r['main_ns'] - r['call_ns'] - r['render_ns'], wall - r['main_ns']))
            if parts:
                cols = [med([p[i] for p in parts]) / 1e6 for i in range(7)]
                out.append(f'| {row} | {arm} | ' + ' | '.join(f'{v:,.1f}' for v in cols) + ' |')
    out.append('')
    if split is None:
        return
    out.append('Split build, same rows (medians, ms): the engine\'s untimed part by name.\n')
    out.append('| row | arm | input normalization | materialize | drop |')
    out.append('|---|---|---:|---:|---:|')
    for row in split.rows:
        for arm in ('sd1:1', 'scl:16'):
            rs = reports(split, row, arm)
            if rs:
                cols = [med([r['statistics']['split'][k] / 1e6 for r in rs]) for k in ('inputs_ns', 'materialize_ns',
                                                                                     'drop_ns')]
                out.append(f'| {row} | {arm} | ' + ' | '.join(f'{v:,.1f}' for v in cols) + ' |')
    out.append('')


def symbolic_split(split, c, out):
    out.append('## Symbolic stage by component (split build, medians over repetitions)\n')
    out.append('The split build clocks every reducer lookup and unfuses multiplication from interning (products '
               'into a scratch buffer, then interned). That changes the stage itself: its symbolic total differs '
               'from the timed build\'s (last column; the A/B below), so shares are of the split build\'s own '
               'total. "Other" is the remainder: building reducer rows (lead division, signature multiply) and '
               'the row vectors. Frequency: the symbolic thread\'s CPU, `scaling_cur_freq` before and after each '
               'batch, time-weighted; the CPU set\'s sampled mean over the whole child is beside it.\n')
    out.append('| row | workers | symbolic ms | reducer search | multiply | interning | column sort | other | '
               'searches | terms | symbolic-thread MHz | CPU-set mean MHz | timed build symbolic ms |')
    out.append('|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|')
    for row in split.rows:
        for arm, timed in (('sd1:1', 'd1:1'), ('scl:4', 'cl:4'), ('scl:8', 'cl:8'), ('scl:16', 'cl:16')):
            rs = reports(split, row, arm)
            if not rs:
                continue
            sy = [r['statistics']['split']['symbolic'] for r in rs]
            total = med([x['total_ns'] for x in sy])
            shares = [med([x[f'{k}_ns'] / x['total_ns'] for x in sy]) for k in COMPONENTS]
            other = med([1 - sum(x[f'{k}_ns'] for k in COMPONENTS) / x['total_ns'] for x in sy])
            khz = med([x['khz_weighted'] for x in sy if x.get('khz_weighted')])
            sampled = med([r2['freq']['mean_khz'] for r2 in split_records(split, row, arm) if r2.get('freq')])
            t = stat(c, row, timed, 'symbolic_ns') if c is not None and reports(c, row, timed) else None
            out.append(f"| {row} | {arm.split(':')[1]} | {total / 1e6:,.0f} | "
                       + ' | '.join(f'{v:.1%}' for v in shares)
                       + f" | {other:.1%} | {med([x['searches'] for x in sy]):,.0f} | {med([x['terms'] for x in sy]):,.0f} | "
                       f"{'—' if khz is None else f'{khz / 1e3:,.0f}'} | {'—' if sampled is None else f'{sampled / 1e3:,.0f}'} | "
                       f"{'—' if t is None else f'{t * 1e3:,.0f}'} |")
    out.append('')


def ab(c, out):
    out.append('## Split build against the instrument build (same source, feature off; paired, median [95%])\n')
    out.append('`d1`/`cl` run the instrument build, `sd1`/`scl` the split build, interleaved in one session.\n')
    out.append('| row | workers | symbolic ms, instrument | symbolic ms, split | split ÷ instrument, symbolic | '
               'split ÷ instrument, process wall |')
    out.append('|---|---:|---:|---:|---:|---:|')
    for row in c.rows:
        for plain, split in (('d1:1', 'sd1:1'), ('cl:16', 'scl:16')):
            if reports(c, row, plain) and reports(c, row, split):
                symbolic = c.ratio(row, split, plain, lambda r: r['statistics']['symbolic_ns'])
                out.append(f"| {row} | {plain.split(':')[1]} | {stat(c, row, plain, 'symbolic_ns') * 1e3:,.0f} | "
                           f"{stat(c, row, split, 'symbolic_ns') * 1e3:,.0f} | {fmt(symbolic)} | "
                           f"{fmt(c.ratio(row, split, plain))} |")
    out.append('')


def split_records(split, row, arm):
    return split.raw.get((row, arm), [])


def ceilings(c, out):
    eco = 'wide64/eco-12'
    sig = med(list(c.wall[(eco, 'en:16')].values())) * 1e3
    f4 = med(list(c.wall[(eco, 'f4:16')].values())) * 1e3
    sym16, sym1 = stat(c, eco, 'cl:16', 'symbolic_ns') * 1e3, stat(c, eco, 'd1:1', 'symbolic_ns') * 1e3
    out.append('## Plan §6.3 re-derived (additive Amdahl on the baseline medians; estimates, not predictions)\n')
    out.append(f'**Eco-12 / 2⁶⁴−353**: sig path (en:16) {sig:,.0f} ms, symbolic at 16 workers (cl:16) '
               f'{sym16:,.0f} ms, at one worker (d1:1) {sym1:,.0f} ms, conventional F4-16 {f4:,.0f} ms. grobx '
               'figures are quoted from M31\'s and M30\'s sessions, not re-measured.\n')
    out.append('| Symbolic at 16 w | Saved ms | Projected wall | ÷ sig now | ÷ conventional F4-16 | '
               + ' | '.join(f'÷ grobx raw, {k} ({v:,.1f})' for k, v in GROBX_ECO12_MS.items()) + ' |')
    out.append('|---|---:|---:|---:|---:|' + '---:|' * len(GROBX_ECO12_MS))
    for label, target in ((f'growth removed only ({sym1:,.0f})', sym1), ('1.5×', sym16 / 1.5), ('2×', sym16 / 2),
                          ('3×', sym16 / 3), ('free (0)', 0.0)):
        saved = sym16 - target
        wall = sig - saved
        out.append(f"| {label if '(' in label else f'{label} ({target:,.0f})'} | {saved:,.0f} | {wall:,.0f} | "
                   f"{wall / sig:.3f} | {wall / f4:.3f} | "
                   + ' | '.join(f'{wall / v:.3f}' for v in GROBX_ECO12_MS.values()) + ' |')
    out.append('')
    out.append('**MQ10**, symbolic needed for T3 (sig ≤ 1.05 × conventional F4-16) by S1 alone:\n')
    out.append('| Row | Sig 16w | F4-16 | T3 limit (1.05×) | Symbolic now | Symbolic needed | Speedup needed |')
    out.append('|---|---:|---:|---:|---:|---:|---:|')
    for row in ('gf32003/mq-random-10', 'm31/mq-random-10'):
        sig_r = med(list(c.wall[(row, 'en:16')].values())) * 1e3
        f4_r = med(list(c.wall[(row, 'f4:16')].values())) * 1e3
        sym = stat(c, row, 'cl:16', 'symbolic_ns') * 1e3
        limit = 1.05 * f4_r
        need = sym - (sig_r - limit)
        speed = '∞ (not reachable by symbolic alone)' if need <= 0 else f'≥ {sym / need:.1f}×'
        out.append(f'| {row} | {sig_r:,.0f} | {f4_r:,.0f} | {limit:,.0f} | {sym:,.0f} | '
                   f"{'≤ 0' if need <= 0 else f'≤ {need:,.0f}'} | {speed} |")
    out.append('')
    out.append('**Other rows at a 1.5× symbolic cut** (sig path, all else unchanged):\n')
    out.append('| Row | Sig 16w | Symbolic 16w | Projected | ÷ sig now | ÷ conventional F4-16 |')
    out.append('|---|---:|---:|---:|---:|---:|')
    for row in ('goldilocks/katsura-11', 'wide64/katsura-11', 'goldilocks/mq-random-11'):
        sig_r = med(list(c.wall[(row, 'en:16')].values())) * 1e3
        f4_r = med(list(c.wall[(row, 'f4:16')].values())) * 1e3
        sym = stat(c, row, 'cl:16', 'symbolic_ns') * 1e3
        proj = sig_r - sym / 3
        out.append(f'| {row} | {sig_r:,.0f} | {sym:,.0f} | {proj:,.0f} | {proj / sig_r:.3f} | {proj / f4_r:.3f} |')
    out.append('')
    rest = sum(stat(c, eco, 'cl:16', f'{n}_ns') for n in ('bookkeeping', 'interreduction')) * 1e3
    out.append(f'Eco-12\'s serial remainder after S1 (bookkeeping + interreduction at 16 workers): {rest:,.0f} ms.\n')


def small(records, out):
    out.append('## #934: small controls by in-process call time\n')
    out.append('Each process runs `--repeat k`; the first call is cold and dropped, the rest give one median per '
               'process; ratios are paired per repetition (en ÷ f4). Half-width is the larger side of the 95% '
               'interval. Process wall is beside it, same pairing.\n')
    out.append('| row | workers | n | k | f4 call ms | en call ms | en ÷ f4, call [95%] | half-width | '
               'en ÷ f4, process wall [95%] | half-width | dispatch µs |')
    out.append('|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|')
    by = {}
    for r in records:
        if M0.complete(r):
            by.setdefault((r['row'], r['arm']), {})[r['rep']] = r
    for row in sorted({k[0] for k in by}):
        for w in ('1', '16'):
            en, f4 = by.get((row, f'en:{w}'), {}), by.get((row, f'f4:{w}'), {})
            reps = sorted(set(en) & set(f4))
            if not reps:
                continue
            call = lambda r: statistics.median(r['report']['calls_ns'][1:])
            cr = interval([call(en[k]) / call(f4[k]) for k in reps], f'{row} {w} call')
            wr = interval([en[k]['process_wall_ns'] / f4[k]['process_wall_ns'] for k in reps], f'{row} {w} wall')
            half = lambda x: max(x[0] - x[1], x[2] - x[0])
            k = len(en[reps[0]]['report']['calls_ns'])
            out.append(f"| {row} | {w} | {len(reps)} | {k} | {med([call(f4[x]) for x in reps]) / 1e6:.3f} | "
                       f"{med([call(en[x]) for x in reps]) / 1e6:.3f} | {fmt(cr)} | {half(cr):.2%} | {fmt(wr)} | "
                       f"{half(wr):.2%} | {med([en[x]['report']['statistics']['dispatch_ns'] for x in reps]) / 1e3:.1f} |")
    out.append('')


def extract_rs(directory):
    rows = []
    for path in sorted(Path(directory).glob('rs-*-pass*.json.gz')):
        cohort = json.loads(gzip.open(path, 'rt').read())
        for a in cohort['attempts']:
            report = a.get('report') or {}
            basis = report.get('basis')
            rows.append(dict(file=path.name, field=a['field'], name=a['name'], workers=cohort['workers'],
                             status=report.get('status', a.get('stop')), process_wall_ns=a['process_wall_ns'],
                             engine_wall_ns=report.get('engine_wall_ns'), observed_threads=a.get('observed_threads'),
                             pool=(a.get('raw') or {}).get('workers'), load_start=cohort['load_start'][0],
                             basis_sha256=hashlib.sha256(json.dumps(basis).encode()).hexdigest() if basis else None,
                             archive_sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
    return rows


def rs(rows, out):
    out.append('## #935: groebner-rs at 1/4/8/16 workers on the wide rows (wide controller; process wall, ms)\n')
    out.append('One worker count per controller pass, worker order rotated per pass; `observed threads` is the '
               'number of driver threads whose CPU ticks moved during the solve (median; a lower bound). '
               'grobx stays at its declared one worker and is not run here.\n')
    out.append('| row | workers | n | median [95%] | engine solve ms | observed threads | distinct bases | best |')
    out.append('|---|---:|---:|---:|---:|---:|---:|---|')
    for key in sorted({(r['field'], r['name']) for r in rows}):
        cells = {}
        for w in (1, 4, 8, 16):
            done = [r for r in rows if (r['field'], r['name']) == key and r['workers'] == w and r['status'] == 'complete']
            if done:
                cells[w] = (done, interval([r['process_wall_ns'] / 1e9 for r in done], f'{key} {w}'))
        best = min(cells, key=lambda w: cells[w][1][0]) if cells else None
        for w, (done, iv) in cells.items():
            out.append(f"| {key[0]}/{key[1]} | {w} | {len(done)} | {ms(iv)} | "
                       f"{med([r['engine_wall_ns'] / 1e6 for r in done if r['engine_wall_ns']]):,.1f} | "
                       f"{med([r['observed_threads'] for r in done if r['observed_threads'] is not None]) or '—'} | "
                       f"{len({r['basis_sha256'] for r in done})} | {'**best**' if w == best else ''} |")
    out.append('')


class Split(M1.Final):
    def __init__(self, records):
        super().__init__(records)
        self.raw = {}
        for r in records:
            self.raw.setdefault((r['row'], r['arm']), []).append(r)


def main(argv):
    if argv[0] == '--extract-rs':
        rows = extract_rs(argv[1])
        with gzip.open(Path(argv[2]) / 'rs.jsonl.gz', 'wt', compresslevel=9) as f:
            f.writelines(json.dumps(r) + '\n' for r in rows)
        return
    directory = Path(argv[0])
    out = ['# #939 tables (generated by summarize.py; do not edit)\n']
    c = cohort(directory, 'walls')
    m31 = M1.Final(M1.load(ROOT / 'research/m31-final', 'walls'))
    split_records_ = M1.load(directory, 'split')
    split = Split(split_records_) if split_records_ else None
    if c.rows:
        headline(c, m31, out)
        stages(c, out)
        attribution(c, split, out)
    if split is not None:
        symbolic_split(split, c if c.rows else None, out)
    if c.rows:
        ceilings(c, out)
    ab_cohort = cohort(directory, 'ab')
    if ab_cohort.rows:
        ab(ab_cohort, out)
    small_records = M1.load(directory, 'small')
    if small_records:
        small(small_records, out)
    rs_path = directory / 'rs.jsonl.gz'
    if rs_path.exists():
        rs([json.loads(line) for line in gzip.open(rs_path, 'rt')], out)
    if c.rows:
        walls(c, out)
    print('\n'.join(out).rstrip())


if __name__ == '__main__':
    main(sys.argv[1:])
