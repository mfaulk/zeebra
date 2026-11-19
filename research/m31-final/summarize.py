#!/usr/bin/env python3
"""#906 tables from this directory's records. Every attempt is counted; only complete ones are timed.

Zeebra ratios are **paired per repetition** (#901's `summarize.py`: median of per-repetition ratios,
95% percentile bootstrap over repetitions, 20,000 draws). A comparand runs under its own controller,
so a Zeebra ÷ comparand ratio is median ÷ median with each side resampled independently (#862's
`verdicts.interval`), never paired.

    python3 research/m31-final/summarize.py research/m31-final > research/m31-final/tables.md
"""
import gzip
import importlib.util
import json
import statistics
import sys
import zlib
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def _module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


M0 = _module('m31summary', ROOT / 'research/m31-baseline/summarize.py')
verdicts = _module('verdicts', ROOT / 'research/m29-final/verdicts.py')

NAMES = {'wide64/eco-12': 'Eco-12 / 2⁶⁴−353', 'goldilocks/katsura-11': 'Katsura-11 / Goldilocks',
         'wide64/katsura-11': 'Katsura-11 / 2⁶⁴−353', 'goldilocks/mq-random-11': 'MQ11 / Goldilocks',
         'gf32003/mq-random-10': 'MQ10 / 32003', 'm31/mq-random-10': 'MQ10 / 2³¹−1',
         'goldilocks/cyclic-7': 'Cyclic-7 / Goldilocks', 'wide64/cyclic-7': 'Cyclic-7 / 2⁶⁴−353',
         'goldilocks/katsura-4': 'katsura-4 / Goldilocks', 'wide64/katsura-4': 'katsura-4 / 2⁶⁴−353',
         'goldilocks/noon-7': 'noon-7 / Goldilocks', 'wide64/katsura-9': 'katsura-9 / 2⁶⁴−353 (held out)',
         'wide64/noon-8': 'noon-8 / 2⁶⁴−353 (held out)'}
MQ10 = ('gf32003/mq-random-10', 'm31/mq-random-10')
MQ10_FIELD = {'gf32003/mq-random-10': '32003', 'm31/mq-random-10': '2147483647'}
WIDE = ('wide64/eco-12', 'goldilocks/mq-random-11', 'wide64/katsura-11', 'wide64/cyclic-7')
STAGES = ('symbolic', 'elimination', 'bookkeeping', 'interreduction')


def load(directory, name):
    path = directory / f'{name}.jsonl.gz'
    return M0.load([str(path)]) if path.exists() else []


def interval(values, seed):
    if not values:
        return None
    return M0.median_interval(values, zlib.crc32(seed.encode()))


def fmt(r, digits=3):
    return '—' if r is None else f'{r[0]:.{digits}f} [{r[1]:.{digits}f}, {r[2]:.{digits}f}]'


def ms(r):
    return '—' if r is None else f'{r[0] * 1e3:,.1f} [{r[1] * 1e3:,.1f}, {r[2] * 1e3:,.1f}]'


class Final(M0.Cohort):
    def ratio(self, row, a, b, field=None):
        """Paired ratio; `field` reads a value from each report instead of the process wall."""
        if field is None:
            x, y = self.wall[(row, a)], self.wall[(row, b)]
        else:
            x = {k: field(v) for k, v in self.reports[(row, a)].items()}
            y = {k: field(v) for k, v in self.reports[(row, b)].items()}
        values = M0.paired(x, y)
        return interval(values, f'{row} {a} {b}') if values else None

    def stage(self, row, arm, name):
        values = [r['statistics'][f'{name}_ns'] / 1e9 for r in self.reports[(row, arm)].values()]
        return statistics.median(values) if values else None


def rss(report):
    return report['peak_rss_bytes']


def elimination(report):
    return report['statistics']['elimination_ns']


def walls_table(c, out):
    out.append('## Wall cohort (process wall, s)\n')
    out.append('| row | arm | attempts | complete | median [95%] | median RSS MiB | stops |')
    out.append('|---|---|---:|---:|---:|---:|---|')
    for row in c.rows:
        for arm in sorted({a for (r, a) in c.attempts if r == row}, key=arm_order):
            key = (row, arm)
            values = list(c.wall[key].values())
            r = interval(values, f'{row} {arm}')
            rss_values = c.rss[key]
            out.append(f"| {row} | {arm} | {c.attempts[key]} | {len(values)} | "
                       f"{'—' if r is None else f'{r[0]:.3f} [{r[1]:.3f}, {r[2]:.3f}]'} | "
                       f"{statistics.median(rss_values):.0f} | {', '.join(c.failures[key]) or '—'} |"
                       if rss_values else f"| {row} | {arm} | {c.attempts[key]} | 0 | — | — | "
                       f"{', '.join(c.failures[key])} |")
    out.append('')


ARM_ORDER = ['f4:1', 'f4:4', 'f4:8', 'f4:16', 'zf4:16', 'cm:16', 'zcm:16', 'en:1', 'en:16', 'd1:1', 'zd1:1',
             'cl:4', 'cl:8', 'cl:16']


def arm_order(arm):
    return ARM_ORDER.index(arm) if arm in ARM_ORDER else len(ARM_ORDER)


def headline_table(c, out):
    out.append('## End-to-end wall: the opt-in path against shipping F4 (paired, median [95%])\n')
    out.append('`en` is `grobner::f4_signature` with its dispatch; `f4` shipping F4, both from the final '
               'binary; `z` arms are the M31-0 freeze. MQ10\'s freeze arm is `m29_cost_model` (`zcm:16`), so '
               'its "÷ freeze" columns cross instruments and are marked †.\n')
    out.append('| row | route | en:16 ÷ f4:16 | RSS en:16 ÷ f4:16 | en:1 ÷ f4:1 | en:16 ÷ freeze F4-16 | '
               'F4-16 final ÷ freeze | d1 final ÷ freeze d1 | d1 ÷ f4:16 |')
    out.append('|---|---|---:|---:|---:|---:|---:|---:|---:|')
    for row in c.rows:
        routes = sorted({r['statistics']['route'] for r in c.reports[(row, 'en:16')].values()})
        if row in MQ10:
            freeze_en, freeze_f4 = fmt(c.ratio(row, 'en:16', 'zcm:16')) + ' †', fmt(c.ratio(row, 'cm:16', 'zcm:16'))
            d1 = '—'
        else:
            freeze_en, freeze_f4 = fmt(c.ratio(row, 'en:16', 'zf4:16')), fmt(c.ratio(row, 'f4:16', 'zf4:16'))
            d1 = fmt(c.ratio(row, 'd1:1', 'zd1:1'))
        out.append(f"| {row} | {', '.join(routes) or '—'} | {fmt(c.ratio(row, 'en:16', 'f4:16'))} | "
                   f"{fmt(c.ratio(row, 'en:16', 'f4:16', rss))} | {fmt(c.ratio(row, 'en:1', 'f4:1'))} | "
                   f"{freeze_en} | {freeze_f4} | {d1} | {fmt(c.ratio(row, 'd1:1', 'f4:16'))} |")
    out.append('')
    out.append('Peak RSS ratio, every arm of the entry point against shipping F4 at the same workers '
               '(paired medians; criterion 4 reads the worst):\n')
    out.append('| row | en:1 ÷ f4:1 | en:16 ÷ f4:16 |')
    out.append('|---|---:|---:|')
    for row in c.rows:
        out.append(f"| {row} | {fmt(c.ratio(row, 'en:1', 'f4:1', rss))} | {fmt(c.ratio(row, 'en:16', 'f4:16', rss))} |")
    out.append('')


def speedup_table(c, out):
    out.append('## Parallel speedup of the signature engine (medians; stage clocks from the timed binary)\n')
    out.append('`d1:1` is design 1; `cl:W` the parallel cascade at W workers (the route `en:W` takes when it '
               'picks the signature engine). Speedups are paired d1 ÷ cl:W.\n')
    out.append('| row | arm | wall s | symbolic | elimination | bookkeeping | interreduction | wall speedup | '
               'elimination speedup |')
    out.append('|---|---|---:|---:|---:|---:|---:|---:|---:|')
    for row in c.rows:
        for arm in ('d1:1', 'cl:4', 'cl:8', 'cl:16'):
            if not c.reports[(row, arm)]:
                continue
            wall = statistics.median(c.wall[(row, arm)].values())
            st = ' | '.join(f'{c.stage(row, arm, n):.3f}' for n in STAGES)
            if arm == 'd1:1':
                sp = '— | —'
            else:
                sp = f"{fmt(c.ratio(row, 'd1:1', arm), 2)} | {fmt(c.ratio(row, 'd1:1', arm, elimination), 2)}"
            out.append(f'| {row} | {arm} | {wall:.3f} | {st} | {sp} |')
    out.append('')
    out.append('Shipping F4 at the same commit, for scale (paired f4:1 ÷ f4:W):\n')
    out.append('| row | f4:4 | f4:8 | f4:16 |')
    out.append('|---|---:|---:|---:|')
    for row in c.rows:
        out.append(f"| {row} | " + ' | '.join(fmt(c.ratio(row, 'f4:1', f'f4:{w}'), 2) for w in (4, 8, 16)) + ' |')
    out.append('')


WORK = ('pairs_created', 'rejected_product', 'rejected_koszul', 'rejected_zero_row', 'rejected_rewrite',
        'rejected_duplicate', 'targets', 'reductions_to_zero', 'zero_rows', 'coefficient_products',
        'signature_basis_elements', 'reduced_basis_elements')


def work_table(c, census, out):
    out.append('## Algorithmic work (plan §2.2 quantities; one value per cell when every repetition agrees)\n')
    out.append('Signature counts from the timed reports; shipping F4 counts from the `census` suite '
               '(`--discovery`, one worker, research-work build). "varies" means repetitions disagree.\n')
    out.append('| row | arm | pairs created | rejected: product / Koszul / zero-row / rewrite / duplicate | targets | '
               'reductions to zero | zero rows | products | signature basis / reduced |')
    out.append('|---|---|---:|---|---:|---:|---:|---:|---|')

    def one(row, arm, key):
        vals = {r['statistics'][key] for r in c.reports[(row, arm)].values()}
        return f'{vals.pop():,}' if len(vals) == 1 else ('varies' if vals else '—')

    for row in c.rows:
        for arm in ('zd1:1', 'd1:1', 'cl:16'):
            if not c.reports[(row, arm)]:
                continue
            rej = ' / '.join(one(row, arm, k) for k in WORK[1:6])
            out.append(f"| {row} | {arm} | {one(row, arm, 'pairs_created')} | {rej} | {one(row, arm, 'targets')} | "
                       f"{one(row, arm, 'reductions_to_zero')} | {one(row, arm, 'zero_rows')} | "
                       f"{one(row, arm, 'coefficient_products')} | {one(row, arm, 'signature_basis_elements')} / "
                       f"{one(row, arm, 'reduced_basis_elements')} |")
    out.append('')
    out.append('| row | shipping F4 pairs reduced | elements added | reductions to zero | zero rows | products '
               '(forward + backward) | design 1 products ÷ F4 | cascade products ÷ F4 |')
    out.append('|---|---:|---:|---:|---:|---:|---:|---:|')
    for r in census:
        if not M0.complete(r):
            out.append(f"| {r['row']} | stopped: {(r.get('report') or {}).get('status') or r['returncode']} | | | | | | |")
            continue
        s, w = r['report']['statistics'], r['report']['work']
        products = w['forward_products'] + w['backward_products']

        def share(arm):
            vals = {x['statistics']['coefficient_products'] for x in c.reports[(r['row'], arm)].values()}
            return f'{vals.pop() / products:.3f}' if len(vals) == 1 and products else '—'

        out.append(f"| {r['row']} | {s['pairs_reduced']:,} | {s['elements_added']:,} | "
                   f"{s['pairs_reduced'] - s['elements_added']:,} | {w['zero_rows']:,} | {products:,} | "
                   f"{share('d1:1')} | {share('cl:16')} |")
    out.append('')


def dispatch_table(c, out):
    out.append('## Dispatch decision and cost (entry point, in-process)\n')
    out.append('| row | route en:1 | route en:16 | features (variables, least nonlinear, greatest degree) | '
               'median dispatch µs (en:16) |')
    out.append('|---|---|---|---|---:|')
    for row in c.rows:
        reps = list(c.reports[(row, 'en:16')].values())
        if not reps:
            continue
        r1 = sorted({r['statistics']['route'] for r in c.reports[(row, 'en:1')].values()})
        r16 = sorted({r['statistics']['route'] for r in reps})
        s = reps[0]['statistics']
        us = statistics.median(r['statistics']['dispatch_ns'] for r in reps) / 1e3
        out.append(f"| {row} | {', '.join(r1)} | {', '.join(r16)} | {s['variables']}, {s['min_nonlinear_degree']}, "
                   f"{s['max_degree']} | {us:.1f} |")
    out.append('')


def digest_table(c, certify, certified, passes, out):
    out.append('## Correctness: digests and certification (outside solver wall)\n')
    cert = {r['row']: r for r in certify}
    gc = defaultdict(list)
    for r in certified:
        gc[r['row']].append(r)
    grobx_raw = defaultdict(set)
    for p in passes:
        for a in p['attempts']:
            if a['engine'] == 'grobx' and a['status'] == 'complete' and a['basis_text_sha256']:
                grobx_raw[f"{a['field']}/{a['name']}"].add(a['basis_text_sha256'])
    out.append('| row | sig_f4_study digests (all arms, both builds) | children | entry `--certify` (16 w) | '
               'certify s | grobx certified (admitted / n) | grobx certified digest = Zeebra | grobx raw digest = Zeebra |')
    out.append('|---|---|---:|---|---:|---|---|---|')
    for row in c.rows:
        sig = {r['basis_sha256'] for (rw, arm), reps in c.reports.items() if rw == row
               and not arm.endswith(('cm:16',)) for r in reps.values()}
        n = sum(len(reps) for (rw, arm), reps in c.reports.items() if rw == row and not arm.endswith('cm:16'))
        e = cert.get(row)
        if e and M0.complete(e) and e['report'].get('certification'):
            k = e['report']['certification']
            same = e['report']['basis_sha256'] in sig
            ce = f"checks_passed={k['checks_passed']}, complete={k['complete']}, digest {'=' if same else '≠'}"
            cs = f"{k['ns'] / 1e9:.1f}"
        else:
            ce, cs = ('not run' if e is None else f"stopped ({(e.get('report') or {}).get('status') or e['returncode']})"), '—'
        g = gc.get(row, [])
        adm = [x for x in g if (x.get('certified') or {}).get('admitted')]
        gd = {x['certified']['basis_text_sha256'] for x in adm}
        out.append(f"| {row} | {', '.join(d[:8] for d in sorted(sig))} | {n} | {ce} | {cs} | "
                   f"{f'{len(adm)} / {len(g)}' if g else '—'} | {('yes' if gd == sig else 'NO') if gd else '—'} | "
                   f"{('yes' if grobx_raw[row] == sig else 'NO') if grobx_raw.get(row) else '—'} |")
    out.append('')
    mq = [(row, sorted({r['basis_sha256'] for arm in ('cm:16', 'zcm:16') for r in c.reports[(row, arm)].values()}))
          for row in MQ10]
    out.append('MQ10 `m29_cost_model` digests (final and freeze, a different digest format from `sig_f4_study`): '
               + '; '.join(f"{row}: {', '.join(d[:8] for d in ds)}" for row, ds in mq) + '\n')


def comparand_table(c, certified, passes, windows, out):
    out.append('## Competitive position (process wall, ms; independent bootstrap, median ÷ median)\n')
    out.append('Zeebra figures are this cohort\'s final binary: `en` the opt-in path, `f4` shipping. grobx and '
               'groebner-rs run one worker on the wide rows (their wide adapters refuse more), so a 16-worker '
               'Zeebra row against them is a **best-supported-configuration** row, and the equal-worker row is '
               'beside it. msolve and groebner-rs on MQ10 are their fastest median of 1/4/8/16 workers in the '
               'window. grobx raw is randomized and uncertified; grobx certified, groebner-rs (verified), msolve '
               'exact and Zeebra (deterministic, certified) are separate rows, never merged.\n')
    out.append('| row | comparand (mode) | w | n | comparand ms | Zeebra en:16 ms | en:16 ÷ comparand [95%] | '
               'equal-worker: Zeebra sig at w ÷ comparand | f4:16 ÷ comparand | comparand RSS MiB |')
    out.append('|---|---|---:|---:|---:|---:|---:|---:|---:|---:|')

    def zeebra(row, arm):
        return [v * 1e3 for v in c.wall[(row, arm)].values()]

    def sig_at(row, w):
        return zeebra(row, 'en:1' if w == 1 else f'cl:{w}')

    def line(row, label, w, values, rss_values, n_text):
        z16, f16 = zeebra(row, 'en:16'), zeebra(row, 'f4:16')
        eq = sig_at(row, w)

        def r(a):
            if not a or not values:
                return '—'
            lo, hi = verdicts.interval(a, values, zlib.crc32(f'{row} {label} {len(a)}'.encode()))
            return f'{statistics.median(a) / statistics.median(values):.3f} [{lo:.3f}, {hi:.3f}]'

        out.append(f"| {row} | {label} | {w} | {n_text} | "
                   f"{statistics.median(values):,.1f} | {statistics.median(z16):,.1f} | {r(z16)} | {r(eq)} | {r(f16)} | "
                   f"{f'{statistics.median(rss_values):.0f}' if rss_values else 'n/a'} |"
                   if values else f'| {row} | {label} | {w} | {n_text} | — | | | | | |')

    for row in WIDE:
        field, name = row.split('/')
        for engine, label in (('grobx', 'grobx (raw randomized)'), ('groebner-rs', 'groebner-rs (verified)')):
            att = [a for p in passes for a in p['attempts'] if (a['field'], a['name'], a['engine']) == (field, name, engine)]
            v = [a['solver_process_wall_ns'] / 1e6 for a in att if a['status'] == 'complete']
            rs = [a['peak_rss_bytes'] / 2**20 for a in att if a['status'] == 'complete' and a.get('peak_rss_bytes')]
            line(row, label, 1, v, rs, f'{len(v)} of {len(att)}')
        g = [r for r in certified if r['row'] == row]
        v = [r['process_wall_ns'] / 1e6 for r in g if (r.get('certified') or {}).get('admitted')]
        line(row, 'grobx (certified)', 1, v, [], f'{len(v)} of {len(g)}')
    for win in windows:
        groups, rss_groups = {}, {}
        for a in win['attempts']:
            if a['status'] == 'verified' and a.get('process_wall_ns'):
                key = (str(a['field']), a['engine'], a['workers'])
                groups.setdefault(key, []).append(a['process_wall_ns'] / 1e6)
                if a.get('peak_rss_bytes'):
                    rss_groups.setdefault(key, []).append(a['peak_rss_bytes'] / 2**20)
        for row in MQ10:
            field = MQ10_FIELD[row]
            for engine, label in (('msolve', 'msolve (exact)'), ('groebner-rs', 'groebner-rs (verified)'),
                                  ('grobx', 'grobx (raw randomized)'),
                                  ('zeebra', 'Zeebra shipping (`zeebra_driver`, same window)')):
                w, v = verdicts.best(groups, field, engine)
                if not v:
                    continue
                line(row, f"{label}, `{win['archive'].split('.')[0]}`", w, v, rss_groups.get((field, engine, w)),
                     str(len(v)))
    out.append('')
    out.append('Every attempt per comparand window (status counts):\n')
    for win in windows:
        counts = defaultdict(int)
        for a in win['attempts']:
            counts[(a['engine'], a['status'])] += 1
        out.append(f"- `{win['archive']}`: " + ', '.join(f'{e} {s} {n}' for (e, s), n in sorted(counts.items())))
    for p in passes:
        counts = defaultdict(int)
        for a in p['attempts']:
            counts[(a['engine'], str(a['status']))] += 1
        out.append(f"- `{p['archive']}`: " + ', '.join(f'{e} {s} {n}' for (e, s), n in sorted(counts.items())))
    out.append('')


def main():
    directory = Path(sys.argv[1])
    walls = load(directory, 'walls')
    c = Final(walls)
    out = ['# #906 tables (generated by summarize.py; do not edit)\n']
    total = len(walls)
    done = sum(1 for r in walls if M0.complete(r))
    out.append(f'Wall cohort: {done} of {total} children complete.\n')
    passes = json.loads((directory / 'wide-attempts.json').read_text()) if (directory / 'wide-attempts.json').exists() else []
    windows = json.loads((directory / 'mq10-attempts.json').read_text()) if (directory / 'mq10-attempts.json').exists() else []
    certified = load(directory, 'certified')
    walls_table(c, out)
    headline_table(c, out)
    speedup_table(c, out)
    work_table(c, load(directory, 'census'), out)
    dispatch_table(c, out)
    digest_table(c, load(directory, 'certify'), certified, passes, out)
    comparand_table(c, certified, passes, windows, out)
    print('\n'.join(out))


if __name__ == '__main__':
    main()
