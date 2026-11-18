#!/usr/bin/env python3
"""#862: every table in the M30 report, from this directory's records.

    python3 research/m30-final/summarize.py research/m30-final > research/m30-final/tables.md

Medians with 95% bootstrap intervals (`research/m29-final/verdicts.py`'s `interval`, each arm
resampled independently, 20,000 draws, seeded by the CRC-32 of the cell name). A ratio is
median ÷ median. Failed, timed-out and refused children are counted, never dropped silently.
"""
import gzip
import importlib.util
import json
import re
import statistics
import sys
import zlib
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
_spec = importlib.util.spec_from_file_location('verdicts', ROOT / 'research/m29-final/verdicts.py')
verdicts = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(verdicts)
_spec = importlib.util.spec_from_file_location('reconcile', ROOT / 'research/m30-signature/reconcile.py')
reconcile = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(reconcile)

TARGETS = ('mq10-32003', 'mq10-m31', 'eco12-wide64', 'mq11-goldilocks', 'katsura11-m31', 'katsura11-wide64',
           'cyclic7-wide64')
NAMES = {'mq10-32003': 'MQ10 / 32003', 'mq10-m31': 'MQ10 / 2³¹−1', 'eco12-wide64': 'Eco-12 / 2⁶⁴−353',
         'mq11-goldilocks': 'MQ11 / Goldilocks', 'katsura11-m31': 'Katsura-11 / 2³¹−1 (held out, #861)',
         'katsura11-wide64': 'Katsura-11 / 2⁶⁴−353 (held out, pinned)',
         'cyclic7-wide64': 'Cyclic-7 / 2⁶⁴−353 (held out, pinned)'}
WIDE = {'eco12-wide64': ('wide64', 'eco-12'), 'mq11-goldilocks': ('goldilocks', 'mq-random-11'),
        'katsura11-wide64': ('wide64', 'katsura-11'), 'cyclic7-wide64': ('wide64', 'cyclic-7')}
WORKERS = (1, 4, 8, 16)


def load(directory, name):
    path = directory / f'{name}.jsonl.gz'
    if not path.exists():
        return []
    with gzip.open(path, 'rt') as f:
        return [json.loads(line) for line in f if line.strip()]


def ok(r):
    return bool(r.get('report')) and r['report'].get('status') == 'complete'


def ms(values):
    return [v / 1e6 for v in values]


def cell(values):
    if not values:
        return '—'
    return f'{statistics.median(values):,.1f}'


def ratio(a, b, name):
    if not a or not b:
        return None, None, None
    lo, hi = verdicts.interval(a, b, zlib.crc32(name.encode()))
    return statistics.median(a) / statistics.median(b), lo, hi


def fmt_ratio(r):
    value, lo, hi = r
    return '—' if value is None else f'{value:.3f} [{lo:.3f}, {hi:.3f}]'


def walls_table(walls, out):
    out.append('## 1. Zeebra: final `main` against the M30-0 baseline, interleaved (process wall, ms)\n')
    out.append('Both builds in one campaign, adjacent in every rotation. Ratio = final ÷ baseline. RSS is the '
               'median `peak_rss_bytes`. "digests" lists the distinct basis SHA-256 prefixes across both builds.\n')
    out.append('| Instance | Workers | n (base / final) | baseline ms | final ms | final ÷ baseline [95%] | '
               'RSS MiB base / final | not complete | digests |')
    out.append('|---|---:|---:|---:|---:|---:|---:|---:|---|')
    for t in TARGETS:
        for w in WORKERS:
            rows = [r for r in walls if r['target'] == t and r['workers'] == w]
            if not rows:
                continue
            b = [r for r in rows if r['build'] == 'baseline']
            f = [r for r in rows if r['build'] == 'final']
            bw = ms([r['process_wall_ns'] for r in b if ok(r)])
            fw = ms([r['process_wall_ns'] for r in f if ok(r)])
            rss = [statistics.median([r['report']['peak_rss_bytes'] for r in x if ok(r)]) / 2**20
                   if any(ok(r) for r in x) else float('nan') for x in (b, f)]
            bad = sum(1 for r in rows if not ok(r))
            digests = sorted({r['report']['basis_sha256'][:8] for r in rows if ok(r)})
            out.append(f"| {NAMES[t]} | {w} | {len(bw)} / {len(fw)} | {cell(bw)} | {cell(fw)} | "
                       f"{fmt_ratio(ratio(fw, bw, f'final {t} {w}'))} | {rss[0]:.0f} / {rss[1]:.0f} | {bad} | "
                       f"{', '.join(digests)} |")
    out.append('')


def scaling_table(walls, out):
    out.append('## 2. Zeebra worker scaling (final `main`, process wall; speedup over its own one-worker median)\n')
    out.append('| Instance | 1 | 4 | 8 | 16 | 16-worker speedup, final (baseline) |')
    out.append('|---|---:|---:|---:|---:|---:|')
    for t in TARGETS:
        med = {}
        for build in ('baseline', 'final'):
            for w in WORKERS:
                v = ms([r['process_wall_ns'] for r in walls
                        if r['target'] == t and r['workers'] == w and r['build'] == build and ok(r)])
                med[(build, w)] = statistics.median(v) if v else None
        if med[('final', 1)] is None:
            continue
        cells = ' | '.join(f"{med[('final', w)]:,.1f}" if med[('final', w)] else '—' for w in WORKERS)
        sp = lambda b: med[(b, 1)] / med[(b, 16)] if med[(b, 1)] and med[(b, 16)] else float('nan')
        out.append(f"| {NAMES[t]} | {cells} | {sp('final'):.2f}× ({sp('baseline'):.2f}×) |")
    out.append('')


def stages_table(stages, walls, out):
    out.append('## 3. Symbolic preprocessing (stage clocks on, a separate campaign; ms)\n')
    out.append('Share = median clocked symbolic stage ÷ median unclocked process wall of the same build and '
               'worker count (§1).\n')
    out.append('| Instance | Workers | n | symbolic, baseline | symbolic, final | final ÷ baseline [95%] | '
               'share of process wall, baseline / final |')
    out.append('|---|---:|---:|---:|---:|---:|---:|')
    for t in TARGETS:
        for w in (1, 16):
            rows = [r for r in stages if r['target'] == t and r['workers'] == w and ok(r)]
            if not rows:
                continue
            sym = {b: ms([r['report']['statistics']['symbolic_ns'] for r in rows if r['build'] == b])
                   for b in ('baseline', 'final')}
            share = []
            for b in ('baseline', 'final'):
                pw = ms([r['process_wall_ns'] for r in walls
                         if r['target'] == t and r['workers'] == w and r['build'] == b and ok(r)])
                share.append(f'{100 * statistics.median(sym[b]) / statistics.median(pw):.1f}%'
                             if pw and sym[b] else '—')
            out.append(f"| {NAMES[t]} | {w} | {len(sym['final'])} | {cell(sym['baseline'])} | {cell(sym['final'])} | "
                       f"{fmt_ratio(ratio(sym['final'], sym['baseline'], f'stage {t} {w}'))} | {' / '.join(share)} |")
    out.append('')


def criteria(report):
    """Product, chain and Gebauer-Moller rejections from the Debug form of F4Statistics."""
    m = re.search(r'criteria: CriterionCounts \{\s*product: (\d+),\s*chain: (\d+),\s*gebauer_moller: (\d+)',
                  report['statistics'].get('full_statistics') or '')
    return tuple(int(x) for x in m.groups()) if m else None


def census_table(census, out):
    out.append('## 4. Algebraic work (serial `research-work` census, one worker, one run per build)\n')
    out.append('Plan §2.2 quantities, kept apart. Reductions to zero = pairs reduced − elements added; zero rows '
               'from `F4Statistics::zero_rows`; products are forward + backward coefficient products; '
               '"on zero-ending rows" is C1\'s per-batch `zero_row_products` (`--discovery`). '
               'Pair rejections by mechanism are `F4Statistics::criteria` (product, chain, Gebauer–Möller).\n')
    out.append('| Instance | build | pairs considered | rejected: product / chain / GM | pairs reduced | '
               'reductions to zero | zero rows | pair rows adding no rank | products (G) | on zero-ending rows | basis |')
    out.append('|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---|')
    for t in TARGETS:
        for b in ('baseline', 'final'):
            rows = [r for r in census if r['target'] == t and r['build'] == b and r['arm'].endswith('discovery')
                    and ok(r)]
            if not rows:
                continue
            rep = rows[0]['report']
            c = reconcile.row(rep)
            s = rep['statistics']
            cr = criteria(rep)
            crs = ' / '.join(f'{x:,}' for x in cr) if cr else 'n/a'
            out.append(f"| {NAMES[t]} | {b} | {s['pairs_considered']:,} | {crs} | {c['pairs_reduced']:,} | "
                       f"{c['zero_reductions']:,} ({100 * c['zero_reduction_fraction']:.1f}%) | {c['zero_rows']:,} | "
                       f"{c['pair_rows_adding_no_rank']:,} ({100 * c['dependent_row_fraction']:.1f}%) | "
                       f"{c['products'] / 1e9:.3f} | {100 * c['zero_row_product_fraction']:.1f}% | "
                       f"{c['basis_sha256'][:8]} |")
    bad = [r for r in census if not ok(r)]
    if bad:
        out.append(f"\nNot complete: {', '.join(f'{r['target']} {r['arm']} rc={r['rc']}' for r in bad)}")
    out.append('')


def wide_rows(directory):
    path = directory / 'wide-attempts.json'
    return json.loads(path.read_text()) if path.exists() else []


def mq10_windows(directory):
    path = directory / 'mq10-attempts.json'
    return json.loads(path.read_text()) if path.exists() else []


def scoreboard(directory, walls, out):
    out.append('## 5. Scoreboard against the comparands (process wall, ms)\n')
    out.append('Zeebra rows are §1\'s final build. grobx and groebner-rs run one worker only (their adapters refuse '
               'more), so a 16-worker Zeebra row against them is **not** an equal-worker comparison; the '
               'equal-worker row is Zeebra at one worker. msolve is exact mode, fastest median of 1/4/8/16 workers '
               'in the same window. grobx is raw randomized mode; its certified mode is §6, never folded in.\n')
    out.append('| Instance | Engine (mode) | workers | n | median ms | Zeebra 16w ÷ engine [95%] | '
               'Zeebra 1w ÷ engine [95%] (equal-worker only for 1-worker engines) | RSS MiB | verification |')
    out.append('|---|---|---:|---:|---:|---:|---:|---:|---|')
    zeebra = lambda t, w: ms([r['process_wall_ns'] for r in walls
                              if r['target'] == t and r['workers'] == w and r['build'] == 'final' and ok(r)])
    zrss = lambda t, w: statistics.median([r['report']['peak_rss_bytes'] for r in walls if r['target'] == t
                                           and r['workers'] == w and r['build'] == 'final' and ok(r)]) / 2**20
    for win in mq10_windows(directory):
        groups, rss = {}, {}
        for a in win['attempts']:
            if a['status'] == 'verified' and a.get('process_wall_ns'):
                key = (str(a['field']), a['engine'], a['workers'])
                groups.setdefault(key, []).append(a['process_wall_ns'] / 1e6)
                if a.get('peak_rss_bytes'):
                    rss.setdefault(key, []).append(a['peak_rss_bytes'] / 2**20)
        for t, field in (('mq10-32003', '32003'), ('mq10-m31', '2147483647')):
            z16, z1 = zeebra(t, 16), zeebra(t, 1)
            out.append(f"| {NAMES[t]} | Zeebra (shipping) | 16 | {len(z16)} | {cell(z16)} | — | — | "
                       f"{zrss(t, 16):.0f} | verified (Singular reference, `{win['archive'].split('.')[0]}`) |")
            for engine, label in (('zeebra', 'Zeebra (`zeebra_driver`, same window as the comparands)'),
                                  ('msolve', 'msolve (exact)'), ('grobx', 'grobx (raw randomized)'),
                                  ('groebner-rs', 'groebner-rs')):
                w, v = verdicts.best(groups, field, engine)
                if not v:
                    continue
                r16 = ratio(z16, v, f'{win["archive"]} {t} {engine} 16')
                r1 = ratio(z1, v, f'{win["archive"]} {t} {engine} 1') if w == 1 else (None, None, None)
                rs = rss.get((field, engine, w))
                out.append(f"| {NAMES[t]} | {label} | {w} | {len(v)} | {cell(v)} | {fmt_ratio(r16)} | "
                           f"{fmt_ratio(r1)} | {f'{statistics.median(rs):.0f}' if rs else 'n/a'} | verified |")
    passes = wide_rows(directory)
    for t, (field, name) in WIDE.items():
        z16, z1 = zeebra(t, 16), zeebra(t, 1)
        if not z16:
            continue
        out.append(f"| {NAMES[t]} | Zeebra (shipping) | 16 | {len(z16)} | {cell(z16)} | — | — | {zrss(t, 16):.0f} | §6 |")
        for engine, label in (('grobx', 'grobx (raw randomized)'), ('groebner-rs', 'groebner-rs')):
            att = [a for p in passes for a in p['attempts'] if (a['field'], a['name'], a['engine']) == (field, name, engine)]
            v = [a['solver_process_wall_ns'] / 1e6 for a in att if a['status'] == 'complete']
            rs = [a['peak_rss_bytes'] / 2**20 for a in att if a['status'] == 'complete' and a.get('peak_rss_bytes')]
            stops = sorted({str(a['status']) for a in att if a['status'] != 'complete'})
            same = sorted({a['basis_text_sha256'][:8] for a in att if a['status'] == 'complete' and a['basis_text_sha256']})
            out.append(f"| {NAMES[t]} | {label} | 1 | {len(v)} of {len(att)} | {cell(v)} | "
                       f"{fmt_ratio(ratio(z16, v, f'wide {t} {engine} 16'))} | "
                       f"{fmt_ratio(ratio(z1, v, f'wide {t} {engine} 1'))} | "
                       f"{f'{statistics.median(rs):.0f}' if rs else 'n/a'} | "
                       f"{'digest ' + ', '.join(same) if engine == 'grobx' else 'canonical agreement (controller)'}"
                       f"{'; stops: ' + ', '.join(stops) if stops else ''} |")
    out.append('')


def verification(directory, walls, out):
    out.append('## 6. Wide-field verification (outside the timed campaign)\n')
    out.append('| Target | timed digests (both builds) | grobx certified | cap | elements | wall s | '
               'Zeebra `--certify` | verified |')
    out.append('|---|---|---|---:|---:|---:|---|---|')
    for name in ('verification.json', 'verification-eco12-32g.json', 'verification-held-out.json'):
        path = directory / name
        if not path.exists():
            continue
        for row in json.loads(path.read_text()):
            g = row['grobx_certified']
            z = row['zeebra_certify']
            zs = z['status']
            if z.get('certification'):
                zs += f" (complete={z['certification'].get('complete')}, {z['process_wall_ns'] / 1e9:.0f} s)"
            elif 'process_wall_ns' in z:
                zs += f" ({z['process_wall_ns'] / 1e9:.0f} s)"
            out.append(f"| {row['target']} | {', '.join(d[:8] for d in row['timed_digests'])} "
                       f"({row['timed_runs']} runs) | {'admitted, digest ' + g['basis_text_sha256'][:8] if g.get('admitted') else 'not admitted: ' + g.get('error', '')[:80]} | "
                       f"{g['rss_cap_gib']} GiB | {g.get('elements', '—')} | {g['process_wall_ns'] / 1e9:.0f} | {zs} | "
                       f"{'**yes**' if row['verified'] else 'no'} |")
    out.append('')


def sigf4(directory, out):
    path = directory / 'sigf4-gate.jsonl.gz'
    if not path.exists():
        return
    with gzip.open(path, 'rt') as f:
        rows = [json.loads(l) for l in f if l.strip()]
    out.append('## 7. Workstream S arm re-run at the final `main`: `sig_f4_study` design 1 against shipping F4\n')
    out.append('#857\'s `gate` suite, unchanged (`research/m30-sigf4/campaign.sh gate`), CPUs from 8. Design 1 is '
               'serial; its 16-worker design 2 is not on `main`.\n')
    out.append('| Row | arm | n | median ms | ÷ F4 16 workers [95%] | peak RSS MiB | not complete | basis digests |')
    out.append('|---|---|---:|---:|---:|---:|---:|---|')
    done = lambda r: bool(r.get('report')) and r['report'].get('status') == 'complete'
    for row in sorted({r['row'] for r in rows}):
        walls_of = lambda arm: [r['process_wall_ns'] / 1e6 for r in rows if (r['row'], r['arm']) == (row, arm) and done(r)]
        f16 = walls_of('f4:16')
        for arm in ('sigf4:1', 'f4:1', 'f4:16'):
            cells = [r for r in rows if (r['row'], r['arm']) == (row, arm)]
            v = walls_of(arm)
            rs = [r['report']['peak_rss_bytes'] / 2**20 for r in cells if done(r)]
            d = sorted({r['report']['basis_sha256'][:8] for r in cells if done(r)})
            out.append(f"| {row} | {arm} | {len(v)} | {cell(v)} | {fmt_ratio(ratio(v, f16, f'sig {row} {arm}'))} | "
                       f"{statistics.median(rs):.0f} | {sum(1 for r in cells if not done(r))} | {', '.join(d)} |"
                       if rs else f"| {row} | {arm} | 0 | — | — | — | {len(cells)} | — |")
    out.append('')


def main():
    directory = Path(sys.argv[1])
    walls, stages, census = (load(directory, n) for n in ('walls', 'stages', 'census'))
    out = ['# M30 final cohort (#862): tables\n',
           'Generated by `python3 research/m30-final/summarize.py research/m30-final`. '
           'See [README.md](README.md) for the commits, binaries and session.\n']
    walls_table(walls, out)
    scaling_table(walls, out)
    stages_table(stages, walls, out)
    census_table(census, out)
    scoreboard(directory, walls, out)
    verification(directory, walls, out)
    sigf4(directory, out)
    print('\n'.join(out))


if __name__ == '__main__':
    main()
