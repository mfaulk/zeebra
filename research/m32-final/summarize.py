#!/usr/bin/env python3
"""#942 tables from the final cohort (plan §6, §13). Timing ratios are paired per repetition: median
with a 95% bootstrap interval of the median (20,000 draws). `dev` and `held` read process wall;
`small` reads each process's median warm call under `--calls 20` on every arm (#934, #958).
Comparands come from the controllers' own archives through `research/m30-final/extract.py` (wide,
mq10) and `research/m32-baseline/summarize.py`'s `extract_rs`, whose extracts sit beside this file.

    python3 research/m32-final/summarize.py research/m32-final > research/m32-final/tables.md
"""
import gzip
import importlib.util
import json
import random
import statistics
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DRAWS = 20000
BIG = ['wide64/eco-12', 'goldilocks/katsura-11', 'wide64/katsura-11', 'goldilocks/mq-random-11']
MQ10 = ['gf32003/mq-random-10', 'm31/mq-random-10']
CONTROLS = ['goldilocks/cyclic-7', 'wide64/cyclic-7', 'goldilocks/noon-7', 'wide64/noon-8']
SMALL = ['goldilocks/katsura-4', 'wide64/katsura-4', 'wide64/katsura-9']
HELD_OUT = ['goldilocks/mq-random-10', 'm31/katsura-10', 'm31/eco-11']
TIMED = BIG + MQ10 + CONTROLS + SMALL + HELD_OUT
T4_ABSOLUTE = {'goldilocks/katsura-11': 0.50, 'wide64/katsura-11': 0.50, 'goldilocks/mq-random-11': 0.50,
               'wide64/eco-12': 0.70}
# The dev controls plan §10.1 names (pins.json roles), read by T5 at 1 and 16 workers.
T5_DEV = ['goldilocks/cyclic-7', 'wide64/cyclic-7', 'goldilocks/katsura-4', 'wide64/katsura-4',
          'goldilocks/noon-7']
STAGES = ['symbolic_ns', 'elimination_ns', 'bookkeeping_ns', 'interreduction_ns']
LOAD_FLAG = 4.0


def interval(values, seed=942):
    rng = random.Random(seed)
    meds = sorted(statistics.median(rng.choices(values, k=len(values))) for _ in range(DRAWS))
    return meds[int(0.025 * DRAWS)], meds[int(0.975 * DRAWS) - 1]


def load(directory, name):
    path = Path(directory) / f'{name}.jsonl.gz'
    if not path.exists():
        return []
    with gzip.open(path, 'rt') as handle:
        return [json.loads(line) for line in handle if line.strip()]


def complete(r):
    return r['returncode'] == 0 and (r.get('report') or {}).get('status') == 'complete'


def metric(r):
    if r['suite'] != 'small':
        return r['process_wall_ns'] / 1e6
    report = r['report']
    return statistics.median(report.get('warm_ns') or report['calls_ns'][1:]) / 1e6


def stage(r, key):
    return ((r['report'] or {}).get('statistics') or {}).get(key)


class Cohort:
    def __init__(self, records):
        self.cells = defaultdict(dict)  # (row, arm) -> rep -> record
        self.failures = []
        self.records = records
        for r in records:
            if complete(r):
                self.cells[(r['row'], r['arm'])][r['rep']] = r
            else:
                self.failures.append(r)

    def values(self, row, arm, fn=metric):
        return [fn(r) for r in self.cells.get((row, arm), {}).values() if fn(r) is not None]

    def median(self, row, arm, fn=metric):
        v = self.values(row, arm, fn)
        return statistics.median(v) if v else None

    def ratio(self, row, a, b, fn=metric):
        ca, cb = self.cells.get((row, a), {}), self.cells.get((row, b), {})
        pairs = [(fn(ca[k]), fn(cb[k])) for k in sorted(ca) if k in cb]
        pairs = [(x, y) for x, y in pairs if x is not None and y]
        if not pairs:
            return None
        ratios = [x / y for x, y in pairs]
        lo, hi = interval(ratios)
        med = statistics.median(ratios)
        return dict(n=len(ratios), med=med, lo=lo, hi=hi, half=(hi - lo) / 2 / med)

    def route(self, row, arm):
        routes = {(r['report']['statistics'] or {}).get('route') for r in self.cells.get((row, arm), {}).values()}
        return ', '.join(sorted(x for x in routes if x)) or '—'


def fr(c, digits=3):
    if c is None:
        return '—'
    return f"{c['med']:.{digits}f} [{c['lo']:.{digits}f}, {c['hi']:.{digits}f}]"


def fms(v):
    if v is None:
        return '—'
    return f'{v:,.1f}' if v >= 10 else f'{v:.3f}'


def rss(r):
    return (r['report'] or {}).get('peak_rss_bytes')


def scoreboard(c, out):
    out.append('## 1. Primary scoreboard, 16 workers (paired median [95%])\n')
    out.append('`f4` F3 conventional F4; `en` F3 adaptive path (`f4_signature`); `men`/`mf4` the M31 reference '
               '`8715c8ed`. One harness, one protocol (process wall; katsura-4 and katsura-9 are `--calls 20` '
               'warm-call medians on every arm). RSS is peak VmHWM, median ratio.\n')
    out.append('| row | route en:16 | f4:16 ms | men:16 ms | en:16 ms | en ÷ f4 | en ÷ men | f4 ÷ mf4 | RSS en ÷ f4 | RSS en ÷ men |')
    out.append('|---|---|---:|---:|---:|---:|---:|---:|---:|---:|')
    for row in TIMED:
        out.append(f"| {row} | {c.route(row, 'en:16')} | {fms(c.median(row, 'f4:16'))} | {fms(c.median(row, 'men:16'))} | "
                   f"{fms(c.median(row, 'en:16'))} | {fr(c.ratio(row, 'en:16', 'f4:16'))} | "
                   f"{fr(c.ratio(row, 'en:16', 'men:16'))} | {fr(c.ratio(row, 'f4:16', 'mf4:16'))} | "
                   f"{fr(c.ratio(row, 'en:16', 'f4:16', rss))} | {fr(c.ratio(row, 'en:16', 'men:16', rss))} |")
    out.append('')


def scaling(c, out):
    out.append('## 2. Worker scaling: adaptive ÷ conventional at each worker count, and routes\n')
    out.append('| row | en ÷ f4, 1 w | 4 w | 8 w | 16 w | route 1 / 4 / 8 / 16 | en ÷ men, 1 w | en:16 ÷ en:8 (S-b) |')
    out.append('|---|---:|---:|---:|---:|---|---:|---:|')
    for row in TIMED:
        routes = ' / '.join(c.route(row, f'en:{w}') for w in (1, 4, 8, 16))
        out.append(f"| {row} | " + ' | '.join(fr(c.ratio(row, f'en:{w}', f'f4:{w}')) for w in (1, 4, 8, 16))
                   + f" | {routes} | {fr(c.ratio(row, 'en:1', 'men:1'))} | {fr(c.ratio(row, 'en:16', 'en:8'))} |")
    out.append('')
    out.append('### Walls, median ms\n')
    out.append('| row | f4:1 | f4:4 | f4:8 | f4:16 | en:1 | en:4 | en:8 | en:16 | sg:1 | sg:16 | mf4:16 | men:1 | men:16 |')
    out.append('|---|' + '---:|' * 13)
    arms = ['f4:1', 'f4:4', 'f4:8', 'f4:16', 'en:1', 'en:4', 'en:8', 'en:16', 'sg:1', 'sg:16', 'mf4:16', 'men:1', 'men:16']
    for row in TIMED:
        out.append(f'| {row} | ' + ' | '.join(fms(c.median(row, a)) for a in arms) + ' |')
    out.append('')


def stages(c, out):
    out.append('## 3. Signature engine forced (`sg`, F3; `msg`, M31): wall and stage clocks, median ms\n')
    out.append('The `--claim` parallel cascade above one worker, the route `en` takes on signature-routed rows. '
               'Conventional F4 and the entry arms report no stage clocks in this harness.\n')
    out.append('| row | arm | n | wall | symbolic | elimination | bookkeeping | interreduction | coefficient products | signature basis |')
    out.append('|---|---|---:|---:|---:|---:|---:|---:|---:|---:|')
    for row in TIMED:
        for arm in ('sg:1', 'sg:4', 'sg:8', 'sg:16', 'msg:16'):
            if not c.cells.get((row, arm)):
                continue
            cols = [fms(c.median(row, arm, lambda r, k=k: (stage(r, k) or 0) / 1e6)) for k in STAGES]
            prod = c.median(row, arm, lambda r: stage(r, 'coefficient_products'))
            sigb = c.median(row, arm, lambda r: stage(r, 'signature_basis_elements'))
            out.append(f"| {row} | {arm} | {len(c.cells[(row, arm)])} | {fms(c.median(row, arm))} | " + ' | '.join(cols)
                       + f" | {'—' if prod is None else f'{prod:,.0f}'} | {'—' if sigb is None else f'{sigb:,.0f}'} |")
    out.append('')
    out.append('### T1 and the forced engine against M31 (paired)\n')
    out.append('| row | symbolic msg:16 ÷ sg:16 (T1) | wall sg:16 ÷ msg:16 | products sg:16 ÷ msg:16 | sg:16 ÷ f4:16 | sg:1 ÷ f4:1 |')
    out.append('|---|---:|---:|---:|---:|---:|')
    sym = lambda r: stage(r, 'symbolic_ns')  # noqa: E731
    for row in TIMED:
        out.append(f"| {row} | {fr(c.ratio(row, 'msg:16', 'sg:16', sym))} | {fr(c.ratio(row, 'sg:16', 'msg:16'))} | "
                   f"{fr(c.ratio(row, 'sg:16', 'msg:16', lambda r: stage(r, 'coefficient_products')))} | "
                   f"{fr(c.ratio(row, 'sg:16', 'f4:16'))} | {fr(c.ratio(row, 'sg:1', 'f4:1'))} |")
    out.append('')


def criteria(c, out):
    out.append('## 4. Target criteria, read from this cohort\n')
    out.append('| criterion | cell | value | bound | verdict |')
    out.append('|---|---|---:|---|---|')

    def line(name, cell, v, bound, ok):
        out.append(f'| {name} | {cell} | {fr(v)} | {bound} | {"met" if ok else "**missed**"} |')

    sym = lambda r: stage(r, 'symbolic_ns')  # noqa: E731
    v = c.ratio('wide64/eco-12', 'msg:16', 'sg:16', sym)
    if v:
        line('T1', 'Eco-12 symbolic, M31 ÷ F3, 16 w', v, 'median ≥ 1.5, lower ≥ 1.4', v['med'] >= 1.5 and v['lo'] >= 1.4)
    v = c.ratio('wide64/eco-12', 'en:16', 'men:16')
    if v:
        line('T2', 'Eco-12 en ÷ men, 16 w', v, 'median ≤ 0.90, upper ≤ 0.92', v['med'] <= 0.90 and v['hi'] <= 0.92)
    for row in MQ10:
        for w in (1, 4, 8, 16):
            v = c.ratio(row, f'en:{w}', f'f4:{w}')
            if v:
                line('T3', f'{row} en ÷ f4, {w} w', v, 'upper ≤ 1.05', v['hi'] <= 1.05)
    for row, bound in T4_ABSOLUTE.items():
        v = c.ratio(row, 'en:16', 'f4:16')
        if v:
            line('T4 absolute', f'{row} en ÷ f4, 16 w', v, f'median ≤ {bound:.2f}', v['med'] <= bound)
    for row in TIMED:
        if row in HELD_OUT:
            continue
        if 'Signature' not in c.route(row, 'en:16'):
            continue
        v = c.ratio(row, 'en:16', 'men:16')
        if v:
            line('T4 vs M31', f'{row} en ÷ men, 16 w', v, 'upper ≤ 1.03', v['hi'] <= 1.03)
    for row in T5_DEV + HELD_OUT:
        for w in (1, 16):
            v = c.ratio(row, f'en:{w}', f'f4:{w}')
            if v:
                line('T5', f'{row} en ÷ f4, {w} w', v, 'upper ≤ 1.05', v['hi'] <= 1.05)
    out.append('')
    out.append('### T6 peak RSS (median ratio over paired repetitions, every worker count)\n')
    out.append('| row | worst en ÷ f4 (W) | en:16 ÷ men:16 | signature-routed at 16 |')
    out.append('|---|---:|---:|---|')
    for row in TIMED:
        worst = max(((c.ratio(row, f'en:{w}', f'f4:{w}', rss) or {}).get('med', 0), w) for w in (1, 4, 8, 16))
        m = c.ratio(row, 'en:16', 'men:16', rss)
        m16 = '—' if not m else f"{m['med']:.3f}"
        out.append(f"| {row} | {worst[0]:.3f} ({worst[1]}) | {m16} | "
                   f"{'yes' if 'Signature' in c.route(row, 'en:16') else 'no'} |")
    out.append('')


def dispatch(c, out):
    out.append('## 5. Dispatch cost (T9), every `en` child\n')
    worst, share = 0, 0.0
    for (row, arm), reps in c.cells.items():
        if not arm.startswith('en:'):
            continue
        for r in reps.values():
            ns = (r['report']['statistics'] or {}).get('dispatch_ns')
            if ns is None:
                continue
            worst = max(worst, ns)
            if r['suite'] != 'small' and metric(r) >= 50:
                share = max(share, ns / 1e6 / metric(r))
    out.append(f'Max dispatch {worst / 1e3:.1f} µs; worst share of wall on rows ≥ 50 ms {share * 100:.4f}%.\n')


def correctness(c, certify, out):
    out.append('## 6. Correctness: basis digests and certification\n')
    out.append('| row | completed children | distinct digests (all arms, both builds) | certification at 16 w | certify s |')
    out.append('|---|---:|---:|---|---:|')
    certs = {r['row']: r for r in certify}
    for row in TIMED:
        digests = {r['report']['basis_sha256'] for (rw, _), reps in c.cells.items() if rw == row for r in reps.values()}
        n = sum(len(reps) for (rw, _), reps in c.cells.items() if rw == row)
        cr = certs.get(row)
        cert = ((cr or {}).get('report') or {}).get('certification') or {}
        dig_ok = cr and complete(cr) and cr['report']['basis_sha256'] in digests
        status = '—' if not cr else (f"passed={cert.get('checks_passed')} complete={cert.get('complete')}"
                                     f"{'' if dig_ok else ' (digest differs or incomplete)'}")
        out.append(f"| {row} | {n} | {len(digests)} | {status} | "
                   f"{'—' if not cert.get('ns') else f'{cert['ns'] / 1e9:.1f}'} |")
    out.append('')
    out.append(f'Children not complete: {len(c.failures)}.\n')
    for r in c.failures:
        out.append(f"- {r['suite']} rep {r['rep']} {r['row']} {r['arm']}: rc={r['returncode']} "
                   f"status={(r.get('report') or {}).get('status')} guard={r.get('rss_guard_rc')}")
    out.append('')


def load_table(records, out):
    out.append('## 7. Machine context per suite (load at child start; compilers in cpu-context snapshots)\n')
    out.append('| suite | children | load min | median | max | children over 4 | children with a compiler running |')
    out.append('|---|---:|---:|---:|---:|---:|---:|')
    by = defaultdict(list)
    for r in records:
        by[r['suite']].append(r)
    for suite, rs in by.items():
        loads = [r['load_start'] for r in rs]
        comp = sum(1 for r in rs if any(isinstance(s, dict) and s.get('compilers') for s in (r.get('before'), r.get('after'))))
        out.append(f'| {suite} | {len(rs)} | {min(loads):.1f} | {statistics.median(loads):.1f} | {max(loads):.1f} | '
                   f'{sum(1 for x in loads if x > LOAD_FLAG)} | {comp} |')
    out.append('')


def _module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def comparands(directory, c, out):
    d = Path(directory)
    out.append('## 8. Comparands (process wall, ms; median [95%] of independent resamples)\n')
    out.append('Ratios are Zeebra ÷ comparand, median ÷ median. grobx raw is randomized and uncertified; grobx '
               'certified, groebner-rs (verified against its own reduced basis), msolve exact and Zeebra '
               '(deterministic) are never merged. Best-supported-configuration rows divide across worker counts.\n')
    out.append('| row | comparand (mode) | workers | n complete | comparand ms | Zeebra en:16 ÷ it | Zeebra en at equal workers ÷ it | basis = Zeebra |')
    out.append('|---|---|---:|---:|---:|---:|---:|---|')

    def iv(values):
        lo, hi = interval(values)
        return f'{statistics.median(values):,.1f} [{lo:,.1f}, {hi:,.1f}]'

    def zr(row, arm, values):
        """median ÷ median with each side resampled independently (plan §10.2)."""
        z = c.values(row, arm)
        if not z or not values:
            return '—'
        rng = random.Random(f'{row} {arm}')
        draws = sorted(statistics.median(rng.choices(z, k=len(z)))
                       / statistics.median(rng.choices(values, k=len(values))) for _ in range(DRAWS))
        med = statistics.median(z) / statistics.median(values)
        return f'{med:.3f} [{draws[int(0.025 * DRAWS)]:.3f}, {draws[int(0.975 * DRAWS) - 1]:.3f}]'

    zdig = {}
    for (row, _), reps in c.cells.items():
        for r in reps.values():
            zdig.setdefault(row, set()).add(r['report']['basis_sha256'])
    def same(row, digests):
        if not digests:
            return '—'
        return 'yes' if digests <= zdig.get(row, set()) else f'text differs ({len(digests)} distinct; README)'

    rs_path = d / 'rs.jsonl.gz'
    if rs_path.exists():
        rows = [json.loads(x) for x in gzip.open(rs_path, 'rt') if x.strip()]
        for key in sorted({(r['field'], r['name']) for r in rows}):
            done = [r for r in rows if (r['field'], r['name']) == key and r['status'] == 'complete']
            row = '/'.join(key)
            vals = [r['process_wall_ns'] / 1e6 for r in done]
            if vals:
                out.append(f"| {row} | groebner-rs (verified) | 8 | {len(done)} | {iv(vals)} | {zr(row, 'en:16', vals)} | "
                           f"{zr(row, 'en:8', vals)} | {same(row, {r['basis_sha256'] for r in done})} |")
    wide_path = d / 'wide-attempts.json'
    if wide_path.exists():
        cohorts = json.loads(wide_path.read_text())
        acc = defaultdict(list)
        for coh in cohorts:
            for a in coh['attempts']:
                acc[(a['field'], a['name'], a['engine'])].append(a)
        for (field, name, engine), attempts in sorted(acc.items()):
            done = [a for a in attempts if a['status'] in ('complete', 'verified') and a['solver_process_wall_ns']]
            row = f'{field}/{name}'
            vals = [a['solver_process_wall_ns'] / 1e6 for a in done]
            mode = 'raw randomized' if engine == 'grobx' else 'verified'
            if vals:
                out.append(f"| {row} | {engine} ({mode}) | 1 | {len(done)} of {len(attempts)} | {iv(vals)} | "
                           f"{zr(row, 'en:16', vals)} | {zr(row, 'en:1', vals)} | "
                           f"{same(row, {a['basis_text_sha256'] for a in done})} |")
    mq_path = d / 'mq10-attempts.json'
    if mq_path.exists():
        acc = defaultdict(list)
        for coh in json.loads(mq_path.read_text()):
            for a in coh['attempts']:
                acc[(a['field'], a['name'], a['engine'], a['workers'])].append(a)
        fields = {'32003': 'gf32003', '2147483647': 'm31'}
        for (field, name, engine, w), attempts in sorted(acc.items(), key=lambda kv: str(kv[0])):
            done = [a for a in attempts if a['status'] == 'verified' and a['process_wall_ns']]
            row = f"{fields.get(str(field), field)}/{name}"
            vals = [a['process_wall_ns'] / 1e6 for a in done]
            mode = {'grobx': 'raw randomized', 'msolve': 'exact', 'zeebra': "Zeebra's driver"}.get(engine, 'verified')
            out.append(f"| {row} | {engine} ({mode}) | {w} | {len(done)} of {len(attempts)} | {iv(vals) if vals else '—'} | "
                       f"{zr(row, 'en:16', vals)} | {zr(row, f'en:{w}', vals)} | verified by controller |")
    cert_path = d / 'certified.jsonl.gz'
    if cert_path.exists():
        recs = [json.loads(x) for x in gzip.open(cert_path, 'rt') if x.strip()]
        for row in sorted({r['row'] for r in recs}):
            done = [r for r in recs if r['row'] == row and (r.get('certified') or {}).get('admitted')]
            vals = [r['process_wall_ns'] / 1e6 for r in done]
            out.append(f"| {row} | grobx (certified) | 1 | {len(done)} of {sum(1 for r in recs if r['row'] == row)} | "
                       f"{iv(vals) if vals else '—'} | {zr(row, 'en:16', vals)} | {zr(row, 'en:1', vals)} | {same(row, {r['certified']['basis_text_sha256'] for r in done})} |")
    out.append('')


def main(directory):
    records = []
    for name in ('dev', 'small', 'held'):
        records += load(directory, name)
    certify = load(directory, 'certify')
    c = Cohort(records)
    out = ['# #942 final cohort tables (generated by summarize.py; do not edit)', '']
    scoreboard(c, out)
    scaling(c, out)
    stages(c, out)
    criteria(c, out)
    dispatch(c, out)
    correctness(c, certify, out)
    load_table(records + certify, out)
    comparands(directory, c, out)
    print('\n'.join(out))


if __name__ == '__main__':
    if len(sys.argv) > 2 and sys.argv[1] == '--extract-rs':
        base = _module('m32baseline', ROOT / 'research/m32-baseline/summarize.py')
        rows = base.extract_rs(sys.argv[2])
        with gzip.open(Path(sys.argv[3]) / 'rs.jsonl.gz', 'wt') as handle:
            for r in rows:
                handle.write(json.dumps(r) + '\n')
    else:
        main(sys.argv[1])
