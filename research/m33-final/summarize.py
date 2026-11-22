#!/usr/bin/env python3
"""Regenerate tables.md from the retained records alone (#975).

    summarize.py [--check]      # --check: exit 1 if tables.md differs from what the records give

Inputs, all committed beside this script: records-*.jsonl.gz and *.session.json (one per bench-job,
from `campaign.py extract`), sessions.json (which jobs are of record, fixed before they were read),
references.json and threads-*.jsonl. An attempt is timed only if it is ok, uncontaminated under the
publication rule with the clock judged per arm (owner decision 1, #965), and its basis digest equals
the row's independent reference. Every other attempt is counted.
"""
import argparse
import gzip
import json
import statistics
import sys
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
sys.path.insert(0, str(HERE))
import bench_stats as bs  # noqa: E402
from campaign import ROWS, rows, set_of  # noqa: E402

FLOOR_MS = 300
MS = 1e6
TOLERANCE = 0.15  # §8.4: held-out ratio no worse than the development ratio + 0.15
F = {'wide64': '2⁶⁴−353', 'goldilocks': 'Goldilocks', 'gf32003': 'GF(32003)', 'm31': 'GF(2³¹−1)'}


def load():
    recs, sessions = [], []
    for path in sorted(HERE.glob('records-*.jsonl.gz')):
        recs += [json.loads(x) for x in gzip.decompress(path.read_bytes()).decode().splitlines()]
        sessions.append(json.loads(Path(str(path).replace('.jsonl.gz', '.session.json')).read_text()))
    meta = json.loads((HERE / 'sessions.json').read_text())
    refs = json.loads((HERE / 'references.json').read_text())
    threads = [json.loads(x) for p in sorted(HERE.glob('threads-*.jsonl')) for x in p.read_text().splitlines()]
    return recs, sessions, meta, refs, threads


class Data:
    def __init__(self, recs, refs):
        self.recs, self.refs = recs, refs
        self.ext = {(r['track'], r['field'], r['name'], r['workers']) for r in recs if r['session'] == 'extension'}

    def good(self, r):
        ref = self.refs.get(f"{r['field']}__{r['name']}", {}).get('basis_m33')
        return r['status'] == 'ok' and not r['contaminated'] and bool(ref) and r['basis_m33'] == ref

    def cell(self, track, field, name, arm, w):
        return [r for r in self.recs if (r['track'], r['field'], r['name'], r['arm'], r['workers'])
                == (track, field, name, arm, w) and self.good(r)]

    def walls(self, track, field, name, arm, w, minus_digest=False):
        return [(r['wall_ns'] - ((r.get('zeebra') or {}).get('basis_m33_ns') or 0 if minus_digest else 0)) / MS
                for r in self.cell(track, field, name, arm, w)]

    def by_rep(self, track, field, name, arm, w):
        return {(r['job'], r['rep']): r['wall_ns'] / MS for r in self.cell(track, field, name, arm, w)}

    def paired(self, track, field, name, arm_a, arm_b, w):
        ratios = bs.paired_ratios(self.by_rep(track, field, name, arm_a, w), self.by_rep(track, field, name, arm_b, w))
        return bs.paired_ratio(ratios, seed=f'{track}/{field}/{name}/{w}/{arm_a}/{arm_b}') if ratios else None


def ratio(a, b, seed):
    return bs.independent_ratio(a, b, seed=seed) if a and b else None


def fmt(ci):
    return '—' if ci is None else f'{ci.median:.3f} [{ci.lo:.3f}, {ci.hi:.3f}]'


def med(v):
    return f'{statistics.median(v):,.1f}' if v else '—'


def verdict(ci, extended, anomaly=False, small=False):
    if ci is None:
        return None
    # Only a row that could score gets the n = 12 extension (README predeclaration).
    return bs.win_verdict(ci, extended=extended or anomaly or small, anomaly=anomaly, small=small)


def vtext(v):
    return 'no data' if v is None else v.outcome + (' (extend)' if v.extend else '')


def row_name(field, name):
    return f'{name} / {F[field]}'


def sessions_table(recs, sessions, meta):
    out = ['## Sessions and contamination', '',
           '| Job | Track | Session | Of record | Attempts | ok | Contaminated | Void | Stop | Reasons |',
           '|---|---|---|---|---:|---:|---:|---|---|---|']
    for s in sessions:
        job = s['job']['job_id']
        mine = [r for r in recs if r['job'] == job]
        c = (s['stop'] or {}).get('contamination') or {}
        why = Counter(' '.join(x.split(' ')[:2]) for r in mine for x in r['reasons'])
        status = Counter(r['status'] for r in mine)
        out.append(f"| `{job}` | {s['job']['context']['track']} | {s['job']['context'].get('session')} | "
                   f"{'yes' if job in meta['of_record'] else 'no'} | {len(mine)} | {status.get('ok', 0)} | "
                   f"{c.get('contaminated', '—')}/{c.get('total', '—')} | {c.get('void', '—')} | {(s['stop'] or {}).get('reason')} | "
                   f"{', '.join(f'{k} {v}' for k, v in sorted(why.items())) or '—'} |")
    allst = Counter(r['status'] for r in recs)
    out += ['', 'Attempts by status, every job: ' + ', '.join(f'{k} {v}' for k, v in sorted(allst.items())) + '.', '']
    return out


def correctness(d, refs, all_recs):
    agree = differ = missing = 0
    bad = []
    for r in all_recs:
        if r['status'] != 'ok':
            continue
        ref = refs.get(f"{r['field']}__{r['name']}", {}).get('basis_m33')
        if not ref or not r['basis_m33']:
            missing += 1
            bad.append(f"`{r['attempt']}` {r['arm']} {r['field']}/{r['name']}: no digest")
        elif ref == r['basis_m33']:
            agree += 1
        else:
            differ += 1
            bad.append(f"`{r['attempt']}` {r['arm']} {r['field']}/{r['name']}: differs")
    out = ['## Correctness and verification', '',
           f'Every ok attempt\'s `m33-basis-v1` digest against the row\'s independent reference, every job: '
           f'**{agree} agree, {differ} differ, {missing} without a digest**. The references ran once, untimed for any '
           'verdict, on CPUs 24–39 before the sessions; their wall is the verification time, never included in a '
           'ratio (§11.6).', '',
           '| Row | Track | Set | Reference | Verification wall s | Basis size | `m33-basis-v1` | Agrees with M33-0 |',
           '|---|---|---|---|---:|---:|---|---|']
    for t in ('G', 'M'):
        for field, name in rows(t):
            v = refs.get(f'{field}__{name}', {})
            inv = v.get('invariants') or {}
            out.append(f"| {row_name(field, name)} | {t} | {set_of(t, field, name)} | {v.get('reference', '—')} | "
                       f"{v.get('wall_ms', 0) / 1e3:,.1f} | {inv.get('basis_cardinality', '—')} | "
                       f"`{(v.get('basis_m33') or 'none')[:16]}…` | {'yes' if v.get('m33_0_agrees') else 'no'} |")
    return out + [''] + [f'- {b}' for b in bad[:30]] + ([''] if bad else [])


def track_g(d):
    out = ['## Track G: Zeebra ÷ grobx 0.155.1 raw, 1 worker (equal workers)', '',
           'Median process wall, ms. Ratio = median ÷ median [95% independent bootstrap, 20,000 draws]. "−digest" '
           'subtracts Zeebra\'s in-process `basis_m33_ns` (grobx builds its basis text inside its call). Guarantees: '
           'Zeebra deterministic; grobx raw randomized and uncertified. The verdict reads F3 `sigf4`.', '',
           '| Row | Set | grobx | F0 sig | F3 sig | **F3 sig ÷ grobx** | −digest | F3 entry ÷ grobx | F0 sig ÷ grobx | '
           'Verdict | F3 ÷ F0 sig (paired) |', '|---|---|---:|---:|---:|---:|---:|---:|---:|---|---:|']
    verdicts = {}
    for field, name in rows('G'):
        c = d.walls('G', field, name, 'grobx155', 1)
        z = d.walls('G', field, name, 'sigf4', 1)
        seed = f'G/{field}/{name}/1'
        ci = ratio(z, c, seed + '/sigf4')
        small = bool(c and statistics.median(c) < FLOOR_MS)
        v = verdict(ci, ('G', field, name, 1) in d.ext, small=small)
        verdicts[field, name] = (ci, v)
        out.append(f"| {row_name(field, name)} | {set_of('G', field, name)} | {med(c)} | "
                   f"{med(d.walls('G', field, name, 'sigf4-f0', 1))} | {med(z)} | **{fmt(ci)}** | "
                   f"{fmt(ratio(d.walls('G', field, name, 'sigf4', 1, True), c, seed + '/sigf4-d'))} | "
                   f"{fmt(ratio(d.walls('G', field, name, 'entry', 1), c, seed + '/entry'))} | "
                   f"{fmt(ratio(d.walls('G', field, name, 'sigf4-f0', 1), c, seed + '/f0'))} | {vtext(v)} | "
                   f"{fmt(d.paired('G', field, name, 'sigf4', 'sigf4-f0', 1))} |")
    out += ['', '### Best-supported configuration (kept separate, never scoring): Zeebra entry 16 w ÷ grobx 1 w', '',
            '| Row | Set | grobx 1 w | F0 entry 16 w | F3 entry 16 w | F3 ÷ grobx | Class (BSC, not scoring) | '
            '−digest | F3 ÷ F0 (paired) |',
            '|---|---|---:|---:|---:|---:|---|---:|---:|']
    for field, name in rows('G'):
        c = d.walls('G', field, name, 'grobx155', 1)
        z = d.walls('G', field, name, 'entry16', 16)
        bsc = ratio(z, c, f'G/{field}/{name}/bsc')
        small = bool(c and statistics.median(c) < FLOOR_MS)
        out.append(f"| {row_name(field, name)} | {set_of('G', field, name)} | {med(c)} | "
                   f"{med(d.walls('G', field, name, 'entry16-f0', 16))} | {med(z)} | "
                   f"{fmt(bsc)} | {vtext(verdict(bsc, True, small=small))} | "
                   f"{fmt(ratio(d.walls('G', field, name, 'entry16', 16, True), c, f'G/{field}/{name}/bsc-d'))} | "
                   f"{fmt(d.paired('G', field, name, 'entry16', 'entry16-f0', 16))} |")
    out += ['', '### Reference rows (kept separate): groebner-rs verified and grobx certified, 1 worker', '',
            '| Row | groebner-rs | F3 sig ÷ groebner-rs | grobx certified | F3 sig ÷ grobx certified | '
            'grobx certified attempts |', '|---|---:|---:|---:|---:|---|']
    for field, name in rows('G'):
        g = d.walls('G', field, name, 'groebner-rs', 1)
        z = d.walls('G', field, name, 'sigf4', 1)
        cert = d.walls('Gc', field, name, 'grobx155-certified', 1)
        allc = Counter(r['status'] for r in d.recs if r['track'] == 'Gc' and (r['field'], r['name']) == (field, name))
        out.append(f"| {row_name(field, name)} | {med(g)} | {fmt(ratio(z, g, f'G/{field}/{name}/grs'))} | {med(cert)} | "
                   f"{fmt(ratio(z, cert, f'G/{field}/{name}/cert'))} | "
                   f"{', '.join(f'{k} {v}' for k, v in sorted(allc.items())) or 'not run (primary only)'} |")
    return out + [''], verdicts


def msolve_by_workers(d, field, name):
    return {w: d.walls('M', field, name, 'msolve', w) for w in (1, 4, 8, 16)}


def track_m(d):
    out = ['## Track M: Zeebra (default dispatch) ÷ msolve 0.11.0, equal workers', '',
           'msolve writes its basis to stdout inside its wall. "anomalous": msolve\'s median exceeds 1.10× its own best '
           'over {1, 4, 8, 16} in this session (§8.4); a win there is reported as one against an msolve scaling '
           'anomaly and does not score T-M. Both solvers are exact and deterministic.', '',
           '| Row | Set | w | msolve | F0 | F3 | **F3 ÷ msolve** | −digest | msolve anomalous | Verdict | F0 ÷ msolve | '
           'F3 ÷ F0 (paired) |', '|---|---|---:|---:|---:|---:|---:|---:|---|---|---:|---:|']
    verdicts = {}
    for field, name in rows('M'):
        ms = msolve_by_workers(d, field, name)
        for w in (1, 4, 8, 16):
            c, z = ms[w], d.walls('M', field, name, 'entry', w)
            ci = ratio(z, c, f'M/{field}/{name}/{w}')
            anom = bool(all(ms.values()) and bs.msolve_anomaly(ms, w))
            small = bool(c and z and min(statistics.median(c), statistics.median(z)) < FLOOR_MS)
            v = verdict(ci, ('M', field, name, w) in d.ext, anom, small)
            verdicts[field, name, w] = (ci, v)
            out.append(f"| {row_name(field, name)} | {set_of('M', field, name)} | {w} | {med(c)} | "
                       f"{med(d.walls('M', field, name, 'entry-f0', w))} | {med(z)} | **{fmt(ci)}** | "
                       f"{fmt(ratio(d.walls('M', field, name, 'entry', w, True), c, f'M/{field}/{name}/{w}/d'))} | "
                       f"{'yes' if anom else 'no'} | {vtext(v)} | "
                       f"{fmt(ratio(d.walls('M', field, name, 'entry-f0', w), c, f'M/{field}/{name}/{w}/f0'))} | "
                       f"{fmt(d.paired('M', field, name, 'entry', 'entry-f0', w))} |")
    return out + [''], verdicts


def gate_d(gv, mv):
    """§8.4 confirmation: a development win again here, and each held-out row of the track at the same
    worker count no worse than the development ratio + 0.15."""
    out = ['## Gate D confirmation (§8.4)', '',
           'A development-row win scores T-G or T-M only if it wins again in this session **and** each of that '
           'track\'s held-out rows, at the same worker count, reads no worse than the development ratio + 0.15. '
           'Held-out rows are shown whether or not they win.', '',
           '| Track | Development row | w | Ratio here | Verdict here | Held-out row | Held-out ratio | Bar (dev + 0.15) | '
           'Within bar | Held-out verdict |', '|---|---|---:|---:|---|---|---:|---:|---|---|']
    result = {}
    for track, vs in (('G', {(f, n, 1): v for (f, n), v in gv.items()}), ('M', mv)):
        held = ROWS[track]['held-out']
        for (field, name, w), (ci, v) in sorted(vs.items()):
            if (field, name) not in ROWS[track]['development']:
                continue
            within = []
            for hf, hn in held:
                hci, hv = vs.get((hf, hn, w), (None, None))
                ok = hci is not None and ci is not None and hci.median <= ci.median + TOLERANCE
                within.append(ok)
                out.append(f"| {track} | {row_name(field, name)} | {w} | {fmt(ci)} | {vtext(v)} | {row_name(hf, hn)} | "
                           f"{fmt(hci)} | {'—' if ci is None else f'{ci.median + TOLERANCE:.3f}'} | "
                           f"{'yes' if ok else 'no'} | {vtext(hv)} |")
            result[track, field, name, w] = (v is not None and v.outcome == 'win', all(within))
    return out + [''], result


def scaling(d):
    out = ['## Track M scaling', '', 'Median process wall (ms) per worker count; speedup = 1 w ÷ w w. S-3 asks '
           'whether F3\'s 4 → 16 speedup on the Track M primary improves by ≥ 15% against F0\'s.', '',
           '| Row | Solver | 1 w | 4 w | 8 w | 16 w | 4→16 speedup |', '|---|---|---:|---:|---:|---:|---:|']
    s3 = {}
    for field, name in rows('M'):
        for arm, label in (('entry-f0', 'Zeebra F0'), ('entry', 'Zeebra F3'), ('msolve', 'msolve')):
            m = {w: d.walls('M', field, name, arm, w) for w in (1, 4, 8, 16)}
            sp = statistics.median(m[4]) / statistics.median(m[16]) if m[4] and m[16] else None
            s3[field, name, arm] = sp
            out.append(f"| {row_name(field, name)} | {label} | " + ' | '.join(med(m[w]) for w in (1, 4, 8, 16)) +
                       f" | {'—' if sp is None else f'{sp:.2f}×'} |")
    return out + [''], s3


def stages(d):
    out = ['## Zeebra stage clocks (median ms, F3 and F0)', '',
           'The signature route reports its four stages; the dispatch entry reports its route and call time. '
           '"rest" is process wall − call − digest (exec, input, teardown).', '',
           '| Track | Row | Arm | w | Route | process | call | digest | rest | bookkeeping | symbolic | elimination | '
           'interreduction |', '|---|---|---|---:|---|---:|---:|---:|---:|---:|---:|---:|---:|']
    cells = sorted({(r['track'], r['field'], r['name'], r['arm'], r['workers']) for r in d.recs if r.get('zeebra')})
    for track, field, name, arm, w in cells:
        rs = d.cell(track, field, name, arm, w)
        if not rs:
            continue
        m = lambda f: statistics.median(f(r) for r in rs) / MS  # noqa: E731
        st = lambda k: f"{m(lambda r: r['zeebra']['stages'][k]):,.1f}" \
            if all((r['zeebra'].get('stages') or {}).get(k) is not None for r in rs) else '—'  # noqa: E731
        z = rs[0]['zeebra']
        rest = m(lambda r: r['wall_ns'] - (r['zeebra']['call_ns'] or 0) - (r['zeebra']['basis_m33_ns'] or 0))
        out.append(f"| {track} | {row_name(field, name)} | {arm} | {w} | {z.get('route') or '—'} | "
                   f"{m(lambda r: r['wall_ns']):,.1f} | {m(lambda r: r['zeebra']['call_ns'] or 0):,.1f} | "
                   f"{m(lambda r: r['zeebra']['basis_m33_ns'] or 0):,.1f} | {rest:,.1f} | {st('bookkeeping_ns')} | "
                   f"{st('symbolic_ns')} | {st('elimination_ns')} | {st('interreduction_ns')} |")
    return out + ['']


def memory(d, threads):
    out = ['## Peak RSS and observed threads', '',
           'Peak RSS: median of `wait4` maxima over the timed attempts, MiB. Competitor figures are the guarded child '
           'tree\'s maximum, an upper bound (#990). Threads: one census-sampled attempt per arm and cell after the '
           'session (`campaign.py threads`); `active` gained a CPU tick, `concurrent` is the most within one 50 ms '
           'interval. Both are lower bounds; CPU ÷ wall is the robust evidence of parallel work.', '',
           '| Track | Row | Arm | w | peak RSS MiB | ÷ F0 | ÷ competitor | CPU ÷ wall | threads active | concurrent |',
           '|---|---|---|---:|---:|---:|---:|---:|---:|---:|']
    th = {(t['track'], t['instance'], t['arm'], t['workers']): t for t in threads}
    rss = lambda rs: statistics.median(r['peak_rss_bytes'] for r in rs) / 2**20 if rs else None  # noqa: E731
    cells = sorted({(r['track'], r['field'], r['name'], r['arm'], r['workers']) for r in d.recs})
    for track, field, name, arm, w in cells:
        rs = d.cell(track, field, name, arm, w)
        t = th.get((track, f'{field}/{name}', arm, w), {})
        mine = rss(rs)
        f0 = rss(d.cell(track, field, name, arm + '-f0', w)) if not arm.endswith('-f0') and rs and rs[0].get('zeebra') else None
        comp = {'G': 'grobx155', 'M': 'msolve'}.get(track)
        cw = 1 if track == 'G' else w
        c = rss(d.cell(track, field, name, comp, cw)) if comp and rs and rs[0].get('zeebra') else None
        out.append(f"| {track} | {row_name(field, name)} | {arm} | {w} | {'—' if mine is None else f'{mine:,.0f}'} | "
                   f"{'—' if not (mine and f0) else f'{mine / f0:.3f}'} | {'—' if not (mine and c) else f'{mine / c:.2f}'} | "
                   f"{'—' if not rs else '{:.2f}'.format(statistics.median(r['cpu_s'] * 1e9 / r['wall_ns'] for r in rs))} | "
                   f"{t.get('active', '—')} | {t.get('concurrent', '—')} |")
    return out + ['']


def render():
    recs, sessions, meta, refs, threads = load()
    ctx = {s['job']['job_id']: s['job']['context'].get('session') for s in sessions}
    for r in recs:
        r['session'] = ctx[r['job']]
    main = [r for r in recs if r['job'] in meta['of_record']]
    d = Data(main, refs)
    lines = ['# #975 M33-I: publication campaign tables', '',
             'Generated by `summarize.py` from the retained records in this directory; do not edit by hand. '
             'Publication mode (exclusive benchlock, CCDs 1–2 reserved, CPUs 8–23, siblings idle). Every table below '
             'reads only the sessions of record (`sessions.json`) and their extensions; the session table lists every '
             'job.', '']
    gt, gv = track_g(d)
    mt, mv = track_m(d)
    gd, _ = gate_d(gv, mv)
    sc, _ = scaling(d)
    for part in (sessions_table(recs, sessions, meta), correctness(d, refs, recs), gt, mt, gd, sc, stages(d),
                 memory(d, threads)):
        lines += part
    return '\n'.join(lines).rstrip() + '\n'


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--check', action='store_true')
    args = p.parse_args()
    text = render()
    if args.check:
        same = (HERE / 'tables.md').read_text() == text
        print('tables.md is current' if same else 'tables.md is stale')
        return 0 if same else 1
    (HERE / 'tables.md').write_text(text)
    return 0


if __name__ == '__main__':
    sys.exit(main())
