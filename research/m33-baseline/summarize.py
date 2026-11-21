#!/usr/bin/env python3
"""Regenerate tables.md from the retained records alone (#966 Part 2).

    summarize.py [--check]      # --check: exit 1 if tables.md differs from what the records give

Inputs, all committed beside this script: records-*.jsonl.gz and their *.session.json (one per
bench-job, from `campaign.py extract`), references.json and threads-*.jsonl. Contaminated and
non-ok attempts are counted and excluded from every interval (plan §11.2, §11.6).
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
sys.path.insert(0, str(HERE))
import bench_contamination as bc  # noqa: E402
import bench_stats as bs  # noqa: E402
from campaign import ROWS, rows  # noqa: E402

FLOOR_MS = 300
ZEEBRA_G = ('sigf4', 'f4', 'entry')
MS = 1e6


def load():
    recs, sessions = [], []
    for path in sorted(HERE.glob('records-*.jsonl.gz')):
        recs += [json.loads(line) for line in gzip.decompress(path.read_bytes()).decode().splitlines()]
        sessions.append(json.loads(Path(str(path).replace('.jsonl.gz', '.session.json')).read_text()))
    refs = json.loads((HERE / 'references.json').read_text()) if (HERE / 'references.json').exists() else {}
    threads = [json.loads(line) for p in sorted(HERE.glob('threads-*.jsonl')) for line in p.read_text().splitlines()]
    return recs, sessions, refs, threads


def usable(r, clean=False):
    """An ok attempt; with `clean`, also not flagged by bench-job's contamination verdict."""
    return r['status'] == 'ok' and not (clean and r['contaminated'])


def walls(recs, track, field, name, arm, workers, minus_digest=False, clean=False):
    out = []
    for r in recs:
        if (r['track'], r['field'], r['name'], r['arm'], r['workers']) == (track, field, name, arm, workers) and usable(r, clean):
            w = r['wall_ns']
            if minus_digest and r.get('zeebra'):
                w -= r['zeebra']['basis_m33_ns'] or 0
            out.append(w / MS)
    return out


def ratio(a, b, seed):
    return bs.independent_ratio(a, b, seed=seed) if a and b else None


def fmt(ci):
    return '—' if ci is None else f'{ci.median:.3f} [{ci.lo:.3f}, {ci.hi:.3f}]'


def med(v):
    return f'{statistics.median(v):,.1f}' if v else '—'


def verdict(ci, extended, anomaly=False, small=False):
    if ci is None:
        return 'no data'
    v = bs.win_verdict(ci, extended=extended, anomaly=anomaly, small=small)
    return v.outcome + (' (extend)' if v.extend else '')


def cut_to_win(z, c, seed):
    """Smallest additive cut d (ms) from every Zeebra attempt that puts the ratio's upper bound below 1."""
    if not z or not c:
        return None
    if bs.independent_ratio(z, c, seed=seed).hi < 1:
        return 0.0
    lo, hi = 0.0, max(z)
    if bs.independent_ratio([max(x - hi, 1e-9) for x in z], c, seed=seed).hi >= 1:
        return None
    for _ in range(30):
        mid = (lo + hi) / 2
        if bs.independent_ratio([x - mid for x in z], c, seed=seed, draws=4000).hi < 1:
            hi = mid
        else:
            lo = mid
    return hi


def extended_cells(recs):
    return {(r['track'], r['field'], r['name'], r['workers']) for r in recs if r.get('session') == 'extension'}


def session_table(recs, sessions):
    out = ['## Sessions and contamination', '',
           '| Job | Track | Session | Attempts | ok | Contaminated (bench-job, per cell) | Void | '
           'One session median | Per worker group | Per arm and cell | Reasons (bench-job) |',
           '|---|---|---|---:|---:|---:|---|---|---|---|---|']
    for s in sessions:
        job = s['job']['job_id']
        mine = [r for r in recs if r['job'] == job]
        judged = [r for r in mine if r.get('metrics')]
        c = (s['stop'] or {}).get('contamination') or {}
        alt = []
        for groups in (None, [r['workers'] for r in judged],
                       [f"{r['field']}/{r['name']}@{r['workers']}@{r['arm']}" for r in judged]):
            v = bc.session_verdict([r['metrics'] for r in judged], 'dev', groups)
            alt.append(f"{v['contaminated']}/{v['total']}{' void' if v['void'] else ''}")
        why = defaultdict(int)
        for r in mine:
            for x in r['reasons']:
                why[' '.join(x.split(' ')[:2])] += 1
        out.append(f"| `{job}` | {s['job']['context']['track']} | {s['job']['context'].get('session')} | {len(mine)} | "
                   f"{sum(r['status'] == 'ok' for r in mine)} | {c.get('contaminated')}/{c.get('total')} | "
                   f"{c.get('void')} | {alt[0]} | {alt[1]} | {alt[2]} | "
                   f"{', '.join(f'{k} {v}' for k, v in sorted(why.items()))} |")
    out += ['', 'The bench-job verdict judges the clock rule per cell (instance and worker count). The next three '
            'columns re-judge the same metrics, with the thresholds unchanged, against one session median, per worker '
            'count (as #965 asked), and per arm within a cell (a diagnostic: the solvers report different clocks). '
            'Failures by status: ' + ', '.join(f'{k} {v}' for k, v in sorted(_count(recs, 'status').items())) + '.', '']
    return out


def _count(recs, key):
    out = defaultdict(int)
    for r in recs:
        out[r[key]] += 1
    return out


def correctness(recs, refs):
    agree, differ, missing, bad = 0, 0, 0, []
    for r in recs:
        if r['status'] != 'ok':
            continue
        ref = refs.get(f"{r['field']}__{r['name']}", {})
        if not ref.get('basis_m33') or not r['basis_m33']:
            missing += 1
            bad.append(f"{r['attempt']} {r['arm']} missing")
        elif ref['basis_m33'] == r['basis_m33']:
            agree += 1
        else:
            differ += 1
            bad.append(f"{r['attempt']} {r['arm']} {r['field']}/{r['name']} differs")
    out = ['## Correctness', '', f'Every ok attempt\'s `m33-basis-v1` digest against the row\'s independent reference '
           f'(references.json: Singular below 2³¹, groebner-rs at one worker on wide fields): **{agree} agree, '
           f'{differ} differ, {missing} without a digest**.', '']
    out += ['| Row | Reference | `m33-basis-v1` |', '|---|---|---|']
    out += [f"| {k.replace('__', ' / ')} | {v['reference']} | `{(v['basis_m33'] or 'none')[:16]}…` |"
            for k, v in sorted(refs.items())]
    out += [''] + [f'- {b}' for b in bad[:20]] + ([''] if bad else [])
    return out


def track_g(recs):
    ext = extended_cells(recs)
    out = ['## Track G: Zeebra ÷ grobx 0.155.1 raw, 1 worker (equal workers)', '',
           'Median process wall ms; ratio median [95% independent bootstrap, 20,000 draws]. "−digest" subtracts '
           'Zeebra\'s in-process `basis_m33_ns` (grobx renders its basis text inside its call and cannot avoid it).', '',
           '| Row | Set | grobx 0.155.1 | sig 1 w | sig ÷ grobx | sig ÷ grobx −digest | entry ÷ grobx | f4 ÷ grobx | '
           'Verdict (sig) | sig ÷ grobx, rule-clean only (n) |', '|---|---|---:|---:|---:|---:|---:|---:|---|---|']
    for field, name in rows('G'):
        kind = 'dev' if (field, name) in ROWS['G']['development'] else 'control'
        c = walls(recs, 'G', field, name, 'grobx155', 1)
        z = walls(recs, 'G', field, name, 'sigf4', 1)
        seed = f'G/{field}/{name}/1'
        sig = ratio(z, c, seed + '/sigf4')
        small = bool(c and statistics.median(c) < FLOOR_MS)
        out.append(f'| {field} / {name} | {kind} | {med(c)} | {med(z)} | {fmt(sig)} | '
                   f"{fmt(ratio(walls(recs, 'G', field, name, 'sigf4', 1, True), c, seed + '/sigf4-d'))} | "
                   f"{fmt(ratio(walls(recs, 'G', field, name, 'entry', 1), c, seed + '/entry'))} | "
                   f"{fmt(ratio(walls(recs, 'G', field, name, 'f4', 1), c, seed + '/f4'))} | "
                   f"{verdict(sig, ('G', field, name, 1) in ext, small=small)} | "
                   f"{_clean(recs, 'G', field, name, 'sigf4', 'grobx155', 1, seed + '/sigf4')} |")
    out += ['', '### Best-supported configuration (kept separate): Zeebra entry at 16 w ÷ grobx 0.155.1 at 1 w', '',
            '| Row | entry 16 w | grobx 1 w | entry 16 w ÷ grobx | −digest |', '|---|---:|---:|---:|---:|']
    for field, name in rows('G'):
        c = walls(recs, 'G', field, name, 'grobx155', 1)
        z = walls(recs, 'G', field, name, 'entry16', 16)
        out.append(f"| {field} / {name} | {med(z)} | {med(c)} | {fmt(ratio(z, c, f'G/{field}/{name}/bsc'))} | "
                   f"{fmt(ratio(walls(recs, 'G', field, name, 'entry16', 16, True), c, f'G/{field}/{name}/bsc-d'))} |")
    out += ['', '### grobx 0.155.1 ÷ 0.73.3, and the groebner-rs reference row', '',
            '| Row | grobx 0.73.3 | 0.155.1 ÷ 0.73.3 | sig ÷ grobx 0.73.3 | groebner-rs | sig ÷ groebner-rs |',
            '|---|---:|---:|---:|---:|---:|']
    for field, name in rows('G'):
        old = walls(recs, 'G', field, name, 'grobx073', 1)
        new = walls(recs, 'G', field, name, 'grobx155', 1)
        g = walls(recs, 'G', field, name, 'groebner-rs', 1)
        z = walls(recs, 'G', field, name, 'sigf4', 1)
        out.append(f"| {field} / {name} | {med(old)} | {fmt(ratio(new, old, f'G/{field}/{name}/pin'))} | "
                   f"{fmt(ratio(z, old, f'G/{field}/{name}/old'))} | {med(g)} | "
                   f"{fmt(ratio(z, g, f'G/{field}/{name}/grs'))} |")
    return out + ['']


def _clean(recs, track, field, name, arm, comp, w, seed):
    z, c = (walls(recs, track, field, name, a, w, clean=True) for a in (arm, comp))
    return f'{fmt(ratio(z, c, seed))} ({len(z)}/{len(c)})'


def msolve_by_workers(recs, field, name):
    return {w: walls(recs, 'M', field, name, 'msolve', w) for w in (1, 4, 8, 16)}


def track_m(recs):
    ext = extended_cells(recs)
    out = ['## Track M: Zeebra (default dispatch) ÷ msolve 0.11.0, equal workers', '',
           'msolve writes its basis to stdout (`-o /dev/stdout`) inside its wall. "anomalous" marks a count where '
           'msolve\'s median exceeds 1.10× its own best over {1, 4, 8, 16} in this session (§8.4).', '',
           '| Row | Set | w | msolve | Zeebra | Zeebra ÷ msolve | −digest | msolve anomalous | Verdict | '
           'rule-clean only (n) |', '|---|---|---:|---:|---:|---:|---:|---|---|---|']
    for field, name in rows('M'):
        kind = 'dev' if (field, name) in ROWS['M']['development'] else 'control'
        ms = msolve_by_workers(recs, field, name)
        for w in (1, 4, 8, 16):
            c, z = ms[w], walls(recs, 'M', field, name, 'entry', w)
            ci = ratio(z, c, f'M/{field}/{name}/{w}')
            anom = bool(all(ms.values()) and bs.msolve_anomaly(ms, w))
            small = bool(c and z and min(statistics.median(c), statistics.median(z)) < FLOOR_MS)
            out.append(f"| {field} / {name} | {kind} | {w} | {med(c)} | {med(z)} | {fmt(ci)} | "
                       f"{fmt(ratio(walls(recs, 'M', field, name, 'entry', w, True), c, f'M/{field}/{name}/{w}/d'))} | "
                       f"{'yes' if anom else 'no'} | {verdict(ci, ('M', field, name, w) in ext, anom, small)} | "
                       f"{_clean(recs, 'M', field, name, 'entry', 'msolve', w, f'M/{field}/{name}/{w}')} |")
    out += ['', '### Signature route at 1 worker (H0)', '',
            '| Row | msolve 1 w | sig 1 w | sig ÷ msolve | −digest | H0 (≤ 1.25×) |', '|---|---:|---:|---:|---:|---|']
    for field, name in rows('M'):
        c, z = walls(recs, 'M', field, name, 'msolve', 1), walls(recs, 'M', field, name, 'sigf4', 1)
        ci = ratio(z, c, f'M/{field}/{name}/sig')
        h0 = '' if 'katsura-11' not in name or ci is None else ('holds' if ci.median <= 1.25 else 'falsified')
        out.append(f"| {field} / {name} | {med(c)} | {med(z)} | {fmt(ci)} | "
                   f"{fmt(ratio(walls(recs, 'M', field, name, 'sigf4', 1, True), c, f'M/{field}/{name}/sig-d'))} | {h0} |")
    return out + ['']


def replication(recs, record):
    """The headline equal-worker ratios in each session of a track, side by side."""
    cells = [('G', f, n, 'sigf4', 'grobx155', 1) for f, n in ROWS['G']['development']]
    cells += [('M', f, n, 'entry', 'msolve', w) for f, n in ROWS['M']['development'] for w in (1, 4, 8, 16)]
    names = sorted({r['session'] for r in recs if r['session'] != 'extension'})
    out = ['## Replication across sessions', '', 'The development rows\' equal-worker ratio in every session '
           '(Track G: sig ÷ grobx 0.155.1; Track M: entry ÷ msolve).', '',
           '| Track | Row | w | ' + ' | '.join(names) + ' |', '|---|---|---:|' + '---:|' * len(names)]
    for track, field, name, arm, comp, w in cells:
        cols = []
        for sname in names:
            rs = [r for r in recs if r['session'] == sname]
            cols.append(fmt(ratio(walls(rs, track, field, name, arm, w), walls(rs, track, field, name, comp, w),
                                  f'{track}/{field}/{name}/{w}/{sname}')))
        out.append(f'| {track} | {field} / {name} | {w} | ' + ' | '.join(cols) + ' |')
    return out + ['']


def stage_table(recs):
    out = ['## Stage clocks (Zeebra in-process, median ms)', '',
           '`sigf4` reports the signature engine\'s stages; the dispatch entry reports only its route, so its row '
           'splits process wall into the solve call, the digest and the rest (exec, input, teardown).', '',
           '| Track | Row | Arm | w | Route | process | call | digest | bookkeeping | symbolic | elimination | '
           'interreduction |', '|---|---|---|---:|---|---:|---:|---:|---:|---:|---:|---:|']
    cells = sorted({(r['track'], r['field'], r['name'], r['arm'], r['workers']) for r in recs if r.get('zeebra')})
    for track, field, name, arm, w in cells:
        if (field, name) not in ROWS[track]['development']:
            continue
        rs = [r for r in recs if (r['track'], r['field'], r['name'], r['arm'], r['workers']) == (track, field, name, arm, w)
              and usable(r)]
        if not rs:
            continue
        m = lambda f: f'{statistics.median(f(r) for r in rs) / MS:,.1f}'
        st = lambda k: m(lambda r: r['zeebra']['stages'][k]) if all(r['zeebra']['stages'] for r in rs) else '—'
        out.append(f"| {track} | {field} / {name} | {arm} | {w} | {rs[0]['zeebra']['route']} | {m(lambda r: r['wall_ns'])} | "
                   f"{m(lambda r: r['zeebra']['call_ns'])} | {m(lambda r: r['zeebra']['basis_m33_ns'])} | "
                   f"{st('bookkeeping_ns')} | {st('symbolic_ns')} | {st('elimination_ns')} | {st('interreduction_ns')} |")
    return out + ['']


def cost_model(recs):
    out = ['## Per-row additive cost model', '',
           'The cut *d* is the smallest time removed from every Zeebra attempt that brings the equal-worker '
           'ratio\'s 95% upper bound below 1 (bisected on the same bootstrap). "share" is *d* as a fraction of '
           'Zeebra\'s median process wall; a stage share above 100% means that stage alone cannot close the gap. '
           '"median gap" is the cut that only brings the median ratio to 1, the floor under *d*.', '',
           '| Track | Row | w | Zeebra arm | Zeebra ms | competitor ms | median gap ms | cut d ms | share of wall | '
           'd ÷ elimination | d ÷ symbolic |', '|---|---|---:|---|---:|---:|---:|---:|---:|---:|---:|']
    for field, name in ROWS['G']['development']:
        out.append(_cost_row(recs, 'G', field, name, 1, 'sigf4', walls(recs, 'G', field, name, 'grobx155', 1)))
    for field, name in ROWS['M']['development']:
        ms = msolve_by_workers(recs, field, name)
        for w in (1, 4, 8, 16):
            if all(ms.values()) and not bs.msolve_anomaly(ms, w):
                out.append(_cost_row(recs, 'M', field, name, w, 'entry', ms[w]))
    return out + ['']


def _cost_row(recs, track, field, name, w, arm, c):
    z = walls(recs, track, field, name, arm, w)
    d = cut_to_win(z, c, f'{track}/{field}/{name}/{w}/cost')
    rs = [r for r in recs if (r['track'], r['field'], r['name'], r['arm'], r['workers']) == (track, field, name, arm, w)
          and usable(r) and (r['zeebra'] or {}).get('stages')]
    stage = lambda k: statistics.median(r['zeebra']['stages'][k] for r in rs) / MS if rs else None
    share = lambda s: '—' if s is None or d is None else f'{100 * d / s:.0f}%'
    gap = f'{statistics.median(z) - statistics.median(c):,.1f}' if z and c else '—'
    return (f"| {track} | {field} / {name} | {w} | {arm} | {med(z)} | {med(c)} | {gap} | "
            f"{'—' if d is None else f'{d:,.1f}'} | {share(statistics.median(z) if z else None)} | "
            f"{share(stage('elimination_ns'))} | {share(stage('symbolic_ns'))} |")


def resources(recs, threads):
    out = ['## Peak RSS and observed threads', '',
           'Peak RSS is the kernel\'s `wait4` maximum over the timed attempts (median MiB). Threads come from one '
           'census-sampled attempt per arm and cell (`campaign.py threads`): `active` gained a CPU tick over the '
           'attempt, `concurrent` is the most that gained one within a 50 ms interval. Both are lower bounds: a '
           'thread that starts and exits between two samples is never seen, which is how Zeebra\'s per-phase '
           'workers can read as 1. CPU ÷ wall (median over the timed attempts, from `wait4`) is the robust '
           'evidence of parallel work.', '',
           '| Track | Row | Arm | w | peak RSS MiB | CPU ÷ wall | threads active | concurrent |',
           '|---|---|---|---:|---:|---:|---:|---:|']
    th = {(t['track'], t['instance'], t['arm'], t['workers']): t for t in threads}
    cells = sorted({(r['track'], r['field'], r['name'], r['arm'], r['workers']) for r in recs})
    for track, field, name, arm, w in cells:
        rs = [r for r in recs if (r['track'], r['field'], r['name'], r['arm'], r['workers'])
              == (track, field, name, arm, w) and r['status'] == 'ok']
        t = th.get((track, f'{field}/{name}', arm, w), {})
        out.append(f"| {track} | {field} / {name} | {arm} | {w} | "
                   f"{statistics.median(r['peak_rss_bytes'] for r in rs) / 2**20:,.0f} | "
                   f"{statistics.median(r['cpu_s'] * 1e9 / r['wall_ns'] for r in rs):.2f} | "
                   f"{t.get('active', '—')} | {t.get('concurrent', '—')} |"
                   if rs else f'| {track} | {field} / {name} | {arm} | {w} | — | — | — | — |')
    return out + ['']


def render():
    recs, sessions, refs, threads = load()
    for r in recs:
        r['session'] = next(s['job']['context'].get('session') for s in sessions if s['job']['job_id'] == r['job'])
    lines = ['# #966 M33-0 Part 2: baseline cohort tables', '',
             'Generated by `summarize.py` from the retained records in this directory; do not edit by hand. '
             'Dev mode, CCDs 1–2 reserved, CPUs 8–23, siblings idle: absolute walls were taken beside other '
             'sessions\' work and are not publication figures (plan §11.2).', '']
    # The re-run of a void session is the session of record (#966); the first read is kept as a replication.
    record = {t: 'rerun' if any(r['track'] == t and r['session'] == 'rerun' for r in recs) else 'baseline'
              for t in ROWS}
    main = [r for r in recs if r['session'] in (record[r['track']], 'extension')]
    lines += [f"Session of record: Track G `{record['G']}`, Track M `{record['M']}`; every table below reads only "
              "it (and any extension), except the replication table.", '']
    for part in (session_table(recs, sessions), correctness(recs, refs), track_g(main), track_m(main),
                 replication(recs, record), stage_table(main), cost_model(main), resources(main, threads)):
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
