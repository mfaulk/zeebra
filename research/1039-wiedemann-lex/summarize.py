#!/usr/bin/env python3
"""`tables.md` and the #1039 verdict from committed records (deciding `records-*.jsonl.gz`, or
development `probe-*.jsonl` with `--dev`).

    summarize.py [--dev] [FILES...] > tables.md

Per row: the median process wall of each arm at one worker (clean, completed attempts with the
row's agreed digest), the best Zeebra arm ÷ grobx as an independent-ratio bootstrap
(`tools/bench_stats.py`), each engine's stage split, and the adaptive rule's regret: adaptive ÷ the
faster of its two routes (classical, Wiedemann), paired per repetition.
"""
import argparse
import gzip
import json
import statistics
import sys
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1] / 'tools'))
import bench_stats as bs  # noqa: E402

GROBX = ('grobx155', 'grobx-raw')
CONVERT = ('adaptive', 'wiedemann', 'classical')


def arm_of(rec):
    arm = rec.get('arm') or rec['solver']
    return {'grobx-raw': 'grobx155', 'grobx-certified': 'grobx155-cert'}.get(arm, arm.replace('zeebra-', 'zb-'))


def load(paths, dev):
    recs = []
    for p in paths:
        opener = gzip.open if str(p).endswith('.gz') else open
        with opener(p, 'rt') as f:
            for line in f:
                r = json.loads(line)
                if dev:
                    rep = r.get('report') or {}
                    r.update(arm=arm_of(r), status='ok' if r['rc'] == 0 and r['stop'] is None else 'failed',
                             peak_rss_bytes=r['peak'], contaminated=False,
                             basis_m33=r.get('basis_m33') or rep.get('basis_m33'))
                recs.append(r)
    return recs


def completed(r):
    rep = r.get('report') or {}
    if r['status'] != 'ok' or r.get('contaminated') or not r.get('basis_m33'):
        return False
    return r['arm'].startswith('grobx') or rep.get('status') == 'complete'


def ms(ns):
    return f'{ns / 1e6:,.1f}' if ns is not None else '—'


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('files', nargs='*')
    p.add_argument('--dev', action='store_true')
    a = p.parse_args()
    files = a.files or sorted(HERE.glob('records-*.jsonl.gz'))
    recs = load(files, a.dev)
    rows = defaultdict(list)
    for r in recs:
        rows[r['row']].append(r)
    print('| Row | D | grobx route | grobx ms | best Zeebra arm | Zeebra ms | Zeebra ÷ grobx [95%] | adaptive route | regret [95%] | digests |')
    print('|---|---|---|---|---|---|---|---|---|---|')
    stages = []
    for row, rs in rows.items():
        one = [r for r in rs if r['workers'] == 1]
        digests = {r['basis_m33'] for r in one if completed(r)}
        walls = defaultdict(dict)
        failures = defaultdict(list)
        for r in one:
            if completed(r) and len(digests) == 1:
                walls[r['arm']][r['rep']] = r['wall_ns']
            else:
                failures[r['arm']].append((r.get('report') or {}).get('status') or r['status'])
        g = walls.get('grobx155', {})
        zb = {k: v for k, v in walls.items() if k.startswith('zb-') and k != 'zb-probe'}
        best = min(zb, key=lambda k: statistics.median(zb[k].values())) if zb else None
        gr = next((r for r in one if r['arm'] == 'grobx155' and r.get('stages')), None)
        groute = '—'
        if gr:
            st = gr['stages']
            groute = 'FGLM' if 'change' in (st.get('fglm_verdicts') or []) else ('F4-lex' if st.get('lex_s') else '?')
        ad = next((r['report'] for r in one if r['arm'] == 'zb-adaptive' and completed(r)), {})
        ratio = '—'
        if g and best:
            ci = bs.independent_ratio(list(zb[best].values()), list(g.values()), seed=f'{row} {best} grobx')
            ratio = f'{ci.median:.2f} [{ci.lo:.2f}, {ci.hi:.2f}] n={ci.n}/{ci.n_ref}'
        regret = '—'
        routes = [walls[k] for k in ('zb-classical', 'zb-wiedemann') if walls.get(k)]
        if walls.get('zb-adaptive') and routes:
            fastest = min(routes, key=lambda w: statistics.median(w.values()))
            rs_ = bs.paired_ratios(walls['zb-adaptive'], fastest)
            if rs_:
                ci = bs.paired_ratio(rs_, seed=f'{row} regret')
                regret = f'{ci.median:.2f} [{ci.lo:.2f}, {ci.hi:.2f}]'
        fail = '; '.join(f'{k}: {",".join(sorted(set(v)))}' for k, v in failures.items())
        print(f'| {row} | {ad.get("dimension", "—")} | {groute} | {ms(statistics.median(g.values())) if g else "—"} '
              f'| {best or "—"} | {ms(statistics.median(zb[best].values())) if best else "—"} | {ratio} '
              f'| {ad.get("route", "—")}{"/" + ad["fallback"] if ad.get("fallback") else ""} | {regret} '
              f'| {len(digests)}{" (" + fail + ")" if fail else ""} |')
        for arm in sorted(walls):
            attempts = [r for r in one if r['arm'] == arm and completed(r)]
            if arm.startswith('grobx'):
                st = attempts[0]['stages']
                stages.append((row, arm, statistics.median(walls[arm].values()),
                               f'grevlex {st["grevlex_s"] * 1e3:,.1f}; FGLM {st["fglm_s"] * 1e3:,.1f}; lex F4 {st["lex_s"] * 1e3:,.1f}',
                               max(r['peak_rss_bytes'] or 0 for r in attempts)))
            else:
                med = lambda k: statistics.median(r['report'].get(k) or 0 for r in attempts)
                text = f'F4 {ms(med("f4_ns"))}'
                if attempts[0]['report'].get('dimension') is not None:
                    text += (f'; operators {ms(med("operator_ns"))}; sequence {ms(med("sequence_ns"))}; '
                             f'reconstruction {ms(med("reconstruction_ns"))}; certificate {ms(med("certificate_ns"))}; '
                             f'classical walk {ms(med("classical_walk_ns"))}; attempts {attempts[0]["report"].get("attempts")}')
                stages.append((row, arm, statistics.median(walls[arm].values()), text,
                               max(r['peak_rss_bytes'] or 0 for r in attempts)))
    print('\n| Row | Arm | median ms | stages (ms, medians) | peak RSS MiB |')
    print('|---|---|---|---|---|')
    for row, arm, wall, text, rss in stages:
        print(f'| {row} | {arm} | {ms(wall)} | {text} | {rss / 2**20:,.0f} |')


if __name__ == '__main__':
    main()
