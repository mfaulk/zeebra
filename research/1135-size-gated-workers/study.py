#!/usr/bin/env python3
"""#1135: a size-gated worker count for `GradedEngine::Adaptive`, laptop stage.

The gate is fixed in GATE and bezout_bound before any fresh row is timed: one worker when the
Bezout number of the least-degree generators is below 2^11, the caller's workers at or above it.

  study.py dev                      the gate on Gate H's development records -> dev.md
  study.py catalog                  the fresh rows -> catalog.json, predictions.md
  study.py run --bin M34_MATRIX     timed attempts -> attempts.jsonl
  study.py summarize [--check]      attempts.jsonl.gz -> tables.md
"""
import argparse
import collections
import gzip
import json
import math
import os
import statistics
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'tools'))

# Predeclared (docs/research/1135-size-gated-workers.md §3). Do not move after the read.
GATE = 2 ** 11
BAND_MS = (100.0, 300_000.0)
TOLERANCE = 1.10
AGREE_SHARE = 0.80
WORST_REGRET = 1.25
WMAX = 10
REPS = 5
WALL_S = 120

GATE_H = ROOT / 'research' / 'm34-gate-h' / 'results'
CATALOGS = [ROOT / 'research' / 'm34-public-corpus' / 'catalog.json',
            ROOT / 'research' / 'm34-structural-corpus' / 'catalog.json']


def degree(equation):
    terms = [t for t in equation if any(int(c) for c in t['coefficient'])]
    return max((sum(t['exponents']) for t in terms), default=None)


def bezout_bound(record):
    """Product of the min(m, n) least generator degrees, n the variables that appear.

    0 for a nonzero constant generator (the unit ideal). Linear generators contribute 1."""
    n = len(record['variables'])
    used = [False] * n
    degrees = []
    for equation in record['equations']:
        d = degree(equation)
        if d is None:
            continue
        degrees.append(d)
        for t in equation:
            if any(int(c) for c in t['coefficient']):
                for k, e in enumerate(t['exponents']):
                    used[k] |= e > 0
    if 0 in degrees:
        return 0
    return math.prod(sorted(degrees)[:sum(used)])


def gate(record):
    return bezout_bound(record) >= GATE


def medians(attempts):
    walls = collections.defaultdict(list)
    for a in attempts:
        if a['status'] == 'complete':
            walls[(a['row'], a['workers'])].append(a['wall_ms'])
    return {k: statistics.median(v) for k, v in walls.items()}


def in_band(w1_ms, wmax_ms):
    faster = min(w1_ms, wmax_ms)
    return BAND_MS[0] <= faster <= BAND_MS[1]


def agrees(gate_open, w1_ms, wmax_ms):
    chosen, other = (wmax_ms, w1_ms) if gate_open else (w1_ms, wmax_ms)
    return chosen <= TOLERANCE * other


def verdict(rows):
    """rows: dicts with row, gate, w1, wmax (medians in ms), all in band."""
    def regret(r, arm):
        best = min(r['w1'], r['wmax'])
        pick = {'gate': r['wmax'] if r['gate'] else r['w1'], 'w1': r['w1'], 'wmax': r['wmax']}[arm]
        return pick / best
    geo = {arm: math.exp(statistics.mean(math.log(regret(r, arm)) for r in rows))
           for arm in ('gate', 'w1', 'wmax')}
    worst_row = max(rows, key=lambda r: regret(r, 'gate'))
    worst = (regret(worst_row, 'gate'), worst_row['row'])
    agree = sum(agrees(r['gate'], r['w1'], r['wmax']) for r in rows)
    supported = agree >= AGREE_SHARE * len(rows) and worst[0] <= WORST_REGRET
    return dict(agree=agree, scored=len(rows), worst=worst, geo_regret=geo, supported=supported)


# --- development re-read -------------------------------------------------------------------------

def catalog_records(paths):
    out = {}
    for p in paths:
        for r in json.loads(Path(p).read_text()):
            out[r['id']] = r
    return out


def dev():
    records = catalog_records(CATALOGS)
    walls = collections.defaultdict(list)
    for line in open(GATE_H / 'attempts.jsonl'):
        a = json.loads(line)
        if a['config'] in ('P8-w1', 'P8-w16') and a['status'].startswith('completed') \
                and not a['contaminated']:
            walls[(a['record'], a['config'])].append(a['wall_ms'])
    rows = []
    for rid in sorted({r for r, _ in walls}):
        w1, w16 = walls.get((rid, 'P8-w1')), walls.get((rid, 'P8-w16'))
        if w1 and w16:
            b = bezout_bound(records[rid])
            rows.append(dict(row=rid, gate=b >= GATE, bezout=b,
                             w1=statistics.median(w1), wmax=statistics.median(w16)))
    rows.sort(key=lambda r: r['w1'])
    lines = ['# #1135 development re-read: the gate on Gate H\'s P8 cells', '',
             'Re-reads `research/m34-gate-h/results/attempts.jsonl` (tag `measured/1012-matrix`, bench',
             'host, 16 workers). Medians of clean completed repetitions of process wall, in ms. These rows',
             'fitted the gate; they are not evidence for it.', '']
    for title, subset in [('All development records with both cells', rows),
                          ('Records in the 100 ms - 300 s band', [r for r in rows if in_band(r['w1'], r['wmax'])])]:
        v = verdict(subset)
        lines += [f'## {title} ({len(subset)})', '',
                  f'- gate agrees (10% tolerance): {v["agree"]} of {v["scored"]}',
                  f'- worst regret under the gate: {v["worst"][0]:.2f} (`{v["worst"][1]}`)',
                  '- geometric-mean regret: ' + ', '.join(f'{k} {x:.3f}' for k, x in v['geo_regret'].items()),
                  '']
    lines += ['| record | Bezout | gate | P8-w1 | P8-w16 | w1 / w16 | agrees |',
              '|---|---:|:-:|---:|---:|---:|:-:|']
    for r in rows:
        lines.append(f'| `{r["row"]}` | {r["bezout"]:,} | {"16" if r["gate"] else "1"} | {r["w1"]:,.1f} | '
                     f'{r["wmax"]:,.1f} | {r["w1"] / r["wmax"]:.2f} | '
                     f'{"yes" if agrees(r["gate"], r["w1"], r["wmax"]) else "**no**"} |')
    (HERE / 'dev.md').write_text('\n'.join(lines) + '\n')


# --- fresh rows ----------------------------------------------------------------------------------

def fresh_problems():
    import m34_structural_corpus as sc
    col = 'zb/graph-3colouring'
    return [
        *[sc.P(f'zb-{name}-{n}', name, name=name, n=n) for name, n in [
            ('katsura', 10), ('katsura', 11), ('katsura', 13), ('eco', 10), ('eco', 11),
            ('eco', 13), ('cyclic', 8), ('noon', 8), ('noon', 9), ('reimer', 7)]],
        sc.P('zb-col-grid-4x6', col, graph_kind='grid', rows=4, cols=6, count_colourings=False),
        sc.P('zb-col-gnm-16-28-s1', col, 1, graph_kind='gnm', n=16, m=28, count_colourings=False),
        sc.P('zb-col-ktree2-16-s1', col, 1, graph_kind='ktree2', n=16, count_colourings=False),
    ]


def catalog():
    import m34_structural_corpus as sc
    records = [sc.record(p, sc.build(p), 'p31') for p in fresh_problems()]
    (HERE / 'catalog.json').write_text(sc.dump_catalog(records) if hasattr(sc, 'dump_catalog') else
                                       '[\n' + ',\n'.join(json.dumps(r, sort_keys=True, separators=(',', ':'))
                                                          for r in records) + '\n]\n')
    lines = ['| row | variables | generators | Bezout | gate predicts |', '|---|---:|---:|---:|:-:|']
    for r in records:
        b = bezout_bound(r)
        lines.append(f'| `{r["id"]}` | {len(r["variables"])} | {len(r["equations"])} | {b:,} | '
                     f'{WMAX if b >= GATE else 1} workers |')
    (HERE / 'predictions.md').write_text('\n'.join(lines) + '\n')


def run(binary, out, reps, wmax, wall_s):
    records = json.loads((HERE / 'catalog.json').read_text())
    ids = [r['id'] for r in records]
    cat = str(HERE / 'catalog.json')

    def once(rid, w):
        load = os.getloadavg()[0]
        started = time.perf_counter()
        p = subprocess.run([binary, '--catalog', cat, '--id', rid, '--engine', 'adaptive',
                            '--workers', str(w), '--wall-s', str(wall_s)],
                           capture_output=True, text=True, timeout=wall_s + 60)
        wall = (time.perf_counter() - started) * 1e3
        rec = json.loads(p.stdout) if p.returncode == 0 and p.stdout.strip() else {}
        return dict(row=rid, workers=w, wall_ms=wall, load_1m=load, rc=p.returncode,
                    status=rec.get('status', 'crashed'), route=rec.get('route'), team=rec.get('team'),
                    call_ns=rec.get('call_ns'), basis_sha256=rec.get('basis_sha256'),
                    peak_rss_bytes=rec.get('peak_rss_bytes'), error=rec.get('error'))

    once(ids[0], 1)  # warm the binary's pages; not recorded
    with open(out, 'a') as f:
        for rep in range(reps):
            for i, rid in enumerate(ids):
                arms = [1, wmax] if (rep + i) % 2 == 0 else [wmax, 1]
                for w in arms:
                    a = dict(once(rid, w), rep=rep)
                    f.write(json.dumps(a, sort_keys=True) + '\n')
                    f.flush()
                    print(f'{rep} {rid} w{w} {a["wall_ms"]:.0f} ms {a["status"]} {a["route"]} '
                          f'load {a["load_1m"]:.1f}', file=sys.stderr)


def tables():
    records = {r['id']: r for r in json.loads((HERE / 'catalog.json').read_text())}
    with gzip.open(HERE / 'attempts.jsonl.gz', 'rt') as f:
        attempts = [json.loads(line) for line in f]
    med = medians(attempts)
    wmax = max(a['workers'] for a in attempts)
    lines = ['# #1135 laptop read: tables', '',
             f'Generated by `study.py summarize` from `attempts.jsonl.gz`. Process wall, medians in ms of '
             f'the completed attempts, 1 and {wmax} workers.', '',
             f'| row | Bezout | gate | n (1 / {wmax}) | 1 w | {wmax} w | 1 w / {wmax} w | route (1 / {wmax}) '
             f'| bases agree | in band | agrees |',
             '|---|---:|:-:|:-:|---:|---:|---:|---|:-:|:-:|:-:|']
    scored, dropped = [], []
    for rid, r in records.items():
        by = {w: [a for a in attempts if a['row'] == rid and a['workers'] == w] for w in (1, wmax)}
        done = {w: [a for a in by[w] if a['status'] == 'complete'] for w in by}
        routes = ' / '.join(','.join(sorted({f'{a["route"]}@{a["team"]}' for a in by[w]})) for w in by)
        digests = {a['basis_sha256'] for w in by for a in done[w]}
        b = bezout_bound(r)
        if not done[1] or not done[wmax]:
            dropped.append((rid, 'an arm did not complete'))
            lines.append(f'| `{rid}` | {b:,} | {wmax if b >= GATE else 1} | {len(done[1])} / {len(done[wmax])} '
                         f'| - | - | - | {routes} | - | no | - |')
            continue
        w1, wm = med[(rid, 1)], med[(rid, wmax)]
        band = in_band(w1, wm)
        row = dict(row=rid, gate=b >= GATE, w1=w1, wmax=wm)
        (scored if band else dropped).append(row if band else (rid, f'faster median {min(w1, wm):.0f} ms'))
        lines.append(f'| `{rid}` | {b:,} | {wmax if b >= GATE else 1} | {len(done[1])} / {len(done[wmax])} '
                     f'| {w1:,.1f} | {wm:,.1f} | {w1 / wm:.2f} | {routes} | '
                     f'{"yes" if len(digests) == 1 else "**no**"} | {"yes" if band else "no"} | '
                     f'{("yes" if agrees(row["gate"], w1, wm) else "**no**") if band else "-"} |')
    lines.append('')
    if scored:
        v = verdict(scored)
        lines += ['## Pre-declared read', '',
                  f'- scored rows: {v["scored"]}; dropped: ' + (', '.join(f'`{d}` ({why})' for d, why in dropped) or 'none'),
                  f'- gate agrees (within {TOLERANCE - 1:.0%}): {v["agree"]} of {v["scored"]} '
                  f'(criterion >= {AGREE_SHARE:.0%})',
                  f'- worst regret under the gate: {v["worst"][0]:.2f} (`{v["worst"][1]}`; criterion <= {WORST_REGRET})',
                  '- geometric-mean regret: ' + ', '.join(f'{k} {x:.3f}' for k, x in v['geo_regret'].items()),
                  f'- **{"supported" if v["supported"] else "not supported"}**', '']
    loads = [a['load_1m'] for a in attempts]
    lines += [f'1-minute load at attempt start: {min(loads):.1f}-{max(loads):.1f} '
              f'(median {statistics.median(loads):.1f}).']
    return '\n'.join(lines) + '\n'


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    sub.add_parser('dev')
    sub.add_parser('catalog')
    r = sub.add_parser('run')
    r.add_argument('--bin', required=True)
    r.add_argument('--out', default=str(HERE / 'attempts.jsonl'))
    r.add_argument('--reps', type=int, default=REPS)
    r.add_argument('--wmax', type=int, default=WMAX)
    r.add_argument('--wall-s', type=int, default=WALL_S)
    s = sub.add_parser('summarize')
    s.add_argument('--check', action='store_true')
    a = ap.parse_args()
    if a.cmd == 'dev':
        dev()
    elif a.cmd == 'catalog':
        catalog()
    elif a.cmd == 'run':
        run(a.bin, a.out, a.reps, a.wmax, a.wall_s)
    else:
        text = tables()
        if a.check:
            if (HERE / 'tables.md').read_text() != text:
                sys.exit('tables.md is stale: run study.py summarize')
        else:
            (HERE / 'tables.md').write_text(text)


if __name__ == '__main__':
    main()
