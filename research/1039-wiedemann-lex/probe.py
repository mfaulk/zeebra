#!/usr/bin/env python3
"""#1039 development probe: Zeebra's complete lex pipeline arms against pinned grobx's lex route.

    probe.py --pipeline BIN --grobx BIN --rows wd-4-10,katsura-12 [--modulus 65537]
             [--arms grobx,grobx-f4lex,adaptive,classical,direct-lex] [--workers 1] [--reps 3]
             [--wall-s 600] [--rss-gib 16] [--cpus 8-23] [--out records.jsonl]

Development mode only (`docs/guide/benchmarking.md`): it decides nothing; the deciding read is the
bench-job publication run (`campaign.py`). Each record holds process wall, peak RSS, the
`m33-basis-v1` digest of the lex basis, Zeebra's per-stage clocks, and grobx's own stage split
(grevlex runs, FGLM change, lex F4 runs) parsed from its call report by `grobx_stages`.
"""
import argparse
import json
import os
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'research/m33-baseline'))
sys.path.insert(0, str(ROOT / 'tools/external'))
import admission  # noqa: E402

ZEEBRA_ARMS = ('adaptive', 'wiedemann', 'classical', 'shape', 'direct-lex', 'probe')


def case_for(pipeline, row, modulus):
    r = admission.guarded([pipeline, '--family', row, '--modulus', str(modulus), '--input-only'], 60)
    assert r['rc'] == 0, r['stderr']
    return json.loads(r['stdout'])


def grobx_request(case, mode, wall_s, rss_bytes, lex_route='auto'):
    return dict(variables=case['variables'], modulus=int(case['modulus']), order='lex', workers=1,
                generators=case['generators'], mode=mode, wall_ns=wall_s * 10**9, rss_bytes=rss_bytes,
                lex_route=lex_route)


def grobx_stages(report):
    """grobx's lex route from its call report: seconds in grevlex runs, in the FGLM change, and in
    lex runs, plus the FGLM verdicts (`change`, `overflow`, or a refusal that sends it to lex F4)."""
    out = dict(grevlex_s=0.0, lex_s=0.0, fglm_s=0.0, fglm_verdicts=[], staircase=None, runs=[])
    order = {}
    for line in report.splitlines():
        f = dict(kv.split('=', 1) for kv in line.split()[2:] if '=' in kv)
        kind = line.split()[1] if len(line.split()) > 1 else ''
        if kind == 'run':
            order[f.get('number')] = f.get('order')
            out['runs'].append(dict(order=f.get('order'), engine=f.get('engine'), why=f.get('why'),
                                    reduce=f.get('reduce')))
        elif kind == 'ran':
            key = 'lex_s' if order.get(f.get('number')) in ('lex', 'block') else 'grevlex_s'
            out[key] += float(f.get('time', 0))
        elif kind == 'fglm':
            out['fglm_verdicts'].append(f.get('verdict'))
            out['fglm_s'] += float(f.get('find', 0)) + float(f.get('change', 0))
            if 'staircase' in f:
                out['staircase'] = int(f['staircase'])
    return out


def grobx_digest(stdout, case, mode):
    try:
        return admission.grobx_digest(stdout, case, mode)
    except (ValueError, json.JSONDecodeError):
        return None


def run_grobx(binary, case, mode, wall_s, rss_bytes, scratch, lex_route='auto'):
    """`lex_route='f4'` forces grobx's F4-lex route through the exact-lex block order (#1127)."""
    path = scratch / f'{case["name"]}.grobx-{mode}-{lex_route}.json'
    path.write_text(json.dumps(grobx_request(case, mode, wall_s, rss_bytes, lex_route)))
    r = admission.guarded([binary, str(path)], wall_s + 5)
    raw = json.loads(r['stdout']) if r['rc'] == 0 and r['stdout'].strip() else {}
    solver = f'grobx-{mode}' + ('-f4lex' if lex_route == 'f4' else '')
    rec = dict(solver=solver, lex_route=raw.get('lex_route'), grobx_order=raw.get('grobx_order'), workers=1, wall_ns=r['wall_ns'], peak=r['peak'], stop=r['stop'],
               rc=r['rc'], stopped=raw.get('stopped'), certified=raw.get('certified'),
               solve_ns=raw.get('solve_ns'), basis_m33=grobx_digest(r['stdout'] if r['rc'] == 0 else '', case, mode),
               stages=grobx_stages(raw.get('report') or ''))
    if r['rc'] != 0:
        rec['stderr'] = r['stderr'][-500:]
    return rec


def run_zeebra(binary, case, arm, workers, wall_s, scratch, budget='lifted'):
    path = scratch / f'{case["name"]}.case.json'
    path.write_text(json.dumps(case))
    r = admission.guarded([binary, '--input', str(path), '--arm', arm, '--workers', str(workers),
                           '--wall-s', str(wall_s), '--budget', budget], wall_s + 5)
    report = json.loads(r['stdout']) if r['rc'] == 0 and r['stdout'].strip() else {}
    rec = dict(solver=f'zeebra-{arm}', budget=budget, workers=workers, wall_ns=r['wall_ns'], peak=r['peak'],
               stop=r['stop'], rc=r['rc'], report=report)
    if r['rc'] != 0:
        rec['stderr'] = r['stderr'][-500:]
    return rec


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--pipeline', required=True)
    p.add_argument('--grobx', default='/buildcache/cargo-target/zeebra-1029-grobx/release/grobx-driver')
    p.add_argument('--rows', required=True)
    p.add_argument('--modulus', type=int, default=65537)
    p.add_argument('--arms', default='grobx,adaptive,classical,direct-lex')
    p.add_argument('--workers', type=int, nargs='*', default=[1])
    p.add_argument('--reps', type=int, default=1)
    p.add_argument('--wall-s', type=int, default=600)
    p.add_argument('--rss-gib', type=int, default=16)
    p.add_argument('--cpus', default='8-23')
    p.add_argument('--budget', default='lifted')
    p.add_argument('--out', type=Path)
    a = p.parse_args()
    admission.CAP_BYTES = a.rss_gib * 2**30
    first = int(re.split('[-,]', a.cpus)[0])
    admission.CPUS = str(first)
    scratch = Path(os.environ['TMPDIR'], 'probe-1039')
    scratch.mkdir(parents=True, exist_ok=True)
    out = a.out.open('a') if a.out else sys.stdout
    arms = a.arms.split(',')
    for row in a.rows.split(','):
        case = case_for(a.pipeline, row, a.modulus)
        for rep in range(a.reps):
            for arm in arms:
                if arm.startswith('grobx'):
                    admission.CPUS = str(first)
                    mode = 'certified' if arm.startswith('grobx-certified') else 'raw'
                    route = 'f4' if arm.endswith('-f4lex') else 'auto'
                    rec = run_grobx(a.grobx, case, mode, a.wall_s, admission.CAP_BYTES, scratch, route)
                    recs = [rec]
                else:
                    assert arm in ZEEBRA_ARMS, arm
                    recs = []
                    for w in a.workers:
                        admission.CPUS = str(first) if w == 1 else f'{first}-{first + w - 1}'
                        recs.append(run_zeebra(a.pipeline, case, arm, w, a.wall_s, scratch, a.budget))
                for rec in recs:
                    rec.update(row=row, rep=rep, input_digest=case['digest'], modulus=a.modulus,
                               mode='dev', cpus=admission.CPUS)
                    out.write(json.dumps(rec, sort_keys=True) + '\n')
                    out.flush()


if __name__ == '__main__':
    os.environ.setdefault('TMPDIR', '/buildcache/cargo-target/zeebra-1039/tmp')
    main()
