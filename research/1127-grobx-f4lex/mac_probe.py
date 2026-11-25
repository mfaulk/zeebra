#!/usr/bin/env python3
"""#1127 Mac development probe (unpinned, no RSS, decides nothing): grobx lex auto vs forced F4-lex
vs Zeebra adaptive on #1039's class rows. One JSON line per attempt."""
import json, subprocess, sys, time
from pathlib import Path

sys.path.insert(0, sys.argv[4])  # research/1039-wiedemann-lex
import probe  # noqa: E402

pipeline, driver, out = sys.argv[1], sys.argv[2], Path(sys.argv[3])
reps = int(sys.argv[5]) if len(sys.argv) > 5 else 3
rows = [('wd-4-10', 65537), ('wdsq-4-10', 65537), ('wd-3-30', 65537), ('wd-4-12', 2147483647),
        ('wdsq-5-6', 65537), ('wd-5-10', 65537)]
scratch = out.parent / 'mac-probe-inputs'
scratch.mkdir(exist_ok=True)
CAP = 300


def run(argv):
    t = time.perf_counter()
    try:
        p = subprocess.run(argv, capture_output=True, text=True, timeout=CAP + 5)
        return p.returncode, p.stdout, p.stderr, time.perf_counter() - t
    except subprocess.TimeoutExpired:
        return None, '', 'timeout', time.perf_counter() - t


with out.open('a') as f:
    for row, mod in rows:
        rc, so, se, _ = run([pipeline, '--family', row, '--modulus', str(mod), '--input-only'])
        assert rc == 0, se
        case = json.loads(so)
        cpath = scratch / f'{row}.case.json'
        cpath.write_text(json.dumps(case))
        for rep in range(reps):
            for arm in ('grobx', 'grobx-f4lex', 'adaptive'):
                if arm.startswith('grobx'):
                    route = 'f4' if arm.endswith('f4lex') else 'auto'
                    req = probe.grobx_request(case, 'raw', CAP, 16 * 2**30, route)
                    req['digest_only'] = True
                    rpath = scratch / f'{row}.{route}.json'
                    rpath.write_text(json.dumps(req))
                    rc, so, se, wall = run([driver, str(rpath)])
                    raw = json.loads(so) if rc == 0 and so.strip() else {}
                    rec = dict(arm=arm, rc=rc, wall_s=wall, solve_ns=raw.get('solve_ns'),
                               stopped=raw.get('stopped'), basis_m33=raw.get('basis_m33'),
                               grobx_order=raw.get('grobx_order'),
                               stages=probe.grobx_stages(raw.get('report') or ''))
                else:
                    rc, so, se, wall = run([pipeline, '--input', str(cpath), '--arm', arm, '--workers', '1',
                                            '--wall-s', str(CAP), '--budget', 'lifted'])
                    rep_ = json.loads(so) if rc == 0 and so.strip() else {}
                    rec = dict(arm=arm, rc=rc, wall_s=wall, report=rep_)
                if rc != 0:
                    rec['stderr'] = se[-300:]
                rec.update(row=row, modulus=mod, rep=rep, input_digest=case.get('digest'))
                f.write(json.dumps(rec, sort_keys=True) + '\n')
                f.flush()
                print(row, rep, arm, rc, round(wall, 3), flush=True)
