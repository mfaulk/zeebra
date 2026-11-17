#!/usr/bin/env python3
"""#855 wide-field verification, outside the timed campaign.

For each wide target, `verified` needs the timed cohort's Zeebra basis digest to be unique across
every run and worker count, and grobx certified mode (independent exact checker with cofactors),
admitted by comparand-scaling.py's `certified_basis`, to return a basis with the same text digest.
`m29_cost_model --certify` is reported beside it as `zeebra_certified` when `--certifier` is given;
on Eco-12 it exceeded the 600 s budget (README), so the published run omits it.

    python3 research/m30-baseline/verify_wide.py --walls OUT/walls.jsonl [--certifier BIN] \
        --grobx BIN --scratch DIR > research/m30-baseline/verification.json
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('scaling', ROOT / 'tools/external/comparand-scaling.py')
scaling = importlib.util.module_from_spec(spec)
spec.loader.exec_module(scaling)

TARGETS = {'eco12-wide64': ('wide64', 'eco-12'), 'mq11-goldilocks': ('goldilocks', 'mq-random-11')}
WALL_S = 600


def text_digest(basis):
    return hashlib.sha256('\n'.join(sorted(basis)).encode()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--walls', type=Path, required=True)
    p.add_argument('--certifier', type=Path, help='m29_cost_model with --certify; omitted, not run')
    p.add_argument('--grobx', type=Path, required=True)
    p.add_argument('--scratch', type=Path, required=True)
    p.add_argument('--targets', default=','.join(TARGETS), help='comma-separated subset of the wide targets')
    p.add_argument('--grobx-rss-gib', type=int, default=8, help='grobx certified memory cap (declared: 8)')
    a = p.parse_args()
    a.scratch.mkdir(parents=True, exist_ok=True)
    walls = [json.loads(l) for l in a.walls.read_text().splitlines() if l.strip()]
    cases = {(c['field'], c['name']): c for c in json.loads((ROOT / 'research/wide-corpus/cases.json').read_text())}
    out = []
    for target in a.targets.split(','):
        key = TARGETS[target]
        timed = sorted({r['report']['basis_sha256'] for r in walls
                        if r['target'] == target and r['report'] and r['report']['status'] == 'complete'})
        row = dict(target=target, timed_digests=timed,
                   timed_runs=sum(1 for r in walls if r['target'] == target))

        if a.certifier:
            started = time.monotonic_ns()
            try:
                r = subprocess.run([str(a.certifier), '--target', target, '--workers', '16', '--certify',
                                    '--wall-s', str(WALL_S)], capture_output=True, text=True,
                                   timeout=WALL_S + 60)
                report = json.loads(r.stdout) if r.returncode == 0 else None
                row['zeebra_certify'] = dict(
                    exit=r.returncode, process_wall_ns=time.monotonic_ns() - started,
                    status=report and report['status'], basis_sha256=report and report['basis_sha256'],
                    certification=report and report.get('certification'), stderr=r.stderr[-2000:])
            except subprocess.TimeoutExpired:
                # F4's wall budget does not bound the certificate, so the caller's timeout is the cap.
                row['zeebra_certify'] = dict(status='budget', process_wall_ns=time.monotonic_ns() - started)
        else:
            row['zeebra_certify'] = dict(status='not run')

        case = scaling.canonical_case(cases[key])
        request = dict(variables=case['variables'], modulus=case['modulus'], order='grevlex', workers=1,
                       generators=case['generators'], mode='certified', wall_ns=WALL_S * 10**9,
                       rss_bytes=a.grobx_rss_gib * 1024**3)
        stem = a.scratch / f'grobx-certified-{target}-{a.grobx_rss_gib}g'
        stem.with_suffix('.request').write_text(json.dumps(request))
        started = time.monotonic_ns()
        g = subprocess.run([str(a.grobx), str(stem.with_suffix('.request'))], capture_output=True, text=True,
                           timeout=WALL_S + 60)
        wall = time.monotonic_ns() - started
        try:
            basis = scaling.certified_basis(json.loads(g.stdout), case, request)
            grobx = dict(admitted=True, basis_text_sha256=text_digest(basis), elements=len(basis))
        except (ValueError, json.JSONDecodeError) as error:
            grobx = dict(admitted=False, error=str(error))
        stem.with_suffix('.response').write_text(g.stdout)
        grobx.update(exit=g.returncode, process_wall_ns=wall,
                     response_sha256=hashlib.sha256(g.stdout.encode()).hexdigest(), stderr=g.stderr[-2000:])
        grobx['rss_cap_gib'] = a.grobx_rss_gib
        row['grobx_certified'] = grobx

        cert = row['zeebra_certify']
        row['zeebra_certified'] = bool(
            cert['status'] == 'complete' and cert['basis_sha256'] == timed[0]
            and cert['certification'] and cert['certification'].get('complete') is True)
        row['verified'] = bool(len(timed) == 1 and grobx.get('admitted')
                               and grobx['basis_text_sha256'] == timed[0])
        out.append(row)
    print(json.dumps(out, indent=1))


if __name__ == '__main__':
    main()
