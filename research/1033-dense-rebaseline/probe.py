#!/usr/bin/env python3
"""#1033 development probe: one row, Zeebra's shipping F4 (stages on) against pinned grobx raw.

    probe.py --study BIN --grobx BIN --field gf31 --name mq-dense-15-s15 [--workers 1 16] [--reps 3]
             [--wall-s 180] [--rss-gib 8] [--cpus 8-23] [--density BIN] [--out records.jsonl]

Development mode only (`docs/guide/benchmarking.md`): no reservation, no interleaving guarantee, and
nothing here decides #1033's gate; the deciding read is the bench-job publication run. Each record
holds process wall, peak RSS, the `m33-basis-v1` digest, and Zeebra's stage clocks, so the forward
share of process wall and the digest agreement come from one attempt. `--density BIN` adds one
serial `--density` attempt from a `research-work` build, untimed for the gate.
"""
import argparse
import json
import os
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'research/m33-baseline'))
sys.path.insert(0, str(ROOT / 'tools/external'))
import admission  # noqa: E402


def zeebra(study, case, workers, wall_s, extra=()):
    argv = [study, '--field', case['field'], '--name', case['name'], '--generate', '--engine', 'f4',
            '--workers', str(workers), '--digest-only', '--wall-s', str(wall_s), '--stages', *extra]
    r = admission.guarded(argv, wall_s + 5)
    report = json.loads(r['stdout']) if r['rc'] == 0 and r['stdout'].strip() else {}
    return r, report


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--study', required=True)
    p.add_argument('--grobx', required=True)
    p.add_argument('--density')
    p.add_argument('--field', required=True)
    p.add_argument('--name', required=True)
    p.add_argument('--workers', type=int, nargs='*', default=[1, 16])
    p.add_argument('--reps', type=int, default=3)
    p.add_argument('--wall-s', type=int, default=180)
    p.add_argument('--rss-gib', type=int, default=8)
    p.add_argument('--cpus', default='8-23')
    p.add_argument('--skip-grobx', action='store_true')
    p.add_argument('--out', type=Path)
    a = p.parse_args()
    admission.CAP_BYTES = a.rss_gib * 2**30
    cpu_list = a.cpus
    first = int(cpu_list.split('-')[0])
    case = admission.request(a.study, dict(field=a.field, name=a.name))
    case.update(field=a.field, name=a.name)
    out = a.out.open('a') if a.out else sys.stdout

    def emit(rec):
        rec.update(field=a.field, name=a.name, input_digest=case['digest'])
        out.write(json.dumps(rec, sort_keys=True) + '\n')
        out.flush()

    for rep in range(a.reps):
        if not a.skip_grobx:
            admission.CPUS = str(first)
            r, ok, digest = admission.grobx(a.grobx, case, 'raw', a.wall_s)
            emit(dict(solver='grobx', workers=1, rep=rep, wall_ns=r['wall_ns'], peak=r['peak'], stop=r['stop'],
                      rc=r['rc'], basis_m33=digest))
        for w in a.workers:
            admission.CPUS = str(first) if w == 1 else f'{first}-{first + w - 1}'
            r, report = zeebra(a.study, case, w, a.wall_s)
            emit(dict(solver='zeebra-f4', workers=w, rep=rep, wall_ns=r['wall_ns'], peak=r['peak'], stop=r['stop'],
                      rc=r['rc'], basis_m33=report.get('basis_m33'), status=report.get('status'),
                      statistics=report.get('statistics')))
    if a.density:
        admission.CPUS = str(first)
        r, report = zeebra(a.density, case, 1, a.wall_s * 3, ['--density'])
        emit(dict(solver='zeebra-f4-density', workers=1, wall_ns=r['wall_ns'], peak=r['peak'], stop=r['stop'],
                  rc=r['rc'], basis_m33=report.get('basis_m33'), work=report.get('work'),
                  statistics=report.get('statistics')))


if __name__ == '__main__':
    os.environ.setdefault('TMPDIR', '/buildcache/cargo-target/zeebra-1033/tmp')
    main()
