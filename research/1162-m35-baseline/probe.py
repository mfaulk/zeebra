#!/usr/bin/env python3
"""#1162 development-mode attribution probe: every panel record, one worker, three attempts each.

    probe.py --matrix BIN --grobx BIN --catalog catalog.json --cpu N [--ids a,b] [--wall-s 300]
             [--out probe.jsonl]

Per record, in fresh processes pinned to one CPU:
  * `f4-stages`: Zeebra's shipping F4 with `--stages` (stage clocks + always-on counters; the clocks
    cost 4-12%, so this attempt attributes and is never a timing record);
  * `f4`, `adaptive`: Zeebra's shipping default and `GradedEngine::Adaptive`, no stages;
  * `sig-stages` (on request): the forced signature engine with its always-on counters;
  * `grobx`: grobx 0.155.1 raw (its default: randomized, uncertified) with its report, from which the
    engines, handovers, field kernel, reduce mode and per-stage seconds are read;
  * `grobx-certified` (on request): grobx's exact mode, deterministic `rows` reduction plus the exact
    checker. Not passive: it changes grobx's trajectory, so it is the exact-guarantee comparator.
Development mode (`docs/guide/benchmarking.md`): no reservation, no load gate. It fixes the panel's
time bands and the phase shares; it decides nothing.
"""
import argparse
import json
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import m34_public_corpus as public  # noqa: E402

ROUND_STAGES = ('select', 'symbolic', 'encode', 'reduce', 'backsub', 'record', 'decode', 'update')
FIELD = re.compile(r'(\S+?)=(\S+)')


def guarded(argv, cpu, timeout):
    started = time.monotonic_ns()
    try:
        run = subprocess.run(['taskset', '-c', str(cpu), *argv], capture_output=True, text=True,
                             timeout=timeout)
        rc, out, err = run.returncode, run.stdout, run.stderr
    except subprocess.TimeoutExpired:
        rc, out, err = 'timeout', '', ''
    return {'rc': rc, 'stdout': out, 'stderr': err[-400:], 'wall_ns': time.monotonic_ns() - started}


def grobx_report(report):
    """Engines, handovers, kernel, reduce mode and summed per-stage seconds from grobx's report."""
    runs, stages, inter, text, check, end = [], dict.fromkeys(ROUND_STAGES, 0.0), {}, 0.0, None, {}
    rounds = zero = 0
    for line in report.splitlines():
        parts = line.split()
        if len(parts) < 2:
            continue
        kind, fields = parts[1], dict(FIELD.findall(line))
        if kind == 'run':
            runs.append({k: fields.get(k) for k in ('engine', 'engine-by', 'field', 'reduce', 'why')})
        elif kind == 'round':
            rounds += 1
            zero += int(fields.get('zero-rows', 0))
            for s in ROUND_STAGES:
                stages[s] += float(fields.get(s, 0))
        elif kind == 'inter':
            inter = {k: float(fields[k]) for k in ('symbolic', 'encode', 'reduce', 'decode') if k in fields}
        elif kind == 'text':
            text += float(fields.get('time', 0))
        elif kind == 'check':
            check = fields.get('mode')
        elif kind == 'end':
            end = {k: fields[k] for k in ('result', 'time', 'process-rss-peak') if k in fields}
    return {'runs': runs, 'handovers': sum(r['why'] == 'handover' for r in runs), 'rounds': rounds,
            'zero_rows': zero, 'round_stage_s': stages, 'inter_s': inter, 'text_s': text,
            'checker': check, 'end': end}


def zeebra(args, record, engine, stages):
    argv = [args.matrix, '--catalog', args.catalog, '--id', record['id'], '--engine', engine,
            '--workers', '1', '--wall-s', str(args.wall_s)] + (['--stages'] if stages else [])
    r = guarded(argv, args.cpu, args.wall_s + 30)
    out = json.loads(r['stdout']) if r['rc'] == 0 and r['stdout'].strip() else {}
    return {'arm': f'{engine}-stages' if stages else engine, 'process_wall_ns': r['wall_ns'],
            'rc': r['rc'], 'status': out.get('status', 'crashed' if r['rc'] != 'timeout' else 'timeout'),
            'error': out.get('error') or (r['stderr'] or None), 'route': out.get('route'),
            'call_ns': out.get('call_ns'), 'peak_rss_bytes': out.get('peak_rss_bytes'),
            'basis_sha256': out.get('basis_sha256'), 'stages': out.get('stages'),
            'counters': out.get('counters')}


def grobx(args, record, mode='raw'):
    request = dict(variables=record['variables'], modulus=int(record['field']['characteristic']),
                   order='grevlex', workers=1, generators=public.generator_texts(record), mode=mode,
                   wall_ns=args.wall_s * 10**9, rss_bytes=16 * 2**30)
    with tempfile.NamedTemporaryFile('w', suffix='.json', delete=False) as handle:
        json.dump(request, handle)
    try:
        r = guarded([args.grobx, handle.name], args.cpu, args.wall_s + 30)
    finally:
        Path(handle.name).unlink()
    reply = json.loads(r['stdout']) if r['rc'] == 0 and r['stdout'].strip() else {}
    status = 'stopped' if reply.get('stopped') else ('complete' if reply.get('basis') else
                                                     ('timeout' if r['rc'] == 'timeout' else 'crashed'))
    digest = None
    if status == 'complete':
        digest = public.basis_digest(record, public.parse_grobx_basis(reply['basis'], record['variables']))
    return {'arm': 'grobx' if mode == 'raw' else f'grobx-{mode}', 'process_wall_ns': r['wall_ns'], 'rc': r['rc'], 'status': status,
            'error': reply.get('stopped') or (r['stderr'] or None), 'call_ns': reply.get('solve_ns'),
            'parse_ns': reply.get('parse_ns'), 'peak_rss_bytes': reply.get('kernel_peak_rss_bytes'),
            'basis_sha256': digest, 'report': grobx_report(reply.get('report', ''))}


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--matrix', required=True)
    p.add_argument('--grobx', required=True)
    p.add_argument('--catalog', required=True)
    p.add_argument('--cpu', type=int, required=True)
    p.add_argument('--ids')
    p.add_argument('--wall-s', type=int, default=300)
    p.add_argument('--arms', default='f4-stages,f4,adaptive,grobx',
                   help='comma-separated; sig-stages adds the forced signature engine with counters')
    p.add_argument('--out', default=str(HERE / 'probe.jsonl'))
    args = p.parse_args()
    records = json.loads(Path(args.catalog).read_text())
    wanted = set(args.ids.split(',')) if args.ids else None
    with open(args.out, 'a') as out:
        for record in records:
            if wanted and record['id'] not in wanted:
                continue
            arms = {'f4-stages': lambda: zeebra(args, record, 'f4', True),
                    'f4': lambda: zeebra(args, record, 'f4', False),
                    'adaptive': lambda: zeebra(args, record, 'adaptive', False),
                    'sig-stages': lambda: zeebra(args, record, 'sig', True),
                    'grobx': lambda: grobx(args, record),
                    'grobx-certified': lambda: grobx(args, record, 'certified')}
            for attempt in (arms[a] for a in args.arms.split(',')):
                row = dict(attempt(), id=record['id'], family=record['lineage']['family_id'],
                           role=record['lineage'].get('role'), mode='development')
                out.write(json.dumps(row, sort_keys=True) + '\n')
                out.flush()
                print(row['id'], row['arm'], row['status'],
                      f"{(row['call_ns'] or 0) / 1e9:.2f}s", flush=True)


if __name__ == '__main__':
    main()
