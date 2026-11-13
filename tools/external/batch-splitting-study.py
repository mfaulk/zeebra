#!/usr/bin/env python3
import argparse
import datetime
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
FIXTURES = (
    ('cyclic-3', 3), ('cyclic-4', 7), ('katsura-2', 7), ('katsura-3', 18),
    ('mq-random-3', 18), ('mq-homogeneous-3', 20), ('cyclic-homogeneous-4', 10),
    ('katsura-homogeneous-3', 20), ('unit', 1), ('positive-dimensional', 1),
)


def cells():
    for fixture, rows in FIXTURES:
        yield fixture, 'shipping', 'unbounded', 0, 32
        yield fixture, 'static-none', 'unbounded', 0, 32
        for policy in ('shipping', 'static-none', 'static1', 'static2', 'adaptive'):
            yield fixture, policy, 'rows', rows, 32
    yield 'cyclic-4', 'adaptive', 'rows', 0, 32
    yield 'cyclic-4', 'adaptive', 'rows', 7, 0
    yield 'cyclic-4', 'adaptive', 'entries', 19, 32
    yield 'cyclic-4', 'adaptive', 'columns', 3, 32


def solver_command(binary, cell):
    return [str(binary), *map(str, cell)]


def accept_report(row):
    if row['status'] == 'complete':
        if row['basis'] != row['reference_basis'] or not row['exact_reference_and_submitted_checks']:
            raise ValueError('complete basis disagrees with independent exact reference')
        return 'verified'
    if row['status'] == 'refused':
        if row['basis'] or not isinstance(row.get('failure'), dict) or not row['failure'].get('kind'):
            raise ValueError('refusal has a partial basis or no typed reason')
        return 'refused'
    raise ValueError('unknown result status')


def write(path, value):
    path.write_bytes(gzip.compress((json.dumps(value, indent=2) + '\n').encode(), mtime=0))


def main():
    parser = argparse.ArgumentParser(description='Run the frozen bounded F4 splitting feasibility study under benchlock.')
    parser.add_argument('--binary', type=Path, required=True)
    parser.add_argument('--scratch', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True).strip():
        parser.error('commit the complete instrument before measurement')
    spec = importlib.util.spec_from_file_location('grobx_work', Path(__file__).with_name('grobx-work-study.py'))
    guard = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(guard)
    binary = args.binary.resolve()
    args.scratch.mkdir(parents=True, exist_ok=False)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    cohort = dict(
        schema=1, commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),
        cargo_lock_sha256=hashlib.sha256((ROOT / 'Cargo.lock').read_bytes()).hexdigest(),
        rustc=subprocess.check_output(['rustc', '-vV'], text=True),
        singular_version=subprocess.check_output(['Singular', '--version'], text=True),
        cpu=subprocess.check_output(['lscpu'], text=True), affinity=sorted(os.sched_getaffinity(0)), workers=1,
        started_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), command=sys.argv,
        build='release; fat LTO; codegen-units=1; x86-64-v3; system allocator',
        policy='one fresh process per declared cell; single feasibility sample, no speedup claim',
        wall_limit_seconds=60, rss_limit_bytes=2 * 1024**3,
        address_space_limit_bytes=None, attempts=[],
    )
    failed = False
    for index, cell in enumerate(cells()):
        fixture, policy, budget, allowance, retries = cell
        command = solver_command(binary, cell)
        attempt = guard.guarded(command, args.scratch / str(index), 60, 2 * 1024**3)
        attempt.update(fixture=fixture, policy=policy, budget=budget, allowance=allowance,
                       max_retries=retries, load=os.getloadavg())
        try:
            if attempt['exit'] != 0 or attempt['stop']:
                raise ValueError('external watchdog stop or process failure')
            attempt['report'] = json.loads(attempt['stdout'])
            attempt['acceptance'] = accept_report(attempt['report'])
        except (ValueError, KeyError) as error:
            attempt['acceptance'] = 'failed'
            attempt['failure'] = str(error)
            failed = True
        cohort['attempts'].append(attempt)
        write(args.output, cohort)
        print(index, *cell, attempt['acceptance'], flush=True)
    if failed:
        raise RuntimeError('failed attempts retained; inspect cohort')


if __name__ == '__main__':
    main()
