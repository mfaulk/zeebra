#!/usr/bin/env python3
"""Three-arm multirow reuse campaign (#715): single-row, four-row scalar, four-row interleaved."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import resource
import subprocess

ROOT = Path(__file__).resolve().parents[2]
PROBLEMS = ('mq-random-10', 'cyclic-5', 'katsura-6')
MODULI = (32003, 2147483647)
# `stock` is the feature-absent binary; the other arms share one feature binary and ISA.
ARMS = ('stock', 'single', 'band4', 'lanes4')
TRAJECTORY = ('batches', 'pairs_considered', 'pairs_reduced', 'elements_added', 'empty_batches',
              'max_matrix_rows', 'max_matrix_columns', 'degree_sequence', 'peak_basis_elements',
              'peak_basis_terms')


def load(name):
    spec = importlib.util.spec_from_file_location(name.replace('-', '_'), ROOT / 'tools/external' / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def plan(phase):
    """Every cell, repetition-major; arm order rotates so no arm always runs first or last."""
    problems = PROBLEMS if phase == 'native' else ('mq-random-14',)
    repeats = 5 if phase == 'native' else 1
    for repeat in range(repeats):
        arms = ARMS[repeat % len(ARMS):] + ARMS[:repeat % len(ARMS)]
        for problem in problems:
            for modulus in MODULI:
                for arm in arms:
                    yield repeat, problem, modulus, arm


def command(binary, problem, modulus, arm):
    result = [str(binary.resolve()), str(modulus), '--problem=' + problem]
    return result if arm == 'stock' else result + ['--multirow=' + arm]


def census_totals(raw):
    report = raw.get('multirow')
    if report is None:
        return None
    keys = ('pivot_applications', 'pivot_reads', 'entries_applied', 'entries_read', 'lane_products',
            'bands', 'partial_bands', 'intra_band_pivots', 'new_pivots', 'zero_rows', 'target_entries')
    totals = {key: sum(m[key] for m in report['matrices']) for key in keys}
    totals['reads_by_lanes'] = [sum(m['reads_by_lanes'][i] for m in report['matrices']) for i in range(5)]
    totals['eligible_rows'] = sum(m['rows'] - m['first'] for m in report['matrices'])
    totals['matrices'] = len(report['matrices'])
    totals['max_scratch_bytes'] = max((m['scratch_bytes'] for m in report['matrices']), default=0)
    return totals


def validate(raw, reference, problem, arm):
    load('mq10-profile').check_answer(raw, reference)
    if raw.get('problem') != problem:
        raise ValueError('problem differs')
    report = raw.get('multirow')
    if arm == 'stock':
        if report is not None:
            raise ValueError('stock binary reported a multirow mode')
        return
    if report is None or report['mode'] != arm:
        raise ValueError('multirow mode absent or differs')
    if arm == 'single':
        if report['matrices']:
            raise ValueError('single-row arm reached the band kernel')
        return
    if not report['matrices']:
        raise ValueError('band arm never reached the band kernel')
    totals = census_totals(raw)
    if totals['entries_read'] > totals['entries_applied']:
        raise ValueError('band read more pivot entries than it applied')


def check_trajectory(raw, reference):
    for key in TRAJECTORY:
        if raw['statistics'][key] != reference['statistics'][key]:
            raise ValueError('trajectory differs: ' + key)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('stock', 'binary', 'scratch', 'output'):
        parser.add_argument('--' + name, required=True, type=Path)
    parser.add_argument('--phase', choices=('native', 'probe'), default='native')
    parser.add_argument('--max-load', type=float, default=8)
    parser.add_argument('--build-commit', required=True)
    args = parser.parse_args()
    if subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=ROOT, text=True).strip():
        parser.error('commit instruments before measuring')
    build_commit = subprocess.check_output(['git', 'rev-parse', args.build_commit], cwd=ROOT, text=True).strip()
    if subprocess.call(['git', 'diff', '--quiet', build_commit, '--', 'Cargo.toml', 'Cargo.lock', '.cargo', 'src', 'examples'], cwd=ROOT):
        parser.error('frozen build source differs from current library/examples')
    affinity = ','.join(map(str, sorted(os.sched_getaffinity(0))))
    if os.environ.get('ZEEBRA_AFFINITY') != affinity or not os.environ.get('ZEEBRA_MACHINE'):
        parser.error('declare the actual machine and affinity and use benchlock')
    if args.output.exists():
        parser.error('output exists; retain it and use a new campaign path')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.scratch.mkdir(parents=True, exist_ok=True)
    storage, guard, pool = load('study_artifacts'), load('grobx-work-study'), load('worker-pool-study')
    identity = dict(commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        build_commit=build_commit, phase=args.phase, affinity=affinity, machine=os.environ['ZEEBRA_MACHINE'],
        max_load=args.max_load, cargo_lock_sha256=sha(ROOT / 'Cargo.lock'),
        binaries={name: dict(path=str(getattr(args, name).resolve()), sha256=sha(getattr(args, name)))
                  for name in ('stock', 'binary')})
    cohort = dict(schema=1, identity=identity, rustc=subprocess.check_output(['rustc', '-vV'], text=True),
        topology=subprocess.check_output(['lscpu', '-e=CPU,CORE,SOCKET,NODE,CACHE,ONLINE'], text=True),
        build='cargo build --release --example mq10_profile; binary adds --features research-multirow; '
              'fat LTO; codegen-units=1; x86-64-v3 from .cargo/config.toml; system allocator',
        limits=dict(child_wall_seconds=60, rss_bytes=2 * 1024**3, parent_wall_seconds=185), attempts=[])
    refs = load('selective-backward-study').references() if args.phase == 'native' else {}
    trajectories = {}
    for repeat, problem, modulus, arm in plan(args.phase):
        if pool.compiler_processes() or os.getloadavg()[0] > args.max_load:
            cohort['refusal'] = dict(load=os.getloadavg()[0], compilers=pool.compiler_processes(),
                                     next=[repeat, problem, modulus, arm])
            guard.write(args.output, cohort)
            raise RuntimeError('environment gate refused; verified prefix retained')
        binary = args.stock if arm == 'stock' else args.binary
        if sha(binary) != identity['binaries']['stock' if arm == 'stock' else 'binary']['sha256']:
            raise ValueError('binary changed during campaign')
        before = resource.getrusage(resource.RUSAGE_CHILDREN)
        result = guard.guarded(['timeout', '--signal=KILL', '185', *command(binary, problem, modulus, arm)],
                               args.scratch / str(len(cohort['attempts'])), 60, 2 * 1024**3)
        after = resource.getrusage(resource.RUSAGE_CHILDREN)
        result.update(repeat=repeat, problem=problem, modulus=modulus, arm=arm, status='failed',
                      load=os.getloadavg()[0],
                      cpu_seconds=after.ru_utime + after.ru_stime - before.ru_utime - before.ru_stime)
        try:
            if result['exit'] or result['stop']:
                if args.phase != 'probe':
                    raise ValueError('child failed or refused')
                result['status'] = 'incomplete-unverified'
            else:
                raw = json.loads(result['stdout'])
                result['raw'] = raw
                result['census'] = census_totals(raw)
                if args.phase == 'probe':
                    result['status'] = 'completed-needs-independent-reference'
                else:
                    validate(raw, refs[(problem, modulus)], problem, arm)
                    trajectories.setdefault((problem, modulus), raw)
                    check_trajectory(raw, trajectories[(problem, modulus)])
                    result['status'] = 'verified'
        except (ValueError, KeyError, TypeError) as error:
            result['failure'] = str(error)
        result['compiler_after'] = pool.compiler_processes()
        if result['compiler_after'] and result['status'] == 'verified':
            result['status'] = 'contaminated'
        if result['status'] == 'verified':
            result = storage.pack_attempt(result, args.output)
        cohort['attempts'].append(result)
        guard.write(args.output, cohort)
        print(repeat, problem, modulus, arm, result['status'], flush=True)
        if result['status'] in ('failed', 'contaminated'):
            raise RuntimeError('attempt not verified; retained and stopped')


if __name__ == '__main__':
    main()
