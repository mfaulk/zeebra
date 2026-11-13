#!/usr/bin/env python3
"""Four-way forward/backward policy crossing, using the existing guarded full-basis checks."""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import resource
import subprocess

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('driver', ROOT/'tools/external/selective-backward-study.py')
driver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(driver)
SETTINGS = {'serial-full': ('full', None), 'serial-selected': ('dense-selected', None),
            'parallel-full': ('full', 4), 'parallel-selected': ('dense-selected', 4),
            'one-full': ('full', 1), 'one-selected': ('dense-selected', 1)}


def plan(phase):
    if phase not in ('native', 'work', 'probe'): raise ValueError('unknown phase')
    for repeat in range(5 if phase == 'native' else 1):
        for problem in (('mq-random-14',) if phase == 'probe' else
                        ('mq-random-10',) if phase == 'work' else ('mq-random-10', 'cyclic-5', 'katsura-6')):
            for modulus in (32003, 2147483647):
                arms = list(SETTINGS) if problem == 'mq-random-10' else list(SETTINGS)[:4]
                if phase == 'probe': arms = list(SETTINGS)[:2]
                for arm in arms if repeat % 2 == 0 else reversed(arms):
                    yield repeat, problem, modulus, arm


def validate(raw, reference, arm, problem):
    driver.load('mq10-profile').check_answer(raw, reference)
    mode, workers = SETTINGS[arm]
    if raw.get('problem') != problem: raise ValueError('problem differs')
    if workers is None:
        driver.validate(raw, reference, mode, problem)
        if raw.get('parallel') is not None: raise ValueError('serial unexpectedly parallel')
    else:
        parallel = raw.get('parallel')
        if (not parallel or parallel['workers'] != workers or parallel['backward_mode'] != mode
                or parallel['fallbacks'] or not parallel['batches'] or raw.get('backward') is not None):
            raise ValueError('parallel policy differs or fell back')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('binary', 'scratch', 'output'): parser.add_argument('--'+name, required=True, type=Path)
    parser.add_argument('--phase', choices=('native', 'work', 'probe'), default='native')
    parser.add_argument('--resume', action='store_true')
    args = parser.parse_args()
    if subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True).strip():
        parser.error('commit instruments before measuring')
    cpus = sorted(os.sched_getaffinity(0))
    if cpus != [0, 1, 2, 3] or os.environ.get('ZEEBRA_AFFINITY') != '0,1,2,3' or not os.environ.get('ZEEBRA_MACHINE'):
        parser.error('declare actual machine and CPU affinity 0,1,2,3')
    storage, guard = driver.load('study_artifacts'), driver.load('grobx-work-study')
    compiler = driver.load('worker-pool-study').compiler_processes
    identity = dict(commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        binary_sha256=driver.sha(args.binary), phase=args.phase, affinity=cpus,
        machine=os.environ['ZEEBRA_MACHINE'], compiler_gate=True,
        cargo_lock_sha256=driver.sha(ROOT/'Cargo.lock'))
    cohort = dict(schema=1, identity=identity, attempts=[],
        rustc=subprocess.check_output(['rustc', '-vV'], text=True),
        build='cargo build --release --features research-work --example mq10_profile; fat LTO; codegen-units=1; x86-64-v3; mold; system allocator',
        policy='five accepted native repetitions; one separately timed work diagnostic per MQ10 arm; at most one environmentally contaminated retry',
        limits=dict(wall_seconds=60, rss_bytes=2*1024**3, max_load=4),
        reference_files={str(p.relative_to(ROOT)): driver.sha(p) for p in (
            ROOT/'research/competitive/results/grobx-683.json.gz', ROOT/'research/concurrent-pivots/controls.json.gz')})
    cells = list(plan(args.phase))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.scratch.mkdir(parents=True, exist_ok=True)
    trajectories = {}
    if args.resume:
        cohort = storage.load_study(args.output)
        seen = [(a['repeat'], a['problem'], a['modulus'], a['arm']) for a in cohort['attempts']]
        if (cohort['identity'] != identity or cohort.get('refusal', {}).get('reason') not in ('compiler', 'load')
                or seen != cells[:len(seen)] or len(cohort.get('excluded_attempts', [])) > 1):
            parser.error('resume requires identical inputs, verified prefix and environmental refusal')
        for a in cohort['attempts']:
            if a['status'] != 'verified': parser.error('resume requires verified prefix')
            trajectories.setdefault((a['problem'], a['modulus']), a['raw'])
        cohort.setdefault('resumptions', []).append(cohort.pop('refusal'))
        cohort['attempts'] = [storage.pack_attempt(a, args.output) for a in cohort['attempts']]
    elif args.output.exists(): parser.error('retain existing output; use --resume or a new path')
    refs = driver.references()
    for repeat, problem, modulus, arm in cells[len(cohort['attempts']):]:
        refusal = driver.environment_refusal(4, compiler())
        if refusal:
            cohort['refusal'] = refusal
            guard.write(args.output, cohort)
            raise RuntimeError('environment gate refused; prefix retained')
        if driver.sha(args.binary) != identity['binary_sha256']: raise ValueError('binary drift')
        mode, workers = SETTINGS[arm]
        child_cpus = cpus if workers == 4 else [3]
        command = ['taskset', '-c', ','.join(map(str, child_cpus)), str(args.binary.resolve()), str(modulus),
                   '--stages', '--problem='+problem, '--backward='+mode]
        if workers: command += ['--workers='+str(workers), '--schedule=dynamic']
        if args.phase == 'work': command += ['--work']
        before = resource.getrusage(resource.RUSAGE_CHILDREN)
        result = guard.guarded(['timeout', '--signal=KILL', '185', *command], args.scratch/str(len(cohort['attempts'])), 60, 2*1024**3)
        after = resource.getrusage(resource.RUSAGE_CHILDREN)
        result.update(repeat=repeat, problem=problem, modulus=modulus, arm=arm, affinity=child_cpus,
            status='failed', load=os.getloadavg()[0], cpu_seconds=after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime,
            compiler_before=[], compiler_after=compiler())
        try:
            if result['exit'] or result['stop']:
                if args.phase == 'probe': result['status'] = 'incomplete-unverified'
                else: raise ValueError('child failed or stopped')
            else:
                raw = json.loads(result['stdout'])
                result['raw'] = raw
                if args.phase == 'probe': result['status'] = 'completed-needs-independent-reference'
                else:
                    validate(raw, refs[(problem, modulus)], arm, problem)
                    trajectories.setdefault((problem, modulus), raw)
                    driver.check_trajectory(raw, trajectories[(problem, modulus)])
                    result['status'] = 'verified'
        except (ValueError, KeyError, TypeError) as error: result['failure'] = str(error)
        if result['compiler_after']:
            result['status'] = 'contaminated'
            cohort.setdefault('excluded_attempts', []).append(result)
            cohort['refusal'] = dict(reason='compiler', processes=result['compiler_after'])
            guard.write(args.output, cohort)
            raise RuntimeError('new ambient compilation; excluded response retained')
        if result['status'] == 'verified': result = storage.pack_attempt(result, args.output)
        cohort['attempts'].append(result)
        guard.write(args.output, cohort)
        print(repeat, problem, modulus, arm, result['status'], flush=True)
        if result['status'] == 'failed': raise RuntimeError('failed attempt retained')


if __name__ == '__main__': main()
