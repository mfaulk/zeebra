#!/usr/bin/env python3
"""Bounded serial backward experiment using existing watchdogs and independent full references."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import resource
import subprocess

ROOT = Path(__file__).resolve().parents[2]
TRAJECTORY = ('batches', 'pairs_considered', 'pairs_reduced', 'elements_added', 'empty_batches',
              'max_matrix_rows', 'max_matrix_columns', 'degree_sequence', 'max_live_nonzeros_as_built',
              'peak_basis_elements', 'peak_basis_terms')
ARMS = ('stock', 'full', 'dense-all', 'dense-selected')


def load(name):
    spec = importlib.util.spec_from_file_location(name.replace('-', '_'), ROOT / 'tools/external' / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def plan(phase):
    if phase not in ('native', 'work', 'probe', 'adoption', 'adoption-work', 'adoption-off'):
        raise ValueError('unknown campaign phase')
    if phase in ('adoption', 'adoption-work', 'adoption-off'):
        for repeat in range(5):
            for problem in (('mq-random-10','cyclic-5','katsura-6') if phase == 'adoption' else ('mq-random-10',)):
                for modulus in (32003,2147483647):
                    arms=(('stock','production','feature-off') if phase == 'adoption' else
                          ('stock','production') if phase == 'adoption-off' else ('full-on','production-on'))
                    for arm in arms if repeat % 2 == 0 else reversed(arms):
                        yield repeat,problem,modulus,arm
        return
    if phase == 'probe':
        for modulus in (32003, 2147483647):
            for arm in ('full', 'dense-selected'):
                yield (0, 'mq-random-14', modulus, arm)
        return
    for repeat in range(5):
        for problem in (('mq-random-10', 'cyclic-5', 'katsura-6') if phase == 'native' else ('mq-random-10',)):
            for modulus in (32003, 2147483647):
                arms = ARMS if phase == 'native' else ('full-off', 'full-on', 'dense-all-on', 'dense-selected-on')
                for arm in arms if repeat % 2 == 0 else reversed(arms):
                    yield repeat, problem, modulus, arm


def references():
    refs = load('row-merge-study').references()
    controls = load('proof_artifacts').load_cohort(ROOT / 'research/concurrent-pivots/controls.json.gz')
    for modulus in (32003, 2147483647):
        ref = controls['references'][f'katsura-6/{modulus}']
        if (sha_text(ref['script']) != ref['script_sha256'] or ref['singular']['exit']
                or ref['singular']['stop'] or '@match 1\n' not in ref['singular']['stdout']):
            raise ValueError('retained independent Katsura proof is invalid')
        refs[('katsura-6', modulus)] = ref
    return refs


def sha_text(value):
    return hashlib.sha256(value.encode()).hexdigest()


def validate(raw, reference, mode, problem):
    load('mq10-profile').check_answer(raw, reference)
    if raw.get('problem') != problem:
        raise ValueError('problem differs')
    backward = raw.get('backward')
    if mode == 'production':
        if backward is not None or raw.get('parallel') is not None:
            raise ValueError('production unexpectedly uses a research override')
        stats=raw['statistics']
        if stats['candidate_reduction']['batches'] != stats['batches']:
            raise ValueError('production candidate-output contract was not used')
    elif mode == 'stock':
        if backward is not None:
            raise ValueError('stock unexpectedly selected a backward policy')
    elif not backward or backward.get('mode') != mode or not backward.get('batches'):
        raise ValueError('backward policy absent or differs')


def check_trajectory(raw, reference):
    for key in TRAJECTORY:
        if raw['statistics'][key] != reference['statistics'][key]:
            raise ValueError('forward trajectory differs: ' + key)


def resumable_status(status, phase):
    return status == 'verified' or (phase == 'probe' and status in (
        'incomplete-unverified', 'completed-needs-independent-reference'))


def environment_refusal(max_load, compilers):
    if compilers:
        return dict(reason='compiler', processes=compilers)
    if os.getloadavg()[0] > max_load:
        return dict(reason='load', load=os.getloadavg()[0])
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('stock', 'binary', 'scratch', 'output'):
        parser.add_argument('--' + name, required=True, type=Path)
    parser.add_argument('--phase', choices=('native', 'work', 'probe', 'adoption', 'adoption-work', 'adoption-off'), default='native')
    parser.add_argument('--production', type=Path, help='feature-absent adopted production binary')
    parser.add_argument('--baseline-commit', help='source revision of the stock control')
    parser.add_argument('--max-load', type=float, default=4)
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--build-commit', required=True, help='commit used to build the frozen executables')
    args = parser.parse_args()
    if args.phase.startswith('adoption') and (not args.production or not args.baseline_commit):
        parser.error('adoption requires --production and --baseline-commit')
    if subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True).strip():
        parser.error('commit instruments before measuring')
    build_commit = subprocess.check_output(['git', 'rev-parse', args.build_commit], cwd=ROOT, text=True).strip()
    if subprocess.call(['git', 'diff', '--quiet', build_commit, '--', 'Cargo.toml', 'Cargo.lock', '.cargo', 'src', 'examples'], cwd=ROOT):
        parser.error('frozen build source differs from current library/examples')
    affinity = ','.join(map(str, sorted(os.sched_getaffinity(0))))
    if os.environ.get('ZEEBRA_AFFINITY') != affinity or not os.environ.get('ZEEBRA_MACHINE'):
        parser.error('declare the actual machine and affinity and use benchlock')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.scratch.mkdir(parents=True, exist_ok=True)
    storage, guard = load('study_artifacts'), load('grobx-work-study')
    identity = dict(commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        binaries={name: dict(path=str(getattr(args, name).resolve()), sha256=sha(getattr(args, name))) for name in ('stock', 'binary')},
        build_commit=build_commit, compiler_gate=True,
        phase=args.phase, affinity=affinity, machine=os.environ['ZEEBRA_MACHINE'],
        max_load=args.max_load, cargo_lock_sha256=sha(ROOT/'Cargo.lock'))
    if args.production:
        identity['binaries']['production']=dict(path=str(args.production.resolve()),sha256=sha(args.production))
        identity['baseline_commit']=subprocess.check_output(['git','rev-parse',args.baseline_commit],cwd=ROOT,text=True).strip()
    cohort = dict(schema=1, identity=identity, rustc=subprocess.check_output(['rustc', '-vV'], text=True),
        topology=subprocess.check_output(['lscpu', '-e=CPU,CORE,SOCKET,NODE,CACHE,ONLINE'], text=True),
        build='cargo build --release --example mq10_profile; observed adds --features research-work; fat LTO; codegen-units=1; x86-64-v3; mold; system allocator',
        limits=dict(child_wall_seconds=60, rss_bytes=2*1024**3, parent_wall_seconds=185),
        reference_files={str(p.relative_to(ROOT)): sha(p) for p in (
            ROOT/'research/competitive/results/grobx-683.json.gz', ROOT/'research/competitive/results/grobx-683-small.json.gz',
            ROOT/'research/concurrent-pivots/controls.json.gz')}, attempts=[])
    cells = list(plan(args.phase))
    if args.resume:
        cohort = storage.load_study(args.output)
        if (cohort['identity'] != identity or cohort.get('refusal', {}).get('reason') not in ('load', 'compiler')
                or len(cohort.get('excluded_attempts', [])) > 1):
            parser.error('resume requires identical source/binaries/limits, an environmental refusal and at most one excluded attempt')
        seen = [(a['repeat'], a['problem'], a['modulus'], a['arm']) for a in cohort['attempts']]
        if seen != cells[:len(seen)] or any(not resumable_status(a['status'], args.phase) for a in cohort['attempts']):
            parser.error('resume requires a verified plan prefix')
        cohort.setdefault('resumptions', []).append(cohort.pop('refusal'))
        # Repack loaded attempts so the final file retains content-addressed basis storage.
        cohort['attempts'] = [storage.pack_attempt(a, args.output) if a['status'] == 'verified' else a for a in cohort['attempts']]
    elif args.output.exists():
        parser.error('output exists; retain it and use a new campaign path')
    refs, trajectories = references(), {}
    for a in storage.iter_attempts(args.output) if args.resume else ():
        if a['status'] == 'verified': trajectories.setdefault((a['problem'], a['modulus']), a['raw'])
    for repeat, problem, modulus, arm in cells[len(cohort['attempts']):]:
        refusal = environment_refusal(args.max_load, load('worker-pool-study').compiler_processes())
        if refusal:
            cohort['refusal'] = dict(refusal, next=[repeat, problem, modulus, arm])
            guard.write(args.output, cohort)
            raise RuntimeError('environment gate refused; verified prefix retained')
        mode = arm.removesuffix('-on').removesuffix('-off')
        if arm == 'feature-off': mode='production'
        binary_name='stock' if mode == 'stock' else ('production' if arm == 'production' else 'binary')
        binary=getattr(args,binary_name)
        if sha(binary) != identity['binaries'][binary_name]['sha256']:
            raise ValueError('binary changed during campaign')
        command = [str(binary.resolve()), str(modulus), '--problem='+problem]
        if args.phase != 'adoption-off': command += ['--stages']
        if mode not in ('stock','production'): command += ['--backward='+mode]
        if arm.endswith('-on'): command += ['--work']
        before = resource.getrusage(resource.RUSAGE_CHILDREN)
        result = guard.guarded(['timeout', '--signal=KILL', '185', *command], args.scratch/str(len(cohort['attempts'])), 60, 2*1024**3)
        after = resource.getrusage(resource.RUSAGE_CHILDREN)
        result.update(repeat=repeat, problem=problem, modulus=modulus, arm=arm, status='failed',
            load=os.getloadavg()[0], cpu_seconds=after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime)
        try:
            if result['exit'] or result['stop']:
                if args.phase == 'probe':
                    result['status'] = 'incomplete-unverified'
                else:
                    raise ValueError('child failed or refused')
            else:
                raw = json.loads(result['stdout'])
                result['raw'] = raw
                if args.phase == 'probe':
                    result['status'] = 'completed-needs-independent-reference'
                else:
                    validate(raw, refs[(problem, modulus)], mode, problem)
                    trajectories.setdefault((problem, modulus), raw)
                    check_trajectory(raw, trajectories[(problem, modulus)])
                    if mode == 'production' and arm.endswith('-on'):
                        products=sum(b['backward']['coefficient_products'] for b in raw['work']['batches'])
                        if products != raw['statistics']['candidate_reduction']['coefficient_products']:
                            raise ValueError('passive/direct production work differs')
                    result['status'] = 'verified'
        except (ValueError, KeyError, TypeError) as error:
            result['failure'] = str(error)
        result['compiler_before'] = []
        result['compiler_after'] = load('worker-pool-study').compiler_processes()
        if result['compiler_after']:
            result['status'] = 'contaminated'
            cohort.setdefault('excluded_attempts', []).append(result)
            cohort['refusal'] = dict(reason='compiler', processes=result['compiler_after'], next=[repeat, problem, modulus, arm])
            guard.write(args.output, cohort)
            raise RuntimeError('ambient compilation began during attempt; excluded response retained')
        if result['status'] == 'verified': result = storage.pack_attempt(result, args.output)
        cohort['attempts'].append(result)
        guard.write(args.output, cohort)
        print(repeat, problem, modulus, arm, result['status'], flush=True)
        if result['status'] == 'failed': raise RuntimeError('failed attempt retained; stop campaign')


if __name__ == '__main__':
    main()
