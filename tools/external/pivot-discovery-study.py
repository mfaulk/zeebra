#!/usr/bin/env python3
"""Measure serial residual discovery using the existing guarded MQ10/full-answer harness."""
import argparse
from collections import Counter
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import statistics
import subprocess
import resource

ROOT = Path(__file__).resolve().parents[2]
WORKERS = (1, 2, 4, 8, 16, 32, 64)


def resume_keys(attempts, plan):
    keys = [(a['repeat'], a['modulus'], a['arm']) for a in attempts]
    if keys != plan[:len(keys)] or len(set(keys)) != len(keys) or any(a['status'] != 'verified' for a in attempts):
        raise ValueError('resume requires an intact verified prefix, never a discarded or failed sample')
    return set(keys)


def arms_for(phase):
    if phase == 'census': return ('stock', 'off', 'work', 'discovery')
    return ('stock', 'off', 'work', *(f'{schedule}-{workers}-{counter}'
        for schedule in ('dynamic', 'static') for workers in WORKERS for counter in ('off', 'on')))


def physical_cpus(topology, available):
    found, result = set(), []
    for cpu, core, socket in sorted(topology, key=lambda row: (row[0] < 2, row[0])):
        if cpu in available and (socket, core) not in found:
            found.add((socket, core))
            result.append(cpu)
    return result


def sibling(name):
    spec = importlib.util.spec_from_file_location(name.replace('-', '_'), Path(__file__).with_name(name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def census(rows):
    if any(not row['completed'] for row in rows):
        raise ValueError('incomplete discovery row')
    costs = [row['elapsed_ns'] for row in rows]
    claims = Counter(row['first_claim_column'] for row in rows if row['first_claim_column'] is not None)
    finish = {}
    for row in rows:
        # This is a DAG of the serial control trajectory, not a bound on a different pivot schedule.
        finish[row['row']] = row['elapsed_ns'] + max((finish[dep] for dep in row['dependencies']), default=0)
    return dict(rows=len(rows), new_rank=sum(row['pivot_column'] is not None for row in rows),
                zero_rows=sum(row['pivot_column'] is None for row in rows),
                inherited_products=sum(row['inherited_products'] for row in rows),
                discovered_products=sum(row['discovered_products'] for row in rows),
                dependent_rows=sum(bool(row['dependencies']) for row in rows),
                dependency_edges=sum(len(row['dependencies']) for row in rows),
                duplicate_first_claims=sum(count - 1 for count in claims.values()),
                largest_first_claim_group=max(claims.values(), default=0),
                row_sum_ns=sum(costs), row_max_ns=max(costs, default=0),
                row_median_ns=statistics.median(costs) if costs else 0,
                serial_trajectory_dag_ns=max(finish.values(), default=0))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('stock', 'observed', 'scratch', 'output'):
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--repeats', type=int, default=5)
    parser.add_argument('--max-load', type=float, default=4)
    parser.add_argument('--phase', choices=('census', 'parallel'), default='census')
    parser.add_argument('--resume', action='store_true', help='continue only a verified prefix stopped by the load gate')
    args = parser.parse_args()
    affinity = ','.join(map(str, sorted(os.sched_getaffinity(0))))
    if not os.environ.get('ZEEBRA_MACHINE') or os.environ.get('ZEEBRA_AFFINITY') != affinity:
        parser.error('declare ZEEBRA_MACHINE and exact inherited ZEEBRA_AFFINITY under benchlock')
    if args.repeats < 1:
        parser.error('repetitions must be positive')
    if subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True).strip():
        parser.error('commit instruments before measuring')
    study = sibling('grobx-work-study')
    topology = [tuple(map(int, line.split(','))) for line in subprocess.check_output(['lscpu', '-p=CPU,CORE,SOCKET'], text=True).splitlines() if not line.startswith('#')]
    cpus = physical_cpus(topology, os.sched_getaffinity(0))
    if args.phase == 'parallel' and len(cpus) < 64:
        parser.error('parallel campaign requires 64 distinct available physical cores')
    refs = study.references(ROOT / 'research/competitive/results/grobx-683.json.gz')
    binaries = {name: getattr(args, name).resolve() for name in ('stock', 'observed')}
    cohort = dict(schema=1, issue=728, repetitions=args.repeats,
                  commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                  rustc=subprocess.check_output(['rustc', '-vV'], text=True),
                  lock_sha256=hashlib.sha256((ROOT / 'Cargo.lock').read_bytes()).hexdigest(),
                  config=(ROOT / '.cargo/config.toml').read_text(),
                  machine=os.environ['ZEEBRA_MACHINE'], affinity=affinity, workers=list(WORKERS) if args.phase == 'parallel' else 1,
                  phase=args.phase, physical_cpus=cpus, dispatch=[],
                  topology=subprocess.check_output(['lscpu', '-e=CPU,CORE,SOCKET,NODE,CACHE,ONLINE'], text=True),
                  build='release; fat LTO; one codegen unit; x86-64-v3; empty RUSTC_WRAPPER',
                  binaries={key: dict(path=str(path), sha256=hashlib.sha256(path.read_bytes()).hexdigest())
                            for key, path in binaries.items()},
                  limits=dict(wall_seconds=60, rss_bytes=2 * 1024**3, max_load=args.max_load), attempts=[])
    args.scratch.mkdir(parents=True, exist_ok=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    paths = {}
    matrices = {}
    done, dispatch_done = set(), set()
    if args.resume:
        if args.phase != 'parallel': parser.error('resume currently supports the packed parallel campaign')
        previous = sibling('proof_artifacts').load_cohort(args.output)
        if (previous.get('refusal', {}).get('reason') not in ('load', 'load-before-dispatch')
                or previous.get('repetitions', 5) != args.repeats or previous['phase'] != args.phase
                or previous['binaries'] != cohort['binaries'] or previous['limits'] != cohort['limits']
                or previous['affinity'] != affinity or previous['physical_cpus'] != cpus):
            parser.error('resume requires the same frozen binaries, limits, affinity and topology after a load refusal')
        arms = arms_for(args.phase)
        plan = [(repeat, modulus, arm) for repeat in range(args.repeats) for modulus in study.MODULI
                for arm in (arms if repeat % 2 == 0 else tuple(reversed(arms)))]
        done = resume_keys(previous['attempts'], plan)
        dispatch_done = {(a['repeat'], a['workers']) for a in previous['dispatch']}
        previous.setdefault('resumptions', []).append(dict(runner_commit=cohort['commit'], previous_refusal=previous.pop('refusal')))
        cohort = previous
        for attempt in sibling('study_artifacts').iter_attempts(args.output):
            raw = attempt['raw']
            if attempt['arm'] in ('stock', 'off', 'work'):
                paths.setdefault(attempt['modulus'], {key: value for key, value in raw['statistics'].items()
                    if not key.endswith('_ns') and key != 'full_statistics'})
            if attempt['arm'].endswith('-on'):
                for batch in raw['parallel']['batches']:
                    matrices[(attempt['modulus'], batch['batch_index'])] = batch['input_matrix_digest']
        study.write(args.output, cohort)
    for repeat in range(args.repeats):
        for modulus in study.MODULI:
            arms = arms_for(args.phase)
            for arm in arms if repeat % 2 == 0 else reversed(arms):
                if (repeat, modulus, arm) in done: continue
                load = os.getloadavg()[0]
                if load > args.max_load:
                    cohort['refusal'] = dict(reason='load', load=load, next=[repeat, modulus, arm])
                    study.write(args.output, cohort)
                    raise RuntimeError('load gate refused; partial cohort retained')
                binary = binaries['stock' if arm == 'stock' else 'observed']
                command = [str(binary), str(modulus), '--stages']
                if arm in ('work', 'discovery'):
                    command += ['--' + arm]
                parallel = arm.startswith(('dynamic-', 'static-'))
                child_cpus = sorted(os.sched_getaffinity(0))
                if args.phase == 'parallel':
                    workers = int(arm.split('-')[1]) if parallel else 1
                    child_cpus = cpus[:workers]
                    command = ['taskset', '-c', ','.join(map(str, child_cpus)), *command]
                    if parallel:
                        command += [f'--workers={workers}', '--schedule=' + arm.split('-')[0]]
                        if arm.endswith('-on'): command += ['--work']
                cpu_before = resource.getrusage(resource.RUSAGE_CHILDREN)
                result = study.guarded(command, args.scratch / str(len(cohort['attempts'])), 60, 2 * 1024**3)
                cpu_after = resource.getrusage(resource.RUSAGE_CHILDREN)
                result['cpu_seconds'] = cpu_after.ru_utime + cpu_after.ru_stime - cpu_before.ru_utime - cpu_before.ru_stime
                result['affinity'] = child_cpus
                result.update(repeat=repeat, modulus=modulus, arm=arm, load_before=load,
                              load_after=os.getloadavg()[0], status='failed')
                try:
                    if result['exit'] != 0 or result['stop'] is not None:
                        raise ValueError('child failed or exceeded budget')
                    report = json.loads(result['stdout'])
                    sibling('mq10-profile').check_answer(report, refs[modulus])
                    result['report'] = report
                    result['peak_rss_bytes'] = max(result['observed_peak_rss_bytes'], report['peak_rss_bytes'] or 0)
                    if not 0 < result['peak_rss_bytes'] <= 2 * 1024**3:
                        raise ValueError('missing or over-budget peak RSS')
                    path = {key: value for key, value in report['statistics'].items()
                            if not key.endswith('_ns') and key != 'full_statistics'}
                    invariant = {key: value for key, value in path.items() if key not in ('row_operations', 'max_live_nonzeros')}
                    expected = paths.setdefault(modulus, path)
                    if (invariant != {key: value for key, value in expected.items() if key not in ('row_operations', 'max_live_nonzeros')}
                            if parallel else expected != path):
                        raise ValueError('instrumentation changed F4 trajectory')
                    if parallel:
                        output = report['parallel']
                        if output['workers'] != workers or len(output['batches']) + output['fallbacks'] != report['statistics']['batches']:
                            raise ValueError('missing parallel batches')
                        if arm.endswith('-on'):
                            for index, batch in enumerate(output['batches']):
                                if batch['products'] != batch['work']['coefficient_products'] or batch['products'] != batch['inherited_products'] + batch['discovered_products']:
                                    raise ValueError('worker product aggregation differs')
                                if sum(batch['worker_rows']) != batch['rows'] - batch['split']:
                                    raise ValueError('missing worker rows')
                                key = (modulus, batch['batch_index'])
                                if matrices.setdefault(key, batch['input_matrix_digest']) != batch['input_matrix_digest']:
                                    raise ValueError('matrix inputs changed with schedule')
                    elif arm in ('work', 'discovery'):
                        batches = report['work']['batches']
                        if not batches or any(not batch['completed'] for batch in batches):
                            raise ValueError('missing or incomplete matrix work')
                        if arm == 'discovery':
                            result['census'] = [census(batch['discovery']) for batch in batches]
                            for batch, summary in zip(batches, result['census']):
                                if summary['rows'] != batch['rows'] - batch['reducer_rows']:
                                    raise ValueError('missing candidate rows')
                                if summary['inherited_products'] + summary['discovered_products'] != batch['forward']['coefficient_products']:
                                    raise ValueError('row and batch products disagree')
                    elif report['work'] is not None:
                        raise ValueError('disabled counters unexpectedly present')
                    result.update(status='verified', verification='full-basis-match-to-independent-Singular-reference')
                except (ValueError, KeyError, TypeError) as error:
                    result['failure'] = str(error)
                if args.phase == 'parallel' and result['status'] == 'verified':
                    result['raw'] = result.pop('report')
                    result = sibling('study_artifacts').pack_attempt(result, args.output)
                cohort['attempts'].append(result)
                study.write(args.output, cohort)
                print(repeat, modulus, arm, result['status'], flush=True)
                if result['status'] != 'verified':
                    raise RuntimeError('failed attempt retained: ' + result.get('failure', 'unknown'))
        if args.phase == 'parallel':
            for workers in WORKERS:
                if (repeat, workers) in dispatch_done: continue
                if os.getloadavg()[0] > args.max_load:
                    cohort['refusal'] = dict(reason='load-before-dispatch', repeat=repeat, workers=workers)
                    study.write(args.output, cohort)
                    raise RuntimeError('dispatch load gate refused; partial cohort retained')
                command = ['taskset', '-c', ','.join(map(str, cpus[:workers])), str(binaries['observed']), 'dispatch', str(workers)]
                result = study.guarded(command, args.scratch / f'dispatch-{repeat}-{workers}', 60, 2 * 1024**3)
                result.update(repeat=repeat, workers=workers, load=os.getloadavg()[0])
                cohort['dispatch'].append(result)
                study.write(args.output, cohort)
                if result['exit'] or result['stop']:
                    raise RuntimeError('dispatch failed; attempt retained')


if __name__ == '__main__':
    main()
