#!/usr/bin/env python3
"""Bounded #592 campaign; publication keeps failed attempts and complete polynomial identities."""
import argparse
from collections import Counter, defaultdict
from statistics import median
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('mq10_profile', Path(__file__).with_name('mq10-profile.py'))
guard = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(report, cell):
    if report['backend'] != cell[1] or report['workers'] != int(cell[2]):
        raise ValueError('backend/worker identity differs')
    result = report['result']
    if cell[0] == 'floor':
        if len(result['samples_ns']) != 32 or any(n <= 0 for n in result['samples_ns']):
            raise ValueError('incomplete dispatch distribution')
        if result['work'] != int(cell[3]):
            raise ValueError('work identity differs')
    else:
        for name in ['input', 'source']:
            text = result['input' if name == 'input' else 'source_basis']
            if hashlib.sha256(text.encode()).hexdigest() != result[name + '_sha256']:
                raise ValueError('polynomial identity differs')
        if result['system'] != cell[3] or len(result['runs']) != 2:
            raise ValueError('incomplete border experiment')
        for run in result['runs']:
            if run['digest'] != result['reference_digest'] or run['dispatches'] < 1:
                raise ValueError('scalar remainders differ or no work executed')


def compiler_processes(proc=Path('/proc')):
    active = []
    for entry in proc.iterdir():
        if not entry.name.isdigit():
            continue
        try:
            name = (entry / 'comm').read_text().strip()
            if name in {'cargo', 'rustc', 'clippy-driver', 'rust-lld', 'ld.lld', 'rust-analyzer'}:
                active.append((entry.name, name))
        except (FileNotFoundError, ProcessLookupError, PermissionError):
            continue
    return active


def cpu_order(topology, allowed):
    groups = {}
    for line in topology.splitlines():
        if not line or line.startswith('#'):
            continue
        cpu, core, socket, _node = map(int, line.split(','))
        if cpu in allowed:
            groups.setdefault((socket, core), []).append(cpu)
    ordered = [sorted(cpus) for _, cpus in sorted(groups.items())]
    return [cpus[0] for cpus in ordered] + [cpu for cpus in ordered for cpu in cpus[1:]]


def save(path, record):
    path.parent.mkdir(parents=True, exist_ok=True)
    with gzip.open(path, 'wt', compresslevel=1) as stream:
        json.dump(record, stream)


def attempt(binary, cell, cpus):
    command = ['taskset', '-c', ','.join(map(str, cpus)), str(binary), *cell]
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    at = time.monotonic_ns()
    process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
    # communicate drains output while enforcing time; the existing guard samples process-tree RSS.
    peak = 0
    outcome = 'complete'
    try:
        while True:
            peak = max(peak, guard.tree_hwm(process.pid))
            try:
                stdout, stderr = process.communicate(timeout=0.005)
                break
            except subprocess.TimeoutExpired:
                if time.monotonic_ns() - at > 60_000_000_000 or peak > 2 * 1024**3:
                    outcome = 'wall-budget' if time.monotonic_ns() - at > 60_000_000_000 else 'rss-budget'
                    os.killpg(process.pid, signal.SIGKILL)
                    stdout, stderr = process.communicate()
                    break
    except KeyboardInterrupt:
        outcome = 'interrupted'
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        stdout, stderr = process.communicate()
    elapsed = time.monotonic_ns() - at
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    row = dict(cell=cell, cpus=cpus, outcome=outcome, exit=process.returncode,
               process_wall_ns=elapsed, process_cpu_ns=int(1e9 * (after.ru_utime + after.ru_stime - before.ru_utime - before.ru_stime)),
               observed_peak_rss_bytes=peak, load=os.getloadavg(), stderr=stderr.decode(errors='replace'), stdout=stdout.decode(errors='replace'))
    if process.returncode or outcome != 'complete':
        row['outcome'] = outcome if outcome != 'complete' else 'failed'
    else:
        try:
            row['report'] = json.loads(stdout)
            validate(row['report'], cell)
            row['observed_peak_rss_bytes'] = max(peak, row['report']['peak_rss_bytes'] or 0)
        except (ValueError, KeyError, TypeError) as error:
            row.update(outcome='invalid', validation_error=str(error))
    return row


def summarize(record):
    if 'end_load' not in record:
        raise ValueError('campaign did not complete')
    plan = record['plan']
    expected = Counter()
    for repeat in range(plan['repeats']):
        for phase in (['floor', 'border'] if plan['phase'] == 'all' else [plan['phase']]):
            cases = [[str(w)] for w in [0, 256, 65536]] if phase == 'floor' else [[s, z] for s in plan['systems'] for z in ['64', 'all']]
            for case in cases:
                for width in plan['workers']:
                    for backend in ['scoped', 'parked', 'rayon']:
                        expected[(repeat, tuple([phase, backend, str(width), *case]))] += 1
    if Counter((r['repeat'], tuple(r['cell'])) for r in record['attempts']) != expected:
        raise ValueError('campaign cells are missing or duplicated')
    groups, identities = defaultdict(list), {}
    for row in record['attempts']:
        if row['outcome'] != 'complete' or row['exit'] != 0:
            raise ValueError('unsuccessful attempt remains in campaign')
        validate(row['report'], row['cell'])
        cell = row['cell']
        result = row['report']['result']
        if cell[0] == 'border':
            key = tuple(cell[3:])
            identity = (result['input_sha256'], result['source_sha256'], result['reference_digest'])
            if identities.setdefault(key, identity) != identity:
                raise ValueError('input or complete remainder identity changed across arms')
        groups[tuple(cell)].append(row)
    summary = []
    for cell, rows in sorted(groups.items()):
        phase, backend, workers, *case = cell
        reports = [r['report']['result'] for r in rows]
        times = [median(r['samples_ns']) if phase == 'floor' else r['runs'][1]['whole_border_ns'] for r in reports]
        entry = dict(phase=phase, backend=backend, workers=int(workers), case=case,
                     median_ns=median(times), range_ns=[min(times), max(times)],
                     process_wall_ns=median(r['process_wall_ns'] for r in rows),
                     cpu_ns=median(r['process_cpu_ns'] for r in rows),
                     rss_bytes=max(r['observed_peak_rss_bytes'] for r in rows),
                     build_ns=median(r['build_ns'] for r in reports))
        if phase == 'border':
            for name in ['reduction_ns', 'closure_ns', 'peak_batch_ns', 'zeroed_cells', 'jobs', 'dispatches', 'reducer_entries', 'peak_entries']:
                entry[name] = median(r['runs'][1][name] for r in reports)
            entry['scalar_reduction_ns'] = median(r['scalar_border_reduction_ns'] for r in reports)
            entry['scalar_whole_border_ns'] = median(r['scalar_whole_border_ns'] for r in reports)
            entry['retained_scratch_bytes'] = max(r['retained_scratch_capacity_cells'] for r in reports) * 8
        else:
            entry['cold_ns'] = median(r['cold_ns'] for r in reports)
            entry['active_workers_range'] = [min(v for r in reports for v in r['active_workers']), max(v for r in reports for v in r['active_workers'])]
        summary.append(entry)
    for row in summary:
        base = next((r for r in summary if (r['phase'], r['backend'], r['case'], r['workers']) == (row['phase'], row['backend'], row['case'], 1)), None)
        row['speedup'] = base['median_ns'] / row['median_ns'] if base else None
        row['efficiency'] = row['speedup'] / row['workers'] if base else None
    return summary


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--binary', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--phase', choices=['floor', 'border', 'all'], default='all')
    parser.add_argument('--repeats', type=int, default=5)
    parser.add_argument('--workers', default='1,2,4,8,16,32,64,128')
    parser.add_argument('--systems', default='katsura-7,planted-10')
    args = parser.parse_args()
    workers = [int(w) for w in args.workers.split(',')]
    if not 1 <= args.repeats <= 5 or any(w not in [1, 2, 4, 8, 16, 32, 64, 128] for w in workers):
        parser.error('declare 1–5 repetitions and standard worker counts')
    if subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True).strip():
        parser.error('commit source before measuring')
    affinity = ','.join(map(str, sorted(os.sched_getaffinity(0))))
    if not os.environ.get('ZEEBRA_MACHINE') or os.environ.get('ZEEBRA_AFFINITY') != affinity:
        parser.error('set machine and actual parent affinity')
    if compiler_processes():
        parser.error('compiler activity is present; defer measurement')
    if os.getloadavg()[0] >= 8:
        parser.error('start load is at least eight; defer measurement')
    topology = subprocess.check_output(['lscpu', '-p=CPU,CORE,SOCKET,NODE'], text=True)
    cpus = cpu_order(topology, os.sched_getaffinity(0))
    if max(workers) > len(cpus):
        parser.error('requested more workers than available logical CPUs')
    record = dict(schema=1, plan=dict(phase=args.phase, workers=workers, systems=args.systems.split(','), repeats=args.repeats), source=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                  binary=str(args.binary.resolve()), binary_sha256=sha(args.binary), cargo_lock_sha256=sha(ROOT / 'Cargo.lock'),
                  cargo_toml_sha256=sha(ROOT / 'Cargo.toml'), config_sha256=sha(ROOT / '.cargo/config.toml'),
                  profile='release; fat LTO; codegen-units=1; x86-64-v3',
                  rustc=subprocess.check_output(['rustc', '-Vv'], text=True), topology=topology,
                  environment={k: os.environ.get(k) for k in ['ZEEBRA_MACHINE', 'ZEEBRA_AFFINITY', 'RUSTFLAGS', 'CARGO_TARGET_DIR', 'TMPDIR']},
                  command=list(os.sys.argv), start_load=os.getloadavg(), attempts=[])
    def interrupted(_signum, _frame):
        raise KeyboardInterrupt
    for sig in [signal.SIGTERM, signal.SIGHUP]:
        signal.signal(sig, interrupted)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    save(args.output, record)
    try:
        with Path(str(args.output) + '.journal.jsonl').open('w') as journal:
            for repeat in range(args.repeats):
                for phase in (['floor', 'border'] if args.phase == 'all' else [args.phase]):
                    cases = [[str(work)] for work in [0, 256, 65536]] if phase == 'floor' else [[system, size] for system in args.systems.split(',') for size in ['64', 'all']]
                    for case in cases:
                        for width in workers:
                            backends = ['scoped', 'parked', 'rayon']
                            backends = backends[repeat % 3:] + backends[:repeat % 3]
                            for backend in backends:
                                row = attempt(args.binary, [phase, backend, str(width), *case], cpus[:width])
                                row['repeat'] = repeat
                                record['attempts'].append(row)
                                journal.write(json.dumps(row) + '\n')
                                journal.flush()
                                print(len(record['attempts']), row['cell'], row['outcome'], flush=True)
                                if row['outcome'] != 'complete':
                                    raise SystemExit('retained unsuccessful attempt; stop campaign')
            if sha(args.binary) != record['binary_sha256']:
                raise SystemExit('binary changed during campaign')
            record['end_load'] = os.getloadavg()
    finally:
        save(args.output, record)


if __name__ == '__main__':
    main()
