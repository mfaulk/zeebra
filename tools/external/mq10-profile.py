#!/usr/bin/env python3
"""Profile shipped MQ10 strategies; retain complete outputs and require the previously verified bases."""
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]


def check_answer(report, reference):
    if report['digest'] != reference['digest'] or report['modulus'] != reference['modulus']:
        raise ValueError('input identity differs from the verified reference')
    if sorted(report['basis']) != sorted(reference['basis']):
        raise ValueError('full reduced basis differs from the verified reference')


def tree_hwm(pid, proc=Path('/proc')):
    # Sum per-process high waters conservatively so a profiler wrapper cannot hide its child.
    pending, seen, total = [pid], set(), 0
    while pending:
        current = pending.pop()
        if current in seen:
            continue
        seen.add(current)
        path = proc / str(current)
        try:
            for line in (path / 'status').read_text().splitlines():
                if line.startswith('VmHWM:'):
                    total += int(line.split()[1]) * 1024
            pending.extend(int(child) for child in (path / 'task' / str(current) / 'children').read_text().split())
        except (FileNotFoundError, ProcessLookupError):
            pass
    return total


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--binary', type=Path, required=True)
    parser.add_argument('--scratch', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--repeats', type=int, default=5)
    parser.add_argument('--callgrind', action='store_true', help='instruction counts; 1800s/4GiB per run; use --repeats 1')
    parser.add_argument('--perf', type=Path, help='native cycle sampling with this perf executable; no stack capture')
    args = parser.parse_args()
    if args.callgrind and args.perf:
        parser.error('choose one profiler')
    if args.repeats < 1:
        parser.error('repeats must be positive')
    affinity = ','.join(str(c) for c in sorted(os.sched_getaffinity(0)))
    if not os.environ.get('ZEEBRA_MACHINE') or os.environ.get('ZEEBRA_AFFINITY') != affinity:
        parser.error('set ZEEBRA_MACHINE and ZEEBRA_AFFINITY to the actual comma-separated CPU set')
    if subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True).strip():
        parser.error('commit the instrument before measuring')
    with gzip.open(ROOT / 'research/competitive/results/grobx-683.json.gz', 'rt') as stream:
        previous = json.load(stream)
    references = {}
    for attempt in previous['attempts']:
        row = attempt['rows'][0]
        if row['problem'] == 'mq-random-10' and row['library'] == 'grobx' and row['outcome'] == 'verified':
            references[row['field']['characteristic']] = attempt['artifacts']
    cohort = {
        'schema': 1,
        'commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        'binary_sha256': hashlib.sha256(args.binary.read_bytes()).hexdigest(),
        'rustc': subprocess.check_output(['rustc', '-vV'], text=True),
        'build': 'release; fat LTO; codegen-units=1; x86-64-v3; debug=1 (line tables); system allocator',
        'machine': os.environ['ZEEBRA_MACHINE'], 'affinity': affinity, 'workers': 1,
        'policy': 'one fresh process per attempt; full basis equality to retained Singular-verified grobx answers; no new cross-engine ratios',
        'profiler': (subprocess.check_output(['valgrind', '--version'], text=True).strip() if args.callgrind else
                     subprocess.check_output([str(args.perf), '--version'], text=True).strip() if args.perf else 'native'),
        'event': 'cycles:u; frequency=997; no call graph' if args.perf else None,
        'profiler_sha256': hashlib.sha256(args.perf.read_bytes()).hexdigest() if args.perf else None,
        'wall_limit_seconds': 1800 if args.callgrind else 120,
        'rss_limit_bytes': (4 if args.callgrind else 2) * 1024**3,
        'attempts': [],
    }
    args.scratch.mkdir(parents=True, exist_ok=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    for repeat in range(args.repeats):
        for modulus in (32003, 2147483647):
            for measured in ((False,) if (args.callgrind or args.perf) else ((False, True) if repeat % 2 == 0 else (True, False))):
                index = len(cohort['attempts'])
                stem = args.scratch / str(index)
                command = [str(args.binary), str(modulus)] + (['--stages'] if measured else [])
                if args.callgrind:
                    command = ['valgrind', '--tool=callgrind', '--cache-sim=no', '--branch-sim=no',
                               '--callgrind-out-file=' + str(stem.with_suffix('.callgrind')), *command]
                if args.perf:
                    command = [str(args.perf), 'record', '--quiet', '-N', '-e', 'cycles:u', '-F', '997',
                               '-o', str(stem.with_suffix('.perf.data')), '--', *command]
                started = time.monotonic_ns()
                peak = 0
                with stem.with_suffix('.json').open('w') as stdout, stem.with_suffix('.stderr').open('w') as stderr:
                    process = subprocess.Popen(command, stdout=stdout, stderr=stderr, start_new_session=True)
                    stop = None
                    while process.poll() is None:
                        peak = max(peak, tree_hwm(process.pid))
                        if peak > cohort['rss_limit_bytes'] or time.monotonic_ns() - started > cohort['wall_limit_seconds'] * 1_000_000_000:
                            stop = 'rss' if peak > cohort['rss_limit_bytes'] else 'wall'
                            os.killpg(process.pid, signal.SIGKILL)
                            process.wait()
                            break
                        time.sleep(0.002)
                result = {'repeat': repeat, 'modulus': modulus, 'measured': measured,
                          'process_wall_ns': time.monotonic_ns() - started,
                          'observed_peak_rss_bytes': peak, 'exit': process.returncode, 'stop': stop}
                if process.returncode == 0 and peak:
                    report = json.loads(stem.with_suffix('.json').read_text())
                    try:
                        check_answer(report, references[modulus])
                        result.update(report=report, verification='full-basis-match-to-retained-verified-reference')
                        if args.callgrind:
                            payload = stem.with_suffix('.callgrind').read_bytes()
                            archive = args.output.with_name(args.output.name + f'.{index}.callgrind.gz')
                            archive.write_bytes(gzip.compress(payload, mtime=0))
                            result['callgrind'] = {'path': archive.name, 'sha256': hashlib.sha256(payload).hexdigest()}
                            result['profiler_stderr'] = stem.with_suffix('.stderr').read_text()
                        if args.perf:
                            payload = stem.with_suffix('.perf.data').read_bytes()
                            archive = args.output.with_name(args.output.name + f'.{index}.perf.data.gz')
                            archive.write_bytes(gzip.compress(payload, mtime=0))
                            result['perf'] = {'path': archive.name, 'sha256': hashlib.sha256(payload).hexdigest()}
                            result['perf_report'] = subprocess.check_output([str(args.perf), 'report', '--stdio', '--no-children', '--percent-limit', '0', '--sort', 'symbol,dso', '-i', str(stem.with_suffix('.perf.data'))], text=True)
                    except ValueError as error:
                        result.update(report=report, verification=str(error))
                else:
                    result['stderr'] = stem.with_suffix('.stderr').read_text()
                cohort['attempts'].append(result)
                with gzip.GzipFile(filename=str(args.output), mode='wb', mtime=0) as stream:
                    stream.write((json.dumps(cohort, indent=2) + '\n').encode())
                if 'report' not in result or result['verification'] != 'full-basis-match-to-retained-verified-reference':
                    raise RuntimeError(f'failed attempt {index} retained in {args.output}')
                print(index, modulus, 'stages' if measured else 'control', round(report['f4_call_ns']/1e6, 3), 'ms', flush=True)


if __name__ == '__main__':
    main()
