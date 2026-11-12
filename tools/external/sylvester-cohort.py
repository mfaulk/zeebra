#!/usr/bin/env python3
"""Run one digest/engine per guarded process and retain all outcomes and complete artifacts."""
import argparse
import json
import os
from pathlib import Path
import signal
import subprocess
import time


def run(binary, directory, index, row, modulus, workers, engine, wall=60, rss=2048):
    stem = directory / str(index)
    output = stem.with_suffix('.json')
    command = [str(binary), '--row', row, '--modulus', str(modulus), '--workers', str(workers),
               '--engine', engine, '--wall', str(wall), '--rss-mib', str(rss), '--output', str(output)]
    started = time.monotonic_ns()
    peak = 0
    with stem.with_suffix('.stdout').open('w') as stdout, stem.with_suffix('.stderr').open('w') as stderr:
        process = subprocess.Popen(command, stdout=stdout, stderr=stderr, start_new_session=True)
        while process.poll() is None:
            try:
                lines = Path(f'/proc/{process.pid}/status').read_text().splitlines()
                for line in lines:
                    if line.startswith('VmHWM:'):
                        peak = max(peak, int(line.split()[1]) * 1024)
            except FileNotFoundError:
                pass
            if peak > 2 * 1024 * 1024 * 1024 or time.monotonic_ns() - started > 185_000_000_000:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
                raise RuntimeError(f'parent guard stopped {command}; logs retained at {stem}')
            time.sleep(0.002)
        if process.returncode != 0:
            raise RuntimeError(f'runner failed ({process.returncode}); inspect {stem}.stderr')
    if not peak:
        raise RuntimeError('parent RSS was not observed; refusing an unguarded record')
    attempt = json.loads(output.read_text())
    attempt['artifacts']['parent_guard_peak_rss_bytes'] = peak
    attempt['artifacts']['parent_guard_wall_ns'] = time.monotonic_ns() - started
    record = attempt['rows'][0]
    print(index, row, modulus, workers, engine, record['outcome'], flush=True)
    return attempt


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--binary', type=Path, required=True)
    parser.add_argument('--scratch', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--append-history', action='store_true')
    args = parser.parse_args()
    if not os.environ.get('ZEEBRA_MACHINE') or not os.environ.get('ZEEBRA_AFFINITY'):
        parser.error('set ZEEBRA_MACHINE and ZEEBRA_AFFINITY and pin the launcher')
    requested = set()
    for part in os.environ['ZEEBRA_AFFINITY'].split(','):
        endpoints = [int(n) for n in part.split('-')]
        requested.update(range(endpoints[0], endpoints[-1] + 1))
    if requested != set(os.sched_getaffinity(0)):
        parser.error('actual CPU affinity differs from ZEEBRA_AFFINITY')
    args.scratch.mkdir(parents=True, exist_ok=True)
    cases = [(row, modulus) for modulus in (32003, 2147483647)
             for row in ('katsura-4', 'cyclic-5', 'mq-random-6', 'mq-random-10')]
    attempts = []
    for repetition in range(3):
        engines = ('zeebra', 'sylvester', 'sylvester-certified') if repetition % 2 == 0 else ('sylvester-certified', 'sylvester', 'zeebra')
        for workers in (1,):
            for row, modulus in cases:
                for engine in engines:
                    attempts.append(run(args.binary, args.scratch, len(attempts), row, modulus, workers, engine))
    attempts.append(run(args.binary, args.scratch, len(attempts), 'katsura-6', 2147483647, 1, 'sylvester', rss=0))
    attempts.append(run(args.binary, args.scratch, len(attempts), 'katsura-6', 2147483647, 1, 'sylvester', wall=0))
    attempts.append(run(args.binary, args.scratch, len(attempts), 'katsura-4', 32003, 4, 'sylvester-certified'))
    attempts.append(run(args.binary, args.scratch, len(attempts), 'katsura-4', 32003, 4, 'zeebra'))
    rows = [attempt['rows'][0] for attempt in attempts]
    cohort = {key: value for key, value in attempts[0].items() if key not in ('rows', 'artifacts')}
    cohort.update(row_count=len(rows), rows=rows, attempts=attempts)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(cohort, indent=2, ensure_ascii=False) + '\n')
    if args.append_history:
        path = Path('research/competitive/results/history.json')
        history = json.loads(path.read_text())
        original = history['rows'][:]
        history['rows'].extend(rows)
        history['row_count'] = len(history['rows'])
        assert history['rows'][:len(original)] == original
        path.write_text(json.dumps(history, indent=2, ensure_ascii=False) + '\n')


if __name__ == '__main__':
    main()
