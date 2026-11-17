"""#857 campaign controller: fresh-process `sig_f4_study` children, arms rotated per repetition.

Run under `tools/benchlock.sh` with every binary already built. Each child gets
`timeout --signal=INT --kill-after=60s`, and process wall is measured here around the whole
process, which is the authoritative figure (plan §10.2).

    python3 research/m30-sigf4/run.py --bin BIN --out OUT.jsonl --reps 5 \
        --rows wide64/eco-12 goldilocks/katsura-11 --arms sigf4:1 f4:1 f4:16 [--first 24]
"""
import argparse
import json
import os
import subprocess
import sys
import time


def plan(rows, arms, reps):
    """(rep, row, arm) in run order: rows in turn, arms rotated by one place per repetition."""
    order = []
    for rep in range(reps):
        for row in rows:
            shift = rep % len(arms)
            for arm in arms[shift:] + arms[:shift]:
                order.append((rep, row, arm))
    return order


def command(binary, row, arm, cap, first):
    """Pinned to CPUs first..first+workers-1, CCD-aligned as in m29-baseline/costmodel.py."""
    field, name = row.split('/')
    engine, workers = arm.split(':')
    cmd = ['timeout', '--signal=INT', '--kill-after=60s', str(cap), binary,
           '--field', field, '--name', name, '--engine', engine, '--workers', workers,
           '--wall-s', str(cap)]
    if first is None:
        return cmd
    return ['taskset', '-c', f'{first}-{first + int(workers) - 1}'] + cmd


def main(argv):
    parser = argparse.ArgumentParser()
    parser.add_argument('--bin', required=True)
    parser.add_argument('--out', required=True)
    parser.add_argument('--reps', type=int, default=5)
    parser.add_argument('--rows', nargs='+', required=True)
    parser.add_argument('--arms', nargs='+', required=True)
    parser.add_argument('--cap', type=int, default=900)
    parser.add_argument('--first', type=int, default=None)
    args = parser.parse_args(argv)
    with open(args.out, 'a') as out:
        for rep, row, arm in plan(args.rows, args.arms, args.reps):
            cmd = command(args.bin, row, arm, args.cap, args.first)
            load = os.getloadavg()[0]
            started = time.perf_counter_ns()
            child = subprocess.run(cmd, capture_output=True, text=True)
            wall = time.perf_counter_ns() - started
            try:
                report = json.loads(child.stdout.strip().splitlines()[-1])
            except (IndexError, json.JSONDecodeError):
                report = None
            record = dict(rep=rep, row=row, arm=arm, returncode=child.returncode,
                          process_wall_ns=wall, load_start=load, load_end=os.getloadavg()[0],
                          report=report, stderr=child.stderr[-2000:])
            out.write(json.dumps(record) + '\n')
            out.flush()
            status = report.get('status') if report else f'rc={child.returncode}'
            print(f'{rep} {row} {arm} {wall / 1e9:.2f}s {status}', file=sys.stderr)


if __name__ == '__main__':
    main(sys.argv[1:])
