"""#903 A/B controller: design 1 (`--engine sigf4 --workers 1`) from two `sig_f4_study` binaries,
fresh process per child, arms rotated per repetition by `m30-sigf4/run.py`'s `plan`, each child
pinned to one CPU with `tools/cpu-context.sh` snapshots before and after.

    tools/bench-reserve.sh run zb-903 8-23 python3 research/m31-sigf4-serial/ab.py \
        --arm base=BIN_A --arm head=BIN_B --out OUT.jsonl --reps 9 --cpu 8 \
        --rows wide64/eco-12 goldilocks/katsura-11 ...
"""
import argparse
import importlib.util
import json
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
SPEC = importlib.util.spec_from_file_location('m30run', os.path.join(ROOT, 'research/m30-sigf4/run.py'))
M30 = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(M30)


def context(cpu):
    done = subprocess.run(['bash', os.path.join(ROOT, 'tools/cpu-context.sh'), str(cpu)],
                          capture_output=True, text=True)
    try:
        return json.loads(done.stdout)
    except json.JSONDecodeError:
        return None


def main(argv):
    parser = argparse.ArgumentParser()
    parser.add_argument('--arm', action='append', required=True, help='label=binary')
    parser.add_argument('--out', required=True)
    parser.add_argument('--reps', type=int, default=9)
    parser.add_argument('--rows', nargs='+', required=True)
    parser.add_argument('--cap', type=int, default=180)
    parser.add_argument('--cpu', type=int, required=True)
    args = parser.parse_args(argv)
    binaries = dict(arm.split('=', 1) for arm in args.arm)
    with open(args.out, 'a') as out:
        for rep, row, arm in M30.plan(args.rows, list(binaries), args.reps):
            field, name = row.split('/')
            cmd = ['taskset', '-c', str(args.cpu), 'timeout', '--signal=INT', '--kill-after=60s',
                   str(args.cap), binaries[arm], '--field', field, '--name', name,
                   '--engine', 'sigf4', '--workers', '1', '--wall-s', str(args.cap)]
            before = context(args.cpu)
            started = time.perf_counter_ns()
            child = subprocess.run(cmd, capture_output=True, text=True)
            wall = time.perf_counter_ns() - started
            after = context(args.cpu)
            try:
                report = json.loads(child.stdout.strip().splitlines()[-1])
            except (IndexError, json.JSONDecodeError):
                report = None
            record = dict(rep=rep, row=row, arm=arm, binary=binaries[arm],
                          returncode=child.returncode, process_wall_ns=wall,
                          context_before=before, context_after=after, report=report,
                          stderr=child.stderr[-2000:])
            out.write(json.dumps(record) + '\n')
            out.flush()
            status = report.get('status') if report else f'rc={child.returncode}'
            print(f'{rep} {row} {arm} {wall / 1e9:.3f}s {status}', file=sys.stderr)


if __name__ == '__main__':
    main(sys.argv[1:])
