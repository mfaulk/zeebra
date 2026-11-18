#!/usr/bin/env python3
"""#901 campaign controller: M30's two controllers joined, so one rotation holds every arm.

`sig_f4_study` children are #857's (`m30-sigf4/run.py`'s command line); MQ10's shipping-F4 rows,
which that example has no field for, are #834's `m29_cost_model` targets. Each child gets
`tools/cpu-context.sh` before and after and frequency sampling (`m29-baseline/costmodel.py`), a
CCD-aligned `taskset` from CPU 8 inside the `bench-reserve` reservation, the §10.5 solve cap
(`timeout --signal=INT`) and `tools/rss-guard.sh` at 8 GiB on the child's own pid.

    tools/bench-reserve.sh run zb-901 8-23 python3 research/m31-baseline/campaign.py \\
        --suite walls --sig BIN --cost BIN --output OUT.jsonl
"""
import argparse
import importlib.util
import json
import os
import subprocess
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def _module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


costmodel = _module('costmodel', HERE.parent / 'm29-baseline' / 'costmodel.py')

FIRST_CPU = 8
CAP_S = 180
RSS_KB = 8 * 2**20
GATING = ['wide64/eco-12', 'goldilocks/katsura-11']
REPORTED = ['wide64/katsura-11', 'goldilocks/mq-random-11', 'goldilocks/cyclic-7', 'wide64/cyclic-7',
            'goldilocks/katsura-4', 'wide64/katsura-4', 'goldilocks/noon-7']
HELD_OUT = ['wide64/katsura-9', 'wide64/noon-8', 'wide64/eco-14']
# Plan §10.3's drop rule, read off the `probe` suite: shipping F4-16 stops on eco-14 at its default
# 32,000,000 live-nonzero limit (37,152,044 needed), so it leaves the cohort and is not replaced.
DROPPED = {'wide64/eco-14'}
MQ10 = ['mq10-32003', 'mq10-m31']
F4_ARMS = ['f4:1', 'f4:4', 'f4:8', 'f4:16']
SIG_ARMS = ['sigf4:1', 'sigf4:16']
SPLIT_ROWS = ['wide64/eco-12', 'goldilocks/katsura-11', 'wide64/katsura-11', 'goldilocks/mq-random-11']


def suite_rows(suite):
    """[(row, arms)] per suite. `walls` is plan §7.1's cohort; `split` is the stage-clock campaign."""
    if suite == 'walls':
        return ([(r, F4_ARMS + SIG_ARMS) for r in GATING + REPORTED + HELD_OUT if r not in DROPPED]
                + [(t, F4_ARMS) for t in MQ10])
    if suite == 'split':
        return [(r, SIG_ARMS) for r in SPLIT_ROWS]
    if suite == 'probe':
        return [('wide64/eco-14', ['f4:16', 'sigf4:1', 'f4:1'])]
    raise ValueError(suite)


def plan(rows, reps):
    """(rep, row, arm) in run order: rows in turn, arms rotated one place per repetition, so each
    arm's repetition r sits beside every other arm's repetition r (the pairing the ratios use)."""
    order = []
    for rep in range(reps):
        for row, arms in rows:
            shift = rep % len(arms)
            order += [(rep, row, arm) for arm in arms[shift:] + arms[:shift]]
    return order


def command(bins, row, arm):
    engine, workers = arm.split(':')
    if '/' not in row:
        return 'm29_cost_model', [str(bins['cost']), '--target', row, '--workers', workers]
    field, name = row.split('/')
    return 'sig_f4_study', [str(bins['sig']), '--field', field, '--name', name, '--engine', engine,
                            '--workers', workers, '--wall-s', str(CAP_S)]


def run_one(bins, row, arm):
    workers = int(arm.split(':')[1])
    cpus = costmodel.cpulist(workers, FIRST_CPU)
    comm, argv = command(bins, row, arm)
    before = costmodel.snapshot(cpus)
    sampler = costmodel.Sampler(cpus)
    sampler.start()
    started = time.perf_counter_ns()
    child = subprocess.Popen(['taskset', '-c', cpus, 'timeout', '--signal=INT', '--kill-after=60s',
                              str(CAP_S + 30), *argv],
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    guard = subprocess.Popen(['bash', str(ROOT / 'tools/rss-guard.sh'), comm, row.split('/')[-1],
                              str(RSS_KB), '--poll', '0.2', '--signal', 'INT'],
                             stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
    stdout, stderr = child.communicate()
    wall = time.perf_counter_ns() - started
    try:
        guard_rc = guard.wait(timeout=10)
    except subprocess.TimeoutExpired:
        guard.kill()
        guard_rc = 'hung'
    sampler.stop.set()
    sampler.join()
    after = costmodel.snapshot(cpus)
    try:
        report = json.loads(stdout.strip().splitlines()[-1])
    except (IndexError, json.JSONDecodeError):
        report = None
    return dict(cpus=cpus, process_wall_ns=wall, returncode=child.returncode, rss_guard_rc=guard_rc,
                before=before, after=after, freq=costmodel.summarize_freq(sampler.samples),
                report=report, stderr=stderr[-2000:])


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--suite', choices=('walls', 'split', 'probe'), required=True)
    p.add_argument('--sig', type=Path, required=True, help='sig_f4_study')
    p.add_argument('--cost', type=Path, help='m29_cost_model (walls suite only)')
    p.add_argument('--reps', type=int, default=9)
    p.add_argument('--start-rep', type=int, default=0, help='resume a killed session')
    p.add_argument('--rows', help='comma-separated subset of the suite rows')
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    rows = suite_rows(args.suite)
    if args.rows:
        keep = set(args.rows.split(','))
        rows = [(r, a) for r, a in rows if r in keep]
    bins = dict(sig=args.sig, cost=args.cost)
    with args.output.open('a') as out:
        for rep, row, arm in plan(rows, args.reps):
            if rep < args.start_rep:
                continue
            record = dict(suite=args.suite, rep=rep, row=row, arm=arm, binary=str(command(bins, row, arm)[1][0]),
                          load_start=os.getloadavg()[0], **run_one(bins, row, arm))
            out.write(json.dumps(record) + '\n')
            out.flush()
            status = (record['report'] or {}).get('status', f"rc={record['returncode']}")
            print(args.suite, rep, row, arm, f"{record['process_wall_ns'] / 1e9:.3f}s", status,
                  f"load={record['load_start']:.1f}", flush=True)


if __name__ == '__main__':
    main()
