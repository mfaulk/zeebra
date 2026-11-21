#!/usr/bin/env python3
"""#834 cost-model campaign: fresh-process `m29_cost_model` runs with CPU context around each child.

Each child runs under `taskset` on CPUs FIRST..FIRST+w-1 (CCD-aligned from 8), with a
`tools/cpu-context.sh` snapshot before and after and the CPUs' scaling frequency sampled every
25 ms while it runs. Nothing is normalized: process wall is the figure; the context is beside it.
Arm order rotates per repetition so no arm always takes the same slot.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))
# Moved to the shared runner (#967); re-exported so the M29-M32 campaigns that import them replay.
from bench_campaign import Sampler, cpulist, snapshot, summarize_freq  # noqa: E402,F401

TARGETS = ('mq10-32003', 'mq10-m31', 'eco12-wide64', 'mq11-goldilocks')
WORKERS = (1, 4, 8, 16)
FIRST_CPU = 8


def plan(suite, reps):
    """(rep, target, workers, extra-args, arm) in run order; arms rotate across repetitions."""
    if suite == 'walls':
        arms = [(t, w, [], 'plain') for t in TARGETS for w in WORKERS]
    elif suite == 'stages':
        arms = [(t, w, ['--stages'], 'stages') for t in TARGETS for w in WORKERS]
    elif suite == 'ab831':
        arms = [(t, w, ['--pair-multiples', p], p) for t in TARGETS for w in (1, 16)
                for p in ('every', 'distinct')]
    elif suite == 'fl':
        # #828 cross-check: one parallel-FL build, its own default order against FL, 16 workers.
        arms = [(t, 16, ['--batch-order', o], o) for t in ('eco12-wide64', 'mq11-goldilocks')
                for o in ('forward', 'fl')]
    elif suite == 'flstages':
        # The same pairs with stage clocks, to say which stages FL moves.
        arms = [(t, 16, ['--batch-order', o, '--stages'], o) for t in ('eco12-wide64', 'mq11-goldilocks')
                for o in ('forward', 'fl')]
    elif suite == 'census':
        arms = [(t, 1, [m], m.lstrip('-')) for t in TARGETS for m in ('--work', '--discovery')]
    else:
        raise ValueError(suite)
    out = []
    for rep in range(reps):
        shift = (rep * 5) % len(arms)
        out += [(rep, *a) for a in arms[shift:] + arms[:shift]]
    return out


def settle(limit_load, max_wait):
    """Wait (bounded) for the 1-minute load to fall under the limit; return seconds waited."""
    waited = 0.0
    while os.getloadavg()[0] > limit_load and waited < max_wait:
        time.sleep(5)
        waited += 5
    return waited


def run_one(binary, target, workers, extra, child_wall):
    cpus = cpulist(workers)
    before = snapshot(cpus)
    sampler = Sampler(cpus)
    sampler.start()
    started = time.perf_counter_ns()
    try:
        r = subprocess.run(['taskset', '-c', cpus, str(binary), '--target', target, '--workers', str(workers),
                            *extra], capture_output=True, text=True, timeout=child_wall)
        rc, stdout, stderr = r.returncode, r.stdout, r.stderr
    except subprocess.TimeoutExpired as e:
        rc, stdout, stderr = 'timeout', e.stdout or '', e.stderr or ''
    wall = time.perf_counter_ns() - started
    sampler.stop.set()
    sampler.join()
    after = snapshot(cpus)
    report = None
    if rc == 0:
        report = json.loads(stdout)
    return dict(cpus=cpus, process_wall_ns=wall, rc=rc, stderr=stderr[-2000:] if rc else '',
                before=before, after=after, freq=summarize_freq(sampler.samples), report=report)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--binary', type=Path, required=True)
    p.add_argument('--suite', choices=('walls', 'stages', 'ab831', 'census', 'fl', 'flstages'), required=True)
    p.add_argument('--reps', type=int, default=3)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--child-wall', type=float, default=240)
    # Off by default: a 16-worker child lifts the 1-minute load by ~16 itself (see the benchlock notes).
    p.add_argument('--load-limit', type=float, default=float('inf'))
    p.add_argument('--settle-max', type=float, default=120)
    p.add_argument('--targets', default=','.join(TARGETS))
    args = p.parse_args()
    keep = set(args.targets.split(','))
    with args.output.open('a') as out:
        for rep, target, workers, extra, arm in plan(args.suite, args.reps):
            if target not in keep:
                continue
            waited = settle(args.load_limit, args.settle_max)
            record = dict(suite=args.suite, rep=rep, target=target, workers=workers, arm=arm,
                          settle_waited_s=waited, binary=str(args.binary),
                          **run_one(args.binary, target, workers, extra, args.child_wall))
            out.write(json.dumps(record) + '\n')
            out.flush()
            status = record['report']['status'] if record['report'] else f"rc={record['rc']}"
            print(args.suite, rep, target, workers, arm, f"{record['process_wall_ns'] / 1e9:.3f}s",
                  status, f"load={record['before'].get('load1')}", flush=True)


if __name__ == '__main__':
    main()
