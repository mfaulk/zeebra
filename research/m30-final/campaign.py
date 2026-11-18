#!/usr/bin/env python3
"""#862 final cohort: the M30-0 baseline and the final `main` interleaved in one campaign.

Protocol §2: an arm that changes the library runs *beside* a baseline built from the freeze, not
against #855's published walls. Each child goes through #834's `costmodel.run_one` (fresh process,
CCD-aligned `taskset` from CPU 8, `tools/cpu-context.sh` before and after, clock sampling). Arms are
(binary, target, workers); the two binaries alternate inside every rotation, so a load change hits
both. Timed walls, stage clocks and the work census are separate suites, never pooled.
"""
import argparse
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location('costmodel', HERE.parent / 'm29-baseline' / 'costmodel.py')
costmodel = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(costmodel)

PRIMARY = costmodel.TARGETS
# #861's held-out instance, and the two #855 pinned (pins.json `held_out`) and never ran.
HELD_OUT = ('katsura11-m31', 'katsura11-wide64', 'cyclic7-wide64')
TARGETS = PRIMARY + HELD_OUT
WORKERS = costmodel.WORKERS
BINARIES = ('baseline', 'final')
SUITES = ('walls', 'stages', 'census')


def plan(suite, reps, targets=TARGETS):
    """(rep, binary, target, workers, extra-args, arm) in run order; arms rotate per repetition."""
    if suite == 'walls':
        arms = [(b, t, w, [], f'{b}{w}') for t in targets for w in WORKERS for b in BINARIES]
    elif suite == 'stages':
        arms = [(b, t, w, ['--stages'], f'{b}{w}') for t in targets for w in (1, 16) for b in BINARIES]
    elif suite == 'census':
        # Deterministic counts: one repetition per binary and mode, serial route only.
        arms = [(b, t, 1, [m], f'{b}-{m.lstrip("-")}') for t in targets for m in ('--work', '--discovery')
                for b in BINARIES]
    else:
        raise ValueError(suite)
    out = []
    for rep in range(reps):
        # An even shift keeps each baseline/final pair adjacent and in the same order.
        shift = (rep * 10) % len(arms)
        out += [(rep, *a) for a in arms[shift:] + arms[:shift]]
    return out


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--baseline', type=Path, required=True, help='m29_cost_model built on the freeze library')
    p.add_argument('--final', type=Path, required=True, help='m29_cost_model built at the final main')
    p.add_argument('--suite', choices=SUITES, required=True)
    p.add_argument('--reps', type=int, default=9)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--child-wall', type=float, default=600)
    p.add_argument('--targets')
    args = p.parse_args()
    targets = tuple(args.targets.split(',')) if args.targets else TARGETS
    unknown = set(targets) - set(TARGETS)
    if unknown:
        p.error(f'unknown targets {sorted(unknown)}')
    binaries = dict(baseline=args.baseline, final=args.final)
    with args.output.open('a') as out:
        for rep, which, target, workers, extra, arm in plan(args.suite, args.reps, targets):
            record = dict(suite=args.suite, rep=rep, target=target, workers=workers, arm=arm,
                          build=which, binary=str(binaries[which]),
                          **costmodel.run_one(binaries[which], target, workers, extra, args.child_wall))
            out.write(json.dumps(record) + '\n')
            out.flush()
            status = 'ok' if record['report'] else f"rc={record['rc']}"
            print(args.suite, rep, target, workers, arm, f"{record['process_wall_ns'] / 1e9:.3f}s",
                  status, f"load={record['before'].get('load1')}", flush=True)


if __name__ == '__main__':
    main()
