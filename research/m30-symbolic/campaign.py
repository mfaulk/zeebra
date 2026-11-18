#!/usr/bin/env python3
"""#859 symbolic cost-model campaign: fresh-process children through #834's `costmodel.run_one`.

Same placement, CPU-context snapshots, clock sampling and arm rotation as the M29 campaign; only the
arms differ. `walls` and `stages` run `m29_cost_model` (no `research-work`), the replay suites run
`symbolic_cost_model`. Timed walls, stage clocks and replays are separate suites, never pooled.
"""
import argparse
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location('costmodel', HERE.parent / 'm29-baseline' / 'costmodel.py')
costmodel = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(costmodel)

TARGETS = costmodel.TARGETS + ('katsura11-m31',)
# #861: the small tasks the plan's <=5% regression limit is read on. Not in TARGETS, so no earlier
# suite's default plan changes; the `small` suite runs these unless --targets narrows them.
SMALL_TARGETS = ('katsura6-m31', 'katsura7-m31', 'cyclic6-m31')
# #861: mid-size controls for the gate, run at every worker count like the small tasks.
MID_TARGETS = ('katsura8-m31', 'cyclic7-m31')
WORKERS = costmodel.WORKERS
SUITES = ('walls', 'stages', 'components', 'level', 'intern', 'live', 'scratch', 'small', 'gate')
MERGES = ('serial', 'sharded')
# #860: 0 = the team starts lazily at the first wide level. The first intern campaign (retained as
# intern-seed512) used 512, which sent 17 of 23 Eco-12 batches down the serial path: pair count does
# not predict closure size.
MIN_SEED_ROWS = 0


def plan(suite, reps, targets=TARGETS):
    """(rep, target, workers, extra-args, arm) in run order; arms rotate across repetitions."""
    if suite == 'walls':
        arms = [(t, w, [], 'plain') for t in targets for w in WORKERS]
    elif suite == 'stages':
        arms = [(t, w, ['--stages'], 'stages') for t in targets for w in WORKERS]
    elif suite == 'components':
        # The replay is serial; forward elimination at 16 only shortens the run around it.
        arms = [(t, 16, ['--replay', 'components'], 'components') for t in targets]
    elif suite == 'level':
        # Every team size runs on the 16-CPU placement, so only the team differs between arms.
        arms = [(t, 16, ['--replay', 'level', '--level-workers', str(lw)], f'level{lw}')
                for t in targets for lw in WORKERS]
    elif suite == 'intern':
        # #860: both prototypes replayed against the serial closure on every live batch.
        arms = [(t, 16, ['--replay', 'intern', '--merge', m, '--level-workers', str(lw),
                         '--min-seed-rows', str(MIN_SEED_ROWS)], f'{m}{lw}')
                for t in targets for m in MERGES for lw in WORKERS[1:]]
    elif suite == 'live':
        # #860: complete F4 with a prototype serving every batch, against the shipping path in
        # the same binary; the team is the forward worker budget.
        arms = []
        for t in targets:
            for w in WORKERS:
                merges = ('off', 'serial', 'sharded') if w == 16 else ('off', 'serial')
                arms += [(t, w, ['--replay', 'live', '--merge', m, '--level-workers', str(w),
                                 '--min-seed-rows', str(MIN_SEED_ROWS)], f'{m}{w}') for m in merges]
    elif suite == 'scratch':
        # #871: caller-owned scratch. Shipping and the serial merge at 1 and 16 workers; at 16 the
        # run-long retention too, which keeps the scratch resident through every matrix.
        live = ['--replay', 'live', '--min-seed-rows', str(MIN_SEED_ROWS)]
        arms = []
        for t in targets:
            for w in (1, 16):
                arms.append((t, w, live + ['--merge', 'off', '--level-workers', str(w)], f'off{w}'))
                arms.append((t, w, live + ['--merge', 'serial', '--level-workers', str(w),
                                           '--retain', 'batch'], f'serial{w}'))
            arms.append((t, 16, live + ['--merge', 'serial', '--level-workers', '16',
                                        '--retain', 'run'], 'serialrun16'))
    elif suite == 'small':
        # #861 precondition: shipping and the serial merge, paired at every worker count.
        live = ['--replay', 'live', '--min-seed-rows', str(MIN_SEED_ROWS)]
        arms = [(t, w, live + ['--merge', m, '--level-workers', str(w)], f'{m}{w}')
                for t in targets for w in WORKERS for m in ('off', 'serial')]
    elif suite == 'gate':
        # #861 acceptance: the shipped option (`--merge auto`) against the serial closure (`off`),
        # small targets at every worker count, substantial ones at 1 and 16.
        live = ['--replay', 'live', '--min-seed-rows', str(MIN_SEED_ROWS)]
        arms = [(t, w, live + ['--merge', m, '--level-workers', str(w)], f'{m}{w}')
                for t in targets for w in (WORKERS if t in SMALL_TARGETS + MID_TARGETS else (1, 16))
                for m in ('off', 'auto')]
    else:
        raise ValueError(suite)
    out = []
    for rep in range(reps):
        shift = (rep * 5) % len(arms)
        out += [(rep, *a) for a in arms[shift:] + arms[:shift]]
    return out


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--binary', type=Path, required=True)
    p.add_argument('--suite', choices=SUITES, required=True)
    p.add_argument('--reps', type=int, default=5)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--child-wall', type=float, default=600)
    p.add_argument('--targets')
    args = p.parse_args()
    default = {'small': SMALL_TARGETS, 'gate': TARGETS + SMALL_TARGETS + MID_TARGETS}.get(args.suite, TARGETS)
    targets = tuple(args.targets.split(',')) if args.targets else default
    unknown = set(targets) - set(TARGETS) - set(SMALL_TARGETS) - set(MID_TARGETS)
    if unknown:
        p.error(f'unknown targets {sorted(unknown)}')
    with args.output.open('a') as out:
        for rep, target, workers, extra, arm in plan(args.suite, args.reps, targets):
            record = dict(suite=args.suite, rep=rep, target=target, workers=workers, arm=arm,
                          binary=str(args.binary),
                          **costmodel.run_one(args.binary, target, workers, extra, args.child_wall))
            out.write(json.dumps(record) + '\n')
            out.flush()
            status = 'ok' if record['report'] else f"rc={record['rc']}"
            print(args.suite, rep, target, workers, arm, f"{record['process_wall_ns'] / 1e9:.3f}s",
                  status, f"load={record['before'].get('load1')}", flush=True)


if __name__ == '__main__':
    main()
