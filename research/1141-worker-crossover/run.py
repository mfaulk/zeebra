#!/usr/bin/env python3
"""#1141's held-out check of the term-count `WorkerCrossover` rule: fresh pinned processes of
`sig_f4_study --generate` under the conventional F4 (`f4`) and the forced signature engine
(`sigf4`) at 4, 8 and 16 workers. The rule's route is computed from the input's features
(`features.py`), so the entry point is not timed. Run under `tools/bench-reserve.sh run` on
CCDs 1-2; each child is pinned to CPUs 8..8+w-1 by `tools/bench_campaign.run_child`.

    run.py --sig <sig_f4_study> --output held.jsonl [--reps 9] [--rows a,b] [--probe]

`--probe` records each row's features and one solve per forced engine at 16 workers, so the
20 ms floor and the 30 s ceiling are fixed before any timed repetition.
"""
import argparse
import json
import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))
from bench_campaign import cpulist, plan, run_child  # noqa: E402
from features import features  # noqa: E402

ROWS = (
    # Ladder MQ generator at seeds nobody has timed (10-13 are #1141's development data).
    *(f'{f}/mq-random-10-s{s}' for s in range(14, 26) for f in ('gf32003', 'm31')),
    # Controls: MQ10 (seed 10) and katsura-10, both read before.
    'gf32003/mq-random-10-s10', 'm31/mq-random-10-s10', 'gf32003/katsura-10', 'm31/katsura-10',
)
ENGINES = ('f4', 'sigf4')
WORKERS = (4, 8, 16)
CAP_S = 120


def argv(sig, row, engine, workers, extra=()):
    field, name = row.split('/')
    return [str(sig), '--field', field, '--name', name, '--generate', '--engine', engine,
            '--workers', str(workers), '--wall-s', str(CAP_S), '--digest-only', *extra]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--sig', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--reps', type=int, default=9)
    p.add_argument('--rows')
    p.add_argument('--probe', action='store_true')
    args = p.parse_args()
    rows = args.rows.split(',') if args.rows else list(ROWS)
    with args.output.open('a') as out:
        if args.probe:
            for row in rows:
                rec = dict(suite='probe', row=row, features=features(str(args.sig), row))
                for engine in ENGINES:
                    r = run_child(argv(args.sig, row, engine, 16), cpulist(16), CAP_S + 30)
                    rec[engine] = dict(wall_ns=r['process_wall_ns'], rc=r['returncode'])
                out.write(json.dumps(rec) + '\n')
                out.flush()
                print(row, {e: rec[e]['wall_ns'] / 1e6 for e in ENGINES}, rec['features'], flush=True)
            return
        arms = [f'{e}:{w}' for w in WORKERS for e in ENGINES]
        for rep, row, arm in plan([(r, arms) for r in rows], args.reps):
            engine, workers = arm.split(':')
            cpus = cpulist(int(workers))
            r = run_child(argv(args.sig, row, engine, workers), cpus, CAP_S + 30)
            stdout = r['stdout'].decode(errors='replace')
            try:
                report = json.loads(stdout.strip().splitlines()[-1])
            except (IndexError, json.JSONDecodeError):
                report = None
            rec = dict(suite='held', rep=rep, row=row, engine=engine, workers=int(workers), cpus=cpus,
                       load_start=os.getloadavg()[0], process_wall_ns=r['process_wall_ns'],
                       returncode=r['returncode'], before=r['before'], after=r['after'],
                       report=report, stderr=r['stderr'].decode(errors='replace')[-2000:])
            out.write(json.dumps(rec) + '\n')
            out.flush()
            if r['returncode'] != 0 or report is None:
                print('FAILED', rep, row, arm, r['returncode'], flush=True)


if __name__ == '__main__':
    main()
