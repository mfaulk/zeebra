#!/usr/bin/env python3
"""#978's held-out check of the narrowed `WorkerCrossover` band: fresh pinned processes of
`sig_f4_study --generate` under the conventional F4 (`f4`), the forced signature engine (`sigf4`)
and the opt-in entry point (`entry`) at 4, 8 and 16 workers. Run under `tools/bench-reserve.sh run`
on CCDs 1-2; each child is pinned to CPUs 8..8+w-1 by `tools/bench_campaign.run_child`.

    run.py --sig <sig_f4_study> --output held.jsonl [--reps 9] [--rows a,b] [--probe]

`--probe` runs each row's `--input-only` and one `entry` solve at 16 workers, so the witness
grouping and the 20 ms floor are fixed before any timed repetition.
"""
import argparse
import json
import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))
from bench_campaign import cpulist, plan, run_child  # noqa: E402

ROWS = (
    # Ladder MQ generator at seeds the M31/M32 cohorts never read (MQ10 is seed 10).
    'gf32003/mq-random-10-s11', 'gf32003/mq-random-10-s12', 'gf32003/mq-random-10-s13',
    'm31/mq-random-10-s11', 'm31/mq-random-10-s12', 'm31/mq-random-10-s13',
    # Dense planted m = 2n (#945's family).
    'gf32003/mq-dense-10-s1', 'gf32003/mq-dense-10-s2', 'm31/mq-dense-10-s1', 'm31/mq-dense-10-s2',
    # katsura-10 at the fields M32 did not read it at (it read m31).
    'gf32003/katsura-10', 'goldilocks/katsura-10', 'wide64/katsura-10',
)
ENGINES = ('f4', 'sigf4', 'entry')
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
                field, name = row.split('/')
                r = run_child([str(args.sig), '--field', field, '--name', name, '--generate',
                               '--input-only'], cpulist(1), 60)
                entry = run_child(argv(args.sig, row, 'entry', 16), cpulist(16), CAP_S + 30)
                rec = dict(suite='probe', row=row, input=r['stdout'].decode(errors='replace'),
                           entry_wall_ns=entry['process_wall_ns'], entry_rc=entry['returncode'],
                           entry=entry['stdout'].decode(errors='replace').strip().splitlines()[-1:])
                out.write(json.dumps(rec) + '\n')
                out.flush()
                print(row, entry['process_wall_ns'] / 1e6, 'ms', rec['entry'], flush=True)
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
