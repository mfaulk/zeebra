#!/usr/bin/env python3
"""#942 M32-I final cohort at freeze F3 (plan §7.6, §10, §13), on M31's child runner
(`research/m31-baseline/campaign.py` `run_one`: CCD-aligned taskset from CPU 8, `cpu-context`
before and after each child, frequency sampling, `timeout --signal=INT`, `rss-guard` at 8 GiB).

One harness for every Zeebra arm (#958's lesson). Both builds compile the same
`examples/sig_f4_study.rs`: `research/m32-katsura9-gap/harness.rs` (SHA-256 `9d2b2776…`), copied
over each tree's own example, so the library is the only thing that differs between `f3` and
`m31`. One protocol per suite, the same on every arm of it:

  dev, held   one solve per fresh process; the figure is process wall (and the report's stage
              clocks). No `--calls` and no `--repeat` anywhere.
  small       `--calls 20` on every arm (one cold call, 20 warm, the first result kept live; the
              figure is the median warm call per process, #934's method). `--repeat` is not used:
              it costs 5-6% on katsura-9 through glibc heap trimming (#958).

Arms (`label:workers`), interleaved and rotated one place per repetition, 1 s settle before each
child (#827's boost hysteresis):

  f4:W    F3 conventional F4 (`--engine f4`)
  en:W    F3 adaptive path: `grobner::f4_signature` with #950's dispatch (`--engine entry`)
  sg:W    F3 signature engine forced (`--engine sigf4`, `--claim` above one worker: the parallel
          cascade the entry point takes on signature-routed rows), so its change is visible on rows
          the dispatcher routes away
  mf4:W   M31 reference `8715c8ed`, conventional F4
  men:W   M31 reference `8715c8ed`, `f4_signature`
  msg:W   M31 reference `8715c8ed`, signature engine forced as `sg` (T1's stage clocks)
  ec:W    F3 adaptive path with `--certify` after the timed solve (`certify` suite, one child)

    tools/bench-reserve.sh run zb-942 8-23 python3 -u research/m32-final/campaign.py \\
        --suite dev --bins BINDIR --output OUT.jsonl
"""
import argparse
import importlib.util
import json
import os
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SPEC = importlib.util.spec_from_file_location('m31campaign', ROOT / 'research/m31-baseline/campaign.py')
BASE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BASE)

W4 = [1, 4, 8, 16]
BIG = ['wide64/eco-12', 'goldilocks/katsura-11', 'wide64/katsura-11', 'goldilocks/mq-random-11']
MQ10 = ['gf32003/mq-random-10', 'm31/mq-random-10']
CONTROLS = ['goldilocks/cyclic-7', 'wide64/cyclic-7', 'goldilocks/noon-7', 'wide64/noon-8']
KATSURA4 = ['goldilocks/katsura-4', 'wide64/katsura-4']
KATSURA9 = ['wide64/katsura-9']
HELD_OUT = ['goldilocks/mq-random-10', 'm31/katsura-10', 'm31/eco-11']
DEV = BIG + MQ10 + CONTROLS + KATSURA4 + KATSURA9


def arms(labels, workers):
    return [f'{a}:{w}' for a in labels for w in workers]


# Every timed row: F3's two engines at 1/4/8/16, the forced signature engine at 1 and 16, the M31
# reference at 16 (both entry points) and its f4_signature at 1.
COMMON = arms(('f4', 'en'), W4) + arms(('sg',), [1, 16]) + ['mf4:16', 'men:1', 'men:16']
SUITES = {
    # The four large rows add the forced engine at 4 and 8 for §15.3's stage curve, and M31's at 16
    # for T1's symbolic-stage ratio (the entry arms report no stage clocks).
    'dev': [(r, COMMON + ['sg:4', 'sg:8', 'msg:16']) for r in BIG] + [(r, COMMON) for r in MQ10 + CONTROLS],
    'small': [(r, arms(('f4', 'en'), [1, 16]) + ['mf4:16', 'men:16']) for r in KATSURA4]
    + [(r, arms(('en', 'men'), W4) + arms(('f4', 'sg'), [1, 16]) + ['mf4:16']) for r in KATSURA9],
    'held': [(r, COMMON) for r in HELD_OUT],
    'certify': [(r, ['ec:16']) for r in DEV + HELD_OUT],
}
REPS = {'dev': 9, 'small': 31, 'held': 9, 'certify': 1}
WARM = {'small'}
ENGINES = {'f4': 'f4', 'mf4': 'f4', 'en': 'entry', 'men': 'entry', 'ec': 'entry', 'sg': 'sigf4', 'msg': 'sigf4'}
SOLVE_S = 180
CERTIFY_S = 600
SETTLE_S = 1.0


def command(bins, row, arm, warm=False):
    label, workers = arm.split(':')
    field, name = row.split('/')
    binary = bins['m31'] if label.startswith('m') else bins['f3']
    argv = [str(binary), '--field', field, '--name', name, '--engine', ENGINES[label],
            '--workers', workers, '--wall-s', str(SOLVE_S)]
    if label in ('sg', 'msg') and int(workers) > 1:
        argv.append('--claim')
    if label == 'ec':
        argv.append('--certify')
    if warm:
        argv += ['--calls', '20']
    return 'sig_f4_study', argv


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--suite', choices=sorted(SUITES), required=True)
    p.add_argument('--bins', type=Path, required=True, help='directory holding {f3,m31}/sig_f4_study')
    p.add_argument('--reps', type=int, help='override the suite default (the n = 12 extension)')
    p.add_argument('--first-rep', type=int, default=0, help='numbering for an extension block')
    p.add_argument('--start-rep', type=int, default=0, help='resume a killed session at this rep')
    p.add_argument('--rows', nargs='*', help='restrict to these rows')
    p.add_argument('--arms', nargs='*', help='restrict to these arms')
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    bins = dict(f3=args.bins / 'f3/sig_f4_study', m31=args.bins / 'm31/sig_f4_study')
    warm = args.suite in WARM
    if args.suite == 'certify':
        BASE.CAP_S = SOLVE_S + CERTIFY_S
    BASE.command = lambda b, row, arm: command(b, row, arm, warm)
    rows = [(r, [a for a in suite_arms if not args.arms or a in args.arms])
            for r, suite_arms in SUITES[args.suite] if not args.rows or r in args.rows]
    with args.output.open('a') as out:
        for rep, row, arm in BASE.plan([x for x in rows if x[1]], args.reps or REPS[args.suite]):
            if rep < args.start_rep:
                continue
            rep += args.first_rep
            time.sleep(SETTLE_S)
            record = dict(suite=args.suite, rep=rep, row=row, arm=arm,
                          argv=command(bins, row, arm, warm)[1], load_start=os.getloadavg()[0],
                          **BASE.run_one(bins, row, arm))
            out.write(json.dumps(record) + '\n')
            out.flush()
            status = (record['report'] or {}).get('status', f"rc={record['returncode']}")
            print(args.suite, rep, row, arm, f"{record['process_wall_ns'] / 1e9:.3f}s", status,
                  f"load={record['load_start']:.1f}", flush=True)


if __name__ == '__main__':
    main()
