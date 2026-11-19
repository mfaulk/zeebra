#!/usr/bin/env python3
"""#927 Gate R controller (plan §8.2): M31's child runner (`research/m31-baseline/campaign.py`
`run_one`: CCD-aligned taskset from CPU 8, `cpu-context` snapshots, frequency sampling, 180 s cap,
`rss-guard` at 8 GiB) over the development rows only. Arms, interleaved and rotated one place per
repetition:

  f4:W   conventional F4 from the head build, `--engine f4 --workers W`;
  en:W   the head entry point (#927's dispatch), `--engine entry --workers W`;
  m31:W  the base entry point (M31's dispatch, `src/` identical to the M32 baseline `7b25a1ee`),
         `--engine entry --workers W`.

Suites (each read once; §10.3's precision rule decides whether one n = 12 extension block runs):

  mq10   T3: MQ10 at both fields, en ÷ f4 at 1, 4, 8 and 16 workers, n = 9.
  fav    the signature-routed dev rows of ≥ 50 ms, en ÷ m31 at 1, 4, 8 and 16 workers, n = 9.
  ctrl   Cyclic-7 at both fields, en ÷ f4 at 1 and 16 workers, n = 9.
  small  rows under 50 ms by plan §10.3's default (#934 has not landed): `--calls 10`, the median
         of the warm calls per process, n = 31 processes; katsura-4 (both fields) en ÷ f4 and
         katsura-9 en ÷ m31, at 1 and 16 workers (katsura-9 also 4 and 8, where the team cap acts).

    tools/bench-reserve.sh run zb-927 8-23 python3 -u research/m32-adaptive-dispatch/campaign.py \\
        --suite mq10 --bins BINDIR --output OUT.jsonl
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SPEC = importlib.util.spec_from_file_location('m31campaign', ROOT / 'research/m31-baseline/campaign.py')
BASE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BASE)

W4 = [1, 4, 8, 16]
MQ10 = ['gf32003/mq-random-10', 'm31/mq-random-10']
FAVOURABLE = ['wide64/eco-12', 'goldilocks/katsura-11', 'wide64/katsura-11', 'goldilocks/mq-random-11',
              'goldilocks/noon-7', 'wide64/noon-8']
CYCLIC = ['goldilocks/cyclic-7', 'wide64/cyclic-7']
SMALL_VS_F4 = ['goldilocks/katsura-4', 'wide64/katsura-4']
SMALL_VS_M31 = ['wide64/katsura-9']
CALLS = 10

SUITES = {
    'mq10': [(r, [f'{a}:{w}' for w in W4 for a in ('f4', 'en')]) for r in MQ10],
    'fav': [(r, [f'{a}:{w}' for w in W4 for a in ('m31', 'en')]) for r in FAVOURABLE],
    'ctrl': [(r, [f'{a}:{w}' for w in (1, 16) for a in ('f4', 'en')]) for r in CYCLIC],
    'small': [(r, [f'{a}:{w}' for w in (1, 16) for a in ('f4', 'en')]) for r in SMALL_VS_F4]
    + [(r, [f'{a}:{w}' for w in W4 for a in ('m31', 'en')]) for r in SMALL_VS_M31],
}
# Plan §10.3's one extension block (n = 12, pooled), for the cells the first read left imprecise.
SUITES['mq10x'] = [('m31/mq-random-10', ['f4:4', 'en:4'])]
# Revision 1 (team cap 8 and the dispatch clock), read once with `--bins` pointing `head` at its
# build: the cells the revision can move, and the dispatch cost on every dev row.
SUITES['rev1small'] = [(r, [f'{a}:{w}' for w in W4 for a in ('m31', 'en')]) for r in SMALL_VS_M31]
SUITES['rev1fav'] = [(r, [f'{a}:{w}' for w in (8, 16) for a in ('m31', 'en')])
                     for r in ['goldilocks/noon-7', 'wide64/noon-8']]
SUITES['t9'] = [(r, [f'en:{w}' for w in W4]) for r in MQ10 + FAVOURABLE + CYCLIC + SMALL_VS_F4
                + SMALL_VS_M31]
SUITES['rev1favx'] = [(r, ['m31:16', 'en:16']) for r in ['goldilocks/noon-7', 'wide64/noon-8']]
REPS = {'rev1favx': 12, 'mq10': 9, 'fav': 9, 'ctrl': 9, 'small': 31, 'mq10x': 12, 'rev1small': 31, 'rev1fav': 9,
        't9': 3}
WARM = {'small', 'rev1small'}


def command(bins, row, arm, calls=0):
    label, workers = arm.split(':')
    field, name = row.split('/')
    binary = bins['base'] if label == 'm31' else bins['head']
    engine = 'f4' if label == 'f4' else 'entry'
    argv = [str(binary), '--field', field, '--name', name, '--engine', engine,
            '--workers', workers, '--wall-s', str(BASE.CAP_S)]
    if calls:
        argv += ['--calls', str(calls)]
    return 'sig_f4_study', argv


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--suite', choices=sorted(SUITES), required=True)
    p.add_argument('--bins', type=Path, required=True, help='directory holding {base,head}/sig_f4_study')
    p.add_argument('--reps', type=int, help='override the suite default (the n = 12 extension)')
    p.add_argument('--first-rep', type=int, default=0, help='numbering for an extension block')
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    bins = dict(base=args.bins / 'base/sig_f4_study', head=args.bins / 'head/sig_f4_study')
    calls = CALLS if args.suite in WARM else 0
    BASE.command = lambda b, row, arm: command(b, row, arm, calls)
    with args.output.open('a') as out:
        for rep, row, arm in BASE.plan(SUITES[args.suite], args.reps or REPS[args.suite]):
            rep += args.first_rep
            record = dict(suite=args.suite, rep=rep, row=row, arm=arm,
                          argv=command(bins, row, arm, calls)[1], load_start=os.getloadavg()[0],
                          **BASE.run_one(bins, row, arm))
            out.write(json.dumps(record) + '\n')
            out.flush()
            status = (record['report'] or {}).get('status', f"rc={record['returncode']}")
            print(args.suite, rep, row, arm, f"{record['process_wall_ns'] / 1e9:.3f}s", status,
                  f"load={record['load_start']:.1f}", flush=True)


if __name__ == '__main__':
    main()
