#!/usr/bin/env python3
"""#940 Gate S controller: M31's child runner (`research/m31-baseline/campaign.py` `run_one`:
CCD-aligned taskset from CPU 8, `cpu-context` before and after, frequency sampling,
`timeout --signal=INT`, `rss-guard` at 8 GiB) over #940's head and its merge base, interleaved and
rotated in one session (plan §8.2 Gate S, §8.3 F1, §10.2).

Arms are `<build>-<engine>:<workers>`; `h` is the head, `b` the merge base, each `sig_f4_study`
built from a `git archive` of its commit (`BINS/head`, `BINS/base`):

  en:W   the opt-in entry point `grobner::f4_signature`, dispatch included (T2, the dev corpus)
  cl:W   the signature engine with the parallel cascade (`--engine sigf4 --claim`): the route
         `en:W` takes on signature-routed rows, with its stage clocks (T1, the worker curve)
  f4:W   the shipping F4 (MQ10's re-read for #927)

Suites:

  gate   Eco-12 at 16 workers (T1, T2) and every dev row at or above 50 ms, `en` at 1 and 16
         workers, n = 9
  small  the dev rows under 50 ms (plan §10.3), n = 31, read on the in-process call time
  mq10   MQ10 at both fields: `en` at 1/4/8/16 workers on both builds and the head's `f4`, n = 9
  curve  Eco-12 and MQ10 / 32003, `cl` at 1/2/4/8/16 workers on both builds, n = 9

    tools/bench-reserve.sh run zb-940 8-23 python3 -u research/m32-gate-s/campaign.py \\
        --suite gate --bins BINDIR --output OUT.jsonl
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def _module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


BASE = _module('m31campaign', ROOT / 'research/m31-baseline/campaign.py')

ECO = 'wide64/eco-12'
MQ10 = ['gf32003/mq-random-10', 'm31/mq-random-10']
# Plan §10.1's development set less MQ10 (its own suite), split at 50 ms by M31's `en` walls
# (`research/m31-final/tables.md`).
LARGE = ['goldilocks/katsura-11', 'wide64/katsura-11', 'goldilocks/mq-random-11', 'goldilocks/cyclic-7',
         'wide64/cyclic-7', 'goldilocks/noon-7', 'wide64/noon-8']
SMALL = ['goldilocks/katsura-4', 'wide64/katsura-4', 'wide64/katsura-9']


def both(engine, workers):
    return [f'{build}-{engine}:{w}' for w in workers for build in ('h', 'b')]


SUITES = {
    'gate': [(ECO, both('cl', [16]) + both('en', [16, 1]))] + [(r, both('en', [1, 16])) for r in LARGE],
    'small': [(r, both('en', [1, 16])) for r in SMALL],
    'mq10': [(r, both('en', [1, 4, 8, 16]) + [f'h-f4:{w}' for w in (1, 4, 8, 16)]) for r in MQ10],
    'curve': [(r, both('cl', [1, 2, 4, 8, 16])) for r in (ECO, MQ10[0])],
}
REPS = {'gate': 9, 'small': 31, 'mq10': 9, 'curve': 9}


def command(bins, row, arm):
    label, workers = arm.split(':')
    build, engine = label.split('-')
    field, name = row.split('/')
    binary = bins['head' if build == 'h' else 'base']
    argv = [str(binary), '--field', field, '--name', name,
            '--engine', {'en': 'entry', 'cl': 'sigf4', 'f4': 'f4'}[engine],
            '--workers', workers, '--wall-s', str(BASE.CAP_S)]
    if engine == 'cl':
        argv.append('--claim')
    return 'sig_f4_study', argv


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--suite', choices=sorted(SUITES), required=True)
    p.add_argument('--bins', type=Path, required=True, help='directory holding head/ and base/sig_f4_study')
    p.add_argument('--reps', type=int)
    p.add_argument('--start-rep', type=int, default=0, help='resume a killed session')
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    bins = dict(head=args.bins / 'head/sig_f4_study', base=args.bins / 'base/sig_f4_study')
    BASE.command = command
    with args.output.open('a') as out:
        for rep, row, arm in BASE.plan(SUITES[args.suite], args.reps or REPS[args.suite]):
            if rep < args.start_rep:
                continue
            record = dict(suite=args.suite, rep=rep, row=row, arm=arm, argv=command(bins, row, arm)[1],
                          load_start=os.getloadavg()[0], **BASE.run_one(bins, row, arm))
            out.write(json.dumps(record) + '\n')
            out.flush()
            status = (record['report'] or {}).get('status', f"rc={record['returncode']}")
            print(args.suite, rep, row, arm, f"{record['process_wall_ns'] / 1e9:.3f}s", status,
                  f"load={record['load_start']:.1f}", flush=True)


if __name__ == '__main__':
    main()
