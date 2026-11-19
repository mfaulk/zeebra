#!/usr/bin/env python3
"""#939 M32-0 controller: M31's child runner (`research/m31-baseline/campaign.py` `run_one`: CCD-aligned
taskset from CPU 8, `cpu-context` before and after, frequency sampling, `timeout --signal=INT`,
`rss-guard` on the child's own comm) over M32's rows.

Suites (arm = `label:workers`; a label prefixed `r` runs the M31 reference build, `s` the split
build, anything else the baseline build, or the pin build for `admission`):

  admission  plan §10.1's admission read on the held-out candidates: the shipping F4 at 16 workers,
             three repetitions. An admission bound, not a gate; the signature engine is never timed
             on these rows.
  walls      deliverable 3, n = 9 on every development row, arms rotated per repetition:
               f4:W  shipping F4 (`--engine f4`), W = 1, 4, 8, 16
               en:W  the `grobner::f4_signature` entry point, dispatch included, W = 1, 4, 8, 16
               cl:W  the signature engine with the parallel cascade (`--engine sigf4 --claim`),
                     W = 4, 8, 16, and d1:1 the same engine at one worker: the stage clocks of the
                     route `en:W` takes on signature-routed rows
               rf4:W, ren:W  as f4:W and en:W from the M31 reference
  split      deliverable 4, n = 5: sd1:1 and scl:4/8/16 from the split build (symbolic-stage
             components and the symbolic thread's frequency), never timed against `walls`
  small      #934, n = 31 on katsura-4 at both fields: en and f4 at 1 and 16 workers, each process
             `--repeat 21` (one cold call, twenty warm), from the instrument build (`BINS/m32`)

    tools/bench-reserve.sh run zb-939 8-23 python3 -u research/m32-baseline/campaign.py \\
        --suite walls --bins BINDIR --output OUT.jsonl
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

# Plan §10.1, in the plan's order.
HELD_OUT = ['goldilocks/mq-random-10', 'wide64/mq-random-12', 'gf32003/mq-random-9', 'm31/katsura-10',
            'm31/eco-11', 'goldilocks/cyclic-6']
DEV = ['wide64/eco-12', 'goldilocks/katsura-11', 'wide64/katsura-11', 'goldilocks/mq-random-11',
       'gf32003/mq-random-10', 'm31/mq-random-10', 'goldilocks/cyclic-7', 'wide64/cyclic-7',
       'goldilocks/katsura-4', 'wide64/katsura-4', 'goldilocks/noon-7', 'wide64/katsura-9', 'wide64/noon-8']
WORKERS = ('1', '4', '8', '16')
WALL_ARMS = ([f'{e}:{w}' for e in ('f4', 'en') for w in WORKERS] + ['d1:1', 'cl:4', 'cl:8', 'cl:16']
             + [f'r{e}:{w}' for e in ('f4', 'en') for w in WORKERS])
# The rows whose stage clocks the cost model reads (plan §6.3, #939 deliverable 5).
SPLIT_ROWS = ['wide64/eco-12', 'goldilocks/katsura-11', 'goldilocks/mq-random-11', 'gf32003/mq-random-10',
              'm31/mq-random-10']
SUITES = {'admission': [(r, ['f4:16']) for r in HELD_OUT],
          'walls': [(r, WALL_ARMS) for r in DEV],
          'split': [(r, ['sd1:1', 'scl:4', 'scl:8', 'scl:16']) for r in SPLIT_ROWS],
          'small': [(r, ['en:1', 'f4:1', 'en:16', 'f4:16']) for r in ('goldilocks/katsura-4', 'wide64/katsura-4')]}
REPS = {'admission': 3, 'walls': 9, 'split': 5, 'small': 31}
# The build an unprefixed arm runs, per suite; the baseline otherwise.
SIG_BUILD = {'admission': 'pin', 'small': 'm32'}
EXTRA = {'small': ['--repeat', '21']}
BUILDS = {'r': 'ref', 's': 'split'}
ENGINE = {'f4': 'f4', 'en': 'entry', 'cl': 'sigf4', 'd1': 'sigf4'}


def command(bins, row, arm, extra=()):
    label, workers = arm.split(':')
    build = BUILDS.get(label[0]) if label[1:] in ENGINE else None
    engine = label[1:] if build else label
    field, name = row.split('/')
    argv = [str(bins[build or 'sig']), '--field', field, '--name', name, '--engine', ENGINE[engine],
            '--workers', workers, '--wall-s', str(BASE.CAP_S)]
    if engine == 'cl':
        argv.append('--claim')
    return 'sig_f4_study', argv + list(extra)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--suite', choices=sorted(SUITES), required=True)
    p.add_argument('--bins', type=Path, required=True, help='directory holding {pin,base,ref,split}/sig_f4_study')
    p.add_argument('--reps', type=int)
    p.add_argument('--start-rep', type=int, default=0, help='resume a killed session')
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    bins = {k: args.bins / d / 'sig_f4_study'
            for k, d in [('sig', SIG_BUILD.get(args.suite, 'base')), *((d, d) for d in BUILDS.values())]}
    extra = EXTRA.get(args.suite, ())
    BASE.command = lambda b, r, a: command(b, r, a, extra)
    with args.output.open('a') as out:
        for rep, row, arm in BASE.plan(SUITES[args.suite], args.reps or REPS[args.suite]):
            if rep < args.start_rep:
                continue
            record = dict(suite=args.suite, rep=rep, row=row, arm=arm, argv=command(bins, row, arm, extra)[1],
                          load_start=os.getloadavg()[0], **BASE.run_one(bins, row, arm))
            out.write(json.dumps(record) + '\n')
            out.flush()
            status = (record['report'] or {}).get('status', f"rc={record['returncode']}")
            print(args.suite, rep, row, arm, f"{record['process_wall_ns'] / 1e9:.3f}s", status,
                  f"load={record['load_start']:.1f}", flush=True)


if __name__ == '__main__':
    main()
