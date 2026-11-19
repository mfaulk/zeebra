#!/usr/bin/env python3
"""#939 M32-0 controller: M31's child runner (`research/m31-baseline/campaign.py` `run_one`, as
`research/m31-final/campaign.py` drives it) over M32's rows.

Suites:

  admission  plan §10.1's admission read on the held-out candidates: the shipping F4 at 16 workers
             (`sig_f4_study --engine f4`), three repetitions, from the pin build (`BINS/pin`). An
             admission bound, not a gate; the signature engine is never timed on these rows.

    tools/bench-reserve.sh run zb-939 8-23 python3 -u research/m32-baseline/campaign.py \\
        --suite admission --bins BINDIR --output OUT.jsonl
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


M31 = _module('m31final', ROOT / 'research/m31-final/campaign.py')
BASE = M31.BASE

# Plan §10.1, in the plan's order.
HELD_OUT = ['goldilocks/mq-random-10', 'wide64/mq-random-12', 'gf32003/mq-random-9', 'm31/katsura-10',
            'm31/eco-11', 'goldilocks/cyclic-6']
SUITES = {'admission': [(r, ['f4:16']) for r in HELD_OUT]}
REPS = {'admission': 3}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--suite', choices=sorted(SUITES), required=True)
    p.add_argument('--bins', type=Path, required=True, help='directory holding pin/sig_f4_study')
    p.add_argument('--reps', type=int)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    # M31's `command` reads the freeze and census keys eagerly; neither runs here.
    bins = dict(sig=args.bins / 'pin/sig_f4_study', zsig=None, work=None)
    BASE.command = M31.command
    with args.output.open('a') as out:
        for rep, row, arm in BASE.plan(SUITES[args.suite], args.reps or REPS[args.suite]):
            record = dict(suite=args.suite, rep=rep, row=row, arm=arm, argv=M31.command(bins, row, arm)[1],
                          load_start=os.getloadavg()[0], **BASE.run_one(bins, row, arm))
            out.write(json.dumps(record) + '\n')
            out.flush()
            status = (record['report'] or {}).get('status', f"rc={record['returncode']}")
            print(args.suite, rep, row, arm, f"{record['process_wall_ns'] / 1e9:.3f}s", status,
                  f"load={record['load_start']:.1f}", flush=True)


if __name__ == '__main__':
    main()
