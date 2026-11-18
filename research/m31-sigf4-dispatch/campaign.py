#!/usr/bin/env python3
"""#905 Gate C controller: #901's child runner (`m31-baseline/campaign.py`: CCD-aligned taskset
from CPU 8, `cpu-context` snapshots, frequency sampling, 180 s cap, `rss-guard` at 8 GiB), two arms
from ONE `sig_f4_study` binary, interleaved and rotated one place per repetition:

  f4:W  shipping F4, `--engine f4 --workers W`;
  en:W  the opt-in entry point with its dispatch, `--engine entry --workers W`.

    tools/bench-reserve.sh run zb-905 8-23 python3 -u research/m31-sigf4-dispatch/campaign.py \\
        --suite w16 --bin BIN --output OUT.jsonl

`certify` is one repetition of the entry arm per row with `--certify` (plan §9, criterion 5).
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

# Plan §10.3. eco-14 was dropped by M31-0 (shipping F4-16 stops at its live-nonzero limit).
CORPUS = ['wide64/eco-12', 'goldilocks/katsura-11', 'wide64/katsura-11', 'goldilocks/mq-random-11',
          'gf32003/mq-random-10', 'm31/mq-random-10', 'goldilocks/cyclic-7', 'wide64/cyclic-7',
          'goldilocks/katsura-4', 'wide64/katsura-4', 'goldilocks/noon-7']
HELD_OUT = ['wide64/katsura-9', 'wide64/noon-8']
CONTROLS = ['goldilocks/katsura-4', 'wide64/katsura-4', 'goldilocks/noon-7', 'goldilocks/cyclic-7',
            'wide64/cyclic-7']

SUITES = {
    'w16': [(r, ['f4:16', 'en:16']) for r in CORPUS + HELD_OUT],
    'w1': [(r, ['f4:1', 'en:1']) for r in CONTROLS],
    'certify': [(r, ['ec:16']) for r in CORPUS + HELD_OUT],
}


def command(bins, row, arm):
    label, workers = arm.split(':')
    field, name = row.split('/')
    engine = 'f4' if label == 'f4' else 'entry'
    argv = [str(bins['bin']), '--field', field, '--name', name, '--engine', engine,
            '--workers', workers, '--wall-s', str(BASE.CAP_S)]
    if label == 'ec':
        argv.append('--certify')
    return 'sig_f4_study', argv


BASE.command = command


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--suite', choices=sorted(SUITES), required=True)
    p.add_argument('--bin', type=Path, required=True, help='sig_f4_study at the evaluated commit')
    p.add_argument('--reps', type=int, default=9)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    bins = dict(bin=args.bin)
    reps = 1 if args.suite == 'certify' else args.reps
    with args.output.open('a') as out:
        for rep, row, arm in BASE.plan(SUITES[args.suite], reps):
            record = dict(suite=args.suite, rep=rep, row=row, arm=arm, binary=str(args.bin),
                          load_start=os.getloadavg()[0], **BASE.run_one(bins, row, arm))
            out.write(json.dumps(record) + '\n')
            out.flush()
            status = (record['report'] or {}).get('status', f"rc={record['returncode']}")
            print(args.suite, rep, row, arm, f"{record['process_wall_ns'] / 1e9:.3f}s", status,
                  f"load={record['load_start']:.1f}", flush=True)


if __name__ == '__main__':
    main()
