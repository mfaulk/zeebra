#!/usr/bin/env python3
"""#958 controller: katsura-9 / 2^64-353, `--engine entry`, warm in-process calls, on M31's child
runner (`research/m31-baseline/campaign.py` `run_one`: CCD-aligned taskset from CPU 8,
`cpu-context` before and after, frequency sampling, `timeout --signal=INT`, `rss-guard` at 8 GiB).

Every `h-*` build compiles one harness source, `harness.rs` here (`c1d93389`'s `sig_f4_study` with
`f427e8d7`'s `--repeat` backported), so the library is the only thing that differs between them.
Arms (`label:workers`, W = 1 and 16), interleaved and rotated one place per repetition within
one block per worker count, with a 1 s settle before each child:

  m31    h-8715c8ed  --calls 20   the true M31 reference, never timed with warm calls before
  base   h-c1d93389  --calls 20   `ce67df76`'s library: Gate R's and Gate Q's "m31" arm
  rev1   h-588d2a44  --calls 20   Gate R revision 1's head (F2's measured library)
  f2     h-f427e8d7  --calls 20   F2
  f2rep  h-f427e8d7  --repeat 21  F2, the same binary as f2, under the other protocol
  f2own  own-f427e8d7 --repeat 21 F2's own example: #941's head arm exactly
  c1own  own-c1d93389 --calls 20  `c1d93389`'s own example: #941's reference arm exactly

Suite `alloc` (a diagnostic run after `gap`, n = 11) asks why `f2rep` is slower than `f2`: the same
binary under `--calls 20`, `--repeat 21`, and `--repeat 21` with glibc's heap trimming disabled
(`f2rept`: `GLIBC_TUNABLES` trim_threshold and top_pad at 1 GiB, through `env`, so the child's
comm, which `rss-guard` matches, is still `sig_f4_study`).

    tools/bench-reserve.sh run zb-958 8-23 python3 -u research/m32-katsura9-gap/campaign.py \\
        --bins BINDIR --output OUT.jsonl
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

ROW = 'wide64/katsura-9'
ARMS = {
    'm31': ('h-8715c8ed', ['--calls', '20']),
    'base': ('h-c1d93389', ['--calls', '20']),
    'rev1': ('h-588d2a44', ['--calls', '20']),
    'f2': ('h-f427e8d7', ['--calls', '20']),
    'f2rep': ('h-f427e8d7', ['--repeat', '21']),
    'f2own': ('own-f427e8d7', ['--repeat', '21']),
    'c1own': ('own-c1d93389', ['--calls', '20']),
    'f2rept': ('h-f427e8d7', ['--repeat', '21']),
}
NO_TRIM = 'glibc.malloc.trim_threshold=1073741824:glibc.malloc.top_pad=1073741824'
ENV = {'f2rept': ['env', f'GLIBC_TUNABLES={NO_TRIM}']}
SUITES = {'gap': ['m31', 'base', 'rev1', 'f2', 'f2rep', 'f2own', 'c1own'],
          'alloc': ['f2', 'f2rep', 'f2rept']}
WORKERS = (1, 16)
REPS = 21
SETTLE_S = 1.0


def command(bins, row, arm):
    label, workers = arm.split(':')
    build, flags = ARMS[label]
    field, name = row.split('/')
    return 'sig_f4_study', [*ENV.get(label, []), str(bins / build / 'sig_f4_study'), '--field', field, '--name', name,
                            '--engine', 'entry', '--workers', workers, '--wall-s', str(BASE.CAP_S), *flags]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--bins', type=Path, required=True, help='directory holding <build>/sig_f4_study')
    p.add_argument('--suite', choices=sorted(SUITES), default='gap')
    p.add_argument('--reps', type=int, default=REPS)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    BASE.command = command
    # One block per worker count, so each arm's neighbours run at its own width; and a settle
    # before every child, so no 1-worker child starts inside a 16-worker burst's all-core clock (#827).
    rows = [(ROW, [f'{a}:{w}' for a in SUITES[args.suite]]) for w in WORKERS]
    with args.output.open('a') as out:
        for rep, row, arm in BASE.plan(rows, args.reps):
            time.sleep(SETTLE_S)
            record = dict(suite=args.suite, rep=rep, row=row, arm=arm, argv=command(args.bins, row, arm)[1],
                          load_start=os.getloadavg()[0], **BASE.run_one(args.bins, row, arm))
            out.write(json.dumps(record) + '\n')
            out.flush()
            status = (record['report'] or {}).get('status', f"rc={record['returncode']}")
            print(rep, arm, f"{record['process_wall_ns'] / 1e9:.3f}s", status,
                  f"load={record['load_start']:.1f}", flush=True)


if __name__ == '__main__':
    main()
