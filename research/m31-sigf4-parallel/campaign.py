#!/usr/bin/env python3
"""#904 campaign controller: #901's child runner (`m31-baseline/campaign.py`: CCD-aligned taskset
from CPU 8, `cpu-context` snapshots, frequency sampling, 180 s cap, `rss-guard` at 8 GiB) with
#904's arms, interleaved and rotated one place per repetition.

Arms are `label:workers`:
  d1  design 1, `--engine sigf4 --workers 1`, from the BASE binary (post-#903 `main`);
  s2  the parallel cascade, `--engine sigf4 --claim --workers W`, from the HEAD binary;
  d2  design 2, `--engine sigf4 --workers W`, from the HEAD binary;
  f4  shipping F4, `--engine f4 --workers W`, from the HEAD binary (plan §10.2: same tree).

    tools/bench-reserve.sh run zb-904 8-23 python3 -u research/m31-sigf4-parallel/campaign.py \\
        --suite gate --base BIN --head BIN --output OUT.jsonl
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

SUITES = {
    # Gate B (plan §8.2) and #905's Target criterion 1: Eco-12 at 16 workers.
    'gate': [('wide64/eco-12', ['d1:1', 's2:16', 'f4:16', 'd2:16'])],
    # Issue #904: complete wall vs F4-16 on the second family and MQ, plus Cyclic-7.
    'reported': [(r, ['d1:1', 's2:16', 'f4:16'])
                 for r in ['goldilocks/katsura-11', 'goldilocks/mq-random-11', 'goldilocks/cyclic-7']],
    # Issue #904: worker curve.
    'curve': [('wide64/eco-12', ['s2:1', 's2:4', 's2:8', 's2:16'])],
}


def command(bins, row, arm):
    label, workers = arm.split(':')
    field, name = row.split('/')
    binary = bins['base'] if label == 'd1' else bins['head']
    engine = 'f4' if label == 'f4' else 'sigf4'
    argv = [str(binary), '--field', field, '--name', name, '--engine', engine,
            '--workers', workers, '--wall-s', str(BASE.CAP_S)]
    if label == 's2':
        argv.append('--claim')
    return 'sig_f4_study', argv


BASE.command = command


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--suite', choices=sorted(SUITES), required=True)
    p.add_argument('--base', type=Path, required=True, help='sig_f4_study at post-#903 main')
    p.add_argument('--head', type=Path, required=True, help='sig_f4_study at the #904 head')
    p.add_argument('--reps', type=int, default=9)
    p.add_argument('--start-rep', type=int, default=0)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    bins = dict(base=args.base, head=args.head)
    with args.output.open('a') as out:
        for rep, row, arm in BASE.plan(SUITES[args.suite], args.reps):
            if rep < args.start_rep:
                continue
            record = dict(suite=args.suite, rep=rep, row=row, arm=arm,
                          binary=command(bins, row, arm)[1][0],
                          load_start=os.getloadavg()[0], **BASE.run_one(bins, row, arm))
            out.write(json.dumps(record) + '\n')
            out.flush()
            status = (record['report'] or {}).get('status', f"rc={record['returncode']}")
            print(args.suite, rep, row, arm, f"{record['process_wall_ns'] / 1e9:.3f}s", status,
                  f"load={record['load_start']:.1f}", flush=True)


if __name__ == '__main__':
    main()
