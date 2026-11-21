#!/usr/bin/env python3
"""#962 diagnosis: four sig_f4_study builds of one harness (#958's harness.rs), `--engine entry`
at one worker, one solve per process (process wall), interleaved and rotated per rep with
m31-baseline's runner (CPU 8, cpu-context, rss-guard, 1 s settle)."""
import importlib.util
import json
import os
import sys
import time
from pathlib import Path

ROOT = Path('/home/mfaulk/projects/zeebra/.claude/worktrees/agent-aa1286a847fd091a8')
SPEC = importlib.util.spec_from_file_location('m31campaign', ROOT / 'research/m31-baseline/campaign.py')
BASE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BASE)

B = Path('/buildcache/cargo-target/zeebra-961')
BINS = {'head': B / 'binh/f3/sig_f4_study', 'main': B / 'binh/m31/sig_f4_study',
        'v2': B / 't-v2/release/examples/sig_f4_study', 'v3': B / 't-v3/release/examples/sig_f4_study'}
ROWS = ['gf32003/mq-random-10', 'm31/mq-random-10', 'wide64/katsura-11']
ARMS = [f'{k}:1' for k in BINS]


def command(bins, row, arm):
    label, workers = arm.split(':')
    field, name = row.split('/')
    return 'sig_f4_study', [str(BINS[label]), '--field', field, '--name', name, '--engine', 'entry',
                            '--workers', workers, '--wall-s', '180']


BASE.command = command


def main():
    reps, out = int(sys.argv[1]), Path(sys.argv[2])
    with out.open('a') as f:
        for rep, row, arm in BASE.plan([(r, ARMS) for r in ROWS], reps):
            time.sleep(1.0)
            rec = dict(suite='variants', rep=rep, row=row, arm=arm, argv=command(None, row, arm)[1],
                       load_start=os.getloadavg()[0], **BASE.run_one(None, row, arm))
            f.write(json.dumps(rec) + '\n')
            f.flush()
            print(rep, row, arm, f"{rec['process_wall_ns'] / 1e9:.3f}s",
                  (rec['report'] or {}).get('status'), flush=True)


if __name__ == '__main__':
    main()
