#!/usr/bin/env python3
"""#1076 step 1: the predeclared limit check as a dev-mode bench-job manifest.

    limit_check.py --binary PATH --commit SHA --inputs DIR > manifest.json

Does sparse MQ reach conventional F4 only because the signature attempt stops on a limit? Arms:
the forced signature engine under the research envelope, shipping F4 and shipping Adaptive, on the
panel's two exposed sparse-MQ development rows. The rule is on #1076: if `sig-research` completes on
both rows with median <= 1.15 x min(f4, adaptive), the limit is the cause.
"""
import argparse
import hashlib
import json
import sys
from pathlib import Path

ROWS = ('m31/mq-random-11-s11', 'm31/mq-random-12-s12')
CAP_S = 900
RSS = 64 << 30
ARMS = {'sig-research': ['--engine', 'sig', '--research-envelope'],
        'f4': ['--engine', 'f4'], 'adaptive': ['--engine', 'adaptive']}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--binary', required=True)
    p.add_argument('--commit', required=True)
    p.add_argument('--inputs', required=True)
    p.add_argument('--agent', default='synchronous-mapping-dove@research/1080-1076-harness')
    p.add_argument('--cpus', default='8-23')
    a = p.parse_args()
    build = dict(profile='release', recipe=f'git archive {a.commit} | tar -x; cargo build --release '
                 '--features research-sigf4 --example m34_matrix',
                 flags='--features research-sigf4; fat LTO, codegen-units 1 (Cargo.toml); -C target-cpu=x86-64-v3 '
                 '(.cargo/config.toml); RUSTC_WRAPPER="" CARGO_INCREMENTAL=0')
    arms = [dict(name=name, commit=a.commit, binary=a.binary, sha256=sha(a.binary), build=build, library='zeebra',
                 argv=['--catalog', '{inputs[record]}', '--id', '{id}', *flags, '--workers', '1',
                       '--wall-s', str(CAP_S)])
            for name, flags in ARMS.items()]
    instances = []
    for row in ROWS:
        field, name = row.split('/')
        record = Path(a.inputs, row, 'record.json')
        instances.append(dict(name=row, params=dict(id=f'{name}@{field}'),
                              inputs=dict(record=dict(path=str(record), sha256=sha(record)))))
    m = dict(schema='bench-job-manifest-v1', mode='dev', context=dict(issue=1076, agent=a.agent, job='limit-check'),
             arms=arms, instances=instances,
             run=dict(workers=[1], cpus=a.cpus, repetitions=3, interleave='rotate', seeds=[0], retries=0,
                      limits=dict(wall_seconds=CAP_S + 30, kill_after_seconds=30, rss_bytes=RSS, live_bytes=None)))
    json.dump(m, sys.stdout, indent=1)
    print()


if __name__ == '__main__':
    main()
