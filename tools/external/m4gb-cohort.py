#!/usr/bin/env python3
"""#1030 development cohort: Zeebra against the pinned M4GB on dense overdetermined MQ.

Runs `examples/m4gb_comparison` once per (row, engine, repetition), alternating engine order
between repetitions, and appends one JSON line per run to --output. The held-out ratio (m/n = 1.8)
and field (GF(65521)) are refused here: they are read only for the decision
(docs/research/m4gb-m5gb-reference.md §4).

    m4gb-cohort.py --binary target/release/examples/m4gb_comparison --output rows.jsonl \\
        --sizes 31:10,12,14 --sizes 32003:10,12 --reps 3
"""
import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

RATIOS = (1.5, 2.0, 3.0)
HELD_OUT_RATIO = 1.8
HELD_OUT_PRIME = 65521


def m_for(n, ratio):
    return int(round(n * ratio))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--binary', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--sizes', action='append', required=True,
                        help='PRIME:N1,N2,... (repeatable)')
    parser.add_argument('--ratios', default=','.join(map(str, RATIOS)))
    parser.add_argument('--densities', default='1000,500')
    parser.add_argument('--seeds', default='1,2')
    parser.add_argument('--reps', type=int, default=3)
    parser.add_argument('--workers', type=int, default=1)
    parser.add_argument('--wall', type=int, default=180)
    parser.add_argument('--unplanted', action='store_true',
                        help='also run the unplanted (inconsistent) variant')
    args = parser.parse_args()

    ratios = [float(r) for r in args.ratios.split(',')]
    sizes = []
    for spec in args.sizes:
        prime, ns = spec.split(':')
        sizes += [(int(prime), int(n)) for n in ns.split(',')]
    if HELD_OUT_RATIO in ratios or any(p == HELD_OUT_PRIME for p, _ in sizes):
        parser.error('m/n = 1.8 and GF(65521) are held out until the decision is posted')

    cells = [(p, n, m_for(n, r), d, s, planted)
             for p, n in sizes for r in ratios
             for d in map(int, args.densities.split(','))
             for s in map(int, args.seeds.split(','))
             for planted in ((True, False) if args.unplanted else (True,))]
    # macOS checks a new binary on its first exec (about 0.12 s, measured); take that cost here,
    # outside every measured row.
    prefix = os.environ.get('ZEEBRA_EXT_PREFIX', os.path.expanduser('~/.local/opt/zeebra-ext'))
    directory = Path(os.environ.get('ZEEBRA_M4GB_DIR', os.path.join(prefix, 'bin')))
    for p, n in sorted(set(sizes)):
        subprocess.run([str(directory / f'm4gb_n{n}_gf{p}'), '--showconfig'],
                       capture_output=True, check=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open('a') as out:
        for rep in range(args.reps):
            engines = ('zeebra', 'm4gb') if rep % 2 == 0 else ('m4gb', 'zeebra')
            for p, n, m, d, s, planted in cells:
                for engine in engines:
                    command = [str(args.binary), '--n', str(n), '--m', str(m),
                               '--density', str(d), '--seed', str(s), '--modulus', str(p),
                               '--engine', engine, '--workers', str(args.workers),
                               '--wall', str(args.wall)]
                    if not planted:
                        command.append('--unplanted')
                    done = subprocess.run(command, capture_output=True, text=True)
                    if done.returncode != 0:
                        print(f'runner failed: {command}\n{done.stderr}', file=sys.stderr)
                        sys.exit(1)
                    row = json.loads(done.stdout)
                    row['rep'] = rep
                    out.write(json.dumps(row) + '\n')
                    out.flush()
                    print(rep, row['row'], p, engine, row['status'],
                          f"{row['wall_ns'] / 1e9:.3f}s", flush=True)


if __name__ == '__main__':
    main()
