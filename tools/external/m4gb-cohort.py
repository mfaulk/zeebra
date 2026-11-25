#!/usr/bin/env python3
"""#1030 development cohort: Zeebra against the pinned M4GB on dense overdetermined MQ.

Runs `examples/m4gb_comparison` once per (row, engine, repetition), alternating engine order
between repetitions, and appends one JSON line per run to --output. The held-out ratio (m/n = 1.8)
and field (GF(65521)) are refused unless `--deciding-run` is given: they are read only for the
decision (docs/research/m4gb-m5gb-reference.md §4). `--engines` picks the arms (default zeebra and
m4gb), rotated one place per repetition; `--cpus` pins every child with `taskset`.

    m4gb-cohort.py --binary target/release/examples/m4gb_comparison --output rows.jsonl \\
        --sizes 31:10,12,14 --sizes 32003:10,12 --reps 3
"""
import argparse
import json
import os
import statistics
import subprocess
import sys
from pathlib import Path

RATIOS = (1.5, 2.0, 3.0)
HELD_OUT_RATIO = 1.8
HELD_OUT_PRIME = 65521


def m_for(n, ratio):
    return int(round(n * ratio))


def summarize(path):
    """Per row: median wall per engine over answered reps, and M4GB's speedup over each other arm.
    `best` is the faster of the two Zeebra arms (shipping F4 and `GradedEngine::Adaptive`)."""
    rows = [json.loads(line) for line in path.read_text().splitlines() if line.strip()]
    cells = {}
    for r in rows:
        key = (r['modulus'], r['n'], r['m'], r['density'], r['seed'], r['planted'])
        cells.setdefault(key, {}).setdefault(r['engine'], []).append(r)
    engines = [e for e in ('zeebra', 'zeebra-adaptive', 'grobx', 'm4gb')
               if any(e in c for c in cells.values())]
    fmt = (lambda v: f'{v:.3f}' if v is not None else '—')
    head = ' | '.join(f'{e} s' for e in engines)
    others = [e for e in engines if e != 'm4gb'] + (['best'] if 'zeebra-adaptive' in engines else [])
    print(f'| p | n | m | m/n | density | seed | planted | {head} | '
          + ' | '.join(f'{e} ÷ M4GB' for e in others) + ' | M4GB peak RSS MiB | M4GB status |')
    print('|' + '---|' * (7 + len(engines) + len(others) + 2))
    for key in sorted(cells):
        p, n, m, d, s, planted = key
        med = {}
        for e in engines:
            ok = ('verified',) if e in ('m4gb', 'grobx') else ('complete', 'verified')
            w = [r['wall_ns'] / 1e9 for r in cells[key].get(e, []) if r['status'] in ok]
            med[e] = statistics.median(w) if w else None
        zs = [med.get(e) for e in ('zeebra', 'zeebra-adaptive') if med.get(e)]
        med['best'] = min(zs) if zs else None
        g = med.get('m4gb')
        rss = [r['peak_rss_bytes'] / 2**20 for r in cells[key].get('m4gb', []) if r.get('peak_rss_bytes')]
        statuses = sorted({r['status'][:24] for r in cells[key].get('m4gb', [])})
        ratios = ' | '.join(f'{med[e] / g:.1f}x' if med.get(e) and g else '—' for e in others)
        print(f'| {p} | {n} | {m} | {m / n:.1f} | {d} | {s} | {"yes" if planted else "no"} '
              f'| {" | ".join(fmt(med[e]) for e in engines)} | {ratios} '
              f'| {fmt(max(rss)) if rss else "—"} | {", ".join(statuses)} |')


def main():
    if len(sys.argv) == 3 and sys.argv[1] == '--summarize':
        summarize(Path(sys.argv[2]))
        return
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
    parser.add_argument('--engines', default='zeebra,m4gb')
    parser.add_argument('--cpus', help='taskset CPU list for every child')
    parser.add_argument('--deciding-run', action='store_true',
                        help='admit the held-out ratio and field (the decision run only)')
    parser.add_argument('--unplanted', action='store_true',
                        help='also run the unplanted (inconsistent) variant')
    args = parser.parse_args()

    ratios = [float(r) for r in args.ratios.split(',')]
    sizes = []
    for spec in args.sizes:
        prime, ns = spec.split(':')
        sizes += [(int(prime), int(n)) for n in ns.split(',')]
    held_out = HELD_OUT_RATIO in ratios or any(p == HELD_OUT_PRIME for p, _ in sizes)
    if held_out and not args.deciding_run:
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
            arms = args.engines.split(',')
            engines = arms[rep % len(arms):] + arms[:rep % len(arms)]
            for p, n, m, d, s, planted in cells:
                for engine in engines:
                    command = (['taskset', '-c', args.cpus] if args.cpus else []) + [
                               str(args.binary), '--n', str(n), '--m', str(m),
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
                    row['load_start'] = os.getloadavg()[0]
                    out.write(json.dumps(row) + '\n')
                    out.flush()
                    print(rep, row['row'], p, engine, row['status'],
                          f"{row['wall_ns'] / 1e9:.3f}s", flush=True)


if __name__ == '__main__':
    main()
