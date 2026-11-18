"""#903 tables from `ab.py` records: per row, each arm's median process wall and stage clocks, the
head/base ratio paired per repetition with a 95% bootstrap interval of its median, the median
peak-RSS ratio, and whether the algebra (every non-timing statistic and the basis digest) is
identical across arms and repetitions.

    python3 research/m31-sigf4-serial/summarize.py --base base --head head runs.jsonl[.gz] ...
"""
import argparse
import gzip
import json
import random
import statistics
from collections import defaultdict

DRAWS = 20000
STAGES = ['bookkeeping_ns', 'symbolic_ns', 'elimination_ns', 'interreduction_ns']
# Instrument-only fields a change may add; everything else in `statistics` is algebra.
INSTRUMENT = {'interreduction_columns', 'interreduction_nonzeros', 'interreduction_peak_nonzeros',
              'signature_metadata_bytes'}


def paired_interval(ratios, seed=903):
    rng = random.Random(seed)
    medians = sorted(statistics.median(rng.choices(ratios, k=len(ratios))) for _ in range(DRAWS))
    return medians[int(0.025 * DRAWS)], medians[int(0.975 * DRAWS) - 1]


def load(paths):
    records = []
    for path in paths:
        opener = gzip.open if path.endswith('.gz') else open
        with opener(path, 'rt') as handle:
            records.extend(json.loads(line) for line in handle if line.strip())
    return records


def complete(record):
    report = record.get('report') or {}
    return record['returncode'] == 0 and report.get('status') == 'complete'


def untimed(value):
    """Drops every `*_ns` clock, at any depth: #901's `split` nests per-batch clocks beside
    per-batch counts, and the counts are algebra."""
    if isinstance(value, dict):
        return {k: untimed(v) for k, v in value.items()
                if not k.endswith('_ns') and k not in INSTRUMENT}
    if isinstance(value, list):
        return [untimed(v) for v in value]
    return value


def algebra(report):
    return json.dumps(untimed(report['statistics']), sort_keys=True), report.get('basis_sha256')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--base', default='base')
    parser.add_argument('--head', default='head')
    parser.add_argument('paths', nargs='+')
    args = parser.parse_args()
    records = load(args.paths)
    rows = list(dict.fromkeys(r['row'] for r in records))
    failed = [r for r in records if not complete(r)]
    print('| Row | n | base ms | head ms | head/base [95%] | RSS ratio | algebra identical |')
    print('|---|---:|---:|---:|---|---:|---|')
    stage_lines = []
    for row in rows:
        by_rep = defaultdict(dict)
        for r in records:
            if r['row'] == row and complete(r):
                by_rep[r['rep']][r['arm']] = r
        pairs = [(v[args.base], v[args.head]) for v in by_rep.values()
                 if args.base in v and args.head in v]
        if not pairs:
            continue
        ratios = [h['process_wall_ns'] / b['process_wall_ns'] for b, h in pairs]
        lo, hi = paired_interval(ratios)
        base_ms = statistics.median(b['process_wall_ns'] for b, _ in pairs) / 1e6
        head_ms = statistics.median(h['process_wall_ns'] for _, h in pairs) / 1e6
        rss = statistics.median(h['report']['peak_rss_bytes'] / b['report']['peak_rss_bytes']
                                for b, h in pairs)
        identical = len({algebra(x['report']) for pair in pairs for x in pair}) == 1
        print(f'| {row} | {len(pairs)} | {base_ms:,.1f} | {head_ms:,.1f} | '
              f'{statistics.median(ratios):.3f} [{lo:.3f}, {hi:.3f}] | {rss:.3f} | '
              f'{"yes" if identical else "**NO**"} |')
        for label, side in ((args.base, 0), (args.head, 1)):
            cells = [statistics.median(p[side]['report']['statistics'][s] for p in pairs) / 1e6
                     for s in STAGES]
            stage_lines.append(f'| {row} | {label} | ' + ' | '.join(f'{c:,.1f}' for c in cells)
                               + f' | {sum(cells):,.1f} |')
    print()
    print('Stage medians (ms, in-process clocks):')
    print()
    print('| Row | arm | bookkeeping | symbolic | elimination | interreduction | sum |')
    print('|---|---|---:|---:|---:|---:|---:|')
    print('\n'.join(stage_lines))
    print()
    print(f'Attempts: {len(records)}; incomplete: {len(failed)}')
    counts = defaultdict(int)
    for r in failed:
        counts[(r['row'], r['arm'], r['returncode'], tuple(r['stderr'].strip().splitlines()[-2:-1]))] += 1
    for (row, arm, rc, why), n in sorted((k, v) for k, v in counts.items() if v):
        print(f'- {row} {arm}: {n} x rc={rc} {" ".join(why)}')


if __name__ == '__main__':
    main()
