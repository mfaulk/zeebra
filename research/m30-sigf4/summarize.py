"""#857 tables from `run.py` records: medians, 95% bootstrap intervals of median ratios, and
basis-digest agreement between engines (plan §10.2; the interval is `m29-final/verdicts.py`'s).

    python3 research/m30-sigf4/summarize.py walls.jsonl[.gz] ... > tables.md
"""
import gzip
import json
import random
import statistics
import sys
from collections import defaultdict

DRAWS = 20000


def interval(numerator, denominator, seed=857):
    rng = random.Random(seed)
    ratios = sorted(
        statistics.median(rng.choices(numerator, k=len(numerator)))
        / statistics.median(rng.choices(denominator, k=len(denominator)))
        for _ in range(DRAWS))
    return ratios[int(0.025 * DRAWS)], ratios[int(0.975 * DRAWS) - 1]


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


def tables(records):
    walls = defaultdict(list)
    rss = defaultdict(list)
    digests = defaultdict(set)
    failures = defaultdict(int)
    for r in records:
        key = (r['row'], r['arm'])
        if not complete(r):
            failures[key] += 1
            continue
        walls[key].append(r['process_wall_ns'] / 1e9)
        rss[key].append(r['report']['peak_rss_bytes'] / 2**20)
        digests[r['row']].add(r['report']['basis_sha256'])
    lines = ['| row | arm | n | failed | median wall s | median RSS MiB |', '|---|---|---:|---:|---:|---:|']
    for (row, arm), w in sorted(walls.items()):
        lines.append(f'| {row} | {arm} | {len(w)} | {failures[(row, arm)]} | '
                     f'{statistics.median(w):.3f} | {statistics.median(rss[(row, arm)]):.0f} |')
    lines += ['', '| row | sigf4 arm ÷ f4 arm | wall ratio [95%] | RSS ratio | bases identical |',
              '|---|---|---:|---:|---|']
    for (row, sig_arm), sig in sorted(walls.items()):
        if not sig_arm.startswith('sigf4:'):
            continue
        for arm in sorted(arm for r, arm in walls if r == row and arm.startswith('f4:')):
            base = walls[(row, arm)]
            low, high = interval(sig, base)
            ratio = statistics.median(sig) / statistics.median(base)
            mem = statistics.median(rss[(row, sig_arm)]) / statistics.median(rss[(row, arm)])
            same = 'yes' if len(digests[row]) == 1 else f'NO ({len(digests[row])} digests)'
            lines.append(f'| {row} | {sig_arm} ÷ {arm} | {ratio:.3f} [{low:.3f}, {high:.3f}] | '
                         f'{mem:.2f} | {same} |')
    return '\n'.join(lines)


if __name__ == '__main__':
    print(tables(load(sys.argv[1:])))
