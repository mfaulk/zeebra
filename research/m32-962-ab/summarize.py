"""Paired head/main ratios from campaign.py records: per rep, head arm / main arm on the same row,
median ratio with a 95% percentile bootstrap CI of the median (10,000 resamples)."""
import gzip
import json
import random
import statistics
import sys

import os

PAIRS = [tuple(p.split('/')) for p in os.environ.get('PAIRS', 'en:1/men:1').split(',')]


def figure(r):
    rep = r.get('report') or {}
    if r['suite'] == 'small':
        calls = rep.get('calls_ns') or []
        return statistics.median(calls) if calls else None
    return r['process_wall_ns'] if rep.get('status') == 'complete' else None


def main():
    recs = []
    for path in sys.argv[1:]:
        opener = gzip.open if path.endswith('.gz') else open
        with opener(path, 'rt') as f:
            recs += [json.loads(line) for line in f if line.strip()]
    by = {}
    for r in recs:
        by[(r['suite'], r['row'], r['arm'], r['rep'])] = figure(r)
    rows = sorted({(r['suite'], r['row']) for r in recs})
    rng = random.Random(961962)
    print('| suite | row | pair | n | head ms | main ms | head ÷ main [95% CI] |')
    print('|---|---|---|---|---|---|---|')
    worst = 0.0
    for suite, row in rows:
        for head, base in PAIRS:
            reps = sorted({k[3] for k in by if k[:3] == (suite, row, head)})
            ratios, hs, bs = [], [], []
            for rep in reps:
                h, b = by.get((suite, row, head, rep)), by.get((suite, row, base, rep))
                if h and b:
                    ratios.append(h / b)
                    hs.append(h)
                    bs.append(b)
            if not ratios:
                continue
            med = statistics.median(ratios)
            boots = sorted(statistics.median(rng.choices(ratios, k=len(ratios))) for _ in range(10000))
            lo, hi = boots[249], boots[9749]
            worst = max(worst, med)
            print(f'| {suite} | {row} | {head} ÷ {base} | {len(ratios)} | {statistics.median(hs) / 1e6:.2f} '
                  f'| {statistics.median(bs) / 1e6:.2f} | {med:.3f} [{lo:.3f}, {hi:.3f}] |')
    print(f'\nworst median ratio: {worst:.3f}')


if __name__ == '__main__':
    main()
