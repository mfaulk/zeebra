"""The M29 goal verdicts (#837): Zeebra/comparand median ratios with 95% bootstrap intervals.

Plan §9: Goal A needs Zeebra (best of 1/4/8/16 workers) at most 1.5x the fastest exact-mode
msolve configuration within 16 workers, with the interval's upper end below 1.5. Goal B needs
Zeebra at most 0.90x grobx with an interval that establishes the lead. Each arm's samples are
resampled independently. That is conservative, because the arms are interleaved but not paired
one-to-one.

    python3 research/m29-final/verdicts.py research/m29-final
"""
import gzip
import json
import random
import statistics
import sys
import zlib
from pathlib import Path

WIDE = {'eco12-wide64': ('wide64', 'eco-12'), 'mq11-goldilocks': ('goldilocks', 'mq-random-11')}
WORKERS = (1, 4, 8, 16)
DRAWS = 20000


def interval(zeebra, comparand, seed):
    rng = random.Random(seed)
    ratios = sorted(
        statistics.median(rng.choices(zeebra, k=len(zeebra)))
        / statistics.median(rng.choices(comparand, k=len(comparand)))
        for _ in range(DRAWS))
    return ratios[int(0.025 * DRAWS)], ratios[int(0.975 * DRAWS) - 1]


def best(groups, field, engine):
    """The worker count with the lowest median, and its samples."""
    cells = [(statistics.median(groups[(field, engine, w)]), w) for w in WORKERS if groups.get((field, engine, w))]
    if not cells:
        return None, []
    _, w = min(cells)
    return w, groups[(field, engine, w)]


def verdict_rows(directory):
    rows = []
    windows = json.loads((directory / 'mq10-attempts.json').read_text())
    for win in windows:
        groups = {}
        for a in win['attempts']:
            if a['status'] == 'verified' and a.get('process_wall_ns'):
                groups.setdefault((str(a['field']), a['engine'], a['workers']), []).append(a['process_wall_ns'] / 1e6)
        for field in ('32003', '2147483647'):
            zw, z = best(groups, field, 'zeebra')
            mw, m = best(groups, field, 'msolve')
            if not z or not m:
                continue
            ratio = statistics.median(z) / statistics.median(m)
            lo, hi = interval(z, m, zlib.crc32(f'A {field}'.encode()))
            rows.append(dict(goal='A', window=win['archive'].split('.')[0], target=f'MQ10 / {field}',
                             zeebra=statistics.median(z), zeebra_workers=zw, n_zeebra=len(z),
                             comparand='msolve (exact)', comparand_ms=statistics.median(m), comparand_workers=mw,
                             n_comparand=len(m), ratio=ratio, lo=lo, hi=hi, bar=1.5,
                             met=ratio <= 1.5 and hi < 1.5))
    plain = directory / 'walls.jsonl'
    text = plain.read_text() if plain.exists() else gzip.decompress((directory / 'walls.jsonl.gz').read_bytes()).decode()
    walls = [json.loads(l) for l in text.splitlines() if l.strip()]
    passes = json.loads((directory / 'wide-attempts.json').read_text())
    for target, (field, name) in WIDE.items():
        z = [r['process_wall_ns'] / 1e6 for r in walls
             if r['target'] == target and r['workers'] == 16 and r['report'] and r['report']['status'] == 'complete']
        g = [a['solver_process_wall_ns'] / 1e6 for p in passes for a in p['attempts']
             if (a['field'], a['name'], a['engine']) == (field, name, 'grobx') and a['status'] == 'complete']
        if not z or not g:
            continue
        ratio = statistics.median(z) / statistics.median(g)
        lo, hi = interval(z, g, zlib.crc32(f'B {target}'.encode()))
        rows.append(dict(goal='B', window='walls+wide', target=target, zeebra=statistics.median(z), zeebra_workers=16,
                         n_zeebra=len(z), comparand='grobx (raw, randomized)', comparand_ms=statistics.median(g),
                         comparand_workers=1, n_comparand=len(g), ratio=ratio, lo=lo, hi=hi, bar=0.90,
                         met=ratio <= 0.90 and hi < 1.0))
    return rows


def main():
    rows = verdict_rows(Path(sys.argv[1]))
    print('| Goal | Window | Target | Zeebra ms (workers, n) | Comparand ms (workers, n) | Zeebra / comparand [95%] | Bar | Verdict |')
    print('|---|---|---|---:|---:|---:|---:|---|')
    for r in rows:
        print(f"| {r['goal']} | {r['window']} | {r['target']} | {r['zeebra']:.1f} ({r['zeebra_workers']}, {r['n_zeebra']}) | "
              f"{r['comparand']}: {r['comparand_ms']:.1f} ({r['comparand_workers']}, {r['n_comparand']}) | "
              f"**{r['ratio']:.2f}×** [{r['lo']:.2f}, {r['hi']:.2f}] | ≤{r['bar']} | "
              f"{'met' if r['met'] else '**target missed**'} |")


if __name__ == '__main__':
    main()
