#!/usr/bin/env python3
"""#855 drift: every M30-0 cell's median against M29's final cohort (#837), per cell.

A cell is (suite, target, engine, workers). Each side's median gets a 95% bootstrap interval
(20,000 draws, seeded by the CRC-32 of the cell name, as research/m29-final/verdicts.py). A cell is
`inside` when the M30 median lies in M29's interval, `faster`/`slower` otherwise; the verdict ratios
are compared the same way in verdicts.md. The two cohorts are separate windows and are never pooled.

    python3 research/m30-baseline/drift.py research/m29-final research/m30-baseline > drift.md
"""
import gzip
import json
import random
import statistics
import sys
import zlib
from pathlib import Path

DRAWS = 20000
WIDE = {('wide64', 'eco-12'): 'eco12-wide64', ('goldilocks', 'mq-random-11'): 'mq11-goldilocks'}


def interval(xs, name):
    rng = random.Random(zlib.crc32(name.encode()))
    meds = sorted(statistics.median(rng.choices(xs, k=len(xs))) for _ in range(DRAWS))
    return meds[int(0.025 * DRAWS)], meds[int(0.975 * DRAWS) - 1]


def cells(directory):
    out = {}
    text = gzip.decompress((directory / 'walls.jsonl.gz').read_bytes()).decode()
    for line in text.splitlines():
        r = json.loads(line)
        if r['report'] and r['report']['status'] == 'complete':
            out.setdefault(('walls', r['target'], 'zeebra', r['workers']), []).append(r['process_wall_ns'] / 1e6)
    for p in json.loads((directory / 'wide-attempts.json').read_text()):
        for a in p['attempts']:
            if a['status'] == 'complete':
                key = ('wide', WIDE[(a['field'], a['name'])], a['engine'], 1)
                out.setdefault(key, []).append(a['solver_process_wall_ns'] / 1e6)
    for win in json.loads((directory / 'mq10-attempts.json').read_text()):
        if not win['archive'].startswith('mq10-try1'):
            continue  # the reported window only; other windows are kept, not pooled
        for a in win['attempts']:
            if a['status'] == 'verified' and a.get('process_wall_ns'):
                target = 'mq10-32003' if str(a['field']) == '32003' else 'mq10-m31'
                out.setdefault(('mq10', target, a['engine'], a['workers']), []).append(a['process_wall_ns'] / 1e6)
    return out


def main():
    old, new = cells(Path(sys.argv[1])), cells(Path(sys.argv[2]))
    print('| Suite | Target | Engine | Workers | M29 ms [95%] (n) | M30-0 ms [95%] (n) | M30/M29 | Drift |')
    print('|---|---|---|---:|---:|---:|---:|---|')
    tally = {}
    for key in sorted(set(old) | set(new), key=lambda k: (k[0], k[1], k[2], k[3])):
        name = '/'.join(map(str, key))
        if key not in old or key not in new:
            print(f'| {" | ".join(map(str, key))} | {"absent" if key not in old else "-"} | '
                  f'{"absent" if key not in new else "-"} | - | not comparable |')
            continue
        o, n = old[key], new[key]
        olo, ohi = interval(o, 'm29 ' + name)
        nlo, nhi = interval(n, 'm30 ' + name)
        om, nm = statistics.median(o), statistics.median(n)
        verdict = 'inside' if olo <= nm <= ohi else ('faster' if nm < olo else 'slower')
        tally[verdict] = tally.get(verdict, 0) + 1
        print(f'| {key[0]} | {key[1]} | {key[2]} | {key[3]} | {om:.1f} [{olo:.1f}, {ohi:.1f}] ({len(o)}) | '
              f'{nm:.1f} [{nlo:.1f}, {nhi:.1f}] ({len(n)}) | {nm / om:.3f} | {verdict} |')
    print()
    print('Cells: ' + ', '.join(f'{v} {k}' for k, v in sorted(tally.items())) + '.')


if __name__ == '__main__':
    main()
