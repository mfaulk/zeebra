"""#903 stage table: per row and arm, median in-process stage clocks, call time, process wall and
peak RSS from `ab.py` records (complete children only). With `research-sigf4-split` builds it also
reports #901's per-batch setup (row construction inside elimination), summed over batches.

    python3 research/m31-sigf4-serial/stages.py RECORDS.jsonl[.gz] ARM[,ARM...] ROW[,ROW...]
"""
import gzip
import json
import statistics
import sys
from collections import defaultdict

STAGES = ['elimination_ns', 'interreduction_ns', 'bookkeeping_ns', 'symbolic_ns']


def setup_ms(record):
    split = record['report']['statistics'].get('split')
    return None if split is None else sum(b['setup_ns'] for b in split['batches']) / 1e6


def main(path, arms, rows):
    opener = gzip.open if path.endswith('.gz') else open
    runs = defaultdict(list)
    with opener(path, 'rt') as handle:
        for line in handle:
            r = json.loads(line)
            if r['returncode'] == 0 and (r['report'] or {}).get('status') == 'complete':
                runs[(r['row'], r['arm'])].append(r)
    print('| Row | Arm | n | Elimination | Interreduction | Bookkeeping | Symbolic | Sum | Call | '
          'Process wall | Peak RSS MiB | Setup (in elimination) |')
    print('|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|')
    for row in rows:
        for arm in arms:
            rs = runs[(row, arm)]
            if not rs:
                continue
            med = [statistics.median(x['report']['statistics'][s] for x in rs) / 1e6 for s in STAGES]
            call = statistics.median(x['report']['statistics']['total_ns'] for x in rs) / 1e6
            wall = statistics.median(x['process_wall_ns'] for x in rs) / 1e6
            rss = statistics.median(x['report']['peak_rss_bytes'] for x in rs) / 2**20
            setups = [setup_ms(x) for x in rs]
            setup = '—' if None in setups else f'{statistics.median(setups):,.1f}'
            cells = ' | '.join(f'{c:,.1f}' for c in med)
            print(f'| {row} | {arm} | {len(rs)} | {cells} | {sum(med):,.1f} | {call:,.1f} | '
                  f'{wall:,.1f} | {rss:,.1f} | {setup} |')


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2].split(','), sys.argv[3].split(','))
