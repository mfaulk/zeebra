"""§8.4: fit the telemetry limit on the calibration cohort only, all loaded workloads pooled.

Usage: python3 -I fit_limits.py --records <calibration records.jsonl.gz ...> --out limits.json
Prints the SHA-256 of limits.json, which is posted on #1107 before any held-out record is summarized.
"""
import argparse
import json
import sys
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import calib  # noqa: E402
from extract import read  # noqa: E402


def idle_ratios(prs):
    """{(session, cell, num, den): [ratios]} from each session's first W0 job (slot 0)."""
    out = defaultdict(list)
    for p in prs:
        if p['workload'] == 'W0' and p['slot'] == 0:
            out[(p['session'], p['cell'], p['num'], p['den'])].append(p['ratio'])
    return out


def moved_table(prs):
    idle = idle_ratios(prs)
    rows = []
    for p in prs:
        if p['workload'] == 'W0' or p['signals'] is None:
            continue
        ref = idle.get((p['session'], p['cell'], p['num'], p['den']))
        if ref:
            rows.append((p, calib.moved(p['ratio'], ref)))
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--records', nargs='+', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    a = ap.parse_args()
    recs = read(a.records)
    calib.require_cohort(recs, 'calibration')
    refs = json.loads((HERE / 'references.json').read_text())
    rows = moved_table(calib.pairs(calib.select(recs, 'raw', refs)))
    moved = [m for _, m in rows]
    names = sorted(rows[0][0]['signals']) if rows else []
    rule = calib.fit_rule({s: [p['signals'][s] for p, _ in rows] for s in names}, moved)
    out = dict(issue=1107, protocol='docs/research/concurrent-benchmark-calibration-protocol.md §8.4', C=calib.C,
               rule=rule['signals'], j=rule['j'], eligible=rule['eligible'], single=rule.get('single'),
               pairs=len(rows), moved=sum(moved), sessions=sorted({p['session'] for p, _ in rows}),
               workloads=sorted({p['workload'] for p, _ in rows}),
               records={p.name: calib.sha(p) for p in a.records})
    a.out.write_text(json.dumps(out, indent=1, sort_keys=True) + '\n')
    print(f'{a.out}: rule {out["rule"]} J={out["j"]:.3f} over {out["pairs"]} pairs ({out["moved"]} moved)')
    print('sha256', calib.sha(a.out))


if __name__ == '__main__':
    main()
