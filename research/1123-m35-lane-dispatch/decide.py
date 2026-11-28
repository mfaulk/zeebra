#!/usr/bin/env python3
"""#1123 (M35 E): score the held-out read against the criteria frozen on #1123 before its rows existed.

    decide.py heldout.jsonl

Targets pass when D <= L + 0.10 (F - L) on medians. Controls pass when the upper 95% bound of
rule / field is at most 1.05. Every row needs one digest across arms and rule RSS <= 1.15x field.
Contaminated attempts are dropped.
"""
import json
import statistics
import sys
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parents[1] / 'tools'))
import bench_stats  # noqa: E402
from sweep import HELD_OUT  # noqa: E402


def main(path):
    d = defaultdict(list)
    for line in open(path):
        r = json.loads(line)
        if not r['contaminated'] and r['status'] == 'complete':
            d[(r['id'], r['arm'])].append(r)
    failed = []
    for row, field, role in HELD_OUT:
        rid = f'{field}/{row}'
        t = {arm: [r['call_ns'] / 1e9 for r in d[(rid, arm)]] for arm in ('field', 'rule', 'lane')}
        rss = {arm: statistics.median(r['peak_rss_bytes'] for r in d[(rid, arm)]) for arm in ('field', 'rule')}
        digests = {r['basis_sha256'] for arm in ('field', 'rule', 'lane') for r in d[(rid, arm)]}
        F, D, L = (statistics.median(t[a]) for a in ('field', 'rule', 'lane'))
        ratio = bench_stats.independent_ratio(t['rule'], t['field'], seed=1123)
        if role == 'target':
            ok = D <= L + 0.10 * (F - L)
            crit = f'D={D:.3f} L={L:.3f} F={F:.3f} need<={L + 0.10 * (F - L):.3f}'
        else:
            ok = ratio.hi <= 1.05
            crit = ''
        ok = ok and len(digests) == 1 and rss['rule'] <= 1.15 * rss['field']
        if not ok:
            failed.append(rid)
        print(f'{"PASS" if ok else "FAIL"} {rid:28s} [{role}] field={F:.4f}s rule/field={ratio.median:.3f} '
              f'({ratio.lo:.3f}-{ratio.hi:.3f}) lane/field={L / F:.3f} n={ratio.n},{ratio.n_ref} {crit} '
              f'digests={len(digests)} rss={rss["rule"] / rss["field"]:.3f}')
    print('PASS' if not failed else f'FAIL: {failed}')


if __name__ == '__main__':
    main(sys.argv[1])
