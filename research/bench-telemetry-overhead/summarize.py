"""Paired off/on wall ratios per cell from aa.py's JSONL, with tools/bench_stats.py's bootstrap CI.

Gate (#1105): median within 1.000 +/- 0.005 and the 95% CI covers 1.0.
Usage: python3 -I summarize.py <repo> <attempts.jsonl>"""
import json, sys, importlib.util
from collections import defaultdict
from pathlib import Path

repo, path = Path(sys.argv[1]), sys.argv[2]
spec = importlib.util.spec_from_file_location('bench_stats', repo / 'tools/bench_stats.py')
bs = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bs)

walls = defaultdict(dict)
for line in open(path):
    r = json.loads(line)
    if r['exit'] == 0:
        walls[(r['cell'], r['arm'])][r['rep']] = r['wall_s']
print('| cell | pairs | median on s | median off s | off/on median [95% CI] | gate |')
print('|---|---:|---:|---:|---|---|')
for cell in sorted({c for c, _ in walls}):
    on, off = walls[(cell, 'on')], walls[(cell, 'off')]
    ci = bs.paired_ratio(bs.paired_ratios(off, on), seed=f'1105-aa-{cell}')
    ok = abs(ci.median - 1) <= 0.005 and ci.lo <= 1 <= ci.hi
    med = lambda d: sorted(d.values())[len(d) // 2]
    print(f'| {cell} | {ci.n if hasattr(ci, "n") else len(on)} | {med(on):.4f} | {med(off):.4f} | '
          f'{ci.median:.4f} [{ci.lo:.4f}, {ci.hi:.4f}] | {"pass" if ok else "FAIL"} |')
