#!/usr/bin/env python3
"""Median [min,max] per task and arm from run-study.py output, with basis agreement (#752).

  summarize-study.py STUDY.jsonl [--check]

--check fails unless every attempt completed and every arm of a task produced one basis digest.
"""
import collections
import gzip
import json
import statistics
import sys

path = sys.argv[1]
check = "--check" in sys.argv
opener = gzip.open if path.endswith(".gz") else open
records = [json.loads(line) for line in opener(path, "rt") if line.strip()]
cells = collections.defaultdict(list)
digests = collections.defaultdict(set)
failures = []
for r in records:
    task = (r["problem"], r["modulus"])
    if r["status"] != 0:
        failures.append(r)
        continue
    cells[task, r["arm"]].append(r)
    digests[task].add(r["result"]["basis_sha256"])


def stat(values):
    return f"{statistics.median(values):9.2f} [{min(values):9.2f},{max(values):9.2f}]"


tasks = sorted({task for task, _ in cells})
for task in tasks:
    arms = [arm for (t, arm) in cells if t == task]
    serial = statistics.median(r["result"]["f4_ns"] for r in cells[task, "serial/selected"]) / 1e6
    print(f"\n{task[0]} / {task[1]}  basis digests: {len(digests[task])}")
    print(f"  {'arm':22} {'n':>2} {'F4 ms median [min,max]':>32} {'x':>6} {'process ms':>32} "
          f"{'CPU ms':>9} {'RSS MiB':>8} {'disp':>5} {'wk':>3}")
    for arm in sorted(arms, key=lambda a: (a.split("/")[1], a)):
        rs = cells[task, arm]
        f4 = [r["result"]["f4_ns"] / 1e6 for r in rs]
        proc = [r["external_wall_ns"] / 1e6 for r in rs]
        cpu = statistics.median(r["result"]["process_cpu_us"] / 1e3 for r in rs)
        rss = max(r["result"]["peak_rss_bytes"] for r in rs) / 2**20
        res = rs[0]["result"]
        print(f"  {arm:22} {len(rs):2} {stat(f4)} {serial / statistics.median(f4):6.2f} {stat(proc)} "
              f"{cpu:9.1f} {rss:8.2f} {res['parallel_batches']:5} {res['parallel_max_workers']:3}")
print(f"\nattempts: {len(records)}, failed: {len(failures)}")
for f in failures:
    print("  FAILED", f["problem"], f["modulus"], f["arm"], f["rep"], f["status"], f["stderr"][-200:])
if check and (failures or any(len(d) != 1 for d in digests.values())):
    sys.exit("check failed: incomplete attempts or disagreeing bases")
