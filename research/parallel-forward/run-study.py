#!/usr/bin/env python3
"""Complete-task forward x backward campaign for #752. Run under tools/benchlock.sh.

  run-study.py BINARY OUT.jsonl PLAN

PLAN is `adoption` or `scaling`. Every attempt is a fresh process pinned to one logical CPU per
physical core (cores 2..65), five interleaved repetitions with the arm order rotated per
repetition. Nothing is retried or dropped: a failed or timed-out attempt is recorded as such.
"""
import json
import os
import subprocess
import sys
import time

binary, out_path, plan = sys.argv[1:4]

MQ = [("mq-random-10", 32003), ("mq-random-10", 2147483647)]
SMALL = [(f, p) for f in ("cyclic-5", "katsura-6", "cyclic-6", "katsura-7") for p in (32003, 2147483647)]
TRAINING = [("katsura-9", 32003), ("cyclic-7", 32003)]
HELDOUT = [
    ("katsura-8", 2147483647),
    ("cyclic-8", 2147483647),
    ("katsura-10", 32003),
    ("mq-planted-10", 2147483647),
    ("mq-planted-wide-10", 0),
]
AUTO = "auto:16/selected"

if plan == "scaling":
    cells = [
        (task, arm)
        for task in MQ
        for arm in ["serial/selected", "forced:1/selected"]
        + [f"forced:{p}/selected" for p in (2, 4, 8, 16, 32, 64)]
        + [AUTO, "serial/full", "forced:16/full"]
    ]
elif plan == "adoption":
    cells = [(task, arm) for task in SMALL + TRAINING + HELDOUT
             for arm in ("serial/selected", AUTO)]
else:
    sys.exit("PLAN: scaling | adoption")


def physical_cpus():
    seen, cpus = set(), []
    for line in subprocess.run(["lscpu", "-p=CPU,CORE"], capture_output=True, text=True,
                               check=True).stdout.splitlines():
        if line.startswith("#"):
            continue
        cpu, core = line.split(",")
        if core not in seen:
            seen.add(core)
            cpus.append(cpu)
    return ",".join(cpus[2:66])


cpus = physical_cpus()
with open(out_path, "a") as out:
    for rep in range(5):
        shift = rep * len(cells) // 5
        for (problem, modulus), arm in cells[shift:] + cells[:shift]:
            cmd = ["taskset", "-c", cpus, binary, f"--problem={problem}", f"--modulus={modulus}",
                   f"--arm={arm}"]
            load = os.getloadavg()[0]
            t = time.monotonic_ns()
            try:
                r = subprocess.run(cmd, capture_output=True, text=True, timeout=300)
                status, stdout, stderr = r.returncode, r.stdout, r.stderr[-2000:]
            except subprocess.TimeoutExpired:
                status, stdout, stderr = "timeout", "", ""
            wall = time.monotonic_ns() - t
            record = {
                "rep": rep, "problem": problem, "modulus": modulus, "arm": arm,
                "status": status, "external_wall_ns": wall, "load_before": load,
                "result": json.loads(stdout) if status == 0 else None, "stderr": stderr,
            }
            out.write(json.dumps(record) + "\n")
            out.flush()
