#!/usr/bin/env python3
"""Run part of #1034's census one instance and arm per process, under a wall and RSS watchdog.

F4's wall cap is checked between batches, so a run inside one large batch cannot be stopped by
it, and an RSS ceiling has no in-process equivalent on macOS. This driver runs
`bilinear_census` once per (shape, kind, arm, instance), polls the child's RSS, and kills it at
either limit. It applies the pre-declared rule per shape, kind and arm: once one instance is
stopped (censored at the wall cap, or refused at the RSS ceiling), the remaining instances of
that shape, kind and arm are `skipped`.

Every line it appends to the output is `arm<TAB>outcome<TAB>example row`, where the outcome is
`ran`, `censored`, `refused-rss` or `skipped`. `merge.py` folds these into `counts.tsv`.

Usage:
  split_run.py BINARY OUT.tsv --cap S --rss-gb G --entries E --workers W \
      --task 6x6-affine:control [--task ...]
"""

import argparse
import os
import subprocess
import sys
import time

FIELDS = ["31", "32003", "2147483647"]
SUPPORTS = ["1000", "600", "300"]
SEEDS = ["1", "2"]


def rss_kb(pid):
    out = subprocess.run(["ps", "-o", "rss=", "-p", str(pid)], capture_output=True, text=True)
    try:
        return int(out.stdout.strip())
    except ValueError:
        return 0


def prefix(shape, kind, instance):
    k, n_y = (int(x) for x in shape.split("x"))
    n = k + n_y
    m = n if kind == "affine" else n - 2
    return "\t".join(map(str, [k, n_y, n, m, kind, *instance.split("/")]))


def run_one(args, shape, kind, arm, instance, log):
    env = dict(
        os.environ,
        ZB_SHAPES=f"{shape}-{kind}",
        ZB_INSTANCES=instance,
        ZB_ARMS=arm,
        ZB_ENTRIES=str(args.entries),
        ZB_WORKERS=str(args.workers),
        ZB_TRACE="1",
    )
    start = time.monotonic()
    child = subprocess.Popen(
        [args.binary, str(args.cap)], env=env, stdout=subprocess.PIPE, stderr=log, text=True
    )
    limit_kb = int(args.rss_gb * 1024 * 1024)
    peak = 0
    stopped = None
    while child.poll() is None:
        peak = max(peak, rss_kb(child.pid))
        elapsed = time.monotonic() - start
        if peak > limit_kb:
            stopped = "refused-rss"
        elif elapsed > args.cap + args.grace:
            stopped = "censored"
        if stopped:
            child.kill()
            break
        time.sleep(1)
    out, _ = child.communicate()
    elapsed = time.monotonic() - start
    log.write(f"# {shape}-{kind} {arm} {instance}: {stopped or 'ran'} after {elapsed:.0f}s\n")
    log.flush()
    if stopped:
        return stopped, prefix(shape, kind, instance)
    rows = [line for line in out.splitlines() if line and not line.startswith("k\t")]
    if len(rows) != 1:
        sys.exit(f"expected one row for {shape}-{kind} {arm} {instance}, got {rows!r}")
    return "ran", rows[0]


def main():
    p = argparse.ArgumentParser()
    p.add_argument("binary")
    p.add_argument("out")
    p.add_argument("--cap", type=int, required=True, help="wall cap per run, seconds")
    p.add_argument("--grace", type=int, default=30, help="seconds past the cap before a kill")
    p.add_argument("--rss-gb", type=float, required=True)
    p.add_argument("--entries", type=int, required=True)
    p.add_argument("--workers", type=int, required=True)
    p.add_argument("--task", action="append", required=True, help="<k>x<n_y>-<kind>:<arm>")
    p.add_argument("--log", default="split_run.log")
    args = p.parse_args()

    with open(args.out, "a") as out, open(args.log, "a") as log:
        for task in args.task:
            shape_kind, arm = task.split(":")
            shape, kind = shape_kind.split("-")
            stopped = False
            for instance in (f"{f}/{s}/{d}" for f in FIELDS for s in SUPPORTS for d in SEEDS):
                if stopped:
                    outcome, row = "skipped", prefix(shape, kind, instance)
                else:
                    outcome, row = run_one(args, shape, kind, arm, instance, log)
                    # The pre-declared rule: a run past the cap censors the rest of its shape.
                    status = row.split("\t")[8] if outcome == "ran" else None
                    column = {"control": 19, "signature": 21}.get(arm)
                    stopped = outcome != "ran" or status == "censored" or (
                        column is not None and row.split("\t")[column] == "censored"
                    )
                out.write(f"{arm}\t{outcome}\t{row}\n")
                out.flush()


if __name__ == "__main__":
    main()
