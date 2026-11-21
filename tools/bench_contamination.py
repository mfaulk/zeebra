#!/usr/bin/env python3
"""Contamination verdicts and mode checks for M33 measurements (plan §11.2, #968).

Inputs are `tools/cpu-context.sh` snapshots taken before and after each attempt. Thresholds are
the plan's starting values: calibration may tighten them, and loosening one takes an owner
decision on #965. Bench CPUs are judged in aggregate, because /proc/stat cannot split the child's
own time by CPU: foreign = (bench busy - own CPU time) / bench total. Siblings are held idle, so
all their busy time is foreign and each is judged alone.

  bench_contamination.py attempt BEFORE.json AFTER.json [--own-cpu-s S] [--mode M]
                         [--session-median-khz K] [--owner NAME]
  bench_contamination.py session METRICS.jsonl [--mode M] [--owner NAME]   rc 1 when void
  bench_contamination.py check --cpus LIST [--mode M] [--owner NAME] [--wait S] [--poll S]
                         rc 0 may start, 1 refused, 2 snapshot failed
"""

import argparse
import json
import pathlib
import statistics
import subprocess
import sys
import time
from datetime import datetime

USER_HZ = 100
FOREIGN_BUSY = 0.05  # per sibling, and bench CPUs in aggregate
FREQ_DEVIATION = 0.03  # attempt median clock vs session (group) median
VOID_FRACTION = 0.20  # session void above this fraction contaminated
PUBLICATION_LOAD = 4.0  # busy-CPU equivalents on the non-bench CPUs (start: load1)
MODES = ("dev", "publication")


def _ts(s):
    return datetime.fromisoformat(s.replace("Z", "+00:00")).timestamp()


def _delta(before, after, cpu):
    b = next((s for s in before["stat"] if s["cpu"] == cpu), None)
    a = next(s for s in after["stat"] if s["cpu"] == cpu)
    if b is None:
        return None
    return a["busy"] - b["busy"], a["total"] - b["total"]


def _frac(busy, total):
    return busy / total if total > 0 else 0.0


def attempt_metrics(before, after, own_cpu_s=None, khz_samples=None):
    """Busy fractions, clock, power and process counts over one attempt.

    `own_cpu_s` is the child's user + system CPU seconds (`os.wait4` rusage); without it the
    bench CPUs cannot be judged. `khz_samples` overrides the bench clocks read from the two
    snapshots, for a runner that samples `scaling_cur_freq` during the attempt.
    """
    sibling_busy, bench_busy, bench_b, bench_t = {}, {}, 0, 0
    for s in after["stat"]:
        d = _delta(before, after, s["cpu"])
        if d is None:
            continue
        if s["role"] == "sibling":
            sibling_busy[s["cpu"]] = _frac(*d)
        else:
            bench_busy[s["cpu"]] = _frac(*d)
            bench_b, bench_t = bench_b + d[0], bench_t + d[1]
    bench_foreign = None
    if own_cpu_s is not None and bench_t > 0:
        bench_foreign = max(0.0, bench_b - own_cpu_s * USER_HZ) / bench_t
    khz = khz_samples or [c["khz"] for s in (before, after) for c in s["cpus"] if c.get("khz")]
    rest_load = None
    rb, ra = before.get("rest_stat"), after.get("rest_stat")
    if rb and ra and ra["total"] > rb["total"]:
        rest_load = ra["cpus"] * _frac(ra["busy"] - rb["busy"], ra["total"] - rb["total"])
    seconds = _ts(after["at"]) - _ts(before["at"])
    package_w = None
    if before.get("rapl_uj") is not None and after.get("rapl_uj") is not None and seconds > 0:
        e = after["rapl_uj"] - before["rapl_uj"]
        if e < 0 and after.get("rapl_max_uj"):
            e += after["rapl_max_uj"]
        package_w = e * 1e-6 / seconds
    return {
        "seconds": seconds,
        "sibling_busy": sibling_busy,
        "bench_busy": bench_busy,
        "bench_foreign": bench_foreign,
        "median_khz": statistics.median(khz) if khz else None,
        "rest_load": rest_load,
        "load1": max(before["load1"], after["load1"]),
        "compilers": max(before["compilers"], after["compilers"]),
        "runner_workers": max(before.get("runner_workers", 0), after.get("runner_workers", 0)),
        "benchlock_owners": sorted({o["owner"] for s in (before, after)
                                    for o in s.get("benchlock_open", [])}),
        "clock": after.get("clock"),
        "package_w": package_w,
    }


def _process_reasons(compilers, workers, owners, owner):
    reasons = []
    if compilers:
        reasons.append(f"{compilers} compiler process(es)")
    if workers:
        reasons.append(f"{workers} Runner.Worker process(es)")
    others = [o for o in owners if o != owner]
    if others:
        reasons.append("other benchlock owner(s): " + ", ".join(others))
    return reasons


def attempt_verdict(metrics, mode="dev", session_median_khz=None, owner=None):
    """{"contaminated", "reasons", "notes"} for one attempt under the mode's rules.

    The frequency rule applies only when `session_median_khz` is given; `session_verdict`
    recomputes every attempt against the final median. `owner` is this run's benchlock owner,
    which publication mode does not count against itself.
    """
    if mode not in MODES:
        raise ValueError(f"mode must be one of {MODES}")
    reasons, notes = [], []
    for cpu, f in sorted(metrics["sibling_busy"].items()):
        if f > FOREIGN_BUSY:
            reasons.append(f"sibling cpu {cpu} busy {100 * f:.1f}%")
    if metrics["bench_foreign"] is None:
        notes.append("bench_foreign unjudged: no own_cpu_s")
    elif metrics["bench_foreign"] > FOREIGN_BUSY:
        reasons.append(f"bench foreign busy {100 * metrics['bench_foreign']:.1f}%")
    m = metrics["median_khz"]
    if session_median_khz and m is not None:
        dev = abs(m - session_median_khz) / session_median_khz
        if dev > FREQ_DEVIATION:
            reasons.append(f"bench clock {m:.0f} kHz is {100 * dev:.1f}% off the session median")
    if mode == "publication":
        load = metrics["rest_load"]
        if load is None:
            notes.append("rest_load unavailable: using load1")
            load = metrics["load1"]
        if load >= PUBLICATION_LOAD:
            reasons.append(f"rest load {load:.2f} >= {PUBLICATION_LOAD:g}")
        reasons += _process_reasons(metrics["compilers"], metrics["runner_workers"],
                                    metrics["benchlock_owners"], owner)
    return {"contaminated": bool(reasons), "reasons": reasons, "notes": notes}


def session_verdict(metrics_list, mode="dev", groups=None, owner=None):
    """Per-attempt verdicts against each group's median clock, and whether the session is void.

    `groups` (parallel to `metrics_list`) keys the frequency median: attempts at 1 and 16
    workers run at different clocks by design (#827), so each worker count is its own group.
    """
    groups = groups or [None] * len(metrics_list)
    medians = {}
    for g in set(groups):
        khz = [m["median_khz"] for m, k in zip(metrics_list, groups)
               if k == g and m["median_khz"] is not None]
        medians[g] = statistics.median(khz) if khz else None
    verdicts = [attempt_verdict(m, mode, medians[g], owner) for m, g in zip(metrics_list, groups)]
    n = sum(v["contaminated"] for v in verdicts)
    return {"mode": mode, "attempts": verdicts, "contaminated": n, "total": len(verdicts),
            "void": bool(verdicts) and n / len(verdicts) > VOID_FRACTION,
            "median_khz": {str(k): v for k, v in medians.items()}}


def publication_refusals(snapshot, owner=None):
    """Why publication mode may not start now ([] when it may). Nothing of ours runs yet, so
    machine-wide load1 stands in for the non-bench load, which is the stricter reading."""
    reasons = []
    if snapshot["load1"] >= PUBLICATION_LOAD:
        reasons.append(f"load1 {snapshot['load1']:.2f} >= {PUBLICATION_LOAD:g}")
    return reasons + _process_reasons(
        snapshot["compilers"], snapshot.get("runner_workers", 0),
        [o["owner"] for o in snapshot.get("benchlock_open", [])], owner)


def take_snapshot(cpus):
    out = subprocess.run(["bash", str(pathlib.Path(__file__).with_name("cpu-context.sh")), cpus],
                         capture_output=True, text=True)
    if out.returncode != 0:
        raise RuntimeError(f"cpu-context.sh rc {out.returncode}: {out.stderr.strip()}")
    return json.loads(out.stdout)


def _check(args):
    deadline = time.monotonic() + args.wait
    while True:
        try:
            snapshot = take_snapshot(args.cpus)
        except (RuntimeError, ValueError) as e:
            print(json.dumps({"mode": args.mode, "error": str(e)}))
            return 2
        refusals = publication_refusals(snapshot, args.owner) if args.mode == "publication" else []
        if not refusals or time.monotonic() + args.poll > deadline:
            print(json.dumps({"mode": args.mode, "clock": snapshot.get("clock"),
                              "refusals": refusals, "refused": bool(refusals)}))
            return 1 if refusals else 0
        time.sleep(args.poll)


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)
    for name in ("attempt", "session", "check"):
        s = sub.add_parser(name)
        s.add_argument("--mode", choices=MODES, default="dev")
        s.add_argument("--owner")
    a = sub.choices["attempt"]
    a.add_argument("before")
    a.add_argument("after")
    a.add_argument("--own-cpu-s", type=float)
    a.add_argument("--session-median-khz", type=float)
    sub.choices["session"].add_argument("metrics", help="JSON lines of {metrics, group?}")
    c = sub.choices["check"]
    c.add_argument("--cpus", required=True)
    c.add_argument("--wait", type=float, default=0, help="keep polling up to this many seconds")
    c.add_argument("--poll", type=float, default=60)
    args = p.parse_args(argv)
    if args.cmd == "check":
        return _check(args)
    if args.cmd == "attempt":
        m = attempt_metrics(json.loads(pathlib.Path(args.before).read_text()),
                            json.loads(pathlib.Path(args.after).read_text()), args.own_cpu_s)
        print(json.dumps({"metrics": m, "verdict": attempt_verdict(
            m, args.mode, args.session_median_khz, args.owner)}))
        return 0
    rows = [json.loads(line) for line in pathlib.Path(args.metrics).read_text().splitlines() if line]
    s = session_verdict([r["metrics"] for r in rows], args.mode, [r.get("group") for r in rows],
                        args.owner)
    print(json.dumps(s))
    return 1 if s["void"] else 0


if __name__ == "__main__":
    sys.exit(main())
