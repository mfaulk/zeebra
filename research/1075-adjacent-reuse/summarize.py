#!/usr/bin/env python3
"""#1075's adjacent-round census and its timed arms, as markdown tables.

    python3 summarize.py runs.jsonl.gz > tables.md

Each row runs in three modes of the signature engine at one worker (`--adjacent`): `off` (the engine
as it ships, from the same binary), `count` (a previous-batch buffer of run-wide ids kept, every row
still built: upkeep and misses with no saving), and `reuse` (the buffer's hits served from the
stored ids). `count`'s per-batch record is the census.

Decision rules, fixed before any run was read. Ratios are paired per repetition, 95% bootstrap
(tools/bench_stats.py), on the solve call's wall (`call_ns`):

- **adopt-candidate** (worth a bench-host confirmation): reuse ÷ off upper bound < 0.98 on at least
  one development row other than the control, no held-out row with a lower bound > 1.02, the
  control's upper bound ≤ 1.02, and median peak RSS reuse ÷ off ≤ 1.15 on every row;
- **reject**: no development row has an upper bound < 1.0;
- **defer**: anything else.

Any basis digest that differs between arms, or a nonzero `mismatches`, voids the run.
"""

import gzip
import json
import pathlib
import statistics
import sys
from collections import defaultdict

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / "tools"))
import bench_stats as bs  # noqa: E402

CONTROL = "cyclic7-wide64"
HELD_OUT = {"noon8-wide64", "mq12-goldilocks", "dmq-n14-m28-m31-s0"}
ARMS = ("off", "count", "reuse")


def load(path):
    runs = defaultdict(lambda: defaultdict(dict))  # row -> arm -> rep -> record
    for line in gzip.open(path, "rt"):
        r = json.loads(line)
        runs[r["row"]][r["adjacent_mode"]][r["rep"]] = r
    return runs


def census(record):
    batches = record["adjacent"]
    total = lambda k: sum(b[k] for b in batches)  # noqa: E731
    return dict(batches=len(batches), targets=total("targets"), reducers=total("reducers"),
                target_hits=total("target_hits"), reducer_hits=total("reducer_hits"),
                terms=total("terms"), hit_terms=total("hit_terms"), mismatches=total("mismatches"),
                retained=max((b["retained_bytes"] for b in batches), default=0))


def ratio(arms, arm, metric, seed):
    pairs = bs.paired_ratios({k: v["statistics"][metric] if metric != "call_ns" else v[metric]
                              for k, v in arms[arm].items()},
                             {k: v["statistics"][metric] if metric != "call_ns" else v[metric]
                              for k, v in arms["off"].items()})
    return bs.paired_ratio(pairs, seed=seed) if pairs else None


def fmt(ci):
    return "—" if ci is None else f"{ci.median:.3f} [{ci.lo:.3f}, {ci.hi:.3f}]"


def pct(a, b):
    return f"{100 * a / b:.1f}%" if b else "—"


def main(path):
    runs = load(path)
    order = list(runs)
    out = ["## Census (one `count` run per row; identical in every repetition)\n",
           "| row | set | batches | reducer rows | adjacent reducer hits | target hits | hit terms / all terms "
           "| peak buffer | buffer / peak RSS | mismatches |",
           "|---|---|---:|---:|---:|---:|---:|---:|---:|---:|"]
    void = []
    for row in order:
        arms = runs[row]
        digests = {r.get("basis_sha256") for a in ARMS for r in arms[a].values()}
        statuses = {r.get("status") for a in ARMS for r in arms[a].values()}
        if len(digests) != 1 or statuses != {"complete"}:
            void.append(f"{row}: digests {sorted(map(str, digests))}, statuses {sorted(statuses)}")
            continue
        c = census(arms["count"][min(arms["count"])])
        if c["mismatches"]:
            void.append(f"{row}: {c['mismatches']} stored rows differ from the fresh ones")
        known = [r["peak_rss_bytes"] for r in arms["off"].values() if r.get("peak_rss_bytes")]
        rss = statistics.median(known) if known else None  # macOS records none
        kind = "control" if row == CONTROL else "held out" if row in HELD_OUT else "development"
        out.append(f"| {row} | {kind} | {c['batches']} | {c['reducers']:,} | {c['reducer_hits']:,} "
                   f"({pct(c['reducer_hits'], c['reducers'])}) | {c['target_hits']:,} / {c['targets']:,} | "
                   f"{c['hit_terms']:,} / {c['terms']:,} ({pct(c['hit_terms'], c['terms'])}) | "
                   f"{c['retained'] / 2**20:.2f} MiB | {pct(c['retained'], rss) if rss else '—'} | {c['mismatches']} |")
    out += ["\n## Timed arms (medians over repetitions; ratios paired per repetition vs `off`, 95% bootstrap)\n",
            "| row | n | call ms (off) | symbolic ms (off) | symbolic share | symbolic: count ÷ off | "
            "symbolic: reuse ÷ off | call: count ÷ off | call: reuse ÷ off | peak RSS reuse ÷ off |",
            "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|"]
    verdict_rows = {}
    for row in order:
        arms = runs[row]
        if any(v.startswith(row + ":") for v in void):
            continue
        med = lambda arm, f: statistics.median(f(r) for r in arms[arm].values())  # noqa: E731
        call = med("off", lambda r: r["call_ns"]) / 1e6
        sym = med("off", lambda r: r["statistics"]["symbolic_ns"]) / 1e6
        rss = (med("reuse", lambda r: r["peak_rss_bytes"]) / med("off", lambda r: r["peak_rss_bytes"])
               if all(r.get("peak_rss_bytes") for a in ("off", "reuse") for r in arms[a].values()) else None)
        cis = {(arm, m): ratio(arms, arm, m, f"{row} {arm} {m}")
               for arm in ("count", "reuse") for m in ("symbolic_ns", "call_ns")}
        verdict_rows[row] = (cis[("reuse", "call_ns")], rss)
        out.append(f"| {row} | {len(arms['off'])} | {call:,.1f} | {sym:,.1f} | {pct(sym, call)} | "
                   f"{fmt(cis[('count', 'symbolic_ns')])} | {fmt(cis[('reuse', 'symbolic_ns')])} | "
                   f"{fmt(cis[('count', 'call_ns')])} | {fmt(cis[('reuse', 'call_ns')])} | {'—' if rss is None else f'{rss:.3f}'} |")
    dev = {r: v for r, v in verdict_rows.items() if r not in HELD_OUT and r != CONTROL}
    if void:
        decision = "void: " + "; ".join(void)
    elif not any(ci.hi < 1.0 for ci, _ in dev.values()):
        decision = "**reject**: no development row's solve wall improves (every upper bound ≥ 1.0)"
    elif (any(ci.hi < 0.98 for ci, _ in dev.values())
          and not any(verdict_rows[r][0].lo > 1.02 for r in HELD_OUT if r in verdict_rows)
          and (CONTROL not in verdict_rows or verdict_rows[CONTROL][0].hi <= 1.02)
          and all(rss is None or rss <= 1.15 for _, rss in verdict_rows.values())):
        decision = "**adopt-candidate**: confirm pinned on the bench host" + (
            "; peak RSS was not recorded, so the RSS rule is unchecked"
            if any(rss is None for _, rss in verdict_rows.values()) else "")
    else:
        decision = "**defer**: some development row improves, but not past the adopt-candidate rules"
    out += ["\n## Decision (rules in this script's docstring)\n", decision]
    print("\n".join(out))


if __name__ == "__main__":
    main(sys.argv[1])
