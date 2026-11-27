#!/usr/bin/env python3
"""#1075's flat buffer: census counters and timed arms, as markdown tables.

    python3 summarize.py runs.jsonl.gz > tables.md

Each row runs in four modes of the signature engine at one worker (`--adjacent`): `off` (the engine
as it ships, from the same binary), `flat-count` (the flat buffer kept, every row still built:
upkeep and misses with no saving), `flat` (its hits served from the stored ids) and `reuse` (the
census's map buffer, served, for comparison).

Decision rules, fixed before any run was read. Ratios are paired per repetition, 95% bootstrap
(tools/bench_stats.py), on the solve call's wall (`call_ns`). These are unpinned laptop figures, so
the best outcome is a candidate for a pinned bench-host run, never an adoption:

- **bench-host candidate**: flat ÷ off upper bound < 0.98 on at least one development row, the
  adverse control Noon-8's lower bound ≤ 1.02, and no other held-out row's lower bound > 1.02;
- **reject**: no development row has an upper bound < 1.0;
- **defer**: anything else.

Any basis digest or work counter that differs between arms, or a nonzero `mismatches`, voids the row.
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
ADVERSE = "noon8-wide64"
HELD_OUT = {ADVERSE, "mq12-goldilocks", "dmq-n14-m28-m31-s0"}
ARMS = ("off", "flat-count", "flat", "reuse")
# The engine's work, which no buffer may change.
WORK = ("batches", "targets", "reducer_rows", "zero_rows", "singular_rows", "coefficient_products",
        "products_on_zero_rows", "max_matrix_rows", "max_matrix_columns",
        "signature_basis_elements")


def load(path):
    runs = defaultdict(lambda: defaultdict(dict))  # row -> arm -> rep -> record
    opener = gzip.open if str(path).endswith(".gz") else open
    for line in opener(path, "rt"):
        r = json.loads(line)
        runs[r["row"]][r["adjacent_mode"]][r["rep"]] = r
    return runs


def census(record):
    batches = record["adjacent"]
    total = lambda k: sum(b.get(k, 0) for b in batches)  # noqa: E731
    keys = ("targets", "reducers", "target_hits", "reducer_hits", "terms", "hit_terms",
            "saved_probes", "mismatches", "unbuffered")
    out = {k: total(k) for k in keys}
    out["batches"] = len(batches)
    out["retained"] = max((b["retained_bytes"] for b in batches), default=0)
    return out


def ratio(arms, arm, metric, seed):
    value = lambda r: r[metric] if metric == "call_ns" else r["statistics"][metric]  # noqa: E731
    pairs = bs.paired_ratios({k: value(v) for k, v in arms[arm].items()},
                             {k: value(v) for k, v in arms["off"].items()})
    return bs.paired_ratio(pairs, seed=seed) if pairs else None


def fmt(ci):
    return "—" if ci is None else f"{ci.median:.3f} [{ci.lo:.3f}, {ci.hi:.3f}]"


def pct(a, b):
    return f"{100 * a / b:.1f}%" if b else "—"


def kind(row):
    return ("control" if row == CONTROL else "adverse control" if row == ADVERSE
            else "held out" if row in HELD_OUT else "development")


def main(path):
    runs = load(path)
    order = list(runs)
    void = []
    for row in order:
        arms = runs[row]
        records = [r for a in ARMS for r in arms[a].values()]
        digests = {r.get("basis_sha256") for r in records}
        statuses = {r.get("status") for r in records}
        work = {tuple(r["statistics"][k] for k in WORK) for r in records if r.get("statistics")}
        if len(digests) != 1 or statuses != {"complete"} or len(work) != 1:
            void.append(f"{row}: digests {len(digests)}, statuses {sorted(statuses)}, "
                        f"work-count sets {len(work)}")
            continue
        for arm in ("flat-count", "reuse"):
            m = census(arms[arm][min(arms[arm])])["mismatches"]
            if m:
                void.append(f"{row}: {arm} has {m} stored rows that differ from the fresh ones")
    voided = {v.split(":")[0] for v in void}

    out = ["## Census (`flat-count` and `reuse` records; identical in every repetition)\n",
           "| row | set | batches | reducer rows | flat reducer hits | map reducer hits | "
           "flat target hits | probes skipped / all terms | flat peak buffer | map peak buffer |",
           "|---|---|---:|---:|---:|---:|---:|---:|---:|---:|"]
    for row in order:
        if row in voided:
            continue
        arms = runs[row]
        f = census(arms["flat-count"][min(arms["flat-count"])])
        m = census(arms["reuse"][min(arms["reuse"])])
        out.append(f"| {row} | {kind(row)} | {f['batches']} | {f['reducers']:,} | "
                   f"{f['reducer_hits']:,} ({pct(f['reducer_hits'], f['reducers'])}) | "
                   f"{m['reducer_hits']:,} ({pct(m['reducer_hits'], m['reducers'])}) | "
                   f"{f['target_hits']:,} / {f['targets']:,} | "
                   f"{f['saved_probes']:,} / {f['terms']:,} ({pct(f['saved_probes'], f['terms'])}) | "
                   f"{f['retained'] / 2**20:.2f} MiB | {m['retained'] / 2**20:.2f} MiB |")

    out += ["\n## Timed arms (medians over repetitions; ratios paired per repetition vs `off`, "
            "95% bootstrap; unpinned laptop)\n",
            "| row | set | n | call ms (off) | symbolic share (off) | symbolic: flat-count ÷ off | "
            "symbolic: flat ÷ off | symbolic: reuse ÷ off | call: flat ÷ off | call: reuse ÷ off |",
            "|---|---|---:|---:|---:|---:|---:|---:|---:|---:|"]
    verdict = {}
    for row in order:
        if row in voided:
            continue
        arms = runs[row]
        med = lambda arm, f: statistics.median(f(r) for r in arms[arm].values())  # noqa: E731
        call = med("off", lambda r: r["call_ns"]) / 1e6
        sym = med("off", lambda r: r["statistics"]["symbolic_ns"]) / 1e6
        cis = {(arm, m): ratio(arms, arm, m, f"{row} {arm} {m}")
               for arm in ("flat-count", "flat", "reuse") for m in ("symbolic_ns", "call_ns")}
        verdict[row] = cis[("flat", "call_ns")]
        out.append(f"| {row} | {kind(row)} | {len(arms['off'])} | {call:,.1f} | {pct(sym, call)} | "
                   f"{fmt(cis[('flat-count', 'symbolic_ns')])} | {fmt(cis[('flat', 'symbolic_ns')])} | "
                   f"{fmt(cis[('reuse', 'symbolic_ns')])} | {fmt(cis[('flat', 'call_ns')])} | "
                   f"{fmt(cis[('reuse', 'call_ns')])} |")

    dev = {r: ci for r, ci in verdict.items() if kind(r) == "development"}
    held = {r: ci for r, ci in verdict.items() if r in HELD_OUT and r != ADVERSE}
    if not dev:
        decision = "void: no development row survived validation"
    elif not any(ci.hi < 1.0 for ci in dev.values()):
        decision = "**reject**: no development row's solve wall improves (every upper bound ≥ 1.0)"
    elif (any(ci.hi < 0.98 for ci in dev.values())
          and (ADVERSE not in verdict or verdict[ADVERSE].lo <= 1.02)
          and not any(ci.lo > 1.02 for ci in held.values())):
        decision = "**bench-host candidate**: confirm pinned on the bench host, with peak RSS"
    else:
        decision = "**defer**: some development row improves, but not past the candidate rules"
    if void:
        decision += "\n\nVoided rows: " + "; ".join(void)
    out += ["\n## Decision (rules in this script's docstring)\n", decision]
    print("\n".join(out))


if __name__ == "__main__":
    main(sys.argv[1])
