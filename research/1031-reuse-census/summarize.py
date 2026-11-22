#!/usr/bin/env python3
"""#1031: the census table and the reopen-condition verdicts from runs.jsonl.gz.

Usage: summarize.py runs.jsonl.gz > tables.md

Products are multiply-accumulates past a pivot's lead (the conventional ledger's convention plus
one per application is converted out). Thresholds are #809 §6.1's, with the two it leaves
qualitative fixed here before reading the data: "the zero-row share collapses" is fewer than half
the elimination products on rows that end zero, and "large reducer fractions per batch" is at
least half the products spent in batches whose rows are at least 90% reducer multiples.
"""
import gzip
import json
import sys
from collections import defaultdict

PINNED = ["eco12-wide64", "katsura11-m31", "mq10-32003", "mq10-m31", "mq11-goldilocks"]


def load(path):
    runs = defaultdict(dict)
    with gzip.open(path, "rt") as f:
        for line in f:
            r = json.loads(line)
            runs[(r["row"], r["engine"])]["census" if r.get("census") else "timed"] = r
    return runs


def pct(x):
    return "—" if x is None else f"{100 * x:.1f}%"


def metrics(census, timed):
    """Everything one (row, engine) contributes, or None when either run did not complete."""
    if not census or not timed:
        return None
    if census.get("status") != "complete" or timed.get("status") != "complete":
        return None
    s = census["reuse"]["summary"]
    batches = census["reuse"]["batches"]
    plain = s["plain"]
    forward = plain["primary_products"] + plain["secondary_products"] + plain["discovered_products"]
    backward = 0
    rto = 0
    if census["engine"] == "f4":
        ledger = census["ledger"]
        backward = ledger["backward_products"] - ledger["backward_applications"]
        rto = ledger["forward_reducer_target_operations"] + ledger["backward_reducer_target_operations"]
    elimination = forward + backward
    reducer = plain["primary_products"] + plain["secondary_products"]
    # Avoided by a never-evicting store whose hits are tail-reduced in this batch; abandoned
    # batches count every reducer product as avoidable, so the figure stays an upper bound.
    avoid_hits = s["plain_where_reduced"]["primary_products"] + s["plain_where_reduced"]["secondary_products"] \
        - s["hits_reduced"]["primary_products"] - s["hits_reduced"]["secondary_products"]
    avoid_all = s["plain_where_reduced"]["primary_products"] + s["plain_where_reduced"]["secondary_products"] \
        - s["reduced"]["primary_products"] - s["reduced"]["secondary_products"]
    abandoned = sum(
        b["plain"]["primary_products"] + b["plain"]["secondary_products"]
        for b in batches if b["tail_abandoned"]
    )
    done_hits, done_all = avoid_hits, avoid_all
    avoid_hits += abandoned
    avoid_all += abandoned
    weighted = 0
    for b in batches:
        rows = b["reducers"] + b["targets"]
        p = b["plain"]
        total = p["primary_products"] + p["secondary_products"] + p["discovered_products"]
        if rows and b["reducers"] / rows >= 0.9:
            weighted += total
    st = timed["statistics"]
    wall = st["total_ns"]
    symbolic = st["symbolic_ns"] / wall if wall else None
    reducers = s["reducers"]
    rate = lambda x: x / reducers if reducers else 0.0
    applications = plain["primary_applications"] + plain["secondary_applications"] + plain["discovered_applications"]
    m = {
        "row": census["row"],
        "engine": census["engine"],
        "n": census["variables"],
        "m": census["equations"],
        "batches": s["batches"],
        "reducers": reducers,
        "elimination": elimination,
        "backward": backward,
        "rto_share": rto / max(1, applications),
        "zero_share": plain["zero_row_products"] / elimination if elimination else 0.0,
        "inherited_share": reducer / elimination if elimination else 0.0,
        "secondary_share": plain["secondary_products"] / elimination if elimination else 0.0,
        "repetition": rate(s["exact_hits"]),
        "chain": rate(s["exact_hits"] + s["ancestor_hits"]),
        "lead_only": rate(s["lead_only"]),
        "lead_only_admissible": rate(s["lead_only_admissible"]),
        "symbolic": symbolic,
        "reducer_heavy": weighted / forward if forward else 0.0,
        "avoid_hits": avoid_hits / elimination if elimination else 0.0,
        "avoid_all": avoid_all / elimination if elimination else 0.0,
        "done_hits": done_hits / elimination if elimination else 0.0,
        "done_all": done_all / elimination if elimination else 0.0,
        "upkeep":s["tail_products_hits"] / elimination if elimination else 0.0,
        "net_hits": (avoid_hits - s["tail_products_hits"]) / elimination if elimination else 0.0,
        "abandoned": s["abandoned_batches"],
        "mismatches": s["residual_mismatches"] + s["live_mismatches"],
        "store": s["store_peak_bytes_reduced"],
        "lru2": s["lru"][0]["peak_bytes"],
        "lru4": s["lru"][1]["peak_bytes"],
        "lru2_hits": s["lru"][0]["hits_retained"] / s["exact_hits"] if s["exact_hits"] else 0.0,
        "lru4_hits": s["lru"][1]["hits_retained"] / s["exact_hits"] if s["exact_hits"] else 0.0,
        "rss": timed["peak_rss_bytes"],
        "wall_ms": timed["call_ns"] / 1e6,
        "digest_ok": census["basis_sha256"] == timed["basis_sha256"],
        "digest": timed["basis_sha256"],
    }
    m["a"] = m["rto_share"] >= 0.10
    m["b"] = m["zero_share"] < 0.5 and m["inherited_share"] >= 0.5 and m["repetition"] >= 0.5
    m["c"] = m["symbolic"] is not None and m["symbolic"] >= 0.30 and m["reducer_heavy"] >= 0.5
    m["d"] = m["chain"] >= 0.5
    m["any"] = m["a"] or m["b"] or m["c"] or m["d"]
    return m


def yn(v):
    return "**met**" if v else "not met"


def main(path):
    runs = load(path)
    rows = []
    failed = []
    for (row, engine), pair in sorted(runs.items()):
        m = metrics(pair.get("census"), pair.get("timed"))
        if m is None:
            failed.append((row, engine, (pair.get("timed") or {}).get("status"), (pair.get("census") or {}).get("status")))
        else:
            rows.append(m)
    order = lambda m: (m["row"] not in PINNED, m["row"], m["engine"])
    rows.sort(key=order)
    out = print
    out("## Census table (one worker)\n")
    out("| Row | Engine | n | m | Wall ms | Elim. products | Zero-row | Inherited | Secondary | Repetition | Chain | Symbolic | Reducer-heavy | (a) | (b) | (c) | (d) |")
    out("|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|---|---|")
    for m in rows:
        out(f"| {m['row']} | {m['engine']} | {m['n']} | {m['m']} | {m['wall_ms']:.0f} | {m['elimination']:,} | "
            f"{pct(m['zero_share'])} | {pct(m['inherited_share'])} | {pct(m['secondary_share'])} | {pct(m['repetition'])} | "
            f"{pct(m['chain'])} | {pct(m['symbolic'])} | {pct(m['reducer_heavy'])} | "
            f"{yn(m['a'])} | {yn(m['b'])} | {yn(m['c'])} | {yn(m['d'])} |")
    out("\n## Avoidable products and store size\n")
    out("Avoidable shares are of elimination products. *Bound* credits every reducer product of an")
    out("abandoned batch as avoided; *done* counts only batches whose tail reduction finished.\n")
    out("| Row | Engine | Hits, done | Hits, bound | All, done | All, bound | Upkeep, hits | Net, hits | Abandoned | Store peak MB | LRU 2× MB (hits kept) | LRU 4× MB (hits kept) | Peak RSS MB | Store / RSS |")
    out("|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    mb = lambda b: f"{b / 1e6:.1f}"
    for m in rows:
        out(f"| {m['row']} | {m['engine']} | {pct(m['done_hits'])} | {pct(m['avoid_hits'])} | {pct(m['done_all'])} | "
            f"{pct(m['avoid_all'])} | {pct(m['upkeep'])} | "
            f"{pct(m['net_hits'])} | {m['abandoned']} | {mb(m['store'])} | {mb(m['lru2'])} ({pct(m['lru2_hits'])}) | "
            f"{mb(m['lru4'])} ({pct(m['lru4_hits'])}) | {mb(m['rss'])} | {m['store'] / m['rss']:.2f}× |")
    out("\n## Checks\n")
    bad_digest = [m for m in rows if not m["digest_ok"]]
    out(f"- (row, engine) pairs complete in both modes: {len(rows)}; incomplete: {len(failed)}.")
    out(f"- Census digest differs from the timed run's: {len(bad_digest)}.")
    by_row = defaultdict(set)
    for m in rows:
        by_row[m["row"]].add(m["digest"])
    out(f"- Rows where the two engines' bases differ: {sum(1 for v in by_row.values() if len(v) > 1)}.")
    out(f"- Replay mismatches (residual or engine product count): {sum(m['mismatches'] for m in rows)}.")
    out(f"- Batches whose tail reduction was abandoned: {sum(m['abandoned'] for m in rows)}.")
    for row, engine, t, c in failed:
        out(f"- Incomplete: {row} / {engine}: timed `{t}`, census `{c}`.")
    out("\n## Verdicts\n")
    dense = [m for m in rows if m["row"].startswith("dmq-") and not m["row"].endswith("-u") and m["m"] / m["n"] >= 1.8]
    for engine in ["f4", "sigf4"]:
        sel = [m for m in rows if m["engine"] == engine]
        dsel = [m for m in dense if m["engine"] == engine]
        out(f"- **{engine}**: rows meeting (a) {sum(m['a'] for m in sel)}/{len(sel)}, (b) {sum(m['b'] for m in sel)}/{len(sel)}, "
            f"(c) {sum(m['c'] for m in sel)}/{len(sel)}, (d) {sum(m['d'] for m in sel)}/{len(sel)}. "
            f"Dense planted m/n ≥ 1.8: {len(dsel)} rows, a condition holds on {sum(m['any'] for m in dsel)}, "
            f"hit-avoidable share > 25% on {sum(m['avoid_hits'] > 0.25 for m in dsel)}, "
            f"max hit-avoidable {pct(max((m['avoid_hits'] for m in dsel), default=None))}, "
            f"max all-avoidable {pct(max((m['avoid_all'] for m in dsel), default=None))}; "
            f"store ≤ 2× peak RSS on {sum(m['store'] <= 2 * m['rss'] for m in dsel)}. "
            f"All rows: hit-avoidable bound > 25% on {sum(m['avoid_hits'] > 0.25 for m in sel)}, "
            f"all-avoidable bound > 25% on {sum(m['avoid_all'] > 0.25 for m in sel)} "
            f"({', '.join(m['row'] for m in sel if m['avoid_all'] > 0.25) or 'none'}), "
            f"net of upkeep positive on {sum(m['net_hits'] > 0 for m in sel)}.")


if __name__ == "__main__":
    main(sys.argv[1])
