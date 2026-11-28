#!/usr/bin/env python3
"""Tables for #1197 from the census reports in runs.jsonl.gz (one `reuse_census --census` report
per line).

Definitions, fixed before the runs were read:

- An *episode* is a stored entry going from valid to stale: a lead that joined the basis after the
  entry was built divides one of its irreducible tail terms. It ends in a *stale hit* (the key is
  built again: one lazy update) or at the end of the run (never reused: a lazy store pays nothing).
- *Eager (lower)* is the episode count: an eager store updates each episode at least once.
  *Eager (rounds)* counts (entry, round) pairs in which a new lead hits the tail as last built.
- *Lazy + flagged* adds the valid hits on an entry keeping a signature-blocked tail term: M5GB's
  case 2, an update a lazy M5GB store also makes once the served row's signature passes the
  blocking pivot's, as every later batch's does on these rows.
- *Generation-flagged* is the exact hits M4GB's generation test (basis grown since the entry was
  built) would send to an update. The ledger does not record it per hit, so it is bracketed: at
  least the hits in batches some new lead preceded (each was built before those leads), at most
  that plus the hits from more than one batch back.
- *Reused* is stale hits over episodes. The issue's stop rule is "fewer than a few percent";
  3% is used here.
"""

import gzip
import json
import sys


def pct(a, b):
    return f"{100.0 * a / b:.1f}%" if b else "n/a"


def shape(r):
    return f"({r['variables']}, {r['equations']})"


def main(path):
    rows = [json.loads(line) for line in gzip.open(path, "rt") if line.strip()]
    rows.sort(key=lambda r: (r["variables"], r["equations"], r["row"], r["engine"]))
    out = []
    out.append("## Eager against lazy updates\n")
    out.append(
        "| Row | Engine | Batches | New leads | Stored | Exact hits | Valid hits | Episodes "
        "| Eager (lower) | Eager (rounds) | Lazy | Lazy / eager | Lazy + flagged | Reused | Unreused |"
    )
    out.append("|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    for r in rows:
        s = r["reuse"]["summary"]
        t = s["store"]
        out.append(
            f"| {r['row']} | {r['engine']} | {s['batches']} | {t['new_elements']} | {t['stored']} "
            f"| {s['exact_hits']} | {t['valid_hits']} | {t['invalidations']} | {t['invalidations']} "
            f"| {t['eager_updates']} | {t['stale_hits']} "
            f"| {t['stale_hits'] / max(t['eager_updates'], 1):.2f}–{t['stale_hits'] / max(t['invalidations'], 1):.2f} "
            f"| {t['stale_hits'] + t['flagged_hits']} "
            f"| {pct(t['stale_hits'], t['invalidations'])} | {t['stale_unreused']} |"
        )
    out.append("\n## Generation test\n")
    out.append("| Row | Engine | Exact hits | One batch back | Generation-flagged | Stale hits |")
    out.append("|---|---|---:|---:|---:|---:|")
    for r in rows:
        s = r["reuse"]["summary"]
        t = s["store"]
        low = sum(b["exact_hits"] for b in r["reuse"]["batches"] if b["new_elements"] > 0)
        far = s["exact_hits"] - s["reuse_distance"][0]
        high = min(s["exact_hits"], low + far)
        flagged = f"{low}" if low == high else f"{low}–{high}"
        out.append(
            f"| {r['row']} | {r['engine']} | {s['exact_hits']} "
            f"| {s['reuse_distance'][0]} ({pct(s['reuse_distance'][0], s['exact_hits'])}) "
            f"| {flagged} | {t['stale_hits']} |"
        )
    out.append("\n## Per new lead, distance, and update work in products\n")
    out.append(
        "| Row | Engine | Stale per new lead | Eager rounds per new lead | Stale share of hits "
        "| Reuse 0 / 1 / 2 / 3–4 / 5–8 / 9+ rounds after | Stale-hit tail products | All-hit tail products "
        "| Elimination products | Blocked entries | Blocked terms |"
    )
    out.append("|---|---|---:|---:|---:|---|---:|---:|---:|---:|---:|")
    for r in rows:
        s = r["reuse"]["summary"]
        t = s["store"]
        p = s["plain"]
        elim = p["primary_products"] + p["secondary_products"] + p["discovered_products"]
        dist = " / ".join(str(d) for d in t["since_invalidation"])
        out.append(
            f"| {r['row']} | {r['engine']} | {t['invalidations'] / max(t['new_elements'], 1):.2f} "
            f"| {t['eager_updates'] / max(t['new_elements'], 1):.2f} "
            f"| {pct(t['stale_hits'], s['exact_hits'])} | {dist} | {t['stale_tail_products']} "
            f"| {s['tail_products_hits']} ({pct(t['stale_tail_products'], s['tail_products_hits'])} stale) "
            f"| {elim} | {t['blocked_entries']} ({pct(t['blocked_entries'], t['stored'])}) "
            f"| {t['blocked_terms']} |"
        )
    out.append("\n## Checks\n")
    out.append("| Row | Engine | Status | Basis digest | Residual mismatches | Live mismatches | Abandoned batches | Born stale | Episodes = stale hits + unreused |")
    out.append("|---|---|---|---|---:|---:|---:|---:|---|")
    # distinct_keys is the store's size in entries.
    for r in rows:
        s = r["reuse"]["summary"]
        t = s["store"]
        balanced = t["invalidations"] == t["stale_hits"] + t["stale_unreused"]
        out.append(
            f"| {r['row']} | {r['engine']} | {r['status']} | `{(r['basis_sha256'] or '')[:12]}` "
            f"| {s['residual_mismatches']} | {s['live_mismatches']} | {s['abandoned_batches']} "
            f"| {t['born_stale']} | {'yes' if balanced else 'NO'} |"
        )
    out.append("\n## Per batch\n")
    for r in rows:
        out.append(f"\n### {r['row']} / {r['engine']}\n")
        out.append("| Batch | Reducers | Exact hits | New leads | Made stale | Eager updates | Stale hits | Stale-hit tail products |")
        out.append("|---:|---:|---:|---:|---:|---:|---:|---:|")
        for b in r["reuse"]["batches"]:
            out.append(
                f"| {b['batch']} | {b['reducers']} | {b['exact_hits']} | {b['new_elements']} "
                f"| {b['invalidated']} | {b['eager_updates']} | {b['stale_hits']} | {b['stale_tail_products']} |"
            )
    print("\n".join(out))


if __name__ == "__main__":
    main(sys.argv[1])
