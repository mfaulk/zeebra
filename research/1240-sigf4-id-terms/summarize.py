"""Summarize the #1240 paired campaign: per row, each arm's median wall and RSS, and pair ratios."""
import gzip
import json
import statistics
import sys
from collections import defaultdict

MIB = 1 << 20
rows = defaultdict(lambda: defaultdict(list))
order = []
for path in sys.argv[1:]:
    for line in (gzip.open(path, "rt") if path.endswith(".gz") else open(path)):
        r = json.loads(line)
        label = r["label"]
        if label not in order:
            order.append(label)
        rows[label][r["arm"]].append(r)

print("| row | reps | basis | terms | term MiB off → on | peak RSS MiB off → on | Δ RSS MiB | wall s off → on | on/off wall (pairs) |")
print("|---|---|---|---|---|---|---|---|---|")
for label in order:
    arms = rows[label]
    off, on = arms["off"], arms["on"]
    statuses = {x["run"]["status"] for x in off + on}
    digests = {x["run"]["basis_m33"] for x in off + on}
    same = "same" if len(digests) == 1 and statuses == {"complete"} else f"DIFF {statuses}"
    s_off, s_on = off[0]["run"]["statistics"], on[0]["run"]["statistics"]
    terms = s_off["signature_basis_terms"]
    tb = (s_off["signature_basis_term_bytes"] / MIB, s_on["signature_basis_term_bytes"] / MIB)
    rss = lambda xs: statistics.median(x["max_rss"] for x in xs) / MIB
    wall = lambda xs: statistics.median(x["run"]["call_ns"] for x in xs) / 1e9
    by_rep = defaultdict(dict)
    for x in off + on:
        by_rep[x["rep"]][x["arm"]] = x["run"]["call_ns"]
    ratios = sorted(v["on"] / v["off"] for v in by_rep.values() if len(v) == 2)
    ratio = statistics.median(ratios)
    spread = f"{ratio:.3f} ({ratios[0]:.3f}–{ratios[-1]:.3f})" if len(ratios) > 1 else f"{ratio:.3f}"
    span = lambda xs: f"{min(x['max_rss'] for x in xs) / MIB:.0f}–{max(x['max_rss'] for x in xs) / MIB:.0f}"
    print(
        f"| {label} | {len(ratios)} | {same} | {terms:,} | {tb[0]:.1f} → {tb[1]:.1f} | "
        f"{rss(off):.1f} [{span(off)}] → {rss(on):.1f} [{span(on)}] | {rss(on) - rss(off):+.1f} | "
        f"{wall(off):.2f} → {wall(on):.2f} | {spread} |"
    )
