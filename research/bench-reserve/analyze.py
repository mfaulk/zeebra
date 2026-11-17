import json, statistics as st, sys
from collections import defaultdict

rows = [json.loads(l) for l in open(sys.argv[1])]
by = defaultdict(list)
for r in rows:
    by[(r["arm"], r["subject"])].append(r)
arms = [a for a in ["A1", "B", "D", "C", "A2"] if any(k[0] == a for k in by)]
subjects = ["mq10-1w", "mq10-16w", "eco12-16w"]
basis = {}


print("| subject | arm | n | median wall ms | min–max | vs A1 | spread % | load1 | compilers |")
print("|---|---|---:|---:|---|---:|---:|---:|---:|")
for s in subjects:
    ref = st.median(r["wall_ms"] for r in by[("A1", s)]) if by[("A1", s)] else None
    for a in arms:
        rs = by[(a, s)]
        if not rs:
            continue
        w = [r["wall_ms"] for r in rs]
        med = st.median(w)
        bad = [r for r in rs if r["status"] != "complete"]
        basis.setdefault(s, set()).update(r["basis"] for r in rs if r["basis"])
        print(f"| {s} | {a} | {len(w)}{' BAD' if bad else ''} | {med:.1f} | {min(w):.1f}–{max(w):.1f} | "
              f"{med / ref:.3f}x | {100 * (max(w) - min(w)) / med:.1f} | "
              f"{st.median(r['before']['load1'] for r in rs if r['before']):.1f} | "
              f"{max(r['before']['compilers'] for r in rs if r['before'])} |")
print()
for s, b in basis.items():
    print(f"{s}: {len(b)} distinct basis digest(s)")

if len(sys.argv) > 2:
    pairs = defaultdict(list)
    for line in open(sys.argv[2]):
        r = json.loads(line)
        pairs[(r["subject"], r["arm"])].append(r)
    print()
    print("| subject | box | pairs | median wall ms | A/A ratio median | min | max |")
    print("|---|---|---:|---:|---:|---:|---:|")
    for (s, arm), v in pairs.items():
        rat = [x["b"] / x["a"] for x in v]
        w = [x["a"] for x in v] + [x["b"] for x in v]
        print(f"| {s} | {arm} | {len(v)} | {st.median(w):.1f} | {st.median(rat):.4f} | {min(rat):.4f} | {max(rat):.4f} |")
