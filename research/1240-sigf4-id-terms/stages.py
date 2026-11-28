"""#1240: median stage clocks per row and arm (ms), with the symbolic on/off ratio."""
import gzip
import json
import statistics
import sys
from collections import defaultdict

KEYS = ["symbolic_ns", "elimination_ns", "bookkeeping_ns", "element_hashing_ns", "interreduction_ns"]
data = defaultdict(lambda: defaultdict(lambda: defaultdict(list)))
order = []
for path in sys.argv[1:]:
    for line in (gzip.open(path, "rt") if path.endswith(".gz") else open(path)):
        r = json.loads(line)
        if r["label"] not in order:
            order.append(r["label"])
        s = r["run"]["statistics"]
        for k in KEYS:
            data[r["label"]][r["arm"]][k].append(s[k])
print("| row | symbolic ms off → on | on/off | element hashing ms off → on | elimination ms off → on | interreduction ms off → on |")
print("|---|---|---|---|---|---|")
for label in order:
    m = lambda arm, k: statistics.median(data[label][arm][k]) / 1e6
    print(
        f"| {label} | {m('off','symbolic_ns'):.1f} → {m('on','symbolic_ns'):.1f} | "
        f"{m('on','symbolic_ns') / m('off','symbolic_ns'):.3f} | "
        f"{m('off','element_hashing_ns'):.2f} → {m('on','element_hashing_ns'):.2f} | "
        f"{m('off','elimination_ns'):.1f} → {m('on','elimination_ns'):.1f} | "
        f"{m('off','interreduction_ns'):.1f} → {m('on','interreduction_ns'):.1f} |"
    )
