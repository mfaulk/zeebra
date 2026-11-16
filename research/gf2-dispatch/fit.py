import itertools
import math
import sys

sys.path.insert(0, sys.argv[1])
from analyze import load, score  # noqa: E402

old = load(sys.argv[2])  # #777's table
new = load(sys.argv[3])  # #794 sweep


def excess(rows, rule):
    total, oracle, _, wrong = score(rows, rule)
    return total / oracle - 1, len(wrong), total - oracle


def report(name, rule):
    o = excess(old, rule)
    n = excess(new, rule)
    print(f"{name:60} old {100*o[0]:6.2f}% ({o[1]:2} wrong, {o[2]:7.0f}us)  new {100*n[0]:6.2f}% ({n[1]:2} wrong, {n[2]:9.0f}us)")


def shipped(r):
    return r["cols"] >= 128 and r["pair"] >= 16 and r["ppm"] >= 18000


report("shipped", shipped)


def r_or_nnz(c, p, d, z):
    return lambda r: r["cols"] >= c and r["pair"] >= p and (r["ppm"] >= d or r["nnz"] >= z)


best = []
for c, p, d, z in itertools.product((64, 96, 128, 160, 192), (8, 16, 32), (18000, 25000, 40000, 60000, 10**9),
                                    (2000, 4000, 8000, 16000, 32000, 10**12)):
    rule = r_or_nnz(c, p, d, z)
    best.append((excess(old, rule)[0] + excess(new, rule)[0], (c, p, d, z)))
for e, args in sorted(best)[:6]:
    report(f"cols>={args[0]} pair>={args[1]} (ppm>={args[2]} or nnz>={args[3]})", r_or_nnz(*args))


# Work model: generic ~ nonzeros * mean row length (merge cost times fill proxy);
# packed ~ pair rows * words * (reducer groups + pair rows / k).
def k_of(p):
    return 4 if p < 128 else 6 if p < 1024 else 8


def model(alpha, c, p):
    def rule(r):
        if r["cols"] < c or r["pair"] < p:
            return False
        words = math.ceil(r["cols"] / 64)
        packed = r["pair"] * words * (r["red"] / 8 + r["pair"] / k_of(r["pair"]) + 4)
        generic = r["nnz"] * (r["nnz"] / r["rows"])
        return generic >= alpha * packed
    return rule


best = []
for a, c, p in itertools.product((0.25, 0.5, 1, 2, 4, 8, 16), (64, 96, 128), (8, 16, 32)):
    rule = model(a, c, p)
    best.append((excess(old, rule)[0] + excess(new, rule)[0], (a, c, p)))
for e, args in sorted(best)[:6]:
    report(f"model alpha={args[0]} cols>={args[1]} pair>={args[2]}", model(*args))

for z in (1000, 2000, 4000):
    for floor in (0, 7000):
        report(f"cols>=128 pair>=16 (ppm>=18000 or (nnz>={z} and ppm>={floor}))",
               lambda r, z=z, floor=floor: r["cols"] >= 128 and r["pair"] >= 16 and (r["ppm"] >= 18000 or (r["nnz"] >= z and r["ppm"] >= floor)))
report("packed everywhere", lambda r: True)
