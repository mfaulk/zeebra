"""Score dispatch rules on per-batch tables: time lost against the per-batch oracle."""
import math
import sys


def load(path):
    rows = []
    for line in open(path):
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) != 12 or cells[11] not in ("packed", "generic") or not all(c.replace(".", "").isdigit() for c in cells[1:10]):
            continue
        inst, batch, rows_, red, pair, cols, nnz, ppm, g, p, _, _ = cells
        rows.append(dict(inst=inst, batch=int(batch), rows=int(rows_), red=int(red), pair=int(pair),
                         cols=int(cols), nnz=int(nnz), ppm=float(ppm), g=float(g), p=float(p)))
    return rows


def fixed(min_cols=128, min_pair=16, min_ppm=18000):
    return lambda r: r["cols"] >= min_cols and r["pair"] >= min_pair and r["ppm"] >= min_ppm


def score(rows, rule):
    total = oracle = generic = 0.0
    wrong = []
    for r in rows:
        t = r["p"] if rule(r) else r["g"]
        best = min(r["g"], r["p"])
        total += t
        oracle += best
        generic += r["g"]
        if t > best * 1.10 and t - best > 5:
            wrong.append((r["inst"], r["batch"], r["ppm"], r["pair"], r["cols"], round(r["g"] / r["p"], 2), round(t - best, 1)))
    return total, oracle, generic, wrong


if __name__ == "__main__":
    rows = []
    for path in sys.argv[1:]:
        rows += load(path)
    print(f"{len(rows)} batches")
    for ppm in (10000, 12000, 14000, 16000, 18000, 20000, 25000):
        total, oracle, generic, wrong = score(rows, fixed(min_ppm=ppm))
        print(f"ppm>={ppm}: total {total/1e3:.1f} ms, oracle {oracle/1e3:.1f}, generic {generic/1e3:.1f}, "
              f"excess {100*(total/oracle-1):.2f}%, wrong>10%&5us: {len(wrong)}")
    _, _, _, wrong = score(rows, fixed())
    for w in sorted(wrong, key=lambda w: -w[-1])[:25]:
        print("  shipped wrong:", w)
