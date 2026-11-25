#!/usr/bin/env python3
"""#1035: the sparse side of the predeclared comparison (issuecomment-7171870608), counted.

  python3 research/1035-sparse-toric/counts.py paper  > research/1035-sparse-toric/paper.json
  python3 research/1035-sparse-toric/counts.py survey > research/1035-sparse-toric/survey.json

`paper` counts the Macaulay matrix of Faugère–Spaenlehauer–Svartz (ISSAC 2014, arXiv:1402.7205) in
the polytopal algebra k[P], for every row of their Tables 1–2 and the smaller rows commented out
in their source. Here P = dx·Δ_{nx} × Δ_{ny}, with `dx` 1 (bilinear) or 2 (bidegree (2,1)), and
every generator has sparse degree 1. The control rows count the same shapes with the y-block
scaled to 2·Δ_{ny}. That is the smallest product of simplices that holds a support with an added
y_a·y_b.

- columns(d) = HP_P(d) = ∏ C(n_j + d·b_j, n_j), the Ehrhart polynomial of a product of simplices.
- The witness degree is the first index at which HS_P(t)·(1 − t)^m has a non-positive coefficient.
  That is the paper's Conjecture 1 (sparse semi-regularity) for m > n.
- rank(d) = HP_P(d) − [HS_P(t)(1 − t)^m]_+ at d: the rows an F5-pruned matrix holds.
- full_rows(d) = m·HP_P(d − 1): the unpruned Macaulay matrix.

`survey` screens every base problem of the #1006 panel (its p31 records). For each problem it
searches 2-block splits for the product P = a_X·Δ × a_Y·Δ that holds every generator's support,
with a_B the largest block degree of any term. It compares HP_P(3) with the total-degree count
C(n + 3D, n), where D is the largest generator degree. The search is exhaustive for n ≤ 20. Above
that it is a local search: the best single-variable moves from every one-variable split, repeated
to a fixed point. A problem is eligible if the ratio is at most 0.1.
"""
import json
import math
import pathlib
import sys

import numpy as np

ROOT = pathlib.Path(__file__).resolve().parents[2]

# (nx, ny, m) from Table 1 (dx = 1) and Table 2 (dx = 2), then the commented-out rows of the
# source's full Table 2 that are not already listed.
TABLE1 = [(2, 29, 40), (2, 39, 53), (2, 49, 65), (2, 59, 78), (6, 19, 52), (6, 21, 56), (6, 27, 71)]
TABLE2 = [(1, 34, 36), (1, 39, 41), (1, 44, 46), (2, 15, 25), (2, 17, 27), (2, 19, 30), (3, 10, 24),
          (10, 4, 50), (11, 5, 66), (12, 6, 86)]
TABLE2_SOURCE = [(1, 14, 16), (1, 19, 21), (1, 24, 26), (1, 29, 31), (2, 4, 9), (2, 7, 13),
                 (2, 9, 16), (2, 11, 19), (2, 13, 22), (3, 6, 16), (3, 7, 18), (3, 8, 20),
                 (3, 9, 22), (14, 1, 42), (8, 2, 25), (9, 2, 29), (10, 2, 33), (11, 2, 39),
                 (12, 2, 44), (13, 2, 50), (14, 2, 56), (8, 3, 30), (9, 3, 36), (10, 5, 43)]


def hp(blocks, d):
    """Ehrhart polynomial of ∏ b_j·Δ_{n_j} at d, for blocks [(n_j, b_j)]."""
    return math.prod(math.comb(n + d * b, n) for n, b in blocks)


def witness(blocks, m, limit=200):
    """First d with a non-positive coefficient of HS_P(t)(1-t)^m, and those coefficients."""
    q = []
    for d in range(limit):
        q.append(sum((-1) ** k * math.comb(m, k) * hp(blocks, d - k) for k in range(min(m, d) + 1)))
        if q[-1] <= 0:
            return d, q
    raise ValueError("no witness degree below the limit")


def macaulay(blocks, m):
    d, q = witness(blocks, m)
    columns = hp(blocks, d)
    return dict(witness_degree=d, columns=columns, rank_rows=columns - max(q[d], 0),
                full_rows=m * hp(blocks, d - 1))


def paper():
    rows = []
    for table, dx, shapes in [("1", 1, TABLE1), ("2", 2, TABLE2), ("2-source", 2, TABLE2_SOURCE)]:
        for nx, ny, m in shapes:
            row: dict = dict(table=table, nx=nx, ny=ny, m=m, dx=dx)
            row["sparse"] = macaulay([(nx, dx), (ny, 1)], m)
            row["control"] = macaulay([(nx, dx), (ny, 2)], m)
            rows.append(row)
    return rows


def exponents(record):
    return [np.array([t["exponents"] for t in eq], dtype=np.int64) for eq in record["equations"]]


def survey_problem(record):
    eqs = exponents(record)
    terms = np.vstack(eqs)
    n = terms.shape[1]
    total = int(terms.sum(axis=1).max())
    dense = math.comb(n + 3 * total, n)

    def ratio(mask):
        x = terms[:, mask].sum(axis=1).max()
        y = terms[:, ~mask].sum(axis=1).max()
        nx = int(mask.sum())
        return hp([(nx, int(x)), (n - nx, int(y))], 3) / dense

    best, best_mask = 1.0, None
    if n <= 20:
        method = "exhaustive"
        # Variable 0 stays in X, so each split is visited once.
        for bits in range(1 << (n - 1)):
            mask = np.array([True] + [(bits >> i) & 1 == 1 for i in range(n - 1)])
            if mask.all():
                continue
            r = ratio(mask)
            if r < best:
                best, best_mask = r, mask
    else:
        method = "local search"
        for start in range(n):
            mask = np.zeros(n, dtype=bool)
            mask[start] = True
            current = ratio(mask)
            improved = True
            while improved:
                improved = False
                for i in range(n):
                    trial = mask.copy()
                    trial[i] = not trial[i]
                    if trial.all() or not trial.any():
                        continue
                    r = ratio(trial)
                    if r < current:
                        mask, current, improved = trial, r, True
            if current < best:
                best, best_mask = current, mask
    names = record["variables"]
    split = None if best_mask is None else [
        [v for v, b in zip(names, best_mask) if b], [v for v, b in zip(names, best_mask) if not b]]
    return dict(id=record["id"].split("@")[0], family=record["lineage"]["family_id"], n=n,
                m=len(eqs), max_degree=total, method=method, best_ratio=best, split=split,
                eligible=best <= 0.1)


def survey():
    records = json.loads((ROOT / "research/m34-public-corpus/catalog.json").read_text())
    return [survey_problem(r) for r in records if r["id"].endswith("@p31")]


# Affine solution counts with multiplicity (research/m34-public-corpus/README.md): 2·sites + 1,
# and the -nonzero variants equal their parent. sd-ellipsoid-4 has 4 generators in 10 variables.
VDIM = {"gen-phosphorylation-5": 11, "gen-phosphorylation-6": 13, "gen-phosphorylation-7": 15,
        "gen-phosphorylation-2-nonzero": 5, "gen-phosphorylation-4-nonzero": 9,
        "gen-phosphorylation-6-nonzero": 13}


def square(blocks, m):
    """Lemma 5 for m = n generators of sparse degree 1 that form a regular sequence in k[P]."""
    n = sum(b[0] for b in blocks)
    ell = max(-(-(nj + 1) // bj) for nj, bj in blocks)
    d = n + 2 - ell
    # h*(t) = HS_P(t)(1 − t)^{n+1}; the quotient by n regular elements has HS = h*(t)/(1 − t).
    h = [sum((-1) ** k * math.comb(n + 1, k) * hp(blocks, i - k) for k in range(min(n + 1, i) + 1))
         for i in range(d + 1)]
    columns = hp(blocks, d)
    volume = math.factorial(n) // math.prod(math.factorial(nj) for nj, _ in blocks) * math.prod(
        bj ** nj for nj, bj in blocks)
    return dict(witness_degree=d, columns=columns, rank_rows=columns - sum(h),
                full_rows=m * hp(blocks, d - 1), normalized_volume=volume)


def public():
    """The eligible survey problems, counted under the regularity Lemma 5 needs."""
    records = {r["id"].split("@")[0]: r for r in json.loads(
        (ROOT / "research/m34-public-corpus/catalog.json").read_text())}
    rows = []
    for s in survey():
        if not s["eligible"]:
            continue
        record = records[s["id"]]
        terms = np.vstack(exponents(record))
        mask = np.array([v in s["split"][0] for v in record["variables"]])
        blocks = [(int(mask.sum()), int(terms[:, mask].sum(axis=1).max())),
                  (int((~mask).sum()), int(terms[:, ~mask].sum(axis=1).max()))]
        row = dict(id=s["id"], n=s["n"], m=s["m"], blocks=blocks, vdim=VDIM.get(s["id"]))
        if s["m"] < s["n"]:
            row["sparse"] = None
            row["note"] = "fewer generators than variables: not zero-dimensional, Lemma 5 does not apply"
        else:
            row["sparse"] = square(blocks, s["m"])
        rows.append(row)
    return rows


def main():
    modes = {"paper": paper, "survey": survey, "public": public}
    if len(sys.argv) != 2 or sys.argv[1] not in modes:
        raise SystemExit("usage: counts.py paper|survey|public")
    what = modes[sys.argv[1]]()
    sys.stdout.write("[\n" + ",\n".join(json.dumps(r, separators=(",", ":")) for r in what) + "\n]\n")


if __name__ == "__main__":
    main()
