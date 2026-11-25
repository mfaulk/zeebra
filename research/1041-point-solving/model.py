#!/usr/bin/env python3
"""#1041: counted costs of crossbred and XL + block Wiedemann, as log2 operation counts.

  python3 research/1041-point-solving/model.py check     # the published-figure self-checks
  python3 research/1041-point-solving/model.py > research/1041-point-solving/counted.json

Crossbred is #75's accounting, ported from `src/grobner/research/crossbred.rs` as it stood before
#668 moved it out (commit cd338ac4^). Admissibility is 2024/758 Definition 5 under the
q-semi-regular model. Preprocessing is 2026/360 §4 (T1 matrix generation, T2 block Lanczos
cokernel, T3 new polynomials). Enumeration is 2022/708's m·q^(n−k)·N^ω. `check` asserts the same
published figures the Rust module did, so a run that passes has reproduced Joux–Vitse Table 1 and
2026/360 Tables 1–2 and Example 2.

XL + block Wiedemann is the #76 construction (docs/research/xl-block-wiedemann.md): D = the
model's degree of regularity, N = monomials of degree ≤ D, t = monomials of degree ≤ 2, cost
3·N²·t field operations. Over GF(2) a 64-bit block runs 64 of those at once.

Every count is a prediction under the semi-regular model. None is a measurement.
"""
import json
import math
import sys

OMEGA = 2.8074
WORD = 64


def mul(a, b, up):
    out = [0] * (up + 1)
    for i, x in enumerate(a[: up + 1]):
        if x:
            for j, y in enumerate(b[: up + 1 - i]):
                out[i + j] += x * y
    return out


def inv(s, up):
    out = [0] * (up + 1)
    out[0] = 1
    for i in range(1, up + 1):
        out[i] = -sum(s[j] * out[i - j] for j in range(1, i + 1) if j < len(s))
    return out


def pw(s, e, up):
    r = [1] + [0] * up
    for _ in range(e):
        r = mul(r, s, up)
    return r


def one_minus(power, up):
    s = [1] + [0] * up
    if power <= up:
        s[power] = -1
    return s


def monomial_series(n, q, up):
    """((1 − z^q)/(1 − z))^n: monomials with every exponent below q, by degree."""
    return pw(mul(one_minus(q, up), [1] * (up + 1), up), n, up)


def semiregular_series(n, m, q, up):
    """M_{n,q}(z)·((1 − z²)/(1 − z^{2q}))^m, untruncated."""
    frob = mul(one_minus(2, up), inv(one_minus(2 * q, up), up), up)
    return mul(monomial_series(n, q, up), pw(frob, m, up), up)


def first_non_positive(s):
    return next((i for i, c in enumerate(s) if c <= 0), None)


def monomials_up_to(n, q, d):
    return sum(monomial_series(n, q, d))


def prefix_both(t):
    out = [row[:] for row in t]
    for row in out:
        for j in range(1, len(row)):
            row[j] += row[j - 1]
    for i in range(1, len(out)):
        out[i] = [a + b for a, b in zip(out[i], out[i - 1])]
    return out


class Series:
    """The bivariate series T (polynomials preprocessing produces) and S (their surplus)."""

    def __init__(self, q, n, m, k, up):
        assert q >= 2 and 0 < k < n
        self.q, self.m, self.k = q, m, k
        kept_h = semiregular_series(k, m, q, up)
        whole_h = semiregular_series(n, m, q, up)
        free_m = monomial_series(n - k, q, up)
        t = [[0] * (up + 1) for _ in range(up + 1)]
        for diag, kc in enumerate(kept_h):
            for shift, fc in enumerate(free_m):
                if diag + shift <= up:
                    t[diag + shift][diag] += kc * fc
        for deg, c in enumerate(whole_h):
            t[deg][0] -= c
        s = [row[:] for row in t]
        for deg, c in enumerate(kept_h):
            s[0][deg] -= c
        self.T, self.S = prefix_both(t), prefix_both(s)
        cumulative = list(__import__("itertools").accumulate(kept_h))
        cut = first_non_positive(cumulative)
        self.spec_cum = [0 if cut is not None and i >= cut else c for i, c in enumerate(cumulative)]
        self.dreg = first_non_positive(whole_h)
        self.kdreg = first_non_positive(kept_h)

    def polynomials(self, D, d):
        return self.T[D][d]

    def admissible(self, D, d):
        cond_i = self.S[D][d] >= 0
        cond_ii = self.spec_cum[D] == 0
        below = (self.dreg is None or D < self.dreg) and (self.kdreg is None or d < self.kdreg)
        return cond_i and cond_ii and below


def shape(series, n, D, d):
    k, q = series.k, series.q
    km, fm = monomial_series(k, q, D), monomial_series(n - k, q, D)
    columns = mac_columns = multipliers = 0
    for total in range(D + 1):
        for ink in range(total + 1):
            p = km[ink] * fm[total - ink]
            mac_columns += p
            if ink > d:
                columns += p
            if total + 2 <= D and ink + 1 >= d:
                multipliers += p
    polys = series.polynomials(D, d)
    return dict(columns=columns, macaulay_columns=mac_columns, naive_rows=multipliers * series.m,
                rows=polys + columns, polynomials=polys)


def log2_sum(a, b):
    hi, lo = max(a, b), min(a, b)
    if hi == -math.inf:
        return hi
    return hi + math.log2(1 + 2 ** (lo - hi))


def crossbred_work(q, n, m, k, D, d):
    """2026/360 §4 preprocessing plus 2022/708 enumeration, log2 operations (no hybridation)."""
    series = Series(q, n, m, k, D)
    sh = shape(series, n, D, d)
    mons = monomial_series(n, q, D)
    gen = crit = -math.inf
    for total in range(2, D + 1):
        c = mons[total]
        if c <= 0:
            continue
        bits = math.log2(c)
        if total < D:
            gen = log2_sum(gen, bits)
        if total + 2 <= D:
            crit = log2_sum(crit, OMEGA * bits)
    nb = math.log2(n)
    t1 = log2_sum(3 * nb + gen, crit)
    retained = sh["polynomials"]
    if retained <= 0:
        return None
    rb, rows = math.log2(retained), math.log2(max(sh["rows"], 1))
    wb = math.log2(WORD)
    t2 = rb - wb + 2 * rows + max(2 * nb - wb, 0)
    t3 = rb + 2 * nb + rows
    pre = log2_sum(log2_sum(t1, t2), t3)
    guesses = (n - k) * math.log2(q)
    per = math.log2(m) + OMEGA * math.log2(max(monomials_up_to(k, q, d), 1))
    return dict(k=k, D=D, d=d, log2_preprocessing=pre, log2_guesses=guesses,
                log2_per_guess=per, log2_total=log2_sum(pre, guesses + per))


def best_crossbred(q, n, m, max_degree=12):
    best = None
    for k in range(1, n):
        series = Series(q, n, m, k, max_degree)
        for D in range(2, max_degree + 1):
            for d in range(1, D):
                if not series.admissible(D, d):
                    continue
                w = crossbred_work(q, n, m, k, D, d)
                if w and (best is None or w["log2_total"] < best["log2_total"]):
                    best = w
    return best


def xl_wiedemann(q, n, m, up=40):
    """XL at the model's degree of regularity, solved by block Wiedemann."""
    D = first_non_positive(semiregular_series(n, m, q, up))
    if D is None:
        return None
    N = monomials_up_to(n, q, D)
    t = monomials_up_to(n, q, 2)
    ops = math.log2(3) + 2 * math.log2(N) + math.log2(t) - (math.log2(WORD) if q == 2 else 0)
    return dict(D=D, columns=N, terms=t, log2_total=ops)


def check():
    # Joux–Vitse Table 1: (n, m, k, D) -> columns, polynomials (their R − N).
    for n, m, k, D, cols, polys in [(35, 35, 9, 3, 1056, 204), (35, 70, 14, 3, 2366, 154),
                                    (41, 41, 11, 4, 31075, 3406), (41, 82, 15, 3, 3290, 154),
                                    (62, 148, 23, 4, 277288, 878)]:
        sh = shape(Series(2, n, m, k, D), n, D, 1)
        assert (sh["columns"], sh["polynomials"]) == (cols, polys), (n, m, k, D, sh)
    # 2026/360 Tables 1–2: (m, n, k, D, d) -> r.
    for m, n, k, D, d, r in [(63, 30, 17, 4, 1, 2930), (59, 28, 17, 4, 1, 2591),
                             (49, 23, 18, 4, 1, 1944), (69, 33, 22, 4, 2, 5945),
                             (63, 30, 20, 4, 2, 6429), (43, 20, 14, 3, 2, 238),
                             (47, 22, 14, 3, 2, 294), (79, 38, 27, 4, 3, 7019),
                             (83, 40, 27, 4, 3, 8097), (49, 23, 16, 4, 1, 2568),
                             (49, 23, 15, 4, 1, 3003)]:
        assert Series(2, n, m, k, D).polynomials(D, d) == r, (m, n, k, D, d)
    # 2026/360 Example 2: D = 3 gives 2 polynomials (inadmissible), D = 4 gives 3230.
    ex = Series(2, 21, 45, 13, 4)
    assert ex.polynomials(3, 1) == 2 and ex.polynomials(4, 1) == 3230
    assert ex.S[3][1] < 0 and ex.S[4][1] >= 0  # condition i), as the Rust test asserted
    # 2024/758 Example 2: q = 16, n = m = 8, k = 7: (7, 4) passes i) and fails ii).
    e2 = Series(16, 8, 8, 7, 9)
    assert e2.S[7][4] >= 0 and e2.spec_cum[7] != 0 and not e2.admissible(7, 4)
    # #76's XL column count at the Fukuoka type III n = 38 record: 45,379,620.
    xl = xl_wiedemann(31, 38, 76)
    assert xl is not None and xl["columns"] == 45379620
    print("ok: Joux–Vitse Table 1, 2026/360 Tables 1–2 and Example 2, 2024/758 Example 2, "
          "#76's n = 38 XL columns", file=sys.stderr)


FAMILIES = {
    "A": (31, [(n, 2 * n) for n in (6, 8, 10, 12, 14, 16, 18)]),
    "B": (31, [(3 * m // 2, m) for m in (4, 6, 8, 10)]),
    "C": (2, [(n, 2 * n) for n in (8, 12, 16, 20, 24, 28)]),
    "D": (2, [(3 * m // 2, m) for m in (8, 12, 16, 20)]),
}
# Expected attempts until a square random system has a base-field point: 1 / (1 − e^{−1}).
ATTEMPTS = 1 / (1 - math.exp(-1))


def counted():
    rows = []
    for family, (q, shapes) in FAMILIES.items():
        for n, m in shapes:
            # Underdetermined: fix n − m variables, then a square system, retried.
            nn, extra = (m, math.log2(ATTEMPTS)) if n > m else (n, 0.0)
            cb, xl = best_crossbred(q, nn, m), xl_wiedemann(q, nn, m)
            for w in (cb, xl):
                if w:
                    w["log2_total"] += extra
            rows.append(dict(family=family, q=q, n=n, m=m, solved_variables=nn,
                             log2_attempts=extra, crossbred=cb, xl_wiedemann=xl))
    return rows


if __name__ == "__main__":
    if sys.argv[1:] == ["check"]:
        check()
    else:
        check()
        sys.stdout.write("[\n" + ",\n".join(json.dumps(r) for r in counted()) + "\n]\n")
