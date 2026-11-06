#!/usr/bin/env python3
"""Reconstruction check for A3 (#72): is the FreeLunch Griffin instance specified completely?

The deliverable of issue #72 is a shortlist, and its go/no-go is a *reconstruction* check: take one
published parameter set and confirm the specification in hand is complete enough to instantiate the
permutation — field, S-box, linear layer, round constants — without guessing. A value that has to be
guessed means the instance is not reproducible, and the candidate should be recorded as such.

The target is Griffin with (t, alpha) = (12, 3) over p = 28407454060060787, reduced to r rounds, as
used for the experiments in Table 3 of

    A. Bariant, A. Boeuf, A. Lemoine, I. Manterola Ayala, M. Oeygarden, L. Perrin, H. Raddum,
    "The Algebraic FreeLunch: Efficient Groebner Basis Attacks Against Arithmetization-Oriented
    Primitives", CRYPTO 2024.  https://inria.hal.science/hal-04690640

whose appendix "Parameters of Griffin instances" publishes p, alpha, t, the quadratic-function
parameters, the round constants, and CICO solutions for r in {5, 6, 7}. Those solutions are what
makes this check decisive rather than a reading exercise: a reconstruction that is wrong anywhere
will not map the published input to the published output.

Two things are *not* in that appendix and are resolved here:

  * The linear layer M. The paper's Definition 11 says only "for M in F^{t x t} a matrix". The
    construction comes from the Griffin designers' reference implementation, `instantiate_matrix`
    in plain_impls/src/griffin/griffin_params.rs of
    https://extgit.isec.tugraz.at/krypto/zkfriendlyhashzoo — for t divisible by 4, entry (i, j) is
    M4[i mod 4][j mod 4], doubled when i and j fall in the same 4-wide block.

  * The index convention for (delta_i, mu_i). The appendix gives "delta_i = 4(i+1),
    mu_i = 7(i+1)^2, i = 0, ..., r-1", but delta and mu are indexed by *branch*, of which there are
    t, not by round. Both readings are tried; the published solutions select one.

Usage:

    tools/check-griffin-reconstruction.py            # all five published solutions
    tools/check-griffin-reconstruction.py --verbose  # also print each reconstructed output

Exit status is 0 only if exactly one index convention reproduces every published solution.

M25-D extends the tool past the permutation to the *polynomial system*, because a reconstructed
permutation is not a reconstructed attack. Two further modes:

    tools/check-griffin-reconstruction.py --witness-system
        For each of the five published witnesses, exhibit the FreeLunch variable assignment
        (x_0 and the per-round alpha-th roots x_1, ..., x_r) and check that every modelling
        equation p_i = x_i^alpha - L_i(z_{i-1}) and the CICO equation g vanish at it. This is
        the M21-B faithfulness gate for the *system*, at r in {5, 6, 7}, in field arithmetic
        only. It needs no symbolic algebra because Eq. (4) of the FreeLunch paper is an
        identity: G_i agrees with the round function F_i exactly on the locus (3).

    tools/check-griffin-reconstruction.py --build-system R [--singular PATH]
        Build the naive FreeLunch system P_G of Section 3.4 symbolically at R rounds, reduced
        modulo the p_i as Appendix A prescribes, and report: the monomial counts, the leading
        monomials under the FreeLunch order <_G, whether Proposition 6's hypothesis (g contains
        x_0^{d_<=R}) holds, the resulting ideal degree D_I, and a faithfulness check of the
        symbolic g against the numeric permutation at random x_0. With --singular it also
        writes the same system as a Singular script in degrevlex, which is the comparand the
        FreeLunch paper only asserts qualitatively.

Exponent growth makes the symbolic mode a small-R instrument: the reduced state after round i
carries up to 7^i * 3^i monomials, so R = 3 is comfortable in CPython and R = 4 is not.
"""

from __future__ import annotations

import argparse
import sys

# Field and permutation parameters, from the FreeLunch appendix.
P = 28407454060060787  # 0x64ec6dd0392073, 55 bits
T = 12
ALPHA = 3

# 4x4 block of the Griffin linear layer, from the reference implementation.
M4 = [
    [5, 7, 1, 3],
    [4, 6, 1, 1],
    [1, 3, 5, 7],
    [1, 1, 4, 6],
]

# Round constants c0..c6, from the FreeLunch appendix. Footnote: "Our Griffin with r <= 7 rounds
# will use constants (c0, ..., c_{r-2}, c6)", and c6 is zero, matching Definition 11's c(r) = 0.
ROUND_CONSTANTS = [
    (24948861045225956, 21203603017242449, 5137804740880040, 17203989140901077,
     15884693750499599, 202426034695061, 21925627314327927, 14915791625715646,
     2270637844838412, 19287066862534400, 23053628619630528, 20205234482325465),
    (1953994697959081, 13694436956212586, 2244645965787647, 20803493439220167,
     13296675195272853, 18296898451764242, 20376008308269607, 10239947264048958,
     1116873941458788, 19425600591729552, 20854422412323996, 10085561279368253),
    (16905640598099854, 25230133406843513, 8957962046730991, 14294289436907403,
     10949906559535418, 28179662462119909, 20848690834284278, 5962920227944130,
     15129107418293752, 6002695762195648, 6114627516150292, 22521669951514122),
    (13008050022403386, 28091350245684079, 23189230572909585, 8101795236077784,
     3593606052472638, 11330866710107896, 9840541134611106, 13915746912957553,
     19822110644988410, 24750875289653592, 25496607366081073, 2269647499797729),
    (15770582149454036, 4472996328290429, 8197094411507273, 14151116175893923,
     19977244056516294, 22071066831282832, 10912395968228633, 28293903648852908,
     15600461636809584, 16248565278833955, 23850742575902912, 12384888390231181),
    (24731271392756981, 4234794164011219, 5709721189329773, 23115678305163655,
     11185048660199721, 21406367947811616, 14929808901464726, 14209993563715217,
     19373914823111461, 12307896526346864, 16319890415782340, 19440350754040851),
    (0,) * 12,
]

# Published CICO solutions, as (rounds, input, output). Both ends have a zero first coordinate,
# which is the CICO condition being solved for.
SOLUTIONS = [
    (5,
     (0, 3490692521816093, 23601145558450866, 12269607430774150, 9967688977125539,
      6082447726448232, 5654276540748670, 3202643372242143, 14009612926527540,
      18297056060918841, 3219981769736554, 1403954519004962),
     (0, 5621630451433068, 19970363721022544, 26741918912648639, 19340983417234439,
      703450676999922, 28208520610521445, 25436703150515389, 27364572020087999,
      24554342355067488, 12423823785589327, 9583319713824981)),
    (5,
     (0, 20508905520120247, 23936168820965785, 23455122418677455, 17553236564762600,
      3639182016432478, 17868020430519088, 3713757452078792, 5123533774106823,
      15978370877576178, 18526890154199809, 7146019784219766),
     (0, 398957666284762, 14158444455164092, 23271855932022231, 21234778660794826,
      254005063154066, 20580021469733731, 20943402370356289, 5582293336098692,
      4611071270038675, 18302255515509522, 26476200309584297)),
    (6,
     (0, 15940424764849354, 15734551202904841, 2252716448242183, 24464738475171520,
      22965208929786740, 9160692692879124, 10856186368261439, 8227155735266026,
      27520010287112407, 2695459349798501, 26535488466949249),
     (0, 28084819548111304, 27440009447766981, 18719426192325148, 15867588640423583,
      21846560125606713, 6096085299560336, 3230042720230543, 8933226700213982,
      16946922076875842, 4787108825372316, 24658818061833687)),
    (6,
     (0, 13453267118668680, 16821847582014700, 16088365946216368, 5399506335051336,
      27388226484505332, 23347730487451583, 17984517745797377, 8860239602618916,
      21421104166559501, 2200106791585633, 4277034158946419),
     (0, 15056970863769267, 16790578228924700, 8672008243997393, 19887571512638539,
      26391726423500753, 20727079056917053, 20813391870109600, 20843251064205404,
      18441611384455618, 7490737291933204, 20355381094708976)),
    (7,
     (0, 471901030567494, 19368389705049758, 6207658171606065, 13611402711597287,
      12429039749894833, 22884233714242756, 18540641300363820, 25230426657954964,
      17547513396056919, 15871260254068404, 5181585218256522),
     (0, 24311659110177349, 24245222836079936, 1360999973748497, 25535756342488541,
      10834064085568113, 2487598456547217, 22567275155120838, 2042666706826108,
      694695024982032, 10782435475712749, 20264250160050251)),
]

# alpha-th root exponent. Griffin asks for the smallest alpha with gcd(alpha, p - 1) = 1, so the
# inverse exists and x -> x^alpha is a permutation.
ALPHA_INVERSE = pow(ALPHA, -1, P - 1)


def linear_layer() -> list[list[int]]:
    """The t x t Griffin matrix for t divisible by 4."""
    return [
        [
            (M4[i % 4][j % 4] * (2 if i // 4 == j // 4 else 1)) % P
            for j in range(T)
        ]
        for i in range(T)
    ]


M = linear_layer()


def apply_matrix(state: list[int]) -> list[int]:
    return [sum(M[i][j] * state[j] for j in range(T)) % P for i in range(T)]


def sbox(state: list[int], quadratic: dict[int, tuple[int, int]]) -> list[int]:
    """Definition 10: the non-linear layer of Griffin-pi."""
    out = [0] * T
    out[0] = pow(state[0], ALPHA_INVERSE, P)
    out[1] = pow(state[1], ALPHA, P)
    for i in range(2, T):
        previous = 0 if i == 2 else state[i - 1]
        ell = ((i - 1) * out[0] + out[1] + previous) % P
        delta, mu = quadratic[i]
        out[i] = state[i] * (ell * ell + delta * ell + mu) % P
    return out


def permutation(state: list[int], rounds: int, quadratic: dict[int, tuple[int, int]]) -> list[int]:
    """Definition 11: G_pi = F_r o ... o F_1 (M x .), with F_i(.) = c(i) + M x S(.)."""
    constants = [ROUND_CONSTANTS[i] for i in range(rounds - 1)] + [ROUND_CONSTANTS[6]]
    state = apply_matrix(state)
    for constant in constants:
        state = apply_matrix(sbox(state, quadratic))
        state = [(state[i] + constant[i]) % P for i in range(T)]
    return state


# The two readings of "delta_i = 4(i+1), mu_i = 7(i+1)^2".
CONVENTIONS = {
    "branch-indexed: branch i takes (4(i+1), 7(i+1)^2)":
        {i: (4 * (i + 1) % P, 7 * (i + 1) ** 2 % P) for i in range(T)},
    "offset: branch i takes the (i-2)-th pair, (4(i-1), 7(i-1)^2)":
        {i: (4 * (i - 1) % P, 7 * (i - 1) ** 2 % P) for i in range(T)},
}


# ---------------------------------------------------------------------------
# The FreeLunch modelling of Griffin (FreeLunch paper, Section 3.4 and 4.1)
# ---------------------------------------------------------------------------
#
# One variable x_i per round, introduced for the alpha-th root taken on branch 0, plus the free
# input word x_0.  Each round's G_i has degree d_i = 2*alpha + 1 = 7, so d_<=i = 7^i, and the
# FreeLunch order <_G of Proposition 6 has weight vector (1, 1/alpha, 7/alpha, ..., 7^(r-1)/alpha),
# which is scaled here by alpha to stay in the integers.

ROUND_DEGREE = 2 * ALPHA + 1  # d_i, the degree of G_i in (z_{i-1}, x_i)


def winning_convention() -> dict[int, tuple[int, int]]:
    """The one (delta, mu) reading that reproduces all five published solutions."""
    for quadratic in CONVENTIONS.values():
        if all(permutation(list(i), r, quadratic) == list(o) for r, i, o in SOLUTIONS):
            return quadratic
    raise SystemExit("no (delta, mu) convention reproduces the published solutions")


def round_constants(rounds: int) -> list[tuple[int, ...]]:
    return [ROUND_CONSTANTS[i] for i in range(rounds - 1)] + [ROUND_CONSTANTS[6]]


def trace_roots(state, rounds, quadratic):
    """Run the permutation, also returning the FreeLunch variable assignment it induces.

    Returns (output, roots, radicands) where roots[i-1] is the alpha-th root taken on branch 0 in
    round i -- the value of the FreeLunch variable x_i -- and radicands[i-1] is L_i(z_{i-1}), the
    branch-0 value it is a root of.
    """
    state = apply_matrix(state)
    roots, radicands = [], []
    for constant in round_constants(rounds):
        radicands.append(state[0])
        roots.append(pow(state[0], ALPHA_INVERSE, P))
        state = apply_matrix(sbox(state, quadratic))
        state = [(state[i] + constant[i]) % P for i in range(T)]
    return state, roots, radicands


def check_witness_system(verbose: bool) -> int:
    """The M21-B faithfulness gate, at the system level, on all five published witnesses.

    Also recovers the bypass line of the FreeLunch paper's Appendix B, which the paper does not
    publish: the first three alpha-th roots come out as the same three constants at every witness
    and every round count, which is exactly the three-round bypass for t >= 12.
    """
    quadratic = winning_convention()
    print("\nFreeLunch modelling checked at the published witnesses")
    print("  p_i = x_i^alpha - L_i(z_{i-1}) for i = 1..r, and g = [output]_0")
    failures = 0
    traces = []
    for rounds, given_input, given_output in SOLUTIONS:
        out, roots, radicands = trace_roots(list(given_input), rounds, quadratic)
        checks = {
            "permutation reproduces the witness": out == list(given_output),
            "input is CICO-admissible ([input]_0 = 0)": given_input[0] == 0,
            "every p_i vanishes": all(pow(x, ALPHA, P) == L for x, L in zip(roots, radicands)),
            "g vanishes ([output]_0 = 0)": out[0] == 0,
        }
        bad = [name for name, ok in checks.items() if not ok]
        failures += len(bad)
        traces.append((rounds, given_input, roots))
        print(f"  r={rounds} x_0={given_input[1]} -> {'PASS' if not bad else 'FAIL ' + str(bad)}")
        if verbose:
            for i, x in enumerate(roots, start=1):
                print(f"      x_{i} = {x}")

    # Appendix B: for t >= 12 the first three rounds take a constant into x^(1/alpha).
    prefixes = {tuple(roots[:3]) for _, _, roots in traces}
    print(f"\n  rounds bypassed (constant x_i across all five witnesses): "
          f"{'3' if len(prefixes) == 1 else 'NOT CONSTANT'}")
    if len(prefixes) == 1:
        for i, x in enumerate(sorted(prefixes)[0], start=1):
            print(f"    x_{i} = {x}")
    else:
        failures += 1

    # Two witnesses on the same affine line determine it. Parametrise by input word 1.
    (_, w, _), (_, v, _) = traces[0], traces[1]
    denominator = pow((w[1] - v[1]) % P, -1, P)
    a = [((w[j] - v[j]) % P) * denominator % P for j in range(T)]
    b = [(w[j] - a[j] * w[1]) % P for j in range(T)]
    print(f"\n  bypass line recovered from the two r=5 witnesses, z_0(x_0) = a*x_0 + b")
    print(f"    a = {a}")
    print(f"    b = {b}")
    nonzero = [j for j in range(T) if a[j]]
    on_line = []
    for rounds, given_input, _ in traces[2:]:
        params = {((given_input[j] - b[j]) % P) * pow(a[j], -1, P) % P for j in nonzero}
        offline = [j for j in range(T) if not a[j] and given_input[j] != b[j]]
        on_line.append(len(params) == 1 and not offline)
    print(f"    the r=6 and r=7 witnesses lie on the same line: {all(on_line)} {on_line}")
    if not all(on_line):
        failures += 1
    print(f"    zero pattern of a (branches constant in x_0): "
          f"{[j for j in range(T) if not a[j]]}")
    return 1 if failures else 0


# --- sparse multivariate polynomials over F_p, exponent tuples of length n -------------------


def poly_const(c: int, n: int) -> dict:
    c %= P
    return {(0,) * n: c} if c else {}


def poly_var(j: int, n: int) -> dict:
    e = [0] * n
    e[j] = 1
    return {tuple(e): 1}


def poly_add(a: dict, b: dict) -> dict:
    out = dict(a)
    for m, c in b.items():
        v = (out.get(m, 0) + c) % P
        if v:
            out[m] = v
        else:
            out.pop(m, None)
    return out


def poly_scale(a: dict, k: int) -> dict:
    k %= P
    return {} if k == 0 else {m: (c * k) % P for m, c in a.items()}


def poly_mul(a: dict, b: dict) -> dict:
    if len(a) > len(b):
        a, b = b, a
    out: dict = {}
    for ma, ca in a.items():
        for mb, cb in b.items():
            m = tuple(x + y for x, y in zip(ma, mb))
            out[m] = out.get(m, 0) + ca * cb
    return {m: c % P for m, c in out.items() if c % P}


def poly_pow(a: dict, k: int) -> dict:
    out = poly_const(1, len(next(iter(a))) if a else 1)
    for _ in range(k):
        out = poly_mul(out, a)
    return out


def poly_reduce(a: dict, relations: dict, n: int) -> dict:
    """Reduce x_1..x_{n-1} below alpha using x_j^alpha = relations[j].

    One descending pass suffices: relations[j] involves only x_0..x_{j-1}, so substituting for
    x_j can raise exponents only at indices below j, which the pass has not reached yet.
    """
    for j in range(n - 1, 0, -1):
        rel = relations.get(j)
        if rel is None:
            continue
        low: dict = {}
        groups: dict = {}
        for m, c in a.items():
            k = m[j] // ALPHA
            if k == 0:
                low[m] = c
            else:
                rest = list(m)
                rest[j] -= ALPHA * k
                groups.setdefault(k, {})[tuple(rest)] = c
        if not groups:
            continue
        a = low
        for k, part in groups.items():
            a = poly_add(a, poly_mul(part, poly_pow(rel, k)))
    return a


def mat_apply(vec: list[dict], n: int) -> list[dict]:
    out = []
    for i in range(T):
        acc: dict = {}
        for j in range(T):
            acc = poly_add(acc, poly_scale(vec[j], M[i][j]))
        out.append(acc)
    return out


def weight_key(m: tuple, weights: list) -> tuple:
    """Sort key realising <_G: weighted degree first, then lex read from the last variable.

    Definition 2 of the FreeLunch paper breaks ties at the *highest* differing index, with the
    larger exponent winning -- graded lex with the variable order reversed relative to Zeebra's
    `MonomialOrder::GradedLexicographic`.
    """
    return (sum(w * e for w, e in zip(weights, m)), tuple(reversed(m)))


def leading_monomial(f: dict, weights: list) -> tuple:
    return max(f, key=lambda m: weight_key(m, weights))


def bypassed_rounds(rounds: int, line: tuple[list[int], list[int]], quadratic) -> int:
    """How many leading rounds take an x_0-independent value into x^(1/alpha), measured.

    Appendix B's bypass, detected rather than assumed: evaluate the permutation at three points of
    the line and count the leading alpha-th roots that agree.
    """
    a, b = line
    traces = []
    for v in (1, 2, 3):
        state = [(a[j] * v + b[j]) % P for j in range(T)]
        traces.append(trace_roots(state, rounds, quadratic)[1])
    count = 0
    while count < rounds and len({tr[count] for tr in traces}) == 1:
        count += 1
    return count


def build_system(rounds: int, line: tuple[list[int], list[int]]):
    """The FreeLunch system for Griffin at `rounds` rounds over the CICO line z_0(x_0) = a x_0 + b.

    Returns (ps, g, weights, rounds_of, n).  A variable is introduced only for a round whose
    alpha-th root actually depends on x_0; bypassed rounds contribute their known constant root.
    The weight vector is built by Construction 1 -- wt(x) = wt(LM(q))/alpha -- so the monomial
    order is derived from the system rather than quoted, and the polynomials are reduced modulo
    the relations introduced so far, as Appendix A prescribes.
    """
    from fractions import Fraction

    quadratic = winning_convention()
    a, b = line
    skip = bypassed_rounds(rounds, line, quadratic)
    constant_roots = trace_roots([(a[j] + b[j]) % P for j in range(T)], rounds, quadratic)[1][:skip]
    n = 1 + (rounds - skip)
    weights: list = [Fraction(1)]
    slot_of: dict = {}
    rounds_of: dict = {}

    inputs = [poly_add(poly_scale(poly_var(0, n), a[j]), poly_const(b[j], n)) for j in range(T)]
    state = mat_apply(inputs, n)
    relations: dict = {}
    ps = []
    constants = round_constants(rounds)
    for i in range(1, rounds + 1):
        rel = state[0]
        if i <= skip:
            assert len(rel) <= 1 and all(m == (0,) * n for m in rel), (
                f"round {i} was detected as bypassed but its radicand is not constant"
            )
            yzero = poly_const(constant_roots[i - 1], n)
        else:
            slot = len(weights)
            slot_of[i] = slot
            rounds_of[slot] = i
            weights.append(
                Fraction(sum(w * e for w, e in zip(weights, leading_monomial(rel, weights))), ALPHA)
            )
            yzero = poly_var(slot, n)
            ps.append(poly_add(poly_pow(yzero, ALPHA), poly_scale(rel, -1)))
            relations[slot] = rel
        y: list = [None] * T
        y[0] = yzero
        y[1] = poly_reduce(poly_pow(state[1], ALPHA), relations, n)
        for j in range(2, T):
            prev = {} if j == 2 else state[j - 1]
            ell = poly_reduce(
                poly_add(poly_add(poly_scale(y[0], j - 1), y[1]), prev), relations, n
            )
            delta, mu = quadratic[j]
            quad = poly_add(
                poly_add(poly_reduce(poly_mul(ell, ell), relations, n), poly_scale(ell, delta)),
                poly_const(mu, n),
            )
            y[j] = poly_reduce(poly_mul(state[j], quad), relations, n)
        state = mat_apply(y, n)
        c = constants[i - 1]
        state = [
            poly_reduce(poly_add(state[j], poly_const(c[j], n)), relations, n) for j in range(T)
        ]
    return ps, state[0], weights, rounds_of, n


def singular_poly(f: dict, names: list[str]) -> str:
    terms = []
    for m, c in sorted(f.items(), reverse=True):
        factors = [str(c)] + [f"{names[i]}^{e}" for i, e in enumerate(m) if e]
        terms.append("*".join(factors))
    return "+".join(terms) if terms else "0"


def bypass_line() -> tuple[list[int], list[int]]:
    """The affine CICO line through the published witnesses, recovered from two of them."""
    w, v = SOLUTIONS[0][1], SOLUTIONS[1][1]
    inv = pow((w[1] - v[1]) % P, -1, P)
    a = [((w[j] - v[j]) % P) * inv % P for j in range(T)]
    return a, [(w[j] - a[j] * w[1]) % P for j in range(T)]


def report_system(rounds: int, verbose: bool, singular_path: str | None) -> int:
    import random
    import time
    from fractions import Fraction

    quadratic = winning_convention()
    line = bypass_line()
    start = time.perf_counter()
    ps, g, weights, rounds_of, n = build_system(rounds, line)
    build_s = time.perf_counter() - start
    names = [f"x{i}" for i in range(n)]
    scale = 1
    for w in weights:
        scale = scale * w.denominator // __import__("math").gcd(scale, w.denominator)
    scaled = [int(w * scale) for w in weights]

    print(f"\nFreeLunch system for Griffin at r = {rounds} over the recovered bypass line")
    print(f"  rounds bypassed: {rounds - (n - 1)};  variables: {n} "
          f"(x_0 plus one per round in {sorted(rounds_of.values())})")
    print(f"  sysGen (this tool, CPython): {build_s:.2f} s")
    print(f"  weight vector of <_G from Construction 1: {[str(w) for w in weights]}")
    print(f"    cleared of denominators (x{scale}): {scaled}")
    print(f"  tie-break: graded lex with x_0 < x_1 < ... < x_{n - 1} "
          f"(reverse of Zeebra's grlex variable order)")

    ok = True
    exponents = []
    for slot, p in enumerate(ps, start=1):
        lm = leading_monomial(p, weights)
        want = tuple(ALPHA if k == slot else 0 for k in range(n))
        ok &= lm == want
        exponents.append(ALPHA)
        print(f"  p_{slot} (round {rounds_of[slot]}): {len(p):>8} monomials, "
              f"LM = x{slot}^{ALPHA}{'' if lm == want else '  <-- FAIL, got ' + str(lm)}")
    alpha0 = max(m[0] for m in g)
    g_want = (alpha0,) + (0,) * (n - 1)
    prop6 = leading_monomial(g, weights) == g_want and g.get(g_want, 0) != 0
    ok &= prop6
    print(f"  g            : {len(g):>8} monomials, LM = x0^{alpha0}, "
          f"deg_x0 = {alpha0}, total deg = {max(sum(m) for m in g)}")
    print(f"  Proposition 6 hypothesis (LM(g) = x_0^d_<=r, coefficient nonzero): {prop6}")
    print(f"  pairwise-coprime leading monomials (so a Groebner basis by Buchberger's "
          f"first criterion, with no computation): {ok}")
    d_h = ALPHA ** (n - 1)
    print(f"  alpha_0 = {alpha0}   D_H = alpha^{n - 1} = {d_h}   D_I = {alpha0 * d_h}"
          f"   (paper's (6a+3)(a(2a+1))^(r-3) = "
          f"{(6 * ALPHA + 3) * (ALPHA * ROUND_DEGREE) ** (rounds - 3)})")
    print(f"  polyDet object: det(x0^alpha_0 I + sum_i x0^i M_i), a {d_h}x{d_h} matrix over "
          f"F_p[x0] with entries of degree < {alpha0}, output degree {alpha0 * d_h}")

    # Faithfulness against the numeric permutation: the M21-B gate for the symbolic system.
    rng = random.Random(20261106)
    bad = 0
    a, b = line
    for _ in range(8):
        v = rng.randrange(1, P)
        state = [(a[j] * v + b[j]) % P for j in range(T)]
        out, roots, _ = trace_roots(state, rounds, quadratic)
        point = [v] + [roots[rounds_of[s] - 1] for s in range(1, n)]
        for slot, p in enumerate(ps, start=1):
            if poly_eval(p, point) != 0:
                bad += 1
                print(f"  FAIL p_{slot} does not vanish at x_0 = {v}")
        if poly_eval(g, point) != out[0] % P:
            bad += 1
            print(f"  FAIL g != [output]_0 at x_0 = {v}")
    print(f"  faithfulness against the permutation oracle, 8 random x_0 on the line: "
          f"{'PASS' if not bad else 'FAIL'}")

    # The published witnesses are roots of this very system, when the round count matches.
    for wrounds, winput, _ in SOLUTIONS:
        if wrounds != rounds:
            continue
        _, roots, _ = trace_roots(list(winput), rounds, quadratic)
        point = [winput[1]] + [roots[rounds_of[s] - 1] for s in range(1, n)]
        vanishes = all(poly_eval(p, point) == 0 for p in ps) and poly_eval(g, point) == 0
        bad += not vanishes
        print(f"  published witness x_0 = {winput[1]}: whole system vanishes = {vanishes}")

    if singular_path:
        write_singular(ps, g, names, singular_path)
        print(f"  degrevlex comparand written to {singular_path}")
    _ = Fraction, verbose
    return 0 if (ok and not bad) else 1


def poly_eval(f: dict, point: list[int]) -> int:
    total = 0
    for m, c in f.items():
        term = c
        for x, e in zip(point, m):
            if e:
                term = term * pow(x, e, P) % P
        total = (total + term) % P
    return total % P


# Singular's prime fields stop below 2^31, so the degrevlex comparand runs over Zeebra's own
# 31-bit prime.  grevlex F4's degree of regularity and matrix dimensions are set by the monomial
# support, which reduction mod q preserves; only the coefficients change.  Labelled a surrogate.
SURROGATE_PRIME = 2147483647


def write_singular(ps: list[dict], g: dict, names: list[str], path: str) -> None:
    def reduce_mod_q(f: dict) -> dict:
        return {m: c % SURROGATE_PRIME for m, c in f.items() if c % SURROGATE_PRIME}

    lines = [
        'system("--ticks-per-sec", 1000);',
        f"ring R = {SURROGATE_PRIME}, ({','.join(names)}), dp;",
        "option(redSB);",
    ]
    polys = [singular_poly(reduce_mod_q(f), names) for f in (*ps, g)]
    lines.append("ideal I = " + ",\n  ".join(polys) + ";")
    lines += [
        "int t0 = timer;",
        "ideal G = groebner(I);",
        'print("elapsed_ms: " + string(timer - t0));',
        'print("basis_size: " + string(size(G)));',
        'print("vdim: " + string(vdim(G)));',
        'print("max_deg: " + string(deg(G[size(G)])));',
        "exit;",
    ]
    with open(path, "w", encoding="utf-8") as handle:
        handle.write("\n".join(lines) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--verbose", action="store_true", help="print each reconstructed output")
    parser.add_argument(
        "--witness-system",
        action="store_true",
        help="check the FreeLunch modelling equations at the five published witnesses",
    )
    parser.add_argument(
        "--build-system",
        type=int,
        metavar="R",
        help="build the naive FreeLunch system symbolically at R rounds and report its structure",
    )
    parser.add_argument(
        "--singular",
        metavar="PATH",
        help="with --build-system, write the same system as a Singular degrevlex script",
    )
    args = parser.parse_args()

    # Griffin requires delta_i^2 - 4 mu_i to be a quadratic non-residue. For the published formula
    # that difference is -12(i+1)^2, so the condition reduces to -12 being a non-residue.
    non_residue = pow(-12 % P, (P - 1) // 2, P) == P - 1
    print(f"p = {P} ({P.bit_length()} bits), t = {T}, alpha = {ALPHA}")
    print(f"-12 is a quadratic non-residue mod p: {non_residue}")
    if not non_residue:
        print("FAIL: the published (delta, mu) formula does not satisfy Griffin's requirement")
        return 1

    agreeing = []
    for name, quadratic in CONVENTIONS.items():
        matched = 0
        for rounds, given_input, given_output in SOLUTIONS:
            computed = permutation(list(given_input), rounds, quadratic)
            ok = computed == list(given_output)
            matched += ok
            if args.verbose:
                print(f"  [{name}] r={rounds} match={ok} first coordinate={computed[0]}")
        print(f"{matched}/{len(SOLUTIONS)} published solutions reproduced — {name}")
        if matched == len(SOLUTIONS):
            agreeing.append(name)

    if len(agreeing) != 1:
        print("\nFAIL: expected exactly one reading to reproduce every published solution, "
              f"got {len(agreeing)}")
        return 1
    print(f"\nPASS: the instance reconstructs under exactly one reading — {agreeing[0]}")

    status = 0
    if args.witness_system:
        status |= check_witness_system(args.verbose)
    if args.build_system is not None:
        status |= report_system(args.build_system, args.verbose, args.singular)
    return status


if __name__ == "__main__":
    sys.exit(main())
