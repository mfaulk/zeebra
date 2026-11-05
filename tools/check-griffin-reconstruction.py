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


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--verbose", action="store_true", help="print each reconstructed output")
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

    if len(agreeing) == 1:
        print(f"\nPASS: the instance reconstructs under exactly one reading — {agreeing[0]}")
        return 0
    print("\nFAIL: expected exactly one reading to reproduce every published solution, "
          f"got {len(agreeing)}")
    return 1


if __name__ == "__main__":
    sys.exit(main())
