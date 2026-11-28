"""Monomial pairs whose MathicGB hash collides, on this host's libc (#1165).

MathicGB's monomial hash (`MonoMonoid.hpp`, `computeHash`) is the dot product of the exponent
vector with coefficients drawn by `srand(0); rand()` once per variable, truncated to the 32-bit
exponent type. It is not injective, and the coefficients depend on the C library, so a colliding
pair found here is valid for binaries run on the same platform only.

    python3 tools/external/m5gb-paper/hash_collision.py --n 5 --degree 24 [--limit 5]
"""

import argparse
import ctypes
import ctypes.util
import itertools
import json
import sys


def hash_coefficients(n):
    libc = ctypes.CDLL(ctypes.util.find_library("c"))
    libc.rand.restype = ctypes.c_int
    libc.srand(0)
    return [libc.rand() & 0xFFFFFFFF for _ in range(n)]


def mathic_hash(exponents, coefficients):
    return sum(e * c for e, c in zip(exponents, coefficients)) & 0xFFFFFFFF


def monomials(n, degree):
    for d in range(degree + 1):
        for bars in itertools.combinations(range(d + n - 1), n - 1):
            prev, exps = -1, []
            for b in bars:
                exps.append(b - prev - 1)
                prev = b
            exps.append(d + n - 2 - prev)
            yield tuple(exps)


def collisions(n, degree, limit):
    coefficients = hash_coefficients(n)
    seen = {}
    found = []
    for e in monomials(n, degree):
        h = mathic_hash(e, coefficients)
        if h in seen:
            found.append({"a": list(seen[h]), "b": list(e), "hash": h})
            if len(found) >= limit:
                break
        else:
            seen[h] = e
    return coefficients, found


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--degree", type=int, required=True)
    parser.add_argument("--limit", type=int, default=5)
    args = parser.parse_args()
    coefficients, found = collisions(args.n, args.degree, args.limit)
    json.dump(
        {"n": args.n, "degree": args.degree, "coefficients": coefficients, "pairs": found},
        sys.stdout,
    )
    print()


if __name__ == "__main__":
    main()
