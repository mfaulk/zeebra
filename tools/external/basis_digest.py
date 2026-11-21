#!/usr/bin/env python3
"""`m33-basis-v1`, the one basis digest every M33 solver is compared by (plan §11.3).

Each element is made monic and encoded as its terms in ascending exponent-tuple order, each term
its exponents as unsigned LEB128 then its coefficient in decimal and `;`. The encoded elements are
sorted as bytes, each prefixed by its u32 length, and hashed after a `m33-basis-v1 p n` header line.
The encoding is compact because hashing dominates its cost: Eco-12's basis has 400,000 terms.
`examples/support/basis_digest.rs` computes the same digest inside Zeebra without rendering the
basis, so a solver's timed region carries only the hash.

    basis_digest.py --modulus P --variables x1,x2 BASIS.txt   # one polynomial per line
"""
import argparse
import hashlib
import re
import struct
import sys

FORMAT = 'm33-basis-v1'


def canonical_polynomial(text, modulus, variables):
    """`text` as a monic tuple of `(exponents, coefficient)`, ascending by exponents."""
    terms = {}
    for term in ''.join(text.split()).replace('-', '+-').split('+'):
        if not term:
            continue
        coefficient = -1 if term.startswith('-') else 1
        exponents = [0] * len(variables)
        for factor in term.lstrip('-').split('*'):
            match = re.fullmatch(r'([A-Za-z][A-Za-z0-9_]*|[0-9]+)(?:\^([0-9]+))?', factor)
            if not match:
                raise ValueError('invalid polynomial factor: ' + factor)
            base, power = match[1], int(match[2] or 1)
            if base.isdigit():
                coefficient = coefficient * pow(int(base), power, modulus) % modulus
            elif base in variables:
                exponents[variables.index(base)] += power
            else:
                raise ValueError('unknown polynomial variable: ' + base)
        key = tuple(exponents)
        terms[key] = (terms.get(key, 0) + coefficient) % modulus
    terms = {m: c for m, c in terms.items() if c}
    if not terms:
        return ()
    leading = max(terms, key=lambda m: (sum(m), tuple(-e for e in reversed(m))))
    scale = pow(terms[leading], -1, modulus)
    return tuple(sorted((m, c * scale % modulus) for m, c in terms.items()))


def leb128(e):
    out = bytearray()
    while e >= 0x80:
        out.append(e & 0x7f | 0x80)
        e >>= 7
    out.append(e)
    return bytes(out)


def digest_canonical(polynomials, modulus, nvars):
    """The digest of already-canonical elements; zero elements are dropped."""
    elements = sorted(b''.join(b''.join(map(leb128, m)) + f'{c};'.encode() for m, c in p)
                      for p in polynomials if p)
    data = f'{FORMAT} {modulus} {nvars}\n'.encode() + b''.join(struct.pack('<I', len(e)) + e for e in elements)
    return hashlib.sha256(data).hexdigest()


def basis_digest(texts, modulus, variables):
    """The digest of a basis given as polynomial strings over `variables`."""
    return digest_canonical([canonical_polynomial(t, modulus, variables) for t in texts], modulus, len(variables))


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--modulus', type=int, required=True)
    p.add_argument('--variables', required=True, help='comma-separated, in the solver\'s order')
    p.add_argument('basis', nargs='?', type=argparse.FileType(), default=sys.stdin)
    args = p.parse_args()
    texts = [line.strip().rstrip(',') for line in args.basis if line.strip()]
    print(basis_digest(texts, args.modulus, args.variables.split(',')))


if __name__ == '__main__':
    main()
