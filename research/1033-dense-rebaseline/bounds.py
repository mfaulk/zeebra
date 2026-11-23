#!/usr/bin/env python3
"""#1033 deliverable 4: how many products a delayed-reduction accumulator holds before it must reduce.

    bounds.py            # the markdown table on stdout

An accumulator starts from a reduced residue (< p) and adds lambda products, each at most (p-1)^2,
so an unsigned gamma-bit lane is safe while (p-1) + lambda*(p-1)^2 <= 2^gamma - 1. A double holds
integers exactly up to 2^53 (Dumas, Giorgi & Pernet, TOMS 35(3), 2009), so f64 is safe while
(p-1) + lambda*(p-1)^2 <= 2^53. A centred representation, |r| <= (p-1)/2, quadruples lambda and is
not tabulated. Exact integer arithmetic throughout; nothing here is measured.
"""

FIELDS = [
    ('gf31', 31),
    ('gf32003', 32003),
    ('m31 (2^31 - 1)', 2**31 - 1),
    ('goldilocks (2^64 - 2^32 + 1)', 2**64 - 2**32 + 1),
    ('wide64 (2^64 - 353)', 2**64 - 353),
    ('2^64 - 59', 2**64 - 59),
]
ACCUMULATORS = [('u16', 2**16 - 1), ('u32', 2**32 - 1), ('u64', 2**64 - 1), ('u128', 2**128 - 1),
                ('f64', 2**53)]
STORAGE = [('u8', 2**8), ('u16', 2**16), ('u32', 2**32), ('u64', 2**64)]


def safe_products(p, ceiling):
    """The most products of two reduced residues addable to a reduced residue below `ceiling`."""
    square = (p - 1) ** 2
    room = ceiling - (p - 1)
    return max(room // square, 0)


def cell(p, ceiling):
    lam = safe_products(p, ceiling)
    return '—' if lam == 0 else f'{lam:,}'


def table():
    head = '| Field | p bits | smallest storage | ' + ' | '.join(f'λ, {a}' for a, _ in ACCUMULATORS) + ' |'
    rule = '|' + '---|' * (3 + len(ACCUMULATORS))
    rows = [head, rule]
    for name, p in FIELDS:
        storage = next(s for s, bound in STORAGE if p <= bound)
        cells = [cell(p, c) for _, c in ACCUMULATORS]
        rows.append(f'| {name} | {p.bit_length()} | {storage} | ' + ' | '.join(cells) + ' |')
    return '\n'.join(rows)


def test():
    # 31: (p-1)^2 = 900, u16 room 65535 - 30 = 65505, so 72 products.
    assert safe_products(31, 2**16 - 1) == 72
    # A 64-bit prime does not fit one product into f64 or u64.
    assert safe_products(2**64 - 59, 2**53) == 0
    assert safe_products(2**64 - 59, 2**64 - 1) == 0
    assert safe_products(2**64 - 59, 2**128 - 1) == 1
    # m31: (2^31 - 2)^2 < 2^62, so u64 holds four products and f64 none.
    assert safe_products(2**31 - 1, 2**64 - 1) == 4
    assert safe_products(2**31 - 1, 2**53) == 0


if __name__ == '__main__':
    test()
    print(table())
