import math


FIELDS = [
    ('Mersenne31', 4, 1, 4096),
    ('KoalaBear', 4, 24, 4096),
    ('Goldilocks', 8, 32, 512),
    ('BN254 Fr', 32, 28, 512),
]
SIZES = [13123, 2**14, 2**20]


def ntt_domain(a_len, b_len):
    if a_len < 1 or b_len < 1:
        raise ValueError('nonempty coefficient arrays required')
    return 1 << (a_len + b_len - 2).bit_length()


def geometry(n, threshold, two_adicity):
    if n < 1 or threshold < 0 or two_adicity < 0:
        raise ValueError('invalid tree/field parameters')
    counts = dict(build_calls=0, combine_calls=0, eligible_build=0,
                  eligible_combine=0, max_build_domain=0, max_combine_domain=0)
    # Equal spans share geometry; coalescing keeps the million-leaf model small.
    spans = {1: n}
    while sum(spans.values()) > 1:
        above = {}
        carry = None
        for span, count in sorted(spans.items(), reverse=True):
            if carry is not None and count:
                a, b = carry, span
                add_pair(counts, a, b, 1, threshold, two_adicity)
                above[a + b] = above.get(a + b, 0) + 1
                count -= 1
                carry = None
            pairs, odd = divmod(count, 2)
            if pairs:
                add_pair(counts, span, span, pairs, threshold, two_adicity)
                above[2 * span] = above.get(2 * span, 0) + pairs
            if odd:
                carry = span
        if carry is not None:
            above[carry] = above.get(carry, 0) + 1
        spans = above
    return counts


def add_pair(counts, a, b, multiplicity, threshold, two_adicity):
    # Build degrees are a,b; each combine product has degrees a-1,b (or a,b-1).
    for kind, a_len, b_len, calls in [('build', a + 1, b + 1, multiplicity),
                                      ('combine', a, b + 1, 2 * multiplicity)]:
        domain = ntt_domain(a_len, b_len)
        counts[kind + '_calls'] += calls
        counts['max_' + kind + '_domain'] = max(counts['max_' + kind + '_domain'], domain)
        if a_len + b_len - 2 >= threshold and domain <= 2**two_adicity:
            counts['eligible_' + kind] += calls


def normalized_gap(n, exponent):
    if n <= 1 or exponent <= 1:
        raise ValueError('nontrivial size and superlinear exponent required')
    return n ** (exponent - 1) / math.log2(n)**2


def sensitivity(n, exponent, constant_ratio):
    if constant_ratio <= 0:
        raise ValueError('positive transform/Karatsuba model constant required')
    return normalized_gap(n, exponent) / constant_ratio


def main():
    print('| n | field | B | largest build/combine domain | eligible build / all | eligible combine / all | one largest build array bytes |')
    print('|---:|---|---:|---:|---:|---:|---:|')
    for n in SIZES:
        for field, width, adicity, threshold in FIELDS:
            row = geometry(n, threshold, adicity)
            print(f'| {n:,} | {field} | {width} | '
                  f'{row["max_build_domain"]:,} / {row["max_combine_domain"]:,} | '
                  f'{row["eligible_build"]:,} / {row["build_calls"]:,} | '
                  f'{row["eligible_combine"]:,} / {row["combine_calls"]:,} | '
                  f'{width * row["max_build_domain"]:,} |')
    print('\n| n | raw ratio e=1.585 | raw ratio e=1.6 | e=1.6, C_N/C_K=2 | e=1.6, C_N/C_K=4 |')
    print('|---:|---:|---:|---:|---:|')
    for n in SIZES:
        print(f'| {n:,} | {normalized_gap(n, math.log2(3)):.3f} | '
              f'{normalized_gap(n, 1.6):.3f} | {sensitivity(n, 1.6, 2):.3f} | '
              f'{sensitivity(n, 1.6, 4):.3f} |')


if __name__ == '__main__':
    main()
