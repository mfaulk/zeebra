import math
import unittest

from estimate import geometry, ntt_domain, normalized_gap, sensitivity


class EstimateTests(unittest.TestCase):
    # A monic power-of-two subtree needs twice its span in a padded product domain.
    def test_build_padding_differs_from_combine(self):
        self.assertEqual(ntt_domain(9, 9), 32)
        self.assertEqual(ntt_domain(8, 9), 16)

    # Odd nodes are carried without multiplying and every internal pair adds three products.
    def test_odd_carry_and_product_counts(self):
        for n in [1, 3, 8, 13, 13123]:
            result = geometry(n, 0, 28)
            self.assertEqual(result['build_calls'], n - 1)
            self.assertEqual(result['combine_calls'], 2 * (n - 1))
        self.assertEqual(geometry(3, 0, 28)['max_build_domain'], 4)

    # The coalesced model matches literal left-to-right pairing for irregular leaf counts.
    def test_geometry_matches_explicit_tree(self):
        for n in [*range(1, 130), 13123]:
            spans = [1] * n
            expected = dict(build_calls=0, combine_calls=0, eligible_build=0,
                            eligible_combine=0, max_build_domain=0, max_combine_domain=0)
            while len(spans) > 1:
                above = []
                for index in range(0, len(spans), 2):
                    if index + 1 == len(spans):
                        above.append(spans[index])
                        continue
                    a, b = spans[index:index + 2]
                    above.append(a + b)
                    for kind, degree, count in [('build', a + b, 1),
                                                ('combine', a + b - 1, 2)]:
                        domain = 2**math.ceil(math.log2(degree + 1))
                        expected[kind + '_calls'] += count
                        expected['max_' + kind + '_domain'] = max(
                            expected['max_' + kind + '_domain'], domain)
                        if degree >= 8 and domain <= 64:
                            expected['eligible_' + kind] += count
                spans = above
            self.assertEqual(geometry(n, 8, 6), expected)

    # Radix-two unavailability never counts a fallback as a transformed product.
    def test_root_limit_excludes_mersenne(self):
        result = geometry(13123, 4096, 1)
        self.assertEqual(result['eligible_build'], 0)
        self.assertEqual(result['eligible_combine'], 0)

    # Both product degree and available root size gate an eligible transform.
    def test_threshold_and_root_boundary(self):
        self.assertEqual(geometry(8, 8, 4)['eligible_build'], 1)
        self.assertEqual(geometry(8, 8, 4)['eligible_combine'], 0)
        self.assertEqual(geometry(8, 8, 3)['eligible_build'], 0)

    # The raw asymptotic ratio includes the tree's extra logarithm.
    def test_gap_includes_tree_levels(self):
        self.assertAlmostEqual(normalized_gap(2**14, 1.6), 1.7234389, places=5)
        self.assertAlmostEqual(normalized_gap(2**20, 1.6), 10.24)

    # Unknown transform constants remain explicit sensitivity inputs.
    def test_sensitivity_is_not_a_measured_speedup(self):
        gap = normalized_gap(2**14, 1.6)
        self.assertAlmostEqual(sensitivity(2**14, 1.6, 2), gap / 2)
        with self.assertRaises(ValueError):
            sensitivity(2**14, 1.6, 0)

    # Empty trees and invalid transform dimensions fail rather than produce plausible tables.
    def test_refuse_invalid_geometry(self):
        for n in [0, -1]:
            with self.assertRaises(ValueError):
                geometry(n, 512, 28)
        with self.assertRaises(ValueError):
            ntt_domain(0, 1)


if __name__ == '__main__':
    unittest.main()
