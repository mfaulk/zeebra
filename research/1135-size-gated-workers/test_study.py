#!/usr/bin/env python3
"""Unit tests of #1135's predicate and read on synthetic records and attempts."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import study  # noqa: E402


def term(exponents, coefficient=1):
    return {'exponents': list(exponents), 'coefficient': [str(coefficient)]}


def record(equations, n):
    return {'variables': [f'x{i + 1}' for i in range(n)], 'equations': equations}


class Bezout(unittest.TestCase):
    def test_square_system_is_the_product_of_degrees(self):
        # x^2 - 1, y^3 - 1, xy - 1: n = 2, the two least degrees are 2 and 2.
        r = record([[term((2, 0)), term((0, 0), 5)], [term((0, 3)), term((0, 0), 5)],
                    [term((1, 1)), term((0, 0), 5)]], 2)
        self.assertEqual(study.bezout_bound(r), 4)

    def test_underdetermined_uses_every_generator(self):
        r = record([[term((2, 0, 0))], [term((0, 3, 0))]], 3)
        self.assertEqual(study.bezout_bound(r), 6)

    def test_linear_generators_contribute_one(self):
        r = record([[term((1, 0)), term((0, 1))], [term((2, 0))]], 2)
        self.assertEqual(study.bezout_bound(r), 2)

    def test_unused_declared_variables_do_not_count(self):
        # Three declared variables, two appear: only the two least degrees are taken.
        r = record([[term((2, 0, 0))], [term((0, 2, 0))], [term((1, 1, 0))]], 3)
        self.assertEqual(study.bezout_bound(r), 4)

    def test_a_constant_generator_is_the_unit_ideal(self):
        r = record([[term((0, 0), 3)], [term((2, 0))], [term((0, 2))]], 2)
        self.assertEqual(study.bezout_bound(r), 0)

    def test_zero_generators_are_skipped(self):
        r = record([[], [term((2, 0))], [term((0, 2))]], 2)
        self.assertEqual(study.bezout_bound(r), 4)

    def test_zero_coefficients_do_not_count_toward_degree(self):
        r = record([[term((3, 0), 0), term((1, 0))], [term((0, 2))]], 2)
        self.assertEqual(study.bezout_bound(r), 2)

    def test_gate_threshold_is_inclusive(self):
        self.assertEqual(study.GATE, 2048)
        eleven = record([[term(tuple(2 if j == i else 0 for j in range(11)))] for i in range(11)], 11)
        ten = record([[term(tuple(2 if j == i else 0 for j in range(10)))] for i in range(10)], 10)
        self.assertTrue(study.gate(eleven))
        self.assertFalse(study.gate(ten))


def attempt(row, workers, wall_ms, status='complete', digest='d'):
    return {'row': row, 'workers': workers, 'wall_ms': wall_ms, 'status': status, 'basis_sha256': digest}


class Read(unittest.TestCase):
    def test_medians_take_completions_only(self):
        a = [attempt('r', 1, 10), attempt('r', 1, 30), attempt('r', 1, 20), attempt('r', 1, 99, 'stopped')]
        self.assertEqual(study.medians(a)[('r', 1)], 20)

    def test_band_uses_the_faster_arm(self):
        self.assertTrue(study.in_band(150, 110))
        self.assertFalse(study.in_band(150, 90))
        self.assertFalse(study.in_band(99, 500))
        self.assertTrue(study.in_band(400_000, 300_000))
        self.assertFalse(study.in_band(400_000, 300_001))

    def test_agreement_has_a_ten_percent_tolerance(self):
        # Gate open: max workers must be within 10% of one worker.
        self.assertTrue(study.agrees(True, 100, 109))
        self.assertFalse(study.agrees(True, 100, 111))
        # Gate closed: one worker must be within 10% of max workers.
        self.assertTrue(study.agrees(False, 109, 100))
        self.assertFalse(study.agrees(False, 111, 100))

    def test_verdict_needs_eighty_percent_and_no_row_past_one_twenty_five(self):
        good = [dict(row=f'r{i}', gate=True, w1=200, wmax=100) for i in range(4)]
        miss = dict(row='m', gate=False, w1=120, wmax=100)  # disagrees, regret 1.2
        v = study.verdict(good + [miss])
        self.assertEqual((v['agree'], v['scored']), (4, 5))
        self.assertTrue(v['supported'])
        bad = dict(row='b', gate=False, w1=130, wmax=100)  # regret 1.3
        self.assertFalse(study.verdict(good + [bad])['supported'])
        self.assertFalse(study.verdict(good[:3] + [miss, dict(miss, row='m2')])['supported'])

    def test_verdict_reports_the_fixed_arms(self):
        rows = [dict(row='a', gate=True, w1=200, wmax=100), dict(row='b', gate=False, w1=100, wmax=200)]
        v = study.verdict(rows)
        self.assertAlmostEqual(v['geo_regret']['gate'], 1.0)
        self.assertAlmostEqual(v['geo_regret']['w1'], 2 ** 0.5)
        self.assertAlmostEqual(v['geo_regret']['wmax'], 2 ** 0.5)
        self.assertEqual(v['worst'], (1.0, 'a'))


if __name__ == '__main__':
    unittest.main()
