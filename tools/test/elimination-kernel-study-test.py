#!/usr/bin/env python3
"""Offline acceptance checks for the bounded elimination experiment."""
import importlib.util
from pathlib import Path
import unittest

path = Path(__file__).resolve().parents[1] / 'external/elimination-kernel-study.py'
spec = importlib.util.spec_from_file_location('kernels', path)
kernels = importlib.util.module_from_spec(spec)
spec.loader.exec_module(kernels)


class Acceptance(unittest.TestCase):
    # Every field gets three shapes, four nested masks and every backend, without duplicate cells.
    def test_curve_coverage(self):
        cells = list(kernels.curve_cells())
        self.assertEqual(len(cells), 108)
        self.assertEqual(len(set(cells)), 108)
        self.assertEqual({row[0] for row in cells}, {'m31', 'p64', 'bn254'})

    # Matching rank cannot hide a changed coefficient, source capture, support budget or work count.
    def test_matrix_acceptance(self):
        reference = {key: 'same' for key in kernels.IDENTITY}
        kernels.check_matrix(reference, reference)
        for key in kernels.IDENTITY:
            with self.subTest(key=key), self.assertRaises(ValueError):
                kernels.check_matrix(dict(reference, **{key: 'different'}), reference)
        with self.assertRaises(KeyError):
            kernels.check_matrix({}, reference)

    # A missing or zero RSS report is an unmeasured run rather than evidence of low memory use.
    def test_rss_required(self):
        for report in ({}, {'peak_rss_bytes': None}, {'peak_rss_bytes': 0}):
            with self.subTest(report=report), self.assertRaises(ValueError):
                kernels.check_rss(report)
        kernels.check_rss({'peak_rss_bytes': 1000})


if __name__ == '__main__':
    unittest.main()
