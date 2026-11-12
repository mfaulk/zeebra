#!/usr/bin/env python3
"""Check experiment acceptance rejects incorrect arithmetic and stale binaries."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

path = Path(__file__).resolve().parents[1] / 'external/row-merge-study.py'
spec = importlib.util.spec_from_file_location('study', path)
study = importlib.util.module_from_spec(spec)
spec.loader.exec_module(study)


class Acceptance(unittest.TestCase):
    # A matching leading term cannot hide an altered reduced-basis coefficient or field identity.
    def test_complete_basis_and_identity(self):
        reference = dict(digest='input', modulus=13, basis=['x+2*y', 'y^2+1'])
        report = dict(reference, status='complete')
        study.check_answer(report, reference)
        study.check_answer(reference, reference)
        for key, value in [('basis', ['x+3*y', 'y^2+1']), ('digest', 'other'), ('modulus', 7)]:
            with self.subTest(key=key), self.assertRaises(ValueError):
                study.check_answer(dict(report, **{key: value}), reference)

    # Equal rank alone cannot accept a different complete RREF or captured input.
    def test_matrix_identity(self):
        row = dict(rref_hash='coefficients', rank=2, fingerprint='input')
        study.check_matrix(row, row)
        for key in row:
            with self.subTest(key=key), self.assertRaises(ValueError):
                study.check_matrix(row, dict(row, **{key: 'changed'}))

    # A mistyped focused control fails instead of publishing an empty successful cohort.
    def test_named_control_cannot_select_nothing(self):
        label = 'katsura-7/grevlex/m31/default/sparse'
        self.assertEqual([row[0] for row in study.selected_cells('matrices', label)], [label])
        with self.assertRaises(ValueError):
            study.selected_cells('matrices', 'not-a-registered-control')

    # Hardware evidence rejects missing, uncounted or multiplexed events instead of treating them as measurements.
    def test_hardware_counter_acceptance(self):
        raw = '\n'.join(f'100;;{event};1000;100.00;;' for event in study.EVENTS)
        self.assertEqual(set(study.check_counters(raw)), set(study.EVENTS))
        for invalid in ('', raw.replace('100;;', '<not counted>;;', 1), raw.replace(';100.00;', ';50.00;', 1)):
            with self.subTest(raw=invalid), self.assertRaises(ValueError):
                study.check_counters(invalid)

    # Snapshot metadata cannot silently refer to an executable changed after the build.
    def test_snapshot_hash(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'binary'
            path.write_bytes(b'old')
            digest = study.sha(path)
            path.write_bytes(b'new')
            with self.assertRaises(ValueError):
                study.check_binary(path, digest)


if __name__ == '__main__':
    unittest.main()
