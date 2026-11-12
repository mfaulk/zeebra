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
