#!/usr/bin/env python3
"""The profiling campaign refuses changed inputs and changed full reduced answers."""
import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location('mq10_profile', Path(__file__).resolve().parents[1] / 'external/mq10-profile.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class AnswerTests(unittest.TestCase):
    # Basis ordering does not change the full reduced-basis equality check.
    def test_permuted_basis_matches(self):
        module.check_answer({'digest': 'd', 'modulus': 13, 'basis': ['x', 'y']},
                            {'digest': 'd', 'modulus': 13, 'basis': ['y', 'x']})

    # Equal leading monomials cannot hide a changed coefficient in the full answer.
    def test_changed_tail_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'full reduced basis'):
            module.check_answer({'digest': 'd', 'modulus': 13, 'basis': ['x+2*y']},
                                {'digest': 'd', 'modulus': 13, 'basis': ['x+3*y']})

    # A matching answer cannot authorize measurements of a different ideal or field.
    def test_changed_identity_is_rejected(self):
        reference = {'digest': 'd', 'modulus': 13, 'basis': ['x']}
        for key, value in [('digest', 'other'), ('modulus', 17)]:
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, 'input identity'):
                module.check_answer(dict(reference, **{key: value}), reference)


if __name__ == '__main__':
    unittest.main()
