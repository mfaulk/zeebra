#!/usr/bin/env python3
"""The profiling campaign refuses changed inputs and changed full reduced answers."""
import importlib.util
from pathlib import Path
import unittest
import tempfile

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


class GuardTests(unittest.TestCase):
    # A profiler wrapper cannot hide the measured child's memory from the resource guard.
    def test_descendant_high_water_is_included(self):
        with tempfile.TemporaryDirectory() as directory:
            proc = Path(directory)
            for pid, hwm, children in [(1, 3, '2'), (2, 100, '')]:
                path = proc / str(pid)
                (path / 'task' / str(pid)).mkdir(parents=True)
                (path / 'status').write_text(f'VmHWM: {hwm} kB\n')
                (path / 'task' / str(pid) / 'children').write_text(children)
            self.assertEqual(module.tree_hwm(1, proc), 103 * 1024)


if __name__ == '__main__':
    unittest.main()
