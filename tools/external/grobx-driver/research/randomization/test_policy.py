#!/usr/bin/env python3
import importlib.util
from pathlib import Path
import unittest

HERE = Path(__file__).resolve().parent


def load():
    spec = importlib.util.spec_from_file_location('randomization_overlay', HERE / 'overlay.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class PolicyTests(unittest.TestCase):
    # Each policy independently gates the plain and signature paths without changing their cutoffs.
    def test_independent_gates(self):
        source = 'pub(crate) fn combines_rows(p: u64) -> bool {\n    p >= COMBINES_FROM\n}\n' \
                 'pub(crate) fn tests_rows<F: Field>(p: u64) -> bool {\n    F::LANES == 1 && zero_combinations(p).is_some()\n}\n'
        output = load().matrix_policy(source)
        self.assertIn('crate::research_random::plain_enabled() && p >= COMBINES_FROM', output)
        self.assertIn('crate::research_random::signature_enabled() && F::LANES == 1', output)
        self.assertEqual(output.count('COMBINES_FROM'), 1)

    # Missing and duplicated decision anchors fail closed rather than patching a different solver path.
    def test_changed_gates_refused(self):
        for source in ['', '    p >= COMBINES_FROM\n' * 2]:
            with self.subTest(source=source), self.assertRaises(ValueError):
                load().matrix_policy(source)


if __name__ == '__main__':
    unittest.main()
