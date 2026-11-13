import json
import unittest

from summary import validate_profile, ceiling, read_profile


class ProfileTests(unittest.TestCase):
    # Only a completed call with an evaluated root is admissible evidence.
    def test_refuse_missing_verification(self):
        row = dict(degree=6561, verified=False, forward_ns=80, subgroup_ns=5,
                   descent_ns=10, total_ns=100, max_n=8192, transforms=72)
        with self.assertRaises(ValueError):
            validate_profile(row)

    # Stage attribution cannot exceed complete-call time or the declared radix-2 domain.
    def test_refuse_impossible_profile(self):
        row = dict(degree=6561, verified=True, forward_ns=101, subgroup_ns=5,
                   descent_ns=10, total_ns=100, max_n=8192, transforms=72)
        with self.assertRaises(ValueError):
            validate_profile(row)
        row.update(forward_ns=80, max_n=4096)
        with self.assertRaises(ValueError):
            validate_profile(row)

    # An enclosing-stage Amdahl bound remains an optimistic ceiling, not transform timing.
    def test_ceiling(self):
        self.assertAlmostEqual(ceiling(0.8, 4), 2.5)
        self.assertEqual(ceiling(0.8, 1), 1)

    # A partial report or multiple calls cannot masquerade as one completed case.
    def test_exactly_one_complete_call_required(self):
        with self.assertRaises(ValueError):
            read_profile('stopped: exceeded budget', 6561)
        row = dict(degree=6561, verified=True, forward_ns=80, subgroup_ns=5,
                   descent_ns=10, total_ns=100, max_n=8192, transforms=72)
        raw = 'GATE ' + json.dumps(row) + '\n'
        self.assertEqual(read_profile(raw, 6561), row)
        with self.assertRaises(ValueError):
            read_profile(raw + raw, 6561)
        with self.assertRaises(ValueError):
            read_profile(raw, 1594323)


if __name__ == '__main__':
    unittest.main()
