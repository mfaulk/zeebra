import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location('wide', Path(__file__).parents[1] / 'external/wide-corpus.py')
wide = importlib.util.module_from_spec(spec)
spec.loader.exec_module(wide)

class WideCorpusTests(unittest.TestCase):
    # Full basis equality rejects matching leading monomials with different tail coefficients.
    def test_changed_tail_is_rejected(self):
        with self.assertRaises(ValueError):
            wide.verify_bases([{'report': {'status': 'complete', 'basis': ['x1+1']}},
                               {'report': {'status': 'complete', 'basis': ['x1+2']}}])

    # A startup-dominated wall comparison never publishes a ratio.
    def test_floor_gate(self):
        self.assertIsNone(wide.wall_ratio(1.0, 1.5, 0.001, 1.0))
        self.assertEqual(wide.wall_ratio(2.0, 4.0, 0.001, 1.0), 0.5)

    # Julia wall comparisons use the supervised process stage rather than its warmed F4 call.
    def test_julia_uses_process_wall(self):
        a = {'process_wall_ns': 9_000_000_000, 'report': {'engine': 'groebner.jl',
             'engine_wall_ns': 100_000_000, 'solver_process_wall_ns': 5_000_000_000}}
        self.assertEqual(wide.seconds(a), 5)

    # A stopped attempt is retained without being treated as a completed oracle.
    def test_limit_is_not_an_oracle(self):
        self.assertEqual(wide.verify_bases([{'stop': 'wall'}]), 0)

    # Comparison cannot silently combine outputs from different frozen input identities.
    def test_different_identities_are_rejected(self):
        with self.assertRaises(ValueError):
            wide.verify_bases([{'digest': 'a'}, {'digest': 'b'}])

    # A changed canonical input cannot reuse its previous digest.
    def test_catalog_rejects_changed_bytes(self):
        c = {'field': 'bn254', 'name': 'katsura-4', 'canonical': 'prime 1', 'digest': '0'*64}
        with self.assertRaises(ValueError):
            wide.validate_catalog([c])

if __name__ == '__main__':
    unittest.main()
