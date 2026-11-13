#!/usr/bin/env python3
import importlib.util
from pathlib import Path
import unittest

PATH = Path(__file__).resolve().parents[1] / 'external/worker-pool-study.py'
spec = importlib.util.spec_from_file_location('study', PATH)
study = importlib.util.module_from_spec(spec)
spec.loader.exec_module(study)

class Contract(unittest.TestCase):
    # A truncated dispatch distribution cannot be published as a successful sample.
    def test_rejects_incomplete_floor(self):
        with self.assertRaises(ValueError):
            study.validate({'backend': 'parked', 'workers': 2, 'result': {'samples_ns': [1], 'work': 0}}, ['floor', 'parked', '2', '0'])

    # Complete polynomial text must bind to the recorded input identity.
    def test_rejects_corrupted_input(self):
        report = {'backend': 'parked', 'workers': 2, 'result': {'input': 'x', 'source_basis': 'x', 'input_sha256': 'wrong', 'source_sha256': 'wrong'}}
        with self.assertRaises(ValueError):
            study.validate(report, ['border', 'parked', '2', 'katsura-7', '64'])

    # CPU placement uses one hardware thread per core before selecting SMT siblings.
    def test_topology_orders_physical_cores_first(self):
        self.assertEqual(study.cpu_order('0,0,0,0\n1,1,0,0\n2,0,0,0\n3,1,0,0', {0, 1, 2, 3}), [0, 1, 2, 3])

    # Missing cells and a missing completion marker are failures, not a partial published table.
    def test_summary_refuses_incomplete_campaign(self):
        with self.assertRaisesRegex(ValueError, 'did not complete'):
            study.summarize({'attempts': []})
        with self.assertRaisesRegex(ValueError, 'missing or duplicated'):
            study.summarize({'end_load': [0], 'attempts': [], 'plan': {'phase': 'floor', 'workers': [1], 'systems': [], 'repeats': 1}})

if __name__ == '__main__':
    unittest.main()
