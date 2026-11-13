#!/usr/bin/env python3
import importlib.util
from pathlib import Path
import unittest
from unittest.mock import Mock, patch

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

    # Interrupting supervision kills and reaps the owned process group before returning failure.
    def test_interrupt_reaps_child(self):
        child = Mock(pid=12345, returncode=-9)
        child.communicate.side_effect = [KeyboardInterrupt(), (b'', b'')]
        with patch.object(study.subprocess, 'Popen', return_value=child), patch.object(study.guard, 'tree_hwm', return_value=0), patch.object(study.os, 'killpg') as kill:
            try:
                row = study.attempt(Path('/binary'), ['floor', 'parked', '2', '0'], [0, 1])
            except KeyboardInterrupt:
                self.fail('supervisor abandoned its owned child')
        self.assertEqual(row['outcome'], 'interrupted')
        kill.assert_called_once_with(12345, study.signal.SIGKILL)
        self.assertEqual(child.communicate.call_count, 2)

if __name__ == '__main__':
    unittest.main()
