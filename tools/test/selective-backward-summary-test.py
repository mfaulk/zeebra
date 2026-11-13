#!/usr/bin/env python3
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('summary', ROOT/'research/selective-backward/summarize.py')
summary = importlib.util.module_from_spec(spec)
spec.loader.exec_module(summary)


class RetainedEvidence(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cohort = summary.tool('study_artifacts').load_study(ROOT/'research/selective-backward/native.json.gz')
        cls.refs = summary.tool('selective-backward-study').references()

    # The complete retained cohort passes all identity, policy, trajectory and timer checks.
    def test_complete_cohort(self):
        summary.validate_cohort(self.cohort, 'native', self.refs)

    # Missing, duplicated and stopped attempts cannot produce accepted medians.
    def test_incomplete_cohorts(self):
        for kind in ('missing', 'duplicate', 'stopped'):
            cohort = copy.deepcopy(self.cohort)
            if kind == 'missing': cohort['attempts'].pop()
            if kind == 'duplicate': cohort['attempts'][-1] = cohort['attempts'][0]
            if kind == 'stopped': cohort['attempts'][0]['stop'] = 'wall'
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                summary.validate_cohort(cohort, 'native', self.refs)

    # Equal leading terms cannot hide coefficient corruption in a retained complete basis.
    def test_corrupt_basis(self):
        cohort = copy.deepcopy(self.cohort)
        cohort['attempts'][0]['raw']['basis'][0] += '+1'
        with self.assertRaises(ValueError): summary.validate_cohort(cohort, 'native', self.refs)

    # Compiling at an attempt boundary disqualifies it even if its basis agrees.
    def test_ambient_compiler(self):
        cohort = copy.deepcopy(self.cohort)
        cohort['attempts'][0]['compiler_after'] = [[1, 'rustc']]
        with self.assertRaises(ValueError): summary.validate_cohort(cohort, 'native', self.refs)

    # Negative time cannot masquerade as an optimization win.
    def test_invalid_timer(self):
        cohort = copy.deepcopy(self.cohort)
        cohort['attempts'][0]['raw']['f4_call_ns'] = -1
        with self.assertRaises(ValueError): summary.validate_cohort(cohort, 'native', self.refs)

    # Artifact drift fails against the existing inventory before regeneration.
    def test_inventory(self):
        with tempfile.TemporaryDirectory() as d:
            here = Path(d)
            (here/'data').write_bytes(b'changed')
            (here/'inventory.json').write_text(json.dumps({'data': '0'*64}))
            with patch.object(summary, 'HERE', here), self.assertRaisesRegex(ValueError, 'SHA256'):
                summary.main()


if __name__ == '__main__': unittest.main()
