#!/usr/bin/env python3
import copy
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('summary', ROOT/'research/selective-backward/combined_summary.py')
summary = importlib.util.module_from_spec(spec)
spec.loader.exec_module(summary)


class CombinedEvidence(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.storage = summary.cross.driver.load('study_artifacts')
        cls.refs = summary.cross.driver.references()
        cls.native = cls.storage.load_study(ROOT/'research/selective-backward/cross-native.json.gz')
        cls.work = cls.storage.load_study(ROOT/'research/selective-backward/cross-work.json.gz')
        cls.probes = cls.storage.load_study(ROOT/'research/selective-backward/probes.json.gz')

    # The complete four-way cohort and same-algorithm controls pass full-answer validation.
    def test_complete(self):
        summary.validate(self.native, 'native', self.refs)
        summary.validate(self.work, 'work', self.refs)
        summary.validate(self.probes, 'probe', self.refs)

    # Missing repetitions and changed coefficients cannot become a combined performance result.
    def test_incomplete_and_corrupt(self):
        for kind in ('missing', 'coefficient'):
            cohort = copy.deepcopy(self.native)
            if kind == 'missing': cohort['attempts'].pop()
            else: cohort['attempts'][0]['raw']['basis'][0] += '+1'
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                summary.validate(cohort, 'native', self.refs)

    # A native compiler overlap is rejected independently of answer correctness.
    def test_compiler(self):
        cohort = copy.deepcopy(self.native)
        cohort['attempts'][0]['compiler_after'] = [[1, 'rustc']]
        with self.assertRaises(ValueError): summary.validate(cohort, 'native', self.refs)

    # A resource-limited probe cannot be relabelled as a verified answer.
    def test_probe_classification(self):
        cohort = copy.deepcopy(self.probes)
        cohort['attempts'][0]['status'] = 'verified'
        with self.assertRaises(ValueError): summary.validate(cohort, 'probe', self.refs)

    # Direct worker products must agree with worker-local passive instrumentation.
    def test_worker_counter_drift(self):
        cohort = copy.deepcopy(self.work)
        parallel = next(a['raw']['parallel'] for a in cohort['attempts'] if a['raw']['parallel'])
        parallel['batches'][0]['products'] += 1
        with self.assertRaises(ValueError): summary.validate(cohort, 'work', self.refs)

    # A changed replay matrix cannot be hidden behind matching final answers.
    def test_matrix_drift(self):
        cohort = copy.deepcopy(self.work)
        parallel = next(a['raw']['parallel'] for a in cohort['attempts'] if a['raw']['parallel'])
        parallel['batches'][0]['input_matrix_digest'] = 'changed'
        with self.assertRaises(ValueError): summary.validate(cohort, 'work', self.refs)


if __name__ == '__main__': unittest.main()
