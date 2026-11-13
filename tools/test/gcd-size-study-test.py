#!/usr/bin/env python3
import importlib.util
from pathlib import Path
import unittest

PATH = Path(__file__).resolve().parents[1] / 'external/gcd-size-study.py'
spec = importlib.util.spec_from_file_location('gcd_size_study', PATH)
study = importlib.util.module_from_spec(spec)
spec.loader.exec_module(study)


class RecordTests(unittest.TestCase):
    # A digest-bound pair must return the same complete polynomial across routes and observer modes.
    def test_complete_answer_binding(self):
        answers = {}
        raw = {'input': 'pair', 'input_sha256': study.digest(b'pair'), 'gcd': 'x',
               'observed': False, 'profile': None, 'status': 'completed', 'peak_rss_bytes': 100}
        study.validate(raw, answers, ('field', 2, 0), False)
        study.validate(dict(raw), answers, ('field', 2, 0), False)
        with self.assertRaisesRegex(ValueError, 'GCD'):
            study.validate(dict(raw, gcd='1'), answers, ('field', 2, 0), False)
        with self.assertRaisesRegex(ValueError, 'digest'):
            study.validate(dict(raw, input='other'), answers, ('field', 2, 0), False)

    # Missing profiles, negative counters and violated local degree bounds cannot become accepted evidence.
    def test_size_observations_are_checked(self):
        profile = {name: {'observations': 1, 'max_terms': 2, 'max_coefficient_degree': 3}
                   for name in study.PHASES}
        profile['subresultant_bound_violations'] = 0
        raw = {'input': 'pair', 'input_sha256': study.digest(b'pair'), 'gcd': 'x',
               'observed': True, 'profile': profile, 'status': 'completed', 'peak_rss_bytes': 100}
        study.validate(raw, {}, ('field', 2, 0), True)
        with self.assertRaisesRegex(ValueError, 'profile'):
            study.validate(dict(raw, profile=None), {}, ('field', 2, 0), True)
        profile['prs_entries']['max_terms'] = -1
        with self.assertRaisesRegex(ValueError, 'counter'):
            study.validate(raw, {}, ('field', 2, 0), True)
        profile['prs_entries']['max_terms'] = 2
        profile['subresultant_bound_violations'] = 1
        with self.assertRaisesRegex(ValueError, 'bound'):
            study.validate(raw, {}, ('field', 2, 0), True)


if __name__ == '__main__':
    unittest.main()
