#!/usr/bin/env python3
import importlib.util
from pathlib import Path
import tempfile
import unittest

PATH = Path(__file__).resolve().parents[1] / 'external/grobx-work-study.py'
spec = importlib.util.spec_from_file_location('work_study', PATH)
study = importlib.util.module_from_spec(spec)
spec.loader.exec_module(study)


class StudyTests(unittest.TestCase):
    # A complete polynomial list is required rather than accepting a truncated driver answer.
    def test_full_basis_parser(self):
        self.assertEqual(study.basis_list('[x+1,\ny^2]:\n'), ['x+1', 'y^2'])
        for text in ('[x]', '[x,]:', '[x]:junk'):
            with self.subTest(text=text), self.assertRaises(ValueError):
                study.basis_list(text)

    # Matching leading terms cannot hide a changed tail coefficient or changed generator input.
    def test_driver_validation_binds_input_and_basis(self):
        ref = {'digest': 'd', 'modulus': 13, 'basis': ['x+2'],
               'request': {'modulus': 13}, 'input_text': 'x\n13\nx+2\n',
               'input_sha256': 'hash', 'generator_echoes': ['echo'], 'checker_echoes': ['echo']}
        raw = {'input': {'modulus': 13}, 'basis': '[x+2]:\n', 'stopped': None,
               'flaw': None, 'input_text': ref['input_text'], 'input_sha256': 'hash',
               'generator_echoes': ['echo'], 'checker_echoes': ['echo']}
        self.assertEqual(study.validate_driver(raw, ref, ref['request']), ['x+2'])
        for key, value in [('basis', '[x+3]:\n'), ('input_text', 'different'), ('stopped', 'wall')]:
            with self.subTest(key=key), self.assertRaises(ValueError):
                study.validate_driver(dict(raw, **{key: value}), ref, ref['request'])

    # Runtime clocks are removed while path and work differences remain visible to overhead controls.
    def test_trajectory_comparison_retains_structural_differences(self):
        first = {'runs': [{'rounds': [{'number': 1, 'time': 1, 'subtracted': 20,
                                      'stages_seconds': {'reduce': .1}}]}]}
        second = {'runs': [{'rounds': [{'number': 1, 'time': 2, 'subtracted': 20,
                                       'stages_seconds': {'reduce': .2}}]}]}
        self.assertEqual(study.structural(first), study.structural(second))
        second['runs'][0]['rounds'][0]['subtracted'] = 21
        self.assertNotEqual(study.structural(first), study.structural(second))

    # Switching between rows and randomized combinations must remain visible after clock removal.
    def test_reduction_mode_is_structural(self):
        self.assertNotEqual(study.structural({'config': {'reduce': 'rows'}}),
                            study.structural({'config': {'reduce': 'combinations'}}))

    # A wall-budget stop keeps stdout and stderr so refusal never masquerades as a timing answer.
    def test_guard_retains_budget_stop(self):
        with tempfile.TemporaryDirectory() as directory:
            result = study.guarded(['python3', '-c', 'import time;print("started",flush=True);time.sleep(3)'],
                                   Path(directory) / 'attempt', .2, 2**30)
            self.assertEqual(result['stop'], 'wall')
            self.assertIn('started', result['stdout'])
            self.assertNotEqual(result['exit'], 0)


if __name__ == '__main__':
    unittest.main()
