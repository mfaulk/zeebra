#!/usr/bin/env python3
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location('whole_route', ROOT / 'tools/external/whole-route-study.py')
study = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(study)


class WholeRouteStudy(unittest.TestCase):
    # A killed later stage preserves its complete source checkpoint without inventing a solve.
    def test_checkpoint_is_not_a_final_answer(self):
        records = study.responses('{"checkpoint":"source-basis","basis":["x"]}\n')
        self.assertIsNone(records['final'])
        self.assertEqual(records['source']['basis'], ['x'])
        with self.assertRaises(ValueError):
            study.responses('{"checkpoint":"source-basis"}\nnot json')

    # Independent modular substitution rejects a point violating any original equation.
    def test_independent_modular_substitution(self):
        raw = dict(modulus=13, input=dict(variables=['x','y'], generators=['x^2-1','y-x']), point=['1','1'])
        study.check_point(raw)
        raw['point'] = ['1','2']
        with self.assertRaises(ValueError): study.check_point(raw)
        raw['input']['generators'] = ['__import__("os")']
        with self.assertRaises(ValueError): study.check_point(raw)

    # Staged and unstaged runs are repeated in alternating order without pooling work diagnostics.
    def test_plan_is_interleaved_and_bounded(self):
        cells = list(study.plan())
        self.assertEqual(len(cells), len(set(cells)))
        self.assertEqual({c[0] for c in cells if c[-1] != 'work'}, set(range(5)))
        self.assertEqual(study.limits()['rss_bytes'], 2 * 1024**3)
        self.assertLessEqual(study.limits()['aggregate_wall_seconds'], 1800)


if __name__ == '__main__': unittest.main()
