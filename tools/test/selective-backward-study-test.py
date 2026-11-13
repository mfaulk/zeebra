#!/usr/bin/env python3
import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location('study', Path(__file__).resolve().parents[1] / 'external/selective-backward-study.py')
study = importlib.util.module_from_spec(spec)
spec.loader.exec_module(study)


class Acceptance(unittest.TestCase):
    # Complete coefficients, input identity and the selected policy all belong to acceptance.
    def test_answer_and_policy(self):
        ref = dict(digest='d', modulus=13, basis=['x+2*y'])
        raw = dict(ref, problem='mq-random-10', backward=dict(mode='dense-selected', batches=[{}]))
        study.validate(raw, ref, 'dense-selected', 'mq-random-10')
        for key, value in [('basis', ['x+3*y']), ('digest', 'wrong'), ('modulus', 7),
                           ('backward', None), ('backward', dict(mode='full', batches=[{}])),
                           ('backward', dict(mode='dense-selected', batches=[]))]:
            with self.subTest(key=key), self.assertRaises(ValueError):
                study.validate(dict(raw, **{key: value}), ref, 'dense-selected', 'mq-random-10')

    # Pair trajectory drift is rejected instead of being credited to the backward kernel.
    def test_trajectory(self):
        stats = {key: 1 for key in study.TRAJECTORY}
        study.check_trajectory(dict(statistics=stats), dict(statistics=stats))
        for key in study.TRAJECTORY:
            with self.subTest(key=key), self.assertRaises(ValueError):
                study.check_trajectory(dict(statistics=dict(stats, **{key: 2})), dict(statistics=stats))

    # Native and observation-on measurements remain distinct cells in a fixed five-repeat plan.
    def test_plan(self):
        plan = list(study.plan('native'))
        self.assertEqual(len(plan), 120)
        self.assertEqual(len(set(plan)), 120)
        self.assertEqual({c[-1] for c in plan}, {'stock', 'full', 'dense-all', 'dense-selected'})
        self.assertEqual(len(list(study.plan('work'))), 40)
        with self.assertRaises(ValueError):
            list(study.plan('typo'))


if __name__ == '__main__':
    unittest.main()
