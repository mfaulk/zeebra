#!/usr/bin/env python3
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('cross', ROOT/'research/selective-backward/cross.py')
cross = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cross)


class CombinedControls(unittest.TestCase):
    # The fixed plan includes the four-way crossing and separate one-worker algorithm controls.
    def test_plan(self):
        self.assertEqual(len(list(cross.plan('native'))), 140)
        self.assertEqual(len(list(cross.plan('work'))), 12)
        self.assertEqual(len(list(cross.plan('probe'))), 4)

    # A parallel label cannot accept a serial fallback or a different backward policy.
    def test_policy(self):
        ref = dict(digest='d', modulus=13, basis=['x'])
        raw = dict(ref, problem='mq-random-10', backward=None,
                   parallel=dict(workers=4, backward_mode='dense-selected', fallbacks=0, batches=[{}]))
        cross.validate(raw, ref, 'parallel-selected', 'mq-random-10')
        for change in [dict(workers=1), dict(fallbacks=1), dict(backward_mode='full'), dict(batches=[])]:
            with self.subTest(change=change), self.assertRaises(ValueError):
                cross.validate(dict(raw, parallel=dict(raw['parallel'], **change)), ref, 'parallel-selected', 'mq-random-10')


if __name__ == '__main__': unittest.main()
