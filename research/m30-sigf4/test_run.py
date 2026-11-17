"""Unit tests for the #857 campaign plan and its summary statistics."""
import importlib.util
import os
import unittest

HERE = os.path.dirname(__file__)


def module(name):
    spec = importlib.util.spec_from_file_location(name, os.path.join(HERE, f'{name}.py'))
    loaded = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(loaded)
    return loaded


run = module('run')
summarize = module('summarize')


class PlanTest(unittest.TestCase):
    def test_arms_rotate_one_place_per_repetition(self):
        """Every arm leads one repetition in turn, so no arm always runs first."""
        order = run.plan(['r'], ['a', 'b', 'c'], 3)
        self.assertEqual([arm for _, _, arm in order], list('abcbcacab'))

    def test_children_are_pinned_ccd_aligned_and_bounded(self):
        """A 16-worker arm gets 16 CPUs from `first`, and every child runs under timeout."""
        cmd = run.command('bin', 'wide64/eco-12', 'f4:16', 900, 24)
        self.assertEqual(cmd[:3], ['taskset', '-c', '24-39'])
        self.assertIn('--signal=INT', cmd)
        self.assertEqual(run.command('bin', 'wide64/eco-12', 'sigf4:1', 900, None)[0], 'timeout')

    def test_interval_brackets_a_constant_ratio(self):
        """Samples with a fixed 2x ratio give a degenerate interval at 2."""
        self.assertEqual(summarize.interval([2.0] * 5, [1.0] * 5), (2.0, 2.0))


if __name__ == '__main__':
    unittest.main()
