import importlib.util
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent


def _module(name):
    spec = importlib.util.spec_from_file_location(name, HERE / f'{name}.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


campaign = _module('campaign')
summarize = _module('summarize')


class PlanTest(unittest.TestCase):
    def test_every_arm_runs_once_per_rep(self):
        """Each (row, arm) appears exactly once in every repetition of the walls suite."""
        rows = campaign.suite_rows('walls')
        order = campaign.plan(rows, 3)
        self.assertEqual(len(order), 3 * sum(len(a) for _, a in rows))
        for rep in range(3):
            seen = [(r, a) for k, r, a in order if k == rep]
            self.assertEqual(len(seen), len(set(seen)))

    def test_arms_rotate(self):
        """The first arm of a row moves by one place per repetition."""
        order = campaign.plan([('x', ['a', 'b', 'c'])], 3)
        self.assertEqual([a for _, _, a in order], list('abcbcacab'))

    def test_held_out_rows_are_in_the_cohort(self):
        """The pinned held-out rows are timed in the wall cohort and never in the split suite."""
        walls = {r for r, _ in campaign.suite_rows('walls')}
        split = {r for r, _ in campaign.suite_rows('split')}
        self.assertTrue(set(campaign.HELD_OUT) <= walls)
        self.assertFalse(set(campaign.HELD_OUT) & split)

    def test_mq10_uses_the_cost_model(self):
        """MQ10 targets go to m29_cost_model, wide-corpus rows to sig_f4_study."""
        bins = dict(sig='S', cost='C')
        self.assertEqual(campaign.command(bins, 'mq10-m31', 'f4:4')[0], 'm29_cost_model')
        comm, argv = campaign.command(bins, 'wide64/eco-12', 'sigf4:16')
        self.assertEqual((comm, argv[argv.index('--workers') + 1]), ('sig_f4_study', '16'))


class SummaryTest(unittest.TestCase):
    def test_pairs_by_repetition(self):
        """Paired ratios use only repetitions both arms completed, matched by repetition."""
        self.assertEqual(summarize.paired({0: 2.0, 1: 4.0, 2: 9.0}, {0: 1.0, 2: 3.0}), [2.0, 3.0])

    def test_interval_brackets_median(self):
        """The bootstrap interval contains the sample median."""
        m, lo, hi = summarize.median_interval([1.0, 1.1, 0.9, 1.05, 0.95])
        self.assertTrue(lo <= m <= hi)


if __name__ == '__main__':
    unittest.main()
