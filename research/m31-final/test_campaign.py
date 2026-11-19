import importlib.util
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent


def _module(name):
    spec = importlib.util.spec_from_file_location(f'm31final_{name}', HERE / f'{name}.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


campaign = _module('campaign')
summarize = _module('summarize')
BINS = dict(sig=Path('S'), cost=Path('C'), zsig=Path('ZS'), zcost=Path('ZC'), work=Path('W'), grobx=Path('G'),
            requests=Path('R'))


class PlanTest(unittest.TestCase):
    def test_every_arm_runs_once_per_rep(self):
        """Each (row, arm) of the walls suite appears exactly once in every repetition."""
        rows = campaign.SUITES['walls']
        order = campaign.BASE.plan(rows, 3)
        self.assertEqual(len(order), 3 * sum(len(a) for _, a in rows))
        for rep in range(3):
            seen = [(r, a) for k, r, a in order if k == rep]
            self.assertEqual(len(seen), len(set(seen)))

    def test_freeze_beside_final_on_every_row(self):
        """Every walls row carries a freeze shipping-F4 arm next to the final arms."""
        for row, arms in campaign.SUITES['walls']:
            self.assertTrue({'f4:16', 'en:16', 'd1:1'} <= set(arms), row)
            self.assertTrue('zf4:16' in arms or 'zcm:16' in arms, row)

    def test_eco14_stays_dropped(self):
        """M31-0's dropped row is in no suite."""
        for rows in campaign.SUITES.values():
            self.assertNotIn('wide64/eco-14', [r for r, _ in rows])


class CommandTest(unittest.TestCase):
    def test_arms_map_to_binaries_and_engines(self):
        """Each arm label selects its build and engine, and the cascade arm passes --claim."""
        _, argv = campaign.command(BINS, 'wide64/eco-12', 'zf4:16')
        self.assertEqual((argv[0], argv[argv.index('--engine') + 1]), ('ZS', 'f4'))
        _, argv = campaign.command(BINS, 'wide64/eco-12', 'cl:8')
        self.assertEqual((argv[0], argv[argv.index('--engine') + 1]), ('S', 'sigf4'))
        self.assertIn('--claim', argv)
        _, argv = campaign.command(BINS, 'wide64/eco-12', 'en:16')
        self.assertEqual(argv[argv.index('--engine') + 1], 'entry')
        _, argv = campaign.command(BINS, 'wide64/eco-12', 'wk:1')
        self.assertEqual(argv[0], 'W')
        self.assertIn('--discovery', argv)

    def test_cost_model_arms_name_the_target(self):
        """MQ10's cost-model arms pass the m29 target, which rss-guard then finds in the cmdline."""
        comm, argv = campaign.command(BINS, 'm31/mq-random-10', 'zcm:16')
        self.assertEqual((comm, argv[0], argv[2]), ('m29_cost_model', 'ZC', 'mq10-m31'))
        self.assertEqual(campaign.command(BINS, 'mq10-m31', 'cm:16')[1][2], 'mq10-m31')

    def test_certified_request_path_names_the_row(self):
        """grobx's request path contains the row's name, which rss-guard confirms against."""
        comm, argv = campaign.command(BINS, 'wide64/eco-12', 'gc:1')
        self.assertEqual(comm, 'grobx-driver')
        self.assertIn('eco-12', argv[1])


class SummaryTest(unittest.TestCase):
    def test_interval_is_seeded(self):
        """The bootstrap interval is a pure function of the values and the cell name."""
        values = [1.0, 1.1, 0.9, 1.05, 0.95]
        self.assertEqual(summarize.interval(values, 'x'), summarize.interval(values, 'x'))
        self.assertEqual(summarize.interval(values, 'x')[0], 1.0)


if __name__ == '__main__':
    unittest.main()
