import importlib.util
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent


def _module(name):
    spec = importlib.util.spec_from_file_location(f'm32gates_{name}', HERE / f'{name}.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


campaign = _module('campaign')
summarize = _module('summarize')
BINS = dict(head=Path('H/sig_f4_study'), base=Path('B/sig_f4_study'))


def record(suite, rep, row, arm, wall_s, symbolic_s=0.1, rss=100):
    return dict(suite=suite, rep=rep, row=row, arm=arm, returncode=0, process_wall_ns=int(wall_s * 1e9),
                report=dict(status='complete', call_ns=int(wall_s * 1e9), peak_rss_bytes=rss,
                            statistics=dict(symbolic_ns=int(symbolic_s * 1e9))))


class PlanTest(unittest.TestCase):
    def test_every_arm_runs_once_per_rep(self):
        """Each (row, arm) of every suite appears exactly once in every repetition."""
        for suite, rows in campaign.SUITES.items():
            order = campaign.BASE.plan(rows, 3)
            self.assertEqual(len(order), 3 * sum(len(a) for _, a in rows), suite)
            for rep in range(3):
                seen = [(r, a) for k, r, a in order if k == rep]
                self.assertEqual(len(seen), len(set(seen)), suite)

    def test_every_head_arm_has_its_base(self):
        """Every head `en` or `cl` arm is paired with the same arm on the merge base."""
        for rows in campaign.SUITES.values():
            for _, arms in rows:
                for arm in arms:
                    if arm.startswith('h-') and not arm.startswith('h-f4'):
                        self.assertIn('b-' + arm[2:], arms)

    def test_commands_pick_build_and_engine(self):
        """The build letter picks the binary; `cl` adds `--claim` and `en` runs the entry point."""
        _, argv = campaign.command(BINS, 'wide64/eco-12', 'b-cl:16')
        self.assertEqual(argv[0], 'B/sig_f4_study')
        self.assertEqual(argv[argv.index('--engine') + 1], 'sigf4')
        self.assertIn('--claim', argv)
        _, argv = campaign.command(BINS, 'gf32003/mq-random-10', 'h-en:4')
        self.assertEqual(argv[:5], ['H/sig_f4_study', '--field', 'gf32003', '--name', 'mq-random-10'])
        self.assertEqual(argv[argv.index('--engine') + 1], 'entry')
        self.assertNotIn('--claim', argv)

    def test_no_held_out_row_is_timed(self):
        """Plan §10.1's held-out set is never run by this campaign."""
        held_out = {'goldilocks/mq-random-10', 'wide64/mq-random-12', 'gf32003/mq-random-9',
                    'm31/katsura-10', 'm31/eco-11', 'goldilocks/cyclic-6'}
        rows = {r for rows in campaign.SUITES.values() for r, _ in rows}
        self.assertFalse(rows & held_out)


class SummaryTest(unittest.TestCase):
    def test_precision_rule(self):
        """A cell is readable only when its half-width is at most half its threshold's distance to 1."""
        self.assertTrue(summarize.precise((1.0, 0.98, 1.02), 1.05))
        self.assertFalse(summarize.precise((1.0, 0.97, 1.03), 1.05))
        self.assertEqual(summarize.verdict((1.0, 0.97, 1.03), lambda x: True, 1.05), 'imprecise')

    def test_t1_reads_symbolic_base_over_head(self):
        """T1 is the paired base ÷ head symbolic stage on Eco-12's `cl:16` arms."""
        records = []
        for rep in range(9):
            records.append(record('gate', rep, 'wide64/eco-12', 'b-cl:16', 1.7, symbolic_s=0.55))
            records.append(record('gate', rep, 'wide64/eco-12', 'h-cl:16', 1.4, symbolic_s=0.25))
        c = summarize.Cohort(records)
        cell = c.ratio('gate', 'wide64/eco-12', 'b-cl:16', 'h-cl:16', summarize.stage('symbolic'))
        self.assertAlmostEqual(cell[0], 2.2)
        self.assertIn('| met |', summarize.gate_table(c).splitlines()[4])

    def test_failed_attempts_are_counted_not_timed(self):
        """A stopped child counts as an attempt and contributes no time."""
        bad = record('gate', 0, 'wide64/eco-12', 'h-en:16', 9.0)
        bad['report']['status'] = 'stopped: budget'
        c = summarize.Cohort([bad, record('gate', 1, 'wide64/eco-12', 'h-en:16', 1.0)])
        self.assertEqual(c.attempts[('gate', 'wide64/eco-12', 'h-en:16')], 2)
        self.assertEqual(c.median('gate', 'wide64/eco-12', 'h-en:16', summarize.wall), 1.0)


if __name__ == '__main__':
    unittest.main()
