import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location('costmodel', Path(__file__).with_name('costmodel.py'))
costmodel = importlib.util.module_from_spec(spec)
spec.loader.exec_module(costmodel)


class PlanTest(unittest.TestCase):
    def test_cpulists_are_ccd_aligned_from_cpu_8(self):
        # One worker pins CPU 8; w workers take w consecutive CPUs from 8, so 8 fill one CCD.
        self.assertEqual([costmodel.cpulist(w) for w in (1, 4, 8, 16)], ['8', '8-11', '8-15', '8-23'])

    def test_every_arm_runs_once_per_repetition(self):
        # Rotation changes the order only: each repetition holds every target x worker arm exactly once.
        plan = costmodel.plan('walls', 3)
        for rep in range(3):
            arms = sorted((t, w) for r, t, w, _, _ in plan if r == rep)
            self.assertEqual(arms, sorted((t, w) for t in costmodel.TARGETS for w in costmodel.WORKERS))

    def test_rotation_moves_the_first_arm(self):
        # No arm always takes the first slot, so a position effect cannot attach to one arm.
        plan = costmodel.plan('walls', 2)
        per_rep = len(plan) // 2
        self.assertNotEqual(plan[0][1:3], plan[per_rep][1:3])

    def test_census_is_serial_and_ab_pairs_both_policies(self):
        # The thread-local census runs at one worker; the #831 A/B runs both policies at 1 and 16 workers.
        self.assertTrue(all(w == 1 for _, _, w, _, _ in costmodel.plan('census', 1)))
        ab = costmodel.plan('ab831', 1)
        self.assertEqual({a for *_, a in ab}, {'every', 'distinct'})
        self.assertEqual({w for _, _, w, _, _ in ab}, {1, 16})

    def test_fl_cross_check_pairs_both_orders_at_16_workers(self):
        # The #828 cross-check runs forward and FL on each wide target at 16 workers, every repetition.
        plan = costmodel.plan('fl', 5)
        self.assertEqual(len(plan), 20)
        self.assertEqual({(t, a) for _, t, _, _, a in plan},
                         {(t, o) for t in ('eco12-wide64', 'mq11-goldilocks') for o in ('forward', 'fl')})
        self.assertTrue(all(w == 16 for _, _, w, _, _ in plan))

    def test_fl_stages_suite_clocks_the_same_pairs(self):
        # `flstages` runs the same order pairs as `fl`, each with stage clocks on.
        plan = costmodel.plan('flstages', 3)
        self.assertEqual({(t, a) for _, t, _, _, a in plan}, {(t, a) for _, t, _, _, a in costmodel.plan('fl', 3)})
        self.assertTrue(all('--stages' in extra for _, _, _, extra, _ in plan))

    def test_frequency_summary(self):
        # Clock samples reduce to count, mean and extremes; no samples is no summary rather than zeros.
        self.assertIsNone(costmodel.summarize_freq([]))
        s = costmodel.summarize_freq([4.0e6, 4.5e6, 3.9e6])
        self.assertEqual((s['n'], s['min_khz'], s['max_khz']), (3, 3900000, 4500000))


if __name__ == '__main__':
    unittest.main()
