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

    def test_frequency_summary(self):
        # Clock samples reduce to count, mean and extremes; no samples is no summary rather than zeros.
        self.assertIsNone(costmodel.summarize_freq([]))
        s = costmodel.summarize_freq([4.0e6, 4.5e6, 3.9e6])
        self.assertEqual((s['n'], s['min_khz'], s['max_khz']), (3, 3900000, 4500000))


if __name__ == '__main__':
    unittest.main()
