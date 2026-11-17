import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location('campaign', Path(__file__).with_name('campaign.py'))
campaign = importlib.util.module_from_spec(spec)
spec.loader.exec_module(campaign)


class PlanTest(unittest.TestCase):
    def test_targets_extend_m29_with_katsura(self):
        # The M29 four keep their order and Katsura-11 / 2^31-1 is appended, not substituted.
        self.assertEqual(campaign.TARGETS[:4], campaign.costmodel.TARGETS)
        self.assertEqual(campaign.TARGETS[4], 'katsura11-m31')

    def test_walls_and_stages_cover_every_target_and_worker_count_per_rep(self):
        # Each repetition holds every target x worker arm once; stages differ only by the clock flag.
        for suite in ('walls', 'stages'):
            plan = campaign.plan(suite, 5)
            for rep in range(5):
                arms = sorted((t, w) for r, t, w, _, _ in plan if r == rep)
                self.assertEqual(arms, sorted((t, w) for t in campaign.TARGETS for w in campaign.WORKERS))
        self.assertTrue(all(extra == ['--stages'] for *_, extra, _ in campaign.plan('stages', 1)))

    def test_level_arms_differ_only_in_team_size(self):
        # Every level arm runs on the 16-CPU placement; the team size is the only variable.
        plan = campaign.plan('level', 1)
        self.assertTrue(all(w == 16 for _, _, w, _, _ in plan))
        self.assertEqual({a for *_, a in plan}, {f'level{w}' for w in campaign.WORKERS})

    def test_rotation_moves_the_first_arm(self):
        # No arm always runs first, so a position effect cannot attach to one arm.
        plan = campaign.plan('level', 2)
        half = len(plan) // 2
        self.assertNotEqual(plan[0][1:], plan[half][1:])

    def test_a_target_subset_is_respected(self):
        # Restricting targets restricts the plan and nothing else.
        plan = campaign.plan('components', 3, ('mq10-m31',))
        self.assertEqual(len(plan), 3)
        self.assertEqual({t for _, t, *_ in plan}, {'mq10-m31'})


if __name__ == '__main__':
    unittest.main()
