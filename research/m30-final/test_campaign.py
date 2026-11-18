import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location('campaign', Path(__file__).with_name('campaign.py'))
campaign = importlib.util.module_from_spec(spec)
spec.loader.exec_module(campaign)


class PlanTest(unittest.TestCase):
    def test_targets_are_the_m29_four_then_the_held_out_rows(self):
        # The primary targets keep #834's order and the three held-out rows follow them.
        self.assertEqual(campaign.TARGETS[:4], campaign.costmodel.TARGETS)
        self.assertEqual(campaign.TARGETS[4:], ('katsura11-m31', 'katsura11-wide64', 'cyclic7-wide64'))

    def test_walls_cover_both_builds_at_every_target_and_worker_count_per_rep(self):
        # Each repetition holds every (build, target, workers) arm exactly once.
        plan = campaign.plan('walls', 9)
        want = sorted((b, t, w) for b in campaign.BINARIES for t in campaign.TARGETS for w in campaign.WORKERS)
        for rep in range(9):
            self.assertEqual(sorted((b, t, w) for r, b, t, w, _, _ in plan if r == rep), want)

    def test_baseline_and_final_stay_adjacent_after_rotation(self):
        # Rotation keeps each pair together, so the two builds of one cell see the same load.
        for rep in range(9):
            rows = [(b, t, w) for r, b, t, w, _, _ in campaign.plan('walls', 9) if r == rep]
            for i in range(0, len(rows), 2):
                self.assertEqual({rows[i][0], rows[i + 1][0]}, set(campaign.BINARIES))
                self.assertEqual(rows[i][1:], rows[i + 1][1:])

    def test_rotation_changes_the_first_arm(self):
        # Successive repetitions start on different cells, so no cell always runs first.
        firsts = [next(a for a in campaign.plan('walls', 3) if a[0] == rep)[1:4] for rep in range(3)]
        self.assertEqual(len(set(firsts)), 3)

    def test_stages_and_census_are_separate_campaigns(self):
        # Stage clocks run at 1 and 16 workers; the census is serial, one per build and mode.
        stages = campaign.plan('stages', 1)
        self.assertTrue(all(extra == ['--stages'] and w in (1, 16) for _, _, _, w, extra, _ in stages))
        census = campaign.plan('census', 1)
        self.assertTrue(all(w == 1 and extra[0] in ('--work', '--discovery') for _, _, _, w, extra, _ in census))
        self.assertEqual(len(census), 2 * 2 * len(campaign.TARGETS))


if __name__ == '__main__':
    unittest.main()
