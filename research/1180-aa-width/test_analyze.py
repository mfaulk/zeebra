import json
import random
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import analyze as an  # noqa: E402
from analyze import bs  # noqa: E402


def series(seed, n=30, scale=0.01):
    rng = random.Random(seed)
    return [1 + rng.gauss(0, scale) for _ in range(n)]


class StatisticsTest(unittest.TestCase):
    def test_boot_width_matches_bench_stats_draw_for_draw(self):
        xs = series(1)
        ci = bs.paired_ratio(xs, seed='cell key', draws=500)
        self.assertEqual(an.boot_width(xs, seed='cell key', draws=500), ci.hi - ci.lo)

    def test_boot_width_at_a_larger_pool_resamples_k(self):
        # The pooled reference resamples the loaded n from 60 values: about as wide as one block of 30.
        pool = series(2, n=60)
        w30 = an.boot_width(pool, seed='p', draws=2000, k=30)
        w60 = an.boot_width(pool, seed='p', draws=2000)
        self.assertGreater(w30, 1.2 * w60)

    def test_unit_alpha_is_sidak_over_a_workloads_units(self):
        self.assertAlmostEqual(1 - (1 - an.UNIT_ALPHA) ** 14, 0.05)
        self.assertAlmostEqual(an.UNIT_ALPHA, 0.003657, places=6)

    def test_scale_test_ignores_a_shift_and_flags_a_widening(self):
        idle = series(3, n=60)
        shifted = [x * 1.03 for x in series(4)]
        wider = an.inflate(series(5), 0.0, 4.0)
        self.assertGreater(an.scale_pvalue(shifted, idle, perms=2000, seed='s'), 0.05)
        self.assertLessEqual(an.scale_pvalue(wider, idle, perms=2000, seed='w'), an.UNIT_ALPHA)

    def test_scale_pvalue_is_never_zero(self):
        p = an.scale_pvalue(an.inflate(series(6), 0.0, 50.0), series(7, n=60), perms=300, seed='z')
        self.assertEqual(p, 1 / 301)

    def test_inflate_keeps_the_centre_and_scales_log_deviations(self):
        out = an.inflate([0.5, 1.0, 2.0], 0.0, 2.0)
        self.assertAlmostEqual(out[0], 0.25)
        self.assertAlmostEqual(out[1], 1.0)
        self.assertAlmostEqual(out[2], 4.0)


class AggregateTest(unittest.TestCase):
    # Two units, two trials, seven blocks. A workload fails when any unit fails it; a trial is a false
    # no-go when every workload fails.
    def test_workload_and_no_go_rates(self):
        ok = {c: False for c in an.CANDIDATES}
        bad = {c: True for c in an.CANDIDATES}
        u1 = [[bad] * 7, [bad] + [ok] * 6]
        u2 = [[ok] * 7, [ok] * 7]
        agg = an.aggregate({'u1': u1, 'u2': u2})['A0']
        self.assertAlmostEqual(agg['unit'], 8 / 28)
        self.assertAlmostEqual(agg['workload'], 8 / 14)
        self.assertAlmostEqual(agg['no_go'], 1 / 2)


class RetainedRecordsTest(unittest.TestCase):
    # #1107 §5's control, reproduced from the committed records with #1107's own seeds: the closing W0
    # fails "≤ 1.5 × opening" in 4 of 14 held-out cells and 6 of 22 overall.
    @classmethod
    def setUpClass(cls):
        recs = an.read(sorted((an.CAL / 'data').glob('s*/records-*.jsonl.gz')))
        cls.series = an.idle_series(recs)

    def test_reproduces_the_published_control(self):
        aa = {k: v for k, v in self.series.items() if an.is_aa(k[2])}
        self.assertEqual(len(aa), 22)
        rows = []
        for (s, cell, num, den), v in aa.items():
            (_, op), (slot, cl) = v['open'], v['close']
            wo = an.boot_width(op, seed=f'{s} idle {cell} {num}/{den}')
            wc = an.boot_width(cl, seed=f'{s} W0 {slot} {cell} {num}/{den}')
            rows.append((an.is_held_out(cell), wc > an.K * wo, s, cell, round(wo, 4)))
        self.assertEqual(sum(f for _, f, *_ in rows), 6)
        self.assertEqual(sum(f for h, f, *_ in rows if h), 4)
        # The opening widths #1107's tables quote as "idle".
        widths = {(s, c): w for _, _, s, c, w in rows}
        self.assertEqual(widths[('s1-20261125', 'H-D16')], 0.0043)
        self.assertEqual(widths[('s2-20261126', 'H-P1')], 0.0031)

    def test_committed_results_match_the_committed_tables(self):
        res = json.loads((HERE / 'results.json').read_text())
        self.assertEqual(an.tables(res['observed'], res['simulated'], res['meta']),
                         (HERE / 'tables.md').read_text())


if __name__ == '__main__':
    unittest.main()
