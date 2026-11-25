import importlib.machinery
import importlib.util
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(REPO / 'tools'))
import calib  # noqa: E402
import bench_stats as bs  # noqa: E402

_loader = importlib.machinery.SourceFileLoader('bench_job', str(REPO / 'tools/bench-job'))
_spec = importlib.util.spec_from_loader('bench_job', _loader)
bj = importlib.util.module_from_spec(_spec)
_loader.exec_module(bj)


class CellsTest(unittest.TestCase):
    # The cell list is the protocol's §3–§4.5 table, with m5 only on C-E1 and H-S16 = cyclic7-wide64.
    def test_cells_match_the_signed_protocol(self):
        got = {c.name: (c.cohort, c.instance, c.workers, c.roles) for c in calib.CELLS}
        self.assertEqual(got['C-E1'], ('calibration', 'wide64/eco-12', 1, ('a', 'a2', 's5', 'm5')))
        self.assertEqual(got['C-M16'], ('calibration', 'gf32003/mq-random-10', 16, ('a', 'a2', 's5')))
        self.assertEqual(got['H-S16'], ('held-out', 'cyclic7-wide64', 16, ('every', 'distinct', 'distinct2')))
        self.assertEqual(got['X-M16'], ('held-out', 'gf32003/katsura-11', 16, ('entry', 'entry2', 'msolve')))
        self.assertEqual(sorted(got), sorted(['C-E1', 'C-M1', 'C-M16', 'C-P16', 'H-K16', 'H-D16', 'H-C1', 'H-P1',
                                              'H-S16', 'X-G1', 'X-M16']))

    # The two cohorts share no family and no scale (§3.2); a cell that broke that is refused.
    def test_cohorts_are_disjoint_and_a_violation_is_refused(self):
        calib.check_disjoint(calib.CELLS)
        bad = calib.CELLS + [calib.Cell('H-X', 'held-out', 'gf32003/eco-12', 1, ('a', 'a2'), 'eco', 12)]
        with self.assertRaisesRegex(ValueError, 'eco'):
            calib.check_disjoint(bad)

    # A cohort's manifest expands, under bench-job's own planner, to exactly that cohort's cells × arms.
    def test_manifest_expands_to_exactly_the_cohort_cells(self):
        for cohort in ('calibration', 'held-out'):
            m = calib.manifest(cohort, 'W0', 's1', calib.Paths.fake(), reps=2, agent='t@b')
            got = {(c['instance'], c['workers'], c['arm']) for c in bj.expand(m)}
            want = {(c.instance, c.workers, calib.arm_name(c, r)) for c in calib.CELLS if c.cohort == cohort
                    for r in c.roles}
            self.assertEqual(got, want)
            self.assertEqual(m['context']['workload'], 'W0')

    # The session's loaded order is the preregistered shuffle of all eight, with W6 removed after shuffling.
    def test_session_order_shuffles_then_drops_w6(self):
        order = calib.session_order(20261125)
        self.assertEqual(order[0], 'W0')
        self.assertEqual(order[-1], 'W0')
        self.assertNotIn('W6', order)
        import random
        full = ['W1', 'W2', 'W3', 'W4-8', 'W4-16', 'W4-32', 'W5', 'W6']
        random.Random(20261125).shuffle(full)
        self.assertEqual(order[1:-1], [w for w in full if w != 'W6'])


class GatesTest(unittest.TestCase):
    # A/A: ±2.5% CI band on 1-worker cells, ±4% on 16-worker cells, median within ±1%.
    def test_aa_band_depends_on_workers(self):
        ci = bs.Interval(1.002, 0.966, 1.035, 30, 30)
        self.assertFalse(calib.aa_gate(ci, 1).ok)
        self.assertTrue(calib.aa_gate(ci, 16).ok)
        self.assertFalse(calib.aa_gate(bs.Interval(1.012, 1.000, 1.020, 30, 30), 16).ok)

    # A/A under load also fails when its CI is more than 1.5× as wide as the same cell's idle CI.
    def test_aa_loaded_width_is_bounded_by_idle(self):
        idle = bs.Interval(1.0, 0.99, 1.01, 30, 30)
        self.assertTrue(calib.aa_gate(bs.Interval(1.0, 0.986, 1.014, 30, 30), 1, idle=idle).ok)
        self.assertFalse(calib.aa_gate(bs.Interval(1.0, 0.984, 1.016, 30, 30), 1, idle=idle).ok)

    # A/B: the loaded − idle median shift and its CI bound H2, and a sign flip fails regardless.
    def test_ab_gate(self):
        idle = [0.965 + 0.001 * (i % 5) for i in range(30)]
        self.assertTrue(calib.ab_gate(idle, [x + 0.005 for x in idle], 'k').ok)
        self.assertFalse(calib.ab_gate(idle, [x + 0.02 for x in idle], 'k').ok)
        self.assertFalse(calib.ab_gate([0.995] * 30, [1.004] * 30, 'k').ok)

    # The difference CI resamples each side independently with bench_stats' seed and percentiles.
    def test_diff_ci_is_deterministic_and_brackets_the_shift(self):
        a, b = [1.0, 1.01, 0.99] * 10, [1.03, 1.04, 1.02] * 10
        ci = calib.diff_ci(a, b, 'cell')
        self.assertEqual(ci, calib.diff_ci(a, b, 'cell'))
        self.assertAlmostEqual(ci.median, 0.03)
        self.assertLessEqual(ci.lo, 0.03)
        self.assertGreaterEqual(ci.hi, 0.03)

    # Cross-engine and absolute gates are |loaded/idle − 1| bounds of 3% and 2%.
    def test_cross_and_absolute_gates(self):
        self.assertTrue(calib.cross_gate(0.80, 0.82).ok)
        self.assertFalse(calib.cross_gate(0.80, 0.83).ok)
        self.assertTrue(calib.abs_gate([1.0] * 5, [1.019] * 5).ok)
        self.assertFalse(calib.abs_gate([1.0] * 5, [1.021] * 5).ok)


class LimitsTest(unittest.TestCase):
    # A loaded pair is moved when it falls outside the 2.5–97.5 percentile range of the same cell's idle ratios.
    def test_moved_uses_idle_percentiles(self):
        idle = [1.0 + 0.001 * i for i in range(30)]
        self.assertFalse(calib.moved(1.010, idle))
        self.assertTrue(calib.moved(1.040, idle))
        self.assertTrue(calib.moved(0.990, idle))

    # The threshold maximizes Youden's J for "value > L", ties going to the lower L.
    def test_fit_threshold_maximizes_youden_j(self):
        values = [1, 2, 3, 4, 10, 11, 12]
        moved = [False, False, False, False, True, True, True]
        lim, j = calib.fit_threshold(values, moved)
        self.assertEqual((lim, j), (4, 1.0))
        lim, j = calib.fit_threshold([1, 5, 5, 9], [False, True, False, True])
        self.assertEqual(lim, 1)

    # A signal unavailable on any pair is ineligible; the OR of the two best is kept only if J rises ≥ 0.05.
    def test_fit_rule_drops_unavailable_signals_and_ors_only_on_gain(self):
        moved = [True, True, False, False]
        rule = calib.fit_rule({'psi': [9, 0, 0, 0], 'mbm': [None, 1, 2, 3], 'ccd': [0, 9, 0, 0]}, moved)
        self.assertNotIn('mbm', rule['signals'])
        self.assertEqual(sorted(rule['signals']), ['ccd', 'psi'])
        single = calib.fit_rule({'psi': [9, 9, 0, 0], 'ccd': [9, 0, 0, 0]}, moved)
        self.assertEqual(list(single['signals']), ['psi'])
        self.assertTrue(calib.apply_rule(single, {'psi': 9}))
        self.assertFalse(calib.apply_rule(single, {'psi': 0}))

    # Fitting refuses held-out records: the limit is fitted on the calibration cohort only (§8.4).
    def test_fit_refuses_held_out_records(self):
        with self.assertRaisesRegex(ValueError, 'held-out'):
            calib.require_cohort([{'cohort': 'calibration'}, {'cohort': 'held-out'}], 'calibration')


class ExtractTest(unittest.TestCase):
    # A sig_f4_study role reads basis_m33, an m29 role basis_sha256, and an incomplete run has no digest.
    def test_digest_by_role(self):
        sig = b'{"status": "complete", "basis_m33": "m33", "basis_sha256": "raw"}'
        self.assertEqual(calib.digest('s5', sig), 'm33')
        self.assertEqual(calib.digest('distinct2', b'{"status": "complete", "basis_sha256": "raw"}'), 'raw')
        self.assertIsNone(calib.digest('a', b'{"status": "timeout", "basis_m33": "m33"}'))
        self.assertIsNone(calib.digest('a', b'not json'))

    # §8.4's signals: foreign and sibling busy, process counts, the busiest non-bench CCD, PSI, vmstat; unavailable is None.
    def test_signals_flatten_the_1105_telemetry(self):
        m = dict(bench_foreign=0.01, sibling_busy={'72': 0.0, '73': 0.2}, compilers_on_bench=1,
                 runner_workers_on_bench=0,
                 ccd_load={'8-15,72-79': 7.9, '16-23,80-87': 7.5, '24-31,88-95': 3.0, '0-7,64-71': 5.0},
                 psi={'cpu': {'some': 0.1, 'full': 0.0}, 'memory': {'some': 0.2, 'full': 0.05}},
                 psi_bench_slice={'unavailable': 'no zbbench.slice'},
                 vmstat={'pgmajfault': 2, 'pgscan': 3, 'pgsteal': 4, 'pswpin': 0, 'pswpout': 1},
                 mbm_bytes_per_s={'unavailable': 'resctrl not mounted'})
        s = calib.signals(m)
        self.assertEqual(s['sibling_busy_max'], 0.2)
        self.assertEqual(s['ccd_load_rest_max'], 5.0)
        self.assertEqual(s['psi_memory_full'], 0.05)
        self.assertIsNone(s['psi_slice_cpu_some'])
        self.assertEqual((s['vmstat_majfault'], s['vmstat_reclaim'], s['vmstat_swap']), (2, 7, 1))
        self.assertIsNone(s['mbm_bytes_per_s'])
        self.assertEqual(calib.pair_signals(s, dict(s, compilers_on_bench=3))['compilers_on_bench'], 3)
        self.assertIsNone(calib.pair_signals(s, s)['mbm_bytes_per_s'])


def rec(cell, role, rep, wall, **kw):
    c = next(x for x in calib.CELLS if x.name == cell)
    r = dict(cohort=c.cohort, workload='W0', session='s', slot=0, cell=cell, role=role, instance=c.instance,
             workers=c.workers, rep=rep, status='ok', wall_s=wall, digest='d', dev=False, publication=False,
             signals={'psi_cpu_some': 0.0})
    r.update(kw)
    return r


class AnalysisTest(unittest.TestCase):
    # raw keeps complete attempts with the reference digest; dev and publication also drop what their rules flag.
    def test_rule_sets(self):
        refs = {'wide64/eco-12': {'m33': 'd'}}
        rs = [rec('C-E1', 'a', 0, 1.0), rec('C-E1', 'a', 1, 1.0, digest='x'), rec('C-E1', 'a', 2, 1.0, status='timeout'),
              rec('C-E1', 'a', 3, 1.0, dev=True), rec('C-E1', 'a', 4, 1.0, publication=True)]
        self.assertEqual([r['rep'] for r in calib.select(rs, 'raw', refs)], [0, 3, 4])
        self.assertEqual([r['rep'] for r in calib.select(rs, 'dev', refs)], [0, 4])
        self.assertEqual([r['rep'] for r in calib.select(rs, 'publication', refs)], [0, 3])

    # Pairs are one repetition of one arm pair in one cell: the A/A pair and each A/B pair, ratio = role / base.
    def test_pairs(self):
        rs = [rec('C-E1', r, k, w) for k in range(2) for r, w in (('a', 2.0), ('a2', 2.02), ('s5', 2.1), ('m5', 2.08))]
        got = {(p['cell'], p['num'], p['den'], p['rep']): round(p['ratio'], 4) for p in calib.pairs(rs)}
        self.assertEqual(got[('C-E1', 'a2', 'a', 1)], 1.01)
        self.assertEqual(got[('C-E1', 's5', 'a', 0)], 1.05)
        self.assertEqual(got[('C-E1', 'm5', 'a', 0)], 1.04)
        self.assertEqual(len(got), 6)

    # The candidate rule set drops a whole pair when either attempt's signal is over the limit.
    def test_candidate_drops_flagged_pairs(self):
        rule = {'signals': {'psi_cpu_some': 0.5}}
        rs = [rec('C-E1', 'a', 0, 2.0), rec('C-E1', 'a2', 0, 2.0, signals={'psi_cpu_some': 0.9}),
              rec('C-E1', 'a', 1, 2.0), rec('C-E1', 'a2', 1, 2.0)]
        self.assertEqual([p['rep'] for p in calib.pairs(rs, rule=rule)], [1])

    # H6 is scored as recall over moved pairs and the share of flagged pairs that did not move.
    def test_h6_score(self):
        s = calib.h6_score(flags=[True, True, True, False, False], moved=[True, True, False, True, False])
        self.assertAlmostEqual(s['recall'], 2 / 3)
        self.assertAlmostEqual(s['false_flag'], 1 / 3)
        self.assertFalse(s['ok'])

    # A decision entry is `allowed` on raw, else the first rule set that passes, else quiet machine only.
    def test_decide(self):
        self.assertEqual(calib.decide({'raw': True, 'dev': True}), 'allowed')
        self.assertEqual(calib.decide({'raw': False, 'dev': False, 'publication': True, 'candidate': True}),
                         'allowed under rule set publication')
        self.assertEqual(calib.decide({'raw': False, 'dev': False, 'publication': False, 'candidate': False}),
                         'quiet machine only')


class DriftTest(unittest.TestCase):
    # Drift is the median over the first third of repetitions ÷ the median over the last third.
    def test_drift(self):
        self.assertAlmostEqual(calib.drift({r: (1.0 if r < 10 else 1.1) for r in range(30)}), 1 / 1.1)


if __name__ == '__main__':
    unittest.main()
