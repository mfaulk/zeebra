#!/usr/bin/env python3
"""Unit tests for the Gate H read on synthetic matrices: python3 research/m34-gate-h/test_analyse.py"""
import math
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import analyse  # noqa: E402
import campaign  # noqa: E402


def record(name, family, field='p31'):
    return dict(id=f'{name}@{field}', generator=None,
                field=dict(characteristic='2147483647' if field == 'p31' else '18446744073709551557'),
                lineage=dict(formulation_id=f'{family}/{name}', family_id=family, family_parameters={}))


def attempt(rid, config, wall_ms, rep=0, status='completed-verified', digest='d'):
    return dict(job='j', record=rid, config=config, rep=rep, status=status, wall_ms=wall_ms,
                basis_sha256=digest if status.startswith('completed-') else None, contaminated=False)


def matrix(walls, families=4, per_family=2, refs=True, extra=()):
    """walls(family_index, config) -> wall ms for every problem of that family."""
    rs, attempts = [], list(extra)
    for f in range(families):
        for i in range(per_family):
            r = record(f'x{f}-{i}', f'fam{f}')
            rs.append(r)
            for c in campaign.CONFIGS:
                if not any(a['record'] == r['id'] and a['config'] == c for a in extra):
                    attempts.append(attempt(r['id'], c, walls(f, c)))
    references = {r['id']: dict(status='reference', reduced_basis_digest='d') for r in rs} if refs else {}
    return analyse.Matrix(rs, attempts, {}, references)


class GateH(unittest.TestCase):
    def test_one_arm_best_everywhere_has_no_headroom(self):
        """When one arm is fastest on every problem, BF equals VBS⁺ and H is 1."""
        m = matrix(lambda f, c: 100.0 if c == 'P3' else 200.0)
        r = analyse.read(m, analyse.CONTEXTS['W16'], draws=200)
        self.assertAlmostEqual(r['h'], 1.0)
        self.assertFalse(r['go'])
        self.assertEqual(set(r['bf'].values()), {'P3'})

    def test_complementary_arms_show_headroom(self):
        """Two arms each 4x faster on half the families: leave-one-family-out BF picks the other half's arm, so H = 1/4."""
        m = matrix(lambda f, c: (100.0 if (c == 'P3') == (f < 2) else 400.0) if c in ('P3', 'P6') else 1000.0)
        r = analyse.read(m, ('P3', 'P6'), draws=200)
        self.assertAlmostEqual(r["h"], 0.25)
        self.assertEqual(r['families_at_or_below'], 4)

    def test_lofo_scores_a_family_against_the_others_choice(self):
        """A family's BF is the arm best on the other families, never chosen on its own rows."""
        m = matrix(lambda f, c: {('P3', 0): 100.0, ('P6', 0): 1000.0}.get((c, f), 200.0 if c == 'P6' else 300.0))
        r = analyse.read(m, ('P3', 'P6'), draws=50)
        self.assertEqual(r['bf']['fam0'], 'P6')
        self.assertEqual(r["bf"]["fam1"], "P3")  # fam0 pulls the other families toward P3

    def test_censored_attempts_cost_twice_the_cap(self):
        """A timeout costs 2C under PAR-2 and 10C under PAR-10; it is never its wall."""
        rid = 'x0-0@p31'
        m = matrix(lambda f, c: 100.0, extra=[attempt(rid, 'P1', 330_000.0, status='timeout')])
        self.assertEqual(m.cell(rid, 'P1'), 2 * analyse.C_MS)
        self.assertEqual(m.cell(rid, 'P1', k=10), 10 * analyse.C_MS)

    def test_a_wrong_digest_disqualifies_the_arm(self):
        """A completion whose digest differs from the reference disqualifies its arm everywhere."""
        m = matrix(lambda f, c: 100.0, extra=[attempt('x1-1@p31', 'P5', 50.0, digest='bad')])
        self.assertEqual(m.disqualified, ['P5'])
        self.assertNotIn('P5', analyse.read(m, analyse.CONTEXTS['W16'], draws=20)['arms'])

    def test_unreferenced_records_verify_by_cross_engine_agreement(self):
        """Without a reference, agreement of a conventional arm and the signature engine verifies."""
        m = matrix(lambda f, c: 100.0, refs=False)
        self.assertEqual(m.verified_digest['x0-0@p31'], 'd')
        lone = analyse.Matrix([record('y', 'fam9')], [attempt('y@p31', 'P1', 5.0)], {}, {})
        self.assertNotIn('y@p31', lone.verified_digest)
        self.assertEqual(lone.cell('y@p31', 'P1'), 2 * analyse.C_MS)

    def test_feature_cost_is_charged_to_vbs(self):
        """VBS⁺ adds the record's feature cost to the cheapest arm."""
        m = matrix(lambda f, c: 100.0)
        m.feature_ms = {rid: 10.0 for rid in m.records}
        r = analyse.read(m, ('P1', 'P3'), draws=20)
        self.assertAlmostEqual(r['h'], 1.1)

    def test_split_half_uses_odd_and_even_repetitions(self):
        """Odd-numbered repetitions form one half and even-numbered the other."""
        rid = 'x0-0@p31'
        reps = [attempt(rid, 'P1', w, rep=i) for i, w in enumerate((10.0, 20.0, 30.0, 40.0, 50.0))]
        m = matrix(lambda f, c: 100.0, extra=reps)
        self.assertEqual(m.reps(rid, 'P1', half=0), [10.0, 30.0, 50.0])
        self.assertEqual(m.reps(rid, 'P1', half=1), [20.0, 40.0])

    def test_bootstrap_interval_brackets_the_point(self):
        """The grouped bootstrap interval contains the point estimate on a noisy matrix."""
        m = matrix(lambda f, c: 100.0 * (1 + f) * (1.5 if c == 'P6' else 1) if c in ('P3', 'P6') else 9e5)
        r = analyse.read(m, ('P3', 'P6'), draws=300)
        self.assertLessEqual(r['lo'], r['h'] + 1e-12)
        self.assertGreaterEqual(r['hi'], r['h'] - 1e-12)
        self.assertTrue(math.isfinite(r['hi']))


if __name__ == '__main__':
    unittest.main()
