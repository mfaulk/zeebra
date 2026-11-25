#!/usr/bin/env python3
import hashlib
import itertools
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))
import corpus_lineage  # noqa: E402
import m34_structural_corpus as corpus  # noqa: E402

PROBLEMS = {p['id']: p for p in corpus.PANEL}
# Regenerate only when a generator change is intended: every published digest moves with it.
PANEL_DIGEST = '9b8b6121c6300bae27326c86b887bfc04443f6f586b421b1f9826edb448e4191'


def records():
    revision = corpus.GENERATOR_REVISION or '0' * 40
    saved, corpus.GENERATOR_REVISION = corpus.GENERATOR_REVISION, revision
    try:
        return corpus.build_catalog()
    finally:
        corpus.GENERATOR_REVISION = saved


def shape(problem_id):
    _, equations, _, _ = corpus.build(PROBLEMS[problem_id])
    return len(equations), sorted(max(sum(k) for k in f) for f in equations), sorted(len(f) for f in equations)


class Determinism(unittest.TestCase):
    def test_draw_stream_is_pinned(self):
        """The SHA-256 draw stream gives fixed values, so no Python version or platform moves a seed."""
        rng = corpus.Rng('x')
        self.assertEqual([rng.below(1000) for _ in range(3)], [986, 793, 66])

    def test_every_problem_rebuilds_identically(self):
        """Building a problem twice gives the same integer system."""
        for problem in corpus.PANEL:
            self.assertEqual(corpus.build(problem)[1], corpus.build(problem)[1], problem['id'])

    def test_panel_digests_are_stable(self):
        """The (id, normalized input digest) list over both fields matches the pinned digest."""
        pairs = [[r['id'], r['normalized_input_digest']] for r in records()]
        self.assertEqual(hashlib.sha256(json.dumps(pairs).encode()).hexdigest(), PANEL_DIGEST)

    def test_records_validate_and_ids_are_unique(self):
        """Every record passes the corpus-instance-v1 validator, and ids and seeds are well formed."""
        recs = records()
        for rec in recs:
            corpus_lineage.validate_record(rec)
        self.assertEqual(len({r['id'] for r in recs}), len(recs))
        self.assertEqual(len(recs), 2 * len(corpus.PANEL))

    def test_no_coefficient_vanishes_at_either_prime(self):
        """Reduction removes no term, so field twins share their computed support."""
        for rec in records():
            self.assertNotIn('exceptional-reduction', [t['kind'] for t in rec['transformations']], rec['id'])


class Definitions(unittest.TestCase):
    def test_ladders_match_the_rust_generators(self):
        """Each ladder matches the committed wide corpus, which benchmark_systems.rs generated."""
        checked = 0
        for case in json.loads((ROOT / 'research/wide-corpus/cases.json').read_text()):
            family, n = case['name'].rsplit('-', 1)
            if family not in corpus.LADDERS:
                continue
            p, n = int(case['modulus']), int(n)
            rec = dict(field=dict(characteristic=str(p), extension_degree=1, defining_polynomial=[]),
                       variables=corpus.variables(n), order='grevlex',
                       equations=[[dict(exponents=list(k), coefficient=[str(c % p)]) for k, c in f.items()]
                                  for f in corpus.LADDERS[family](n)])
            self.assertEqual(corpus_lineage.input_digest(rec),
                             corpus_lineage.input_digest(corpus_lineage.legacy_input(case)), case['name'])
            checked += 1
        self.assertEqual(checked, 28)

    def test_reimer_matches_its_definition(self):
        """Reimer-3 is 2x^d - 2y^d + 2z^d - 1 for d = 2, 3, 4, as benchmark_systems::reimer defines it."""
        expected = [{(0, 0, 0): -1, (d, 0, 0): 2, (0, d, 0): -2, (0, 0, d): 2} for d in (2, 3, 4)]
        self.assertEqual(corpus.reimer(3), expected)

    def test_colouring_counts_proper_colourings(self):
        """P(C_5, 3) = 30 and P(K_4, 3) = 0, matching the chromatic polynomial."""
        self.assertEqual(corpus.proper_colourings(5, [(i, (i + 1) % 5) for i in range(5)]), 30)
        self.assertEqual(corpus.proper_colourings(4, list(itertools.combinations(range(4), 2))), 0)

    def test_colouring_vanishes_at_a_colouring(self):
        """At p31, where 3 | p - 1, a proper colouring by cube roots of unity is a common zero."""
        p = corpus.FIELDS['p31']
        omega = pow(7, (p - 1) // 3, p)
        self.assertNotEqual(omega, 1)
        n, edges = corpus.graph('path', None, n=4)
        _, equations, _, _ = corpus.colouring(None, 'path', n=4)
        point = [pow(omega, v % 3, p) for v in range(n)]
        for f in equations:
            self.assertEqual(corpus.evaluate(f, point) % p, 0)

    def test_planted_witnesses_satisfy_their_systems(self):
        """Every planted and block system vanishes exactly at its recorded witness."""
        for problem in corpus.PANEL:
            _, equations, expected, _ = corpus.build(problem)
            if 'witness' in expected:
                self.assertTrue(all(corpus.evaluate(f, expected['witness']) == 0 for f in equations),
                                problem['id'])

    def test_toric_minors_vanish_on_the_parametrization(self):
        """RNC minors vanish at (s^d, s^(d-1)t, …, t^d) and Segre minors at x_ij = a_i b_j."""
        _, rnc, _, _ = corpus.toric(None, 'rnc', d=5)
        self.assertTrue(all(corpus.evaluate(f, [3 ** (5 - i) * 7 ** i for i in range(6)]) == 0 for f in rnc))
        _, segre, _, _ = corpus.toric(None, 'segre', rows=3, cols=3)
        a, b = [2, -5, 3], [7, 1, -4]
        self.assertTrue(all(corpus.evaluate(f, [x * y for x in a for y in b]) == 0 for f in segre))

    def test_hiding_transforms_have_determinant_one(self):
        """The coordinate and mixing matrices are L·U with unit diagonals, so det = 1 at every prime."""
        from fractions import Fraction
        a = [[Fraction(x) for x in row] for row in corpus.unit_triangular_product(corpus.Rng('t'), 6)]
        det = Fraction(1)
        for i in range(6):
            pivot = next(r for r in range(i, 6) if a[r][i])
            if pivot != i:
                a[i], a[pivot], det = a[pivot], a[i], -det
            det *= a[i][i]
            for r in range(i + 1, 6):
                a[r] = [x - a[r][i] / a[i][i] * y for x, y in zip(a[r], a[i])]
        self.assertEqual(det, 1)

    def test_visible_chain_is_a_lex_basis_with_known_quotient(self):
        """Each visible chain element has x_i^d as its only pure power of x_i and no later variable."""
        for problem in corpus.PANEL:
            if problem['family'] != corpus.TRI or problem['parameters']['hidden']:
                continue
            _, equations, expected, _ = corpus.build(problem)
            n, d = problem['parameters']['n'], problem['parameters']['degree']
            for i, f in enumerate(equations):
                self.assertEqual(f[corpus.unit(n, *[i] * d)], 1)
                self.assertTrue(all(not any(k[i + 1:]) and k[i] <= d for k in f))
                self.assertTrue(all(k[i] < d for k in f if k != corpus.unit(n, *[i] * d)))
            self.assertEqual(expected['vdim'], d ** n)


class MatchedComparisons(unittest.TestCase):
    PAIRS = [('zb-col-path-8', 'zb-col-tree-8-s1'), ('zb-col-path-12', 'zb-col-tree-12-s1'),
             ('zb-col-grid-3x4', 'zb-col-gnm-12-17-s1'), ('zb-col-ktree2-12-s1', 'zb-col-gnm-12-21-s1'),
             ('zb-nr-6-e1-distinct-s1', 'zb-nr-6-e1-collide-s1'),
             ('zb-blk-2x4-c0-s1', 'zb-blk-2x4-c1-s1'), ('zb-blk-2x4-c0-s1', 'zb-blk-2x4-c2-s1'),
             ('zb-blk-3x3-c0-s1', 'zb-blk-3x3-c3-s1'), ('zb-blk-2x6-c0-s1', 'zb-blk-2x6-c2-s1')]

    def test_pairs_fix_size_degree_and_term_counts(self):
        """Each matched pair has equal equation count, degree profile and per-equation term counts."""
        for a, b in self.PAIRS:
            self.assertEqual(shape(a), shape(b), (a, b))

    def test_coupling_moves_exactly_c_terms_across_blocks(self):
        """A coupled rung differs from its c = 0 rung in c moved quadratic terms plus constants."""
        _, base, _, _ = corpus.build(PROBLEMS['zb-blk-2x4-c0-s1'])
        _, coupled, _, _ = corpus.build(PROBLEMS['zb-blk-2x4-c2-s1'])
        changed = [i for i, (f, g) in enumerate(zip(base, coupled)) if set(f) != set(g)]
        self.assertEqual(changed, [0, 4])
        for f in coupled:
            touched = {i // 4 for k in f for i, e in enumerate(k) if e}
            self.assertLessEqual(len(touched), 2)

    def test_collision_changes_coefficients_not_support(self):
        """The colliding and distinct nonradical rungs share their support exactly."""
        _, a, _, _ = corpus.build(PROBLEMS['zb-nr-8-e1-distinct-s1'])
        _, b, _, _ = corpus.build(PROBLEMS['zb-nr-8-e1-collide-s1'])
        self.assertEqual([set(f) for f in a], [set(f) for f in b])
        self.assertNotEqual(a, b)


class References(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not corpus.REFERENCES.exists():
            raise unittest.SkipTest('references.json is not committed yet')
        cls.refs = json.loads(corpus.REFERENCES.read_text())['references']

    def test_committed_catalog_is_current(self):
        """catalog.json is byte-identical to what the generators at this tree produce."""
        self.assertEqual(corpus.CATALOG.read_text(), corpus.oracle.dump_catalog(corpus.build_catalog()))

    def test_every_record_has_a_reference_row_with_its_digest(self):
        """references.json covers every record and pins the input digest it was computed on."""
        recs = records()
        self.assertEqual(set(self.refs), {r['id'] for r in recs})
        for rec in recs:
            self.assertEqual(self.refs[rec['id']]['normalized_input_digest'], rec['normalized_input_digest'])

    def test_exact_properties_agree_with_the_oracles(self):
        """Every exact vdim or dimension the spec claims agrees with each oracle that finished."""
        for problem in corpus.PANEL:
            _, _, expected, _ = corpus.build(problem)
            for field in corpus.FIELDS:
                ref = self.refs[f'{problem["id"]}@{field}']
                if ref['status'] != 'reference':
                    continue
                if 'vdim' in expected:
                    self.assertEqual(ref['vdim'], expected['vdim'], (problem['id'], field))
                if 'dimension' in expected and 'dimension' in ref:
                    self.assertEqual(ref['dimension'], expected['dimension'], problem['id'])

    def test_fields_agree_on_vdim(self):
        """Where both oracles finished, the p31 and p64 twins agree on vdim."""
        for problem in corpus.PANEL:
            a, b = (self.refs[f'{problem["id"]}@{f}'] for f in corpus.FIELDS)
            if a['status'] == b['status'] == 'reference' and a['vdim'] is not None:
                self.assertEqual(a['vdim'], b['vdim'], problem['id'])


if __name__ == '__main__':
    unittest.main()
