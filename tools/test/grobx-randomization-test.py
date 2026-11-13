#!/usr/bin/env python3
import importlib.util
from itertools import product
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[2]


def load(name):
    path = ROOT / 'tools/external' / (name + '.py')
    spec = importlib.util.spec_from_file_location(name.replace('-', '_'), path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class ContractTests(unittest.TestCase):
    # A missing pivot and a rogue extra pivot are rejected, including when forward inclusion holds.
    def test_both_span_inclusions_are_required(self):
        check = load('randomization_contract').check_span
        self.assertFalse(check([[1, 0], [0, 1]], [[1, 0]], [[1, 0]], 7))
        self.assertFalse(check([[1, 0]], [[1, 0], [0, 1]], [[1], [0]], 7))
        self.assertTrue(check([[1, 0], [0, 1]], [[1, 1], [1, 0]], [[1, 1], [1, 0]], 7))
        self.assertFalse(check([[1, 0], [0, 1]], [[1, 1]], [[1, 0]], 7))

    # Zero/dependent rows are valid, while interrupted checks never count as a successful certificate.
    def test_degeneracy_and_interruption(self):
        check = load('randomization_contract').check_span
        self.assertTrue(check([[0, 0], [1, 2], [2, 4]], [[1, 2]], [[0, 1, 0]], 7))
        self.assertTrue(check([[0, 0]], [], [], 7))
        self.assertFalse(check([[0, 0]], [], [], 7, complete=False))

    # Every two-by-two input over GF(2), GF(3), and GF(7) survives a certified invertible row transform.
    def test_exhaustive_small_field_transform(self):
        check = load('randomization_contract').check_span
        for p in (2, 3, 7):
            for a, b, c, d in product(range(p), repeat=4):
                rows = [[a, b], [c, d]]
                transformed = [[(a+c) % p, (b+d) % p], [c, d]]
                self.assertTrue(check(rows, transformed, [[1, 1], [0, 1]], p))

    # The maximum-atom bound matches every coefficient bucket of a small multiply-high sampler.
    def test_sampler_bound(self):
        model = load('randomization_contract')
        for p in (3, 7, 13):
            counts = [0] * p
            for word in range(256):
                counts[1 + (word * (p-1) >> 8)] += 1
            self.assertEqual(model.maximum_atom(p, bits=8), model.Fraction(max(counts), 256))
        self.assertGreater(model.plain_bound(32003), model.maximum_atom(32003)**2)
        self.assertEqual(model.signature_draws(32003), 3)
        self.assertEqual(model.signature_draws(2147483647), 2)

    # Five interleaved repetitions and a separate finite seed study retain all declared objectives.
    def test_attempt_plan(self):
        study = load('grobx-randomization-study')
        plan = study.plan(5)
        primary = [a for a in plan if a['cohort'] == 'primary']
        self.assertEqual(len(primary), 170)
        self.assertEqual(len(plan), 182)
        for name in study.ARMS:
            for p in study.MODULI:
                selected = [a for a in primary if a['arm'] == name and a['modulus'] == p]
                self.assertEqual(len(selected), 5)
                self.assertEqual({a['seed'] for a in selected}, {0})
        self.assertEqual({a['seed'] for a in plan if a['cohort'] == 'sensitivity'}, {1, 2})

    # Admission binds the executed policy, complete residual checks, and exact-mode checker result.
    def test_policy_admission(self):
        validate = load('grobx-randomization-study').validate_policy
        request = dict(mode='raw', research_work=True, research_signatures=False, research_validate=True)
        raw = dict(work={}, research_policy=dict(plain=True, signature_tests=True, validate=True,
                   signatures=False, seed=0), research_audit=[dict(valid=True)])
        validate(raw, request)
        for key, value in [('research_policy', {}), ('research_audit', []),
                           ('research_audit', [dict(valid=False)]), ('work', None)]:
            changed = dict(raw, **{key: value})
            with self.subTest(key=key, value=value), self.assertRaises(ValueError):
                validate(changed, request)
        with self.assertRaises(ValueError):
            validate(raw, dict(request, mode='certified'))

    # Actual engine reports and events must agree with disabled features, not just echo their flags.
    def test_activation_cannot_be_faked_by_receipt(self):
        validate = load('grobx-randomization-study').validate_activation
        request = dict(modulus=2147483647, research_policy='none')
        runs = {'runs': [{'config': dict(engine='signature', cofactors='off', reduce='rows')},
                         {'config': dict(engine='plain', cofactors='off', reduce='rows')}]}
        validate({}, request, runs)
        for engine, mode in [('signature', 'tests'), ('plain', 'combinations')]:
            with self.subTest(engine=engine), self.assertRaises(ValueError):
                validate({}, request, {'runs': [{'config': dict(engine=engine, cofactors='off', reduce=mode)}]})
        with self.assertRaises(ValueError):
            validate({'research_events': [dict(kind='plain-block')]}, request, runs)


if __name__ == '__main__':
    unittest.main()
