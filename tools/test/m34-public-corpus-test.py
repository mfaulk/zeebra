#!/usr/bin/env python3
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))
spec = importlib.util.spec_from_file_location('m34_public_corpus', ROOT / 'tools/m34_public_corpus.py')
corpus = importlib.util.module_from_spec(spec)
spec.loader.exec_module(corpus)

PROBLEM = dict(id='toy', formulation_id='toy', family_id='toy', source_id='toy', family_parameters=dict(n=2))


def entry(*equations):
    return dict(url='https://example.org/toy', revision='v1', license='CC0-1.0', variables=['x', 'y'],
                equations=list(equations))


class Parser(unittest.TestCase):
    def test_coefficients_and_repeated_variables_combine(self):
        """A mid-term coefficient multiplies, a repeated variable adds exponents, and like terms merge."""
        self.assertEqual(corpus.parse_integer_polynomial('2*x*3*x^2 - 6*x^3 + y - 7', ['x', 'y']),
                         {(0, 1): 1, (0, 0): -7})

    def test_unknown_variable_is_rejected(self):
        """A factor that is not a declared variable fails rather than becoming a parameter."""
        with self.assertRaises(ValueError):
            corpus.parse_integer_polynomial('x*u+1', ['x', 'y'])

    def test_non_integer_coefficients_are_rejected(self):
        """Decimal and rational coefficients are refused, never silently converted."""
        for text in ('0.5*x+1', 'x/2+1', '(x+1)*y'):
            with self.assertRaises(ValueError, msg=text):
                corpus.parse_integer_polynomial(text, ['x', 'y'])


class Reduction(unittest.TestCase):
    def test_clean_reduction_preserves_support(self):
        """Field twins whose reduction removes no term share one computed support id."""
        a = corpus.reduce_record(PROBLEM, entry('3*x^2-y'), 'a', 7)
        b = corpus.reduce_record(PROBLEM, entry('3*x^2-y'), 'b', 11)
        self.assertEqual(a['lineage']['support_id'], b['lineage']['support_id'])
        self.assertEqual([t['kind'] for t in a['transformations']], ['prime-reduction'])
        self.assertEqual(a['equations'][0][0], {'exponents': [0, 1], 'coefficient': ['6']})

    def test_vanishing_coefficient_is_an_exceptional_reduction(self):
        """A coefficient divisible by p is labelled and changes the support id."""
        clean = corpus.reduce_record(PROBLEM, entry('7*x^2-y'), 'a', 11)
        exceptional = corpus.reduce_record(PROBLEM, entry('7*x^2-y'), 'b', 7)
        self.assertIn('exceptional-reduction', [t['kind'] for t in exceptional['transformations']])
        self.assertNotEqual(clean['lineage']['support_id'], exceptional['lineage']['support_id'])


class BasisDigest(unittest.TestCase):
    def test_digest_ignores_scalar_multiples_and_generator_order(self):
        """Two oracles' renderings of one reduced basis, scaled and reordered, give one digest."""
        record = corpus.reduce_record(PROBLEM, entry('x^2-y', 'y^2-1'), 'a', 7)
        a = corpus.basis_digest(record, [{(2, 0): 1, (0, 1): -1}, {(0, 2): 1, (0, 0): -1}])
        b = corpus.basis_digest(record, [{(0, 2): 3, (0, 0): 4}, {(2, 0): 2, (0, 1): 5}])
        self.assertEqual(a, b)

    def test_grevlex_leading_term_sets_the_scale(self):
        """Scaling is by the grevlex leading coefficient, not by the first or largest-exponent term."""
        record = corpus.reduce_record(PROBLEM, entry('x-y^2'), 'a', 7)
        monic = corpus.basis_digest(record, [{(0, 2): 1, (1, 0): 6}])
        self.assertEqual(corpus.basis_digest(record, [{(0, 2): 2, (1, 0): 5}]), monic)
        self.assertNotEqual(corpus.basis_digest(record, [{(0, 2): 1, (1, 0): 1}]), monic)

    def test_grobx_basis_text_parses(self):
        """grobx's bracketed, colon-terminated basis text parses with non-negative residues."""
        text = '[y^2+18446744073709551556*x,\nx^2*y+18446744073709551554*x+1]:\n'
        self.assertEqual(corpus.parse_grobx_basis(text, ['x', 'y']),
                         [{(0, 2): 1, (1, 0): 18446744073709551556},
                          {(2, 1): 1, (1, 0): 18446744073709551554, (0, 0): 1}])

    def test_generator_text_round_trips(self):
        """Rendered reduced generators parse back to the record's equations."""
        record = corpus.reduce_record(PROBLEM, entry('3*x^2*y-y+7'), 'a', 11)
        text = corpus.generator_texts(record)
        self.assertEqual(corpus.parse_integer_polynomial(text[0], ['x', 'y']), {(2, 1): 3, (0, 1): 10, (0, 0): 7})


class Committed(unittest.TestCase):
    def test_catalog_is_current_and_valid(self):
        """The committed catalog equals a rebuild from inputs.json and every record validates."""
        run = subprocess.run([sys.executable, str(ROOT / 'tools/m34_public_corpus.py'), 'check'],
                             capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)

    def test_references_match_catalog_digests(self):
        """Every record has a reference row from its field's oracle, keyed to the input digest it used."""
        catalog = {r['id']: r for r in json.loads(corpus.CATALOG.read_text())}
        references = json.loads(corpus.REFERENCES.read_text())['references']
        self.assertEqual(set(references), set(catalog))
        for name, row in references.items():
            self.assertEqual(row['normalized_input_digest'], catalog[name]['normalized_input_digest'], name)
            self.assertIn(row['status'], ('reference', 'frontier'), name)
            small = int(catalog[name]['field']['characteristic']) < 2 ** 31
            self.assertEqual(row['oracle'], 'singular' if small else 'grobx-certified', name)

    def test_field_twins_agree_on_shape(self):
        """Where both fields have a reference, zero-dimensionality and vdim agree unless a coefficient vanished."""
        catalog = {r['id']: r for r in json.loads(corpus.CATALOG.read_text())}
        references = json.loads(corpus.REFERENCES.read_text())['references']
        for name, row in references.items():
            if not name.endswith('@p31') or row['status'] != 'reference':
                continue
            twin = references.get(name.replace('@p31', '@p64'))
            exceptional = any(t['kind'] == 'exceptional-reduction' for t in catalog[name]['transformations'])
            if twin and twin['status'] == 'reference' and not exceptional:
                self.assertEqual((row['dimension'] == 0, row['vdim']), (twin['zero_dimensional'], twin['vdim']), name)

    def test_staircase_counts_standard_monomials(self):
        """vdim is the number of monomials outside the leading-term ideal, None when it is infinite."""
        self.assertEqual(corpus.staircase_size([(2, 0), (0, 2)]), 4)
        self.assertEqual(corpus.staircase_size([(2, 0), (1, 1), (0, 3)]), 4)
        self.assertEqual(corpus.staircase_size([(0, 0)]), 0)
        self.assertIsNone(corpus.staircase_size([(1, 1)]))


class Generators(unittest.TestCase):
    def test_chandrasekhar_clears_each_equation_denominator(self):
        """Chandrasekhar n=2 at c=51/50 is each H-equation row scaled by the lcm of its denominators."""
        entry = corpus.chandrasekhar_h(n=2, c=[51, 50])
        self.assertEqual(entry['variables'], ['H1', 'H2'])
        self.assertEqual(corpus.parse_integer_polynomial(entry['equations'][0], entry['variables']),
                         {(1, 0): 400, (2, 0): -51, (1, 1): -34, (0, 0): -400})
        self.assertEqual(entry['excluded_primes'], [2, 5])

    def test_chandrasekhar_excluded_primes_are_the_small_denominator_primes(self):
        """At n=13 the excluded primes are the reduced denominators' factors: 17 cancels against c = 51/50."""
        excluded = corpus.chandrasekhar_h(n=13, c=[51, 50])['excluded_primes']
        self.assertEqual(excluded, [2, 3, 5, 7, 11, 13, 19, 23])

    def test_phosphorylation_is_square_and_conserves_mass(self):
        """The n-site steady state has 3n+3 equations in 3n+3 species, three of them conservation laws."""
        for n in (1, 3):
            entry = corpus.multisite_phosphorylation(n=n)
            self.assertEqual(len(entry['variables']), 3 * n + 3)
            self.assertEqual(len(entry['equations']), 3 * n + 3)
        entry = corpus.multisite_phosphorylation(n=1)
        index = entry['variables'].index
        total = corpus.parse_integer_polynomial(entry['equations'][-1], entry['variables'])
        linear = {k for k in total if sum(k) == 1}
        self.assertEqual({k.index(1) for k in linear},
                         {index(v) for v in ('S0', 'S1', 'ES0', 'FS1')})

    def test_rabinowitsch_variant_appends_the_inequation(self):
        """The nonzero variant adds t and t*E*F*S0*...*Sn - 1 to the parent's equations unchanged."""
        parent = corpus.multisite_phosphorylation(n=1)
        child = corpus.multisite_phosphorylation(n=1, nonzero=True)
        self.assertEqual(child['variables'], parent['variables'] + ['t'])
        self.assertEqual(child['equations'][:-1], parent['equations'])
        self.assertEqual(child['equations'][-1], 't*E*F*S0*S1-1')
        self.assertIn('rabinowitsch-augmentation', [t['kind'] for t in child['transformations']])

    def test_composition_counts_scales_per_family(self):
        """The #1007 hand-off groups base problems by family, with distinct n as scales and frontier rows counted."""
        panel = dict(problems=[
            dict(id='a1', family_id='A', source_id='s1', family_parameters=dict(n=3)),
            dict(id='a2', family_id='A', source_id='s1', family_parameters=dict(n=4)),
            dict(id='b1', family_id='B', source_id='s2', family_parameters=dict(n=5))])
        references = {'a1@p31': dict(status='reference'), 'a2@p31': dict(status='frontier'),
                      'b1@p31': dict(status='reference'), 'a2@p64': dict(status='frontier')}
        summary = corpus.composition(panel, references)
        self.assertEqual(summary['base_problems'], 3)
        self.assertEqual(summary['families']['A'], dict(base_problems=2, scales=[3, 4], sources=['s1'],
                                                        multi_scale=True, frontier={'p31': 1, 'p64': 1}))
        self.assertFalse(summary['families']['B']['multi_scale'])

    def test_reduction_refuses_a_prime_dividing_a_denominator(self):
        """A prime that divides a cleared denominator cannot reduce the rational system."""
        entry = dict(corpus.chandrasekhar_h(n=2, c=[51, 50]), url='u', revision='r', license='l')
        with self.assertRaises(ValueError):
            corpus.reduce_record(PROBLEM, entry, 'p5', 5)
        record = corpus.reduce_record(PROBLEM, entry, 'p7', 7)
        self.assertEqual([t['kind'] for t in record['transformations']],
                         ['parameter-specialization', 'clear-denominators', 'prime-reduction'])


if __name__ == '__main__':
    unittest.main()
