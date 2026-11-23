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


class Committed(unittest.TestCase):
    def test_catalog_is_current_and_valid(self):
        """The committed catalog equals a rebuild from inputs.json and every record validates."""
        run = subprocess.run([sys.executable, str(ROOT / 'tools/m34_public_corpus.py'), 'check'],
                             capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)

    def test_references_match_catalog_digests(self):
        """Every reference row names a record below 2^31 and the input digest it was computed from."""
        catalog = {r['id']: r for r in json.loads(corpus.CATALOG.read_text())}
        references = json.loads(corpus.REFERENCES.read_text())['references']
        small = {i for i, r in catalog.items() if int(r['field']['characteristic']) < 2 ** 31}
        self.assertEqual(set(references), small)
        for name, row in references.items():
            self.assertEqual(row['normalized_input_digest'], catalog[name]['normalized_input_digest'], name)
            self.assertIn(row['status'], ('reference', 'frontier'), name)


if __name__ == '__main__':
    unittest.main()
