#!/usr/bin/env python3
"""Reference regeneration validates the complete identity set before changing committed evidence."""
import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location('public_corpus', Path(__file__).resolve().parents[1] / 'external/public-corpus.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


def attempts():
    result = []
    for family, n, tier in [('eco', 4, 'Smoke'), ('noon', 3, 'Smoke'), ('reimer', 3, 'Smoke'), ('eco', 8, 'Performance'), ('noon', 6, 'Performance'), ('reimer', 5, 'Performance')]:
        text = f'field prime 32003\norder grevlex\nvariables x1\ngenerator x1\n{family} {n}\n'
        result.append({'report': dict(name=f'public-{family}-{n}', family=family, variables=[f'x{i}' for i in range(1,n+1)], tier=tier,
                                     engine='singular', version='singular build 44105', status='complete', modulus=32003,
                                     canonical=text, digest=hashlib.sha256(text.encode()).hexdigest(), basis=['x1'], quotient_dimension=1)})
    return result


class RegenerationTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.previous = module.ROOT
        module.ROOT = Path(self.tmp.name)
        (module.ROOT / 'src/grobner/external/public_corpus_references').mkdir(parents=True)

    def tearDown(self):
        module.ROOT = self.previous
        self.tmp.cleanup()

    # An invalid final oracle answer cannot partially overwrite earlier valid references.
    def test_preflight_is_transactional(self):
        data = attempts()
        data[-1]['report']['version'] = 'unknown oracle'
        with self.assertRaises(ValueError):
            module.regenerate(data)
        self.assertEqual(list((module.ROOT / 'src/grobner/external/public_corpus_references').iterdir()), [])

    # Changing the declared field or canonical digest is rejected before a reference is committed.
    def test_wrong_identity_is_rejected(self):
        for key, value in [('modulus', 17), ('digest', 'not-the-input-hash')]:
            with self.subTest(key=key), self.assertRaises(ValueError):
                data = attempts()
                data[0]['report'][key] = value
                module.regenerate(data)

    # Complete valid evidence records each basis and its hash with its original ordered input identity.
    def test_valid_references_bind_the_input_and_basis(self):
        data = attempts()
        module.regenerate(data)
        text = (module.ROOT / 'src/grobner/external/public_corpus_cases.rs').read_text()
        self.assertIn(data[0]['report']['digest'], text)
        self.assertIn(hashlib.sha256(b'x1\n').hexdigest(), text)
        self.assertEqual(len(list((module.ROOT / 'src/grobner/external/public_corpus_references').iterdir())), 6)


if __name__ == '__main__':
    unittest.main()
