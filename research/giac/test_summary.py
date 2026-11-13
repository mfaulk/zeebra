import unittest
from summary import canonical_basis, instance_digest, verify_attempt


class GiacArtifacts(unittest.TestCase):
    # Polynomial normalization distinguishes changed coefficients while ignoring term order and signs modulo p.
    def test_exact_coefficients(self):
        self.assertEqual(canonical_basis(['x1+x10-1'], 13), canonical_basis(['12+x10+x1'], 13))
        self.assertNotEqual(canonical_basis(['x1+x10-1'], 13), canonical_basis(['x1+x10-2'], 13))

    # Frozen input identities cover ordered variables and every generator coefficient.
    def test_input_identity(self):
        a = dict(modulus=13, variables=['x1','x10'], generators=['x1+x10-1'])
        self.assertNotEqual(instance_digest(a), instance_digest(dict(a, variables=['x10','x1'])))
        self.assertNotEqual(instance_digest(a), instance_digest(dict(a, generators=['x1+x10-2'])))
        self.assertNotEqual(instance_digest(a), instance_digest(dict(a, transformation='seed 1')))

    # A successful board row without the independent complete answer is refused offline.
    def test_missing_independent_answer(self):
        a = dict(modulus=13, variables=['x1'], generators=['x1-1'], basis=['x1-1'],
                 independent_outputs=[], status_detail='full-basis-verified')
        attempt = dict(rows=[dict(problem_digest=instance_digest(a), outcome='verified',
            field=dict(characteristic=13), order='grevlex', limits=dict(workers=1))], artifacts=a)
        with self.assertRaises(ValueError):
            verify_attempt(attempt)


    # A verified basis cannot be relabeled as a different task or monomial order.
    def test_task_and_order_are_bound(self):
        a = dict(modulus=13, variables=['x1'], generators=['x1-1'], basis=['x1-1'],
                 independent_outputs=['@gensize 1\n@gen x1-1\n@gbsize 1\n@gb x1-1\n@done\n'],
                 status_detail='full-basis-verified')
        row = dict(problem_digest=instance_digest(a), outcome='verified',
                   field=dict(characteristic=13), order='grevlex', task='reduced-grobner-basis',
                   limits=dict(workers=1), invariants=dict(basis_cardinality=1))
        self.assertTrue(verify_attempt(dict(rows=[row], artifacts=a)))
        row['order'] = 'lex'
        with self.assertRaises(ValueError):
            verify_attempt(dict(rows=[row], artifacts=a))


if __name__ == '__main__':
    unittest.main()
