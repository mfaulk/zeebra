import hashlib
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parents[1] / 'tools/external'))
import admission  # noqa: E402
import basis_digest  # noqa: E402


def record(track, name, admitted=True):
    return dict(track=track, field='m31', name=name, digest=name, admitted=admitted, basis_m33=['d'])


class Draw(unittest.TestCase):
    def test_key_is_the_plans_hash(self):
        """The draw key is SHA-256 of "M33-holdout", the track and the input digest, concatenated."""
        self.assertEqual(admission.draw_key('G', 'ab'), hashlib.sha256(b'M33-holdoutGab').hexdigest())

    def test_first_two_admitted_in_order(self):
        """The draw takes the first two admitted candidates of the track, in record order."""
        records = [record('M', 'eco-10', False), record('M', 'katsura-8'), record('G', 'eco-13'),
                   record('M', 'cyclic-8'), record('M', 'noon-9')]
        self.assertEqual([r['name'] for r in admission.drawn(records, 'M')], ['katsura-8', 'cyclic-8'])

    def test_at_most_one_mq(self):
        """A second admitted MQ row is passed over for the next non-MQ row."""
        records = [record('G', 'mq-random-9-s3'), record('G', 'mq-random-10-s1'), record('G', 'eco-13')]
        self.assertEqual([r['name'] for r in admission.drawn(records, 'G')], ['mq-random-9-s3', 'eco-13'])
        self.assertTrue(admission.skip_mq(records[:1], 'G', dict(name='mq-random-11-s2')))

    def test_pool_uses_fresh_mq_seeds_only(self):
        """Every MQ candidate carries a seed in 1–8; the historical rule was seed = n ≥ 9."""
        seeds = [int(n.rsplit('-s', 1)[1]) for n in admission.FAMILIES if n.startswith('mq-random')]
        self.assertEqual(sorted(set(seeds)), list(range(1, 9)))

    def test_prior_names_scans_text(self):
        """Family sizes named anywhere in a prior document are collected; seeded names reduce to the size."""
        with tempfile.TemporaryDirectory() as d:
            Path(d, 'a.md').write_text('Katsura: katsura-11 and eco-12, not katsura-x')
            self.assertEqual(admission.prior_names([Path(d)]), {'katsura-11', 'eco-12'})
        self.assertEqual(admission.family_size('mq-random-10-s3'), 'mq-random-10')


class Digest(unittest.TestCase):
    def test_vector_shared_with_rust(self):
        """The vector `examples/support/basis_digest.rs` asserts; element order and scaling do not matter."""
        texts = ['2*x1*x2+4', 'x2^2+32002', 'x1^2+3*x2']
        want = '8fb196a0f7de4f7d36d2d8c6b34fb80eebd5f04658fcc799e1f2583781e5fefc'
        self.assertEqual(basis_digest.basis_digest(texts, 32003, ['x1', 'x2']), want)
        self.assertEqual(basis_digest.basis_digest(texts[::-1], 32003, ['x1', 'x2']), want)

    def test_encoding(self):
        """Exponents are LEB128, the coefficient decimal and `;`, elements u32-length-prefixed."""
        import struct
        self.assertEqual(basis_digest.leb128(300), bytes([0xac, 0x02]))
        got = basis_digest.digest_canonical([(((2, 0), 1),), (((1, 0), 3), ((1, 1), 1))], 7, 2)
        a, b = bytes([2, 0]) + b'1;', bytes([1, 0]) + b'3;' + bytes([1, 1]) + b'1;'
        body = b''.join(struct.pack('<I', len(e)) + e for e in sorted([a, b]))
        self.assertEqual(got, hashlib.sha256(b'm33-basis-v1 7 2\n' + body).hexdigest())

    def test_solver_spellings_agree(self):
        """msolve's explicit `1*x^1` spelling and a negative coefficient digest as the plain text does."""
        plain = basis_digest.basis_digest(['x1^2+3*x2', 'x2^2+32002'], 32003, ['x1', 'x2'])
        self.assertEqual(basis_digest.basis_digest(['1*x1^2+3*x2^1', 'x2^2-1'], 32003, ['x1', 'x2']), plain)

    def test_grobx_digest_only_reply(self):
        """A digest-only grobx reply (#1020) yields its `basis_m33`, under the full reply's conditions."""
        import json
        case = dict(modulus='7', variables=['x', 'y'])
        basis = '[y^2+x,\nx*y+6,\nx^2+y]:\n'
        want = admission.grobx_digest(json.dumps(dict(basis=basis, stopped=None, certified=True)), case, 'certified')
        reply = dict(basis=None, basis_m33=want, stopped=None, certified=True)
        self.assertEqual(admission.grobx_digest(json.dumps(reply), case, 'certified'), want)
        for spoiled in (dict(certified=None), dict(stopped='deadline'), dict(basis_m33=None)):
            self.assertIsNone(admission.grobx_digest(json.dumps(dict(reply, **spoiled)), case, 'certified'))
        self.assertEqual(admission.grobx_digest(json.dumps(dict(reply, certified=None)), case), want)


if __name__ == '__main__':
    unittest.main()
