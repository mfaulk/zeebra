import importlib.util
from pathlib import Path
import unittest
import tempfile
import gzip
import json

spec = importlib.util.spec_from_file_location('wide', Path(__file__).parents[1] / 'external/wide-corpus.py')
wide = importlib.util.module_from_spec(spec)
spec.loader.exec_module(wide)

class WideCorpusTests(unittest.TestCase):
    # Full basis equality rejects matching leading monomials with different tail coefficients.
    def test_changed_tail_is_rejected(self):
        with self.assertRaises(ValueError):
            wide.verify_bases([{'report': {'status': 'complete', 'basis': ['x1+1']}},
                               {'report': {'status': 'complete', 'basis': ['x1+2']}}])

    # A startup-dominated wall comparison never publishes a ratio.
    def test_floor_gate(self):
        self.assertIsNone(wide.wall_ratio(1.0, 1.5, 0.001, 1.0))
        self.assertEqual(wide.wall_ratio(2.0, 4.0, 0.001, 1.0), 0.5)

    # Julia wall comparisons use the supervised process stage rather than its warmed F4 call.
    def test_julia_uses_process_wall(self):
        a = {'process_wall_ns': 9_000_000_000, 'report': {'engine': 'groebner.jl',
             'engine_wall_ns': 100_000_000, 'solver_process_wall_ns': 5_000_000_000}}
        self.assertEqual(wide.seconds(a), 5)

    # Residue and scalar representations normalize to the same monic polynomial.
    def test_polynomial_normalization(self):
        self.assertEqual(wide.canonical_polynomial('2*x1+2*x2-2', 13, ['x1','x2']),
                         wide.canonical_polynomial('12+x2+x1', 13, ['x1','x2']))
        with self.assertRaises(ValueError):
            wide.canonical_polynomial('x3+1', 13, ['x1','x2'])

    # A native driver cannot substitute a different ring or generator list.
    def test_native_driver_identity_is_checked(self):
        request = {'variables': ['x1'], 'modulus': 13, 'order': 'grevlex',
                   'workers': 1, 'generators': ['x1+1']}
        raw = dict(request, contract=2, revision=wide.REVISIONS['groebner-rs'],
                   isa='x86-64-v3', build='abc', build_metadata='PROFILE=release;OPT_LEVEL=3;CARGO_PROFILE_RELEASE_LTO=fat;CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1;',
                   basis=['x1+1'])
        self.assertEqual(wide.validate_native(raw, request, 'groebner-rs'), ['x1+1'])
        with self.assertRaises(ValueError):
            wide.validate_native(dict(raw, modulus=17), request, 'groebner-rs')
        with self.assertRaises(ValueError):
            wide.validate_native(dict(raw, generators=['x1+2']), request, 'groebner-rs')

    # A kernel peak above the ceiling remains a memory stop even if the polling loop missed it.
    def test_kernel_peak_cannot_escape_memory_limit(self):
        attempt = {'observed_tree_peak_bytes': 100, 'raw': {'kernel_peak_rss_bytes': 2**31+1},
                   'report': {'status': 'complete'}}
        wide.enforce_peak(attempt)
        self.assertEqual(attempt['report']['status'], 'stopped-by-limit')
        self.assertEqual(attempt['stop'], 'rss-2GiB-kernel')

    # Large retained responses round-trip through bounded, hash-checked repository payload files.
    def test_payload_storage_is_lossless_and_detects_corruption(self):
        cohort = {'commit': 'abc', 'attempts': [{'field': 'wide64', 'name': 'test',
                  'engine': 'zeebra', 'report': {'status': 'complete', 'basis': ['x1+1']}}]}
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'campaign.json.gz'
            wide.pack(cohort, path, chunk_size=32)
            self.assertEqual(wide.load(path), cohort)
            payload = next((path.parent / 'campaign-payloads').iterdir())
            payload.write_bytes(gzip.compress(b'corrupt', mtime=0))
            with self.assertRaises(ValueError):
                wide.load(path)

    # Native report copies share the retained raw basis without losing either restored response.
    def test_native_basis_copy_is_stored_once(self):
        basis = 'x1+' + '+'.join(str(i)+'*x2' for i in range(1,1000))
        for raw_basis in ([basis], '['+basis+']:\n'):
            with self.subTest(kind=type(raw_basis).__name__), tempfile.TemporaryDirectory() as directory:
                attempt = {'field':'wide64','name':'test','engine':'grobx',
                           'raw': {'basis':raw_basis}, 'report':{'basis':[basis]}}
                cohort = {'attempts':[attempt]}
                path = Path(directory) / 'campaign.json.gz'
                wide.pack(cohort, path)
                manifest = json.loads(gzip.decompress(path.read_bytes()))
                stored = sum(p['bytes'] for a in manifest['attempt_payloads'] for p in a['parts'])
                self.assertLess(stored, len(json.dumps(attempt)) - len(basis)//2)
                self.assertEqual(wide.load(path), cohort)

    # Controller updates require explicit continuation and preserve the originating stamp of every attempt.
    def test_compatible_controller_continuation_preserves_provenance(self):
        previous = {'commit':'old', 'attempts':[{'name':'done'}], 'binaries':{'z':'hash'},
                    'affinity':'2','machine':'host','policy':'60s'}
        current = dict(previous, commit='new', attempts=[])
        with self.assertRaises(ValueError):
            wide.resume_cohort(previous, current, False)
        resumed = wide.resume_cohort(previous, current, True)
        self.assertEqual(resumed['attempts'][0]['controller_commit'], 'old')
        self.assertEqual([c['commit'] for c in resumed['controllers']], ['old','new'])

    # A controller continuation cannot change the native binaries, host, affinity or resource policy.
    def test_controller_continuation_rejects_changed_instrument(self):
        previous = {'commit':'old', 'attempts':[], 'binaries':{'z':'hash'},
                    'affinity':'2','machine':'host','policy':'60s'}
        for key, value in [('binaries',{'z':'other'}), ('affinity','3'), ('machine','other'), ('policy','120s')]:
            with self.subTest(key=key), self.assertRaises(ValueError):
                wide.resume_cohort(previous, dict(previous, commit='new', **{key:value}), True)

    # A stopped attempt is retained without being treated as a completed oracle.
    def test_limit_is_not_an_oracle(self):
        self.assertEqual(wide.verify_bases([{'stop': 'wall'}]), 0)

    # Comparison cannot silently combine outputs from different frozen input identities.
    def test_different_identities_are_rejected(self):
        with self.assertRaises(ValueError):
            wide.verify_bases([{'digest': 'a'}, {'digest': 'b'}])

    # A changed canonical input cannot reuse its previous digest.
    def test_catalog_rejects_changed_bytes(self):
        c = {'field': 'bn254', 'name': 'katsura-4', 'canonical': 'prime 1', 'digest': '0'*64}
        with self.assertRaises(ValueError):
            wide.validate_catalog([c])

if __name__ == '__main__':
    unittest.main()
