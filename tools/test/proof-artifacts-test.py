import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location('proof_artifacts', Path(__file__).parents[1] / 'external/proof_artifacts.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class ProofArtifacts(unittest.TestCase):
    # Repeated proof literals are stored once and reconstruct each original response byte for byte.
    def test_lossless_deduplication(self):
        proof = '[[x^2+7*y, "quoted",\\literal\nλ]]'
        raw = [json.dumps({'cofactors': proof, 'time': n}, ensure_ascii=False, separators=(',', ':')) + '\n' for n in range(2)]
        attempts = [{'artifacts': {'raw_output': value}} for value in raw]
        with tempfile.TemporaryDirectory() as scratch:
            output = Path(scratch) / 'cohort.json'
            module.pack_attempts(attempts, output)
            self.assertEqual(len(list(Path(scratch).rglob('*.gz'))), 1)
            for attempt, expected in zip(attempts, raw):
                self.assertEqual(module.restore_response(attempt['artifacts'], output.parent), expected)
                self.assertNotIn('raw_output', attempt['artifacts'])

    # Small raw results and absent outputs remain readable without a proof sidecar.
    def test_small_and_absent_responses(self):
        attempts = [{'artifacts': {'raw_output': '{}\n'}}, {'artifacts': {'raw_output': None}}]
        with tempfile.TemporaryDirectory() as scratch:
            module.pack_attempts(attempts, Path(scratch) / 'cohort.json')
            self.assertEqual(module.restore_response(attempts[0]['artifacts'], Path(scratch)), '{}\n')
            self.assertIsNone(module.restore_response(attempts[1]['artifacts'], Path(scratch)))

    # Compressed cohort files remain readable with their lossless proof references.
    def test_compressed_cohort_roundtrip(self):
        value = {'attempts': [{'artifacts': {'raw_output': '{}\n'}}]}
        with tempfile.TemporaryDirectory() as scratch:
            output = Path(scratch) / 'cohort.json.gz'
            module.write_cohort(output, value)
            self.assertEqual(module.load_cohort(output), value)

    # A corrupted compressed proof is rejected before reconstruction can masquerade as the original.
    def test_payload_hash_is_checked(self):
        import gzip
        attempts = [{'artifacts': {'raw_output': json.dumps({'certificate': 'ab' * 5000})}}]
        with tempfile.TemporaryDirectory() as scratch:
            output = Path(scratch) / 'cohort.json'
            module.pack_attempts(attempts, output)
            payload = next(Path(scratch).rglob('*.gz'))
            payload.write_bytes(gzip.compress(b'"forged"'))
            with self.assertRaises(ValueError):
                module.restore_response(attempts[0]['artifacts'], output.parent)


class OptionalPayloadTests(unittest.TestCase):
    # Optional string and list bases round-trip while repeated JSON literals share one sidecar.
    def test_optional_basis_literals(self):
        for basis in ('[x+1,y^2]:\n', ['x+1', 'y^2']):
            raw = [json.dumps({'basis': basis, 'clock': n}, ensure_ascii=False) + '\n' for n in range(2)]
            attempts = [{'artifacts': {'raw_output': value}} for value in raw]
            with self.subTest(basis=basis), tempfile.TemporaryDirectory() as scratch:
                output = Path(scratch) / 'cohort.json.gz'
                module.pack_attempts(attempts, output, keys=('basis',))
                self.assertEqual(len(list(Path(scratch).rglob('*.gz'))), 1)
                self.assertEqual([module.restore_response(a['artifacts'], output.parent) for a in attempts], raw)

    # Default proof packing still ignores basis payloads and non-string proof values.
    def test_default_contract_is_unchanged(self):
        attempts = [{'artifacts': {'raw_output': json.dumps({'basis': ['x'], 'cofactors': ['proof']})}}]
        expected = copy.deepcopy(attempts)
        with tempfile.TemporaryDirectory() as scratch:
            module.pack_attempts(attempts, Path(scratch) / 'cohort.json')
            self.assertEqual(attempts, expected)
            self.assertFalse(list(Path(scratch).rglob('*.gz')))


class StudyArtifactsTests(unittest.TestCase):
    @staticmethod
    def helper():
        spec = importlib.util.spec_from_file_location('study_artifacts', Path(__file__).parents[1] / 'external/study_artifacts.py')
        helper = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(helper)
        return helper

    # Packing preserves exact stdout, parsed raw data, failures and all existing metadata.
    def test_lossless_study_roundtrip(self):
        helper = self.helper()
        cohort = {'commit': 'revision', 'attempts': []}
        for n in range(2):
            raw = {'basis': ['x+λ', 'y^2'], 'clock': n}
            stdout = '  ' + json.dumps(raw, ensure_ascii=False) + '\n'
            cohort['attempts'].append({'status': 'verified', 'raw': raw, 'stdout': stdout,
                                       'artifacts': {'existing': {'n': n}}, 'command': ['engine']})
        cohort['attempts'].append({'status': 'failed', 'stdout': 'unparsed output',
                                   'raw': None, 'stop': 'wall', 'stderr': 'reason'})
        original = copy.deepcopy(cohort)
        with tempfile.TemporaryDirectory() as scratch:
            output = Path(scratch) / 'study.json.gz'
            helper.pack_study(cohort, output)
            self.assertEqual(cohort, original)
            packed = module.load_cohort(output)
            self.assertNotIn('raw', packed['attempts'][0])
            self.assertNotIn('stdout', packed['attempts'][0])
            self.assertEqual(helper.load_study(output), original)
            self.assertEqual(len(list(Path(scratch).rglob('*.json-string.gz'))), 1)

    # Absent artifacts and an explicitly empty artifacts mapping remain distinguishable after loading.
    def test_artifacts_presence_roundtrips(self):
        helper = self.helper()
        raw = {'basis': '[x]:\n'}
        first = {'status': 'verified', 'raw': raw, 'stdout': json.dumps(raw)}
        second = dict(first, artifacts={})
        cohort = {'attempts': [first, second]}
        with tempfile.TemporaryDirectory() as scratch:
            output = Path(scratch) / 'study.json'
            helper.pack_study(cohort, output)
            self.assertEqual(helper.load_study(output), cohort)

    # A successful attempt cannot pack a stdout stream that differs from its parsed result.
    def test_inconsistent_stdout_is_rejected(self):
        helper = self.helper()
        cohort = {'attempts': [{'status': 'verified', 'raw': {'basis': ['x']},
                               'stdout': '{"basis":["y"]}'}]}
        with tempfile.TemporaryDirectory() as scratch, self.assertRaisesRegex(ValueError, 'stdout'):
            helper.pack_study(cohort, Path(scratch) / 'study.json')


if __name__ == '__main__':
    unittest.main()
