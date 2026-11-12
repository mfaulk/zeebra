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


if __name__ == '__main__':
    unittest.main()
