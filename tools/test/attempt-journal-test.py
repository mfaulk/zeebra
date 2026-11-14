import gzip
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location('attempt_journal', Path(__file__).parents[1] / 'external/attempt_journal.py')
aj = importlib.util.module_from_spec(spec)
spec.loader.exec_module(aj)

PLAN = [['katsura-11', 2147483647, 'basis', 'stage-off', r] for r in range(4)]
HEADER = dict(identity=dict(commit='c0ffee', binary_sha256='ab' * 32, affinity='0-3'),
              references={'katsura-11/2147483647': 'ref'})
LIMITS = dict(aggregate_wall_seconds=100.0, output_bytes=1 << 20)
# A whole-route child prints several JSON records; the journal must keep them byte for byte.
STDOUT = b'{"record":"identity","digest":"d"}\n{"record":"source"}\n{"record":"final","outcome":"basis"}\n'


def metadata(wall=1.5):
    return dict(process_wall_ns=int(wall * 1e9), wall_seconds=wall, cpu_seconds=1.25,
                observed_peak_rss_bytes=123456, exit=0, stop=None, guard=dict(kind='rss-guard', pid=42))


class AttemptJournalTest(unittest.TestCase):
    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory()
        self.dir = Path(self.scratch.name) / 'journal'

    def tearDown(self):
        self.scratch.cleanup()

    def create(self, plan=PLAN, limits=LIMITS):
        return aj.StudyJournal.create(self.dir, HEADER, plan, limits)

    # Exit metadata and raw output are durable and recovered exactly before any verdict is written.
    def test_interruption_after_child_exit_recovers_exact_metadata(self):
        j = self.create()
        j.record_exit(0, PLAN[0], STDOUT, b'warn\n', metadata())
        del j  # controller dies before parsing or checking
        state = aj.load(self.dir)
        (attempt,) = state['attempts']
        self.assertEqual(attempt['status'], 'unverified')
        self.assertEqual(attempt['metadata'], metadata())
        self.assertEqual(attempt['stdout'], STDOUT)
        self.assertEqual(attempt['stderr'], b'warn\n')

    # A verdict is a separate record bound to its exit record; verified and unverified stay distinct.
    def test_verdict_is_distinct_from_unverified(self):
        j = self.create()
        j.record_exit(0, PLAN[0], STDOUT, b'', metadata())
        j.record_verdict(0, 'verified', dict(checked='basis'))
        j.record_exit(1, PLAN[1], STDOUT, b'', metadata())
        statuses = [a['status'] for a in aj.load(self.dir)['attempts']]
        self.assertEqual(statuses, ['verified', 'unverified'])
        with self.assertRaises(ValueError):
            j.record_verdict(0, 'failed', {})

    # A crash while writing a payload leaves only a temporary file, which is never read as an attempt.
    def test_interruption_during_payload_write_is_not_an_attempt(self):
        j = self.create()
        j.record_exit(0, PLAN[0], STDOUT, b'', metadata())
        (self.dir / 'blobs' / 'partial.tmp').write_bytes(b'\x1f\x8b garbage')
        self.assertEqual(len(aj.load(self.dir)['attempts']), 1)
        reopened = aj.StudyJournal.open(self.dir, HEADER, PLAN, LIMITS)
        self.assertEqual(reopened.next_index, 1)

    # A torn final journal line is refused until it is explicitly quarantined, never silently dropped.
    def test_torn_journal_record_requires_explicit_quarantine(self):
        j = self.create()
        j.record_exit(0, PLAN[0], STDOUT, b'', metadata())
        with open(self.dir / 'journal.jsonl', 'ab') as f:
            f.write(b'{"kind":"exit","index":1,"meta')
        with self.assertRaisesRegex(ValueError, 'torn'):
            aj.load(self.dir)
        with self.assertRaisesRegex(ValueError, 'torn'):
            aj.StudyJournal.open(self.dir, HEADER, PLAN, LIMITS)
        reopened = aj.StudyJournal.open(self.dir, HEADER, PLAN, LIMITS, quarantine_torn=True)
        self.assertEqual(reopened.next_index, 1)
        quarantined = list(self.dir.glob('torn-*.partial'))
        self.assertEqual([p.read_bytes() for p in quarantined], [b'{"kind":"exit","index":1,"meta'])
        self.assertEqual(aj.load(self.dir)['quarantined'], [quarantined[0].name])

    # Interrupted publication leaves any earlier rendered cohort intact and a rerun is byte-identical.
    def test_render_is_atomic_and_deterministic(self):
        j = self.create()
        for i in range(2):
            j.record_exit(i, PLAN[i], STDOUT, b'', metadata())
            j.record_verdict(i, 'verified', {})
        out = Path(self.scratch.name) / 'cohort.json.gz'
        aj.render(self.dir, out)
        first = out.read_bytes()
        out.with_name(out.name + '.tmp').write_bytes(b'interrupted publication')
        aj.render(self.dir, out)
        self.assertEqual(out.read_bytes(), first)
        cohort = json.loads(gzip.decompress(first))
        self.assertEqual(cohort['identity'], HEADER['identity'])
        self.assertEqual(cohort['attempts'][1]['stdout'], STDOUT.decode())
        self.assertEqual(cohort['attempts'][1]['metadata'], metadata())
        self.assertEqual(cohort['journal_sha256'], aj.load(self.dir)['journal_sha256'])

    # A changed payload, a missing payload and an edited journal record are each rejected.
    def test_corruption_and_missing_payloads_are_rejected(self):
        j = self.create()
        j.record_exit(0, PLAN[0], STDOUT, b'err', metadata())
        blobs = sorted((self.dir / 'blobs').glob('*.gz'))
        original = blobs[0].read_bytes()
        blobs[0].write_bytes(gzip.compress(b'tampered', mtime=0))
        with self.assertRaisesRegex(ValueError, 'payload'):
            aj.load(self.dir)
        blobs[0].unlink()
        with self.assertRaisesRegex(ValueError, 'payload'):
            aj.load(self.dir)
        blobs[0].write_bytes(original)
        aj.load(self.dir)
        journal = self.dir / 'journal.jsonl'
        journal.write_bytes(journal.read_bytes().replace(b'"cpu_seconds":1.25', b'"cpu_seconds":0.25'))
        with self.assertRaisesRegex(ValueError, 'chain'):
            aj.load(self.dir)

    # The accepted prefix is append-only in plan order and a reopen must match the frozen identity.
    def test_immutable_prefix_and_frozen_identity(self):
        j = self.create()
        j.record_exit(0, PLAN[0], STDOUT, b'', metadata())
        with self.assertRaisesRegex(ValueError, 'index'):
            j.record_exit(0, PLAN[0], STDOUT, b'', metadata())
        with self.assertRaisesRegex(ValueError, 'index'):
            j.record_exit(2, PLAN[2], STDOUT, b'', metadata())
        with self.assertRaisesRegex(ValueError, 'plan'):
            j.record_exit(1, PLAN[2], STDOUT, b'', metadata())
        changed = dict(HEADER, identity=dict(HEADER['identity'], binary_sha256='cd' * 32))
        with self.assertRaisesRegex(ValueError, 'identity'):
            aj.StudyJournal.open(self.dir, changed, PLAN, LIMITS)
        with self.assertRaisesRegex(ValueError, 'identity'):
            aj.StudyJournal.open(self.dir, HEADER, PLAN[::-1], LIMITS)
        with self.assertRaises(FileExistsError):
            self.create()

    # Missing exit metadata cannot be recorded, so lost timing is never reconstructed.
    def test_incomplete_metadata_is_refused(self):
        j = self.create()
        partial = metadata()
        del partial['cpu_seconds']
        with self.assertRaisesRegex(ValueError, 'cpu_seconds'):
            j.record_exit(0, PLAN[0], STDOUT, b'', partial)
        self.assertEqual(aj.load(self.dir)['attempts'], [])

    # Cumulative child wall and retained bytes survive a reopen and refuse the next launch once spent.
    def test_cumulative_budget_refusal_survives_reopen(self):
        j = self.create(limits=dict(aggregate_wall_seconds=3.0, output_bytes=1 << 20))
        j.record_exit(0, PLAN[0], STDOUT, b'', metadata(wall=2.0))
        self.assertIsNone(j.refusal(next_child_wall_seconds=0.5))
        reopened = aj.StudyJournal.open(self.dir, HEADER, PLAN, dict(aggregate_wall_seconds=3.0, output_bytes=1 << 20))
        self.assertAlmostEqual(reopened.child_wall_seconds, 2.0)
        self.assertEqual(reopened.refusal(next_child_wall_seconds=1.5)['reason'], 'aggregate-wall')
        tiny = aj.StudyJournal.open(self.dir, HEADER, PLAN, dict(aggregate_wall_seconds=3.0, output_bytes=1 << 20))
        tiny.limits = dict(tiny.limits, output_bytes=reopened.retained_bytes)
        self.assertEqual(tiny.refusal(next_child_wall_seconds=0.1)['reason'], 'output-bytes')
        reopened.record_stop('aggregate-wall', child_wall_seconds=2.0)
        with self.assertRaisesRegex(ValueError, 'stopped'):
            reopened.record_exit(1, PLAN[1], STDOUT, b'', metadata())
        self.assertEqual(aj.load(self.dir)['stop']['reason'], 'aggregate-wall')

    # Bytes written per attempt stay constant as the cohort grows, unlike a full-cohort rewrite.
    def test_write_volume_is_linear(self):
        n = 200
        plan = [['mq', 31, 'basis', 'stage-off', r] for r in range(n)]
        j = self.create(plan=plan, limits=dict(aggregate_wall_seconds=1e9, output_bytes=1 << 30))
        per_attempt = []
        for i in range(n):
            before = j.bytes_written
            out = STDOUT + (b'{"basis":"%d"}\n' % i) * 50
            j.record_exit(i, plan[i], out, b'', metadata())
            j.record_verdict(i, 'verified', {})
            per_attempt.append(j.bytes_written - before)
        self.assertLess(max(per_attempt[-20:]), 2 * max(per_attempt[:20]))
        self.assertLess(j.bytes_written, 2 * n * max(per_attempt[:20]) + 4096)
        self.assertEqual(len(aj.load(self.dir)['attempts']), n)

    # Identical payloads are stored once and still restored for every attempt that produced them.
    def test_content_addressed_payloads_deduplicate(self):
        j = self.create()
        for i in range(3):
            j.record_exit(i, PLAN[i], STDOUT, b'', metadata())
        self.assertEqual(len(list((self.dir / 'blobs').glob('*.gz'))), 2)
        self.assertTrue(all(a['stdout'] == STDOUT for a in aj.load(self.dir)['attempts']))


if __name__ == '__main__':
    unittest.main()
