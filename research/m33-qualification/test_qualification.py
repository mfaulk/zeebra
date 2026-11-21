import contextlib
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import campaign  # noqa: E402
import summarize  # noqa: E402


def record(arm, workers=1, rep=0, **report):
    version, _, engine = arm.partition('-')
    base = dict(status='complete', digest='in', basis_m33='b', threads_peak=0, route=None)
    return dict(arm=arm, version=version, engine=engine, workers=workers, rep=rep, status='ok',
                report=dict(base, **report), wall_ns=1, rss=1, contaminated=False)


REF = dict(input_digest='in', basis_m33='b', reference='Singular')


class GateDRefusal(unittest.TestCase):
    def gate_d(self, *argv, jobs=()):
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            return summarize.main(['gate-d', *jobs, *argv]), err.getvalue()

    def job(self, d, suite, f2):
        (Path(d) / 'manifest.json').write_text(json.dumps(dict(context=dict(suite=suite, f2=f2))))
        return d

    def test_gate_d_read_is_refused_without_both_flags(self):
        """The held-out read refuses to run unless --gate-d and --f2 are both given."""
        for argv in ([], ['--gate-d'], ['--f2', 'abcdef12']):
            rc, err = self.gate_d(*argv)
            self.assertEqual(rc, 2, argv)
            self.assertIn('refused', err)

    def test_gate_d_read_is_refused_for_another_job_or_commit(self):
        """A non-Gate-D job, or one pinned at another F2, is refused before its journal is read."""
        with tempfile.TemporaryDirectory() as a, tempfile.TemporaryDirectory() as b:
            for job, f2 in ((self.job(a, 'regression-G', 'abcdef12'), 'abcdef12'),
                            (self.job(b, 'gate-d-G', '12345678'), 'abcdef12')):
                rc, err = self.gate_d('--gate-d', '--f2', f2, jobs=[job])
                self.assertEqual(rc, 2)
                self.assertIn('is not a Gate D job', err)

    def test_gate_d_read_happens_once(self):
        """A second read is refused once gate-d.md exists."""
        with tempfile.TemporaryDirectory() as d:
            job = self.job(d, 'gate-d-M', 'abcdef12')
            with mock.patch.object(summarize, 'GATE_D', Path(d) / 'gate-d.md'):
                (Path(d) / 'gate-d.md').write_text('read')
                rc, err = self.gate_d('--gate-d', '--f2', 'abcdef12', jobs=[job])
        self.assertEqual(rc, 2)
        self.assertIn('has been read', err)

    def test_gate_d_manifest_is_refused_without_both_flags(self):
        """The Gate D manifest needs --gate-d and --f2; --gate-d is refused on any other suite."""
        base = ['manifest', '--f0-study', 'x', '--f2-study', 'x']
        for argv in (['--suite', 'gate-d-G'], ['--suite', 'gate-d-M', '--f2', 'abcdef12'],
                     ['--suite', 'gate-d-G', '--gate-d'], ['--suite', 'grevlex', '--gate-d', '--f2', 'abcdef12']):
            with self.assertRaises(SystemExit) as e, contextlib.redirect_stdout(io.StringIO()):
                campaign.main(base + argv)
            self.assertIn('gate-d', str(e.exception).lower(), argv)


class HeldOutGuard(unittest.TestCase):
    SUITES = ('grevlex', 'grlex', 'lex', 'regression-G', 'regression-M', 'small-G', 'small-M')

    def test_no_other_suite_names_a_held_out_row(self):
        """Correctness and regression rows exclude the four held-out rows by name."""
        for suite in self.SUITES:
            self.assertFalse([r for r in campaign.suite_rows(suite) if campaign.held_out(r)], suite)
        self.assertEqual(len(campaign.suite_rows('gate-d-G')) + len(campaign.suite_rows('gate-d-M')), 4)

    def test_a_row_reproducing_a_held_out_digest_is_refused(self):
        """A row whose input digest is a held-out row's is refused even under another name."""
        digest = campaign.HELD_OUT['G'][0]['digest']
        argv = ['manifest', '--suite', 'lex', '--f0-study', 'x', '--f2-study', 'x', '--f2', 'abcdef12']
        with mock.patch.object(campaign, 'case_of', return_value=dict(digest=digest)):
            with self.assertRaises(SystemExit) as e:
                campaign.main(argv)
        self.assertIn('held-out', str(e.exception))


class Correctness(unittest.TestCase):
    def test_agreeing_rows_pass(self):
        """Equal digests across arms, workers and repetitions, equal to the reference, pass."""
        rows = [record(a, w, k) for a in ('f0-entry', 'f2-entry') for w in (1, 16) for k in range(3)]
        self.assertEqual(summarize.correctness_failures('grevlex/m31/katsura-8', rows, REF), [])

    def test_a_changed_or_unreferenced_digest_fails(self):
        """A digest that moved at F2, or a row with no reference, fails."""
        rows = [record('f0-f4'), record('f2-f4', basis_m33='c')]
        self.assertIn('2 basis digests', summarize.correctness_failures('grevlex/w59/eco-9', rows, REF))
        self.assertIn('no reference digest', summarize.correctness_failures('grevlex/w59/eco-9', rows[:1], None))

    def test_lex_entry_must_refuse_and_graded_lex_must_route_to_f4(self):
        """Lex on the entry point is a typed refusal, and F2 sends graded-lex to F4 by rule."""
        lex = [record('f2-entry', status='refused', basis_m33=None), record('f2-entry', rep=1)]
        self.assertTrue(any('typed refusal' in w for w in summarize.correctness_failures('lex/gf2/katsura-4', lex, REF)))
        grlex = [record('f2-entry', route='Signature')]
        self.assertTrue(any('Order' in w for w in summarize.correctness_failures('grlex/m31/eco-11', grlex, REF)))
        routed = [record('f2-entry', route='Shipping(Order)')]
        self.assertEqual(summarize.correctness_failures('grlex/m31/eco-11', routed, REF), [])

    def test_threads_over_the_cap_and_changed_typed_outcomes_fail(self):
        """More threads than requested, or a typed stop that F2 turned into another, fails."""
        self.assertTrue(summarize.correctness_failures('grevlex/m31/katsura-8', [record('f2-f4', 1, threads_peak=2)], REF))
        stops = [record('f0-f4', status='stopped', basis_m33=None, error='TooManyLiveNonzeros { .. }'),
                 record('f2-f4', status='stopped', basis_m33=None, error='TimeBudgetExceeded { .. }')]
        self.assertTrue(any('outcomes' in w for w in summarize.correctness_failures('grlex/goldilocks/mq', stops, REF)))


class Regression(unittest.TestCase):
    def test_small_rows_pair_warm_calls(self):
        """Under the warm-call method each process contributes its median warm call, not its wall."""
        f0 = [dict(record('f0-entry', rep=k, calls_ns=[50, 10, 10, 10]), wall_ns=1000) for k in range(3)]
        f2 = [dict(record('f2-entry', rep=k, calls_ns=[90, 11, 11, 11]), wall_ns=1000) for k in range(3)]
        ratios, rss, _, excluded = summarize.paired(f0 + f2, small=True)
        self.assertEqual(ratios, [1.1, 1.1, 1.1])
        self.assertEqual((rss, excluded), (1.0, 0))
        self.assertEqual(summarize.paired(f0 + f2, small=False)[0], [1.0, 1.0, 1.0])

    def test_repetitions_from_two_jobs_pool(self):
        """A top-up job's rep 0 adds a pair beside the first job's rep 0 instead of replacing it."""
        recs = [dict(record(arm, rep=0), job=job, wall_ns=wall)
                for job, f0, f2 in (('a', 10, 11), ('b', 10, 12)) for arm, wall in (('f0-f4', f0), ('f2-f4', f2))]
        self.assertEqual(sorted(summarize.paired(recs, small=False)[0]), [1.1, 1.2])


if __name__ == '__main__':
    unittest.main()
