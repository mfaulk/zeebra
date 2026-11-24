import importlib.util
import json
import unittest
from pathlib import Path

_spec = importlib.util.spec_from_file_location('gate997', Path(__file__).with_name('gate997.py'))
g = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(g)

PREREG = json.loads(Path(__file__).with_name('gate997.json').read_text())


class Preregistration(unittest.TestCase):
    def test_the_committed_thresholds_are_the_owner_decision(self):
        """The committed preregistration carries #1043's decision: Cyclic-8 on GF(32003) and
        2^64-353 at 1, 4 and 16 w with every upper bound <= 1.05, MQ10 on GF(2^31-1) at 4 w, n = 9."""
        self.assertEqual(PREREG['owner_decision'],
                         'https://github.com/mfaulk/zeebra/issues/1043#issuecomment-7135042005')
        jobs = {j['name']: j for j in PREREG['jobs']}
        self.assertEqual(sorted(jobs['cyclic8']['rows']), ['grevlex/gf32003/cyclic-8', 'grevlex/wide64/cyclic-8'])
        self.assertEqual(jobs['cyclic8']['workers'], [1, 4, 16])
        self.assertEqual(jobs['cyclic8']['pass'], 'every upper <= 1.05')
        self.assertEqual(jobs['mq10']['rows'], ['grevlex/m31/mq-random-10-s10'])
        self.assertEqual(jobs['mq10']['workers'], [4])
        self.assertEqual(jobs['mq10']['pass'], 'upper < 1')
        self.assertEqual(PREREG['repetitions'], 9)

    def test_manifests_follow_the_preregistration(self):
        """Each manifest is publication mode on CCDs 1-2, n = 9, arms interleaved, with exactly the
        shipping F4 and the fewest-fl arm on exactly the preregistered rows and workers."""
        for job in PREREG['jobs']:
            m = g.manifest(job, harness_bin=__file__, agent='test')
            self.assertEqual(m['mode'], 'publication')
            self.assertEqual(m['run']['cpus'], '8-23')
            self.assertEqual(m['run']['repetitions'], 9)
            self.assertEqual(m['run']['interleave'], 'rotate')
            self.assertEqual(m['run']['workers'], job['workers'])
            self.assertEqual([a['name'] for a in m['arms']], ['z0-f4', 'z0-fewest-fl'])
            self.assertEqual(sorted(i['name'] for i in m['instances']), sorted(job['rows']))


class Verdict(unittest.TestCase):
    def rec(self, engine, rep, wall, digest='r', contaminated=False, status='ok'):
        return dict(engine=engine, rep=rep, job='j', wall_ns=wall, status=status, contaminated=contaminated,
                    report=dict(status='complete', basis_m33=digest))

    def cell(self, ratio, n=9):
        return [self.rec('f4', k, 1000) for k in range(n)] + [self.rec('fewest-fl', k, 1000 * ratio) for k in range(n)]

    def test_cyclic8_passes_at_or_under_the_bar_and_fails_over_it(self):
        """A Cyclic-8 cell passes when its paired upper bound is at most 1.05 and fails above it."""
        self.assertEqual(g.cell_verdict(self.cell(1.0), 'r', 'every upper <= 1.05')['verdict'], 'pass')
        self.assertEqual(g.cell_verdict(self.cell(1.2), 'r', 'every upper <= 1.05')['verdict'], 'fail')

    def test_mq10_passes_only_on_a_win(self):
        """The MQ10 regime read passes only when the paired upper bound is under 1."""
        self.assertEqual(g.cell_verdict(self.cell(0.9), 'r', 'upper < 1')['verdict'], 'pass')
        self.assertEqual(g.cell_verdict(self.cell(1.0), 'r', 'upper < 1')['verdict'], 'fail')

    def test_only_clean_reference_equal_attempts_count(self):
        """Contaminated attempts and attempts whose digest differs from the reference are dropped, and a
        cell short of 9 counted pairs is not read."""
        recs = self.cell(1.0)
        recs[0]['contaminated'] = True
        recs[-1]['report']['basis_m33'] = 'wrong'
        v = g.cell_verdict(recs, 'r', 'every upper <= 1.05')
        self.assertEqual(v['pairs'], 7)
        self.assertEqual(v['verdict'], 'short')

    def test_admission_needs_both_reads(self):
        """#997 is admitted only if every Cyclic-8 cell and the MQ10 read pass; a Cyclic-8 failure
        rejects it, and an MQ10 read that does not pass defers it."""
        self.assertEqual(g.decision(['pass'] * 6, 'pass'), 'admit')
        self.assertEqual(g.decision(['pass'] * 5 + ['fail'], 'pass'), 'reject')
        self.assertEqual(g.decision(['pass'] * 6, 'fail'), 'defer')
        self.assertEqual(g.decision(['pass'] * 5 + ['short'], 'pass'), 'defer')


if __name__ == '__main__':
    unittest.main()
