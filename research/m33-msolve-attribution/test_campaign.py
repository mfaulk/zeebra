import importlib.util
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
# Loaded under its own name: it imports the baseline's `campaign` module itself.
_spec = importlib.util.spec_from_file_location('attribution_campaign', HERE / 'campaign.py')
attribution = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(attribution)

VERBOSE = '''deg     sel   pairs        mat          density            new data         time(rd) in sec (real|cpu)
  2       5       6      14 x 40         18.04%        5 new       0 zero         0.00 | 0.00
  7     733     733    9977 x 9607        0.71%        8 new     725 zero         0.07 | 0.23
reduce final basis      252 x 606        44.74%      247 new       0 zero         0.00 | 0.00
overall(elapsed)        0.15 sec
symbolic prep.          0.04 sec  27.1%
linear algebra          0.08 sec  52.5%
#rows reduced                  3807
#zero reductions               1530
'''


class AttributionCampaignTest(unittest.TestCase):
    # msolve's `-v 2` report parses into its F4 rounds (not the final reduction), stage timings and counts.
    def test_msolve_verbose_parses_rounds_timings_and_counts(self):
        report = attribution.msolve_verbose(VERBOSE)
        self.assertEqual([r['rows'] for r in report['rounds']], [14, 9977])
        r = report['rounds'][1]
        self.assertAlmostEqual(r.pop('density'), 0.0071)
        self.assertEqual(r, dict(degree=7, pairs=733, rows=9977, columns=9607, new=8, zero=725, real_s=0.07, cpu_s=0.23))
        self.assertEqual(report['timings'], {'overall(elapsed)': 0.15, 'symbolic prep.': 0.04, 'linear algebra': 0.08})
        self.assertEqual(report['data'], {'rows reduced': 3807, 'zero reductions': 1530})

    # The FL job runs only Zeebra arms at 16 workers and carries no msolve request file.
    def test_fl_manifest_has_no_comparand(self):
        args = type('A', (), dict(job='fl', f0='/bin/true', study='/bin/true', commit='c' * 40, agent='', reps=9,
                                  msolve='/bin/true'))
        try:
            m = attribution.manifest(args)
        except FileNotFoundError:
            self.skipTest('cyclic-8 inputs are not generated on this machine')
        self.assertEqual([a['name'] for a in m['arms']], ['forward', 'fl'])
        self.assertEqual(m['run']['workers'], [16])
        self.assertTrue(all(i['inputs'] == {} for i in m['instances']))


if __name__ == '__main__':
    unittest.main()
