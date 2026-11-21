import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import campaign  # noqa: E402

REPORT = """\
0.000083 run number=1 role=call engine=signature engine-by=signatures field=gf64 reduce=tests handover=on why=start
0.000220 echelon generators=12 rows=12 squares=0 columns=78 subtracted=7 time=0.000006
0.000372 round number=1 degree=3 pairs=10 rows=32 given=10 kept=0 columns=88 entries=229 index=2 pivots=10 zero=0 zero-rows=0 reductions=10 subtracted=593 added=0 bands=no packed=no pending=10 dropped=0 select=0.000008 symbolic=0.000031 encode=0.000010 reduce=0.000019 backsub=0.000000 record=0.000006 decode=0.000002 update=0.000014
0.000651 ran number=1 outcome=handover rounds=2 reduced=65 zero=0 time=0.000568 considered=231
0.000654 run number=2 role=call engine=plain engine-by=handover field=gf64 reduce=combinations why=handover
0.000829 round number=1 degree=3 pairs=10 rows=32 given=20 kept=0 columns=88 entries=229 index=2 pivots=10 zero=0 reductions=10 subtracted=4840 added=1110 bands=no packed=no mode=blocks deferred=0 left=46 select=0.000007 symbolic=0.000005 encode=0.000002 reduce=0.000028 backsub=0.000006 record=0.000000 decode=0.000000 update=0.000005
0.003025 round number=2 degree=4 pairs=46 rows=198 given=92 kept=9 columns=533 entries=4120 index=2 pivots=46 zero=3 reductions=46 subtracted=562660 added=85054 select=0.000031 symbolic=0.000087 encode=0.000013 reduce=0.001635 backsub=0.000363 record=0.000000 decode=0.000000 update=0.000000
1.529461 inter rows=5355 given=743 columns=6379 entries=735707 index=2 subtracted=52410296 elements=743 symbolic=0.003304 encode=0.000348 reduce=0.140441 decode=0.000232
1.529621 ran number=2 outcome=basis rounds=21 reduced=1316 zero=384 elements=743 time=1.528967
1.542300 text kind=basis bytes=12218467 time=0.012668
1.542753 end result=basis bytes=12218467 time=1.542707 process-rss-start=4132864
"""


class CampaignTest(unittest.TestCase):
    def test_report_lines_parse_numbers_and_skip_bare_words(self):
        """Report fields parse as int or float where they are numbers and stay strings otherwise."""
        t, kind, f = campaign.report_lines(REPORT)[0]
        self.assertEqual((t, kind, f['number'], f['engine']), (0.000083, 'run', 1, 'signature'))

    def test_grobx_summary_totals_rounds_per_run(self):
        """Rounds sum into the run they follow, echelon charges count, and clocks become ns."""
        s = campaign.grobx_summary(REPORT)
        sig, plain = s['runs']
        self.assertEqual((sig['engine'], sig['rounds'], sig['subtracted'], sig['outcome']), ('signature', 1, 600, 'handover'))
        self.assertEqual((plain['rounds'], plain['reductions'], plain['zero'], plain['subtracted']), (2, 56, 3, 567500))
        self.assertEqual((plain['reduce_ns'], plain['backsub_ns'], plain['max_columns']), (1663000, 369000, 533))
        self.assertEqual(plain['run_ns'], 1528967000)
        self.assertEqual(sig['zero_rows'], 0)

    def test_grobx_summary_reads_interreduction_text_and_end(self):
        """The final interreduction, the basis-text build and the call's end are kept apart from rounds."""
        s = campaign.grobx_summary(REPORT)
        self.assertEqual((s['inter']['subtracted'], s['inter']['reduce_ns']), (52410296, 140441000))
        self.assertEqual((s['text_ns'], s['call_ns']), (12668000, 1542707000))

    def test_hwcount_of_takes_the_last_marked_line(self):
        """The counters are the final `hwcount` line of stderr; absent, None."""
        err = b'noise\nhwcount {"counts": {"cycles": 1}}\n'
        self.assertEqual(campaign.hwcount_of(err), {'counts': {'cycles': 1}})
        self.assertIsNone(campaign.hwcount_of(b'nothing\n'))


if __name__ == '__main__':
    unittest.main()
