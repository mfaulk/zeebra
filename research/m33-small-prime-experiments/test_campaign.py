import importlib.util
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
# Loaded under its own name: it imports the baseline's `campaign` module itself.
_spec = importlib.util.spec_from_file_location('kir_campaign', HERE / 'campaign.py')
kir = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(kir)

STDERR = '''warning: unrelated
IRSPLIT minimal_ms=7.24
IRSPLIT closure_ms=56.84 build_ms=2.99 rows=537 cols=1561 nnz=387371 seeds=537
IRSPLIT sweep_loop_ms=32.76 of_which_conv_ms=29.32 sort_ms=5.56
'''


class KirCampaignTest(unittest.TestCase):
    # The ZB_IR_SPLIT stderr lines merge into one map of sub-stage clocks and shape counts.
    def test_split_merges_every_irsplit_line(self):
        s = kir.split(STDERR)
        self.assertEqual(len(s), 10)
        self.assertEqual(s['closure_ms'], 56.84)
        self.assertEqual(s['seeds'], 537.0)
        self.assertEqual(s['sort_ms'], 5.56)

    # The manifest runs the entry route at 1/4/8/16 w and never names a held-out row.
    def test_manifest_targets_development_rows_only(self):
        held_out = {('m31', 'mq-random-10-s1'), ('gf32003', 'katsura-12')}
        self.assertFalse(held_out & set(kir.ROWS))
        self.assertEqual(kir.WORKERS, [1, 4, 8, 16])


if __name__ == '__main__':
    unittest.main()
