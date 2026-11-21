import importlib.util
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location('m33_g2_campaign', HERE / 'campaign.py')
campaign = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(campaign)


class GateRows(unittest.TestCase):
    def test_no_gate_times_a_held_out_row(self):
        """Neither gate's row set contains a row from the held-out draw."""
        for rows in campaign.GATE_ROWS.values():
            self.assertFalse(campaign.HELD_OUT & set(rows))

    def test_every_gate_carries_the_development_rows(self):
        """Gates B and C time all three Track G development rows, Eco-12 first."""
        for rows in (campaign.GATE_ROWS['b'], campaign.GATE_ROWS['c']):
            self.assertEqual(rows[:3], campaign.DEVELOPMENT)
            self.assertEqual(rows[0], ('wide64', 'eco-12'))

    def test_warm_call_gate_is_only_the_small_control(self):
        """The warm-call session holds Katsura-4 alone, the one Track G row under 300 ms."""
        self.assertEqual(campaign.GATE_ROWS['c-warm'], [('wide64', 'katsura-4')])


if __name__ == '__main__':
    unittest.main()
