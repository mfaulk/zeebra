import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parents[1] / 'tools'))
import bench_stats as bs  # noqa: E402
import campaign  # noqa: E402
import importlib.util  # noqa: E402
_s = importlib.util.spec_from_file_location("m33_final_summarize", HERE / "summarize.py")
summarize = importlib.util.module_from_spec(_s)
_s.loader.exec_module(summarize)

CASE = dict(modulus='7', variables=['x1', 'x2', 'x3'])


def ci(m, lo, hi):
    return bs.Interval(m, lo, hi, 9, 9)


class Invariants(unittest.TestCase):
    def test_leading_monomials_are_grevlex_sorted_and_counted(self):
        """The reference basis gives its cardinality and its sorted grevlex leading monomials."""
        inv = campaign.invariants(['x1*x2 + x3^3', 'x2^2 - 3*x1', '0'], CASE)
        self.assertEqual(inv, dict(basis_cardinality=2, leading_monomials=['x2^2', 'x3^3']))

    def test_grevlex_tie_breaks_on_the_last_variable(self):
        """Among equal degrees grevlex prefers the smaller exponent in the last variable."""
        self.assertEqual(campaign.invariants(['x1*x3 + x2^2'], CASE)['leading_monomials'], ['x2^2'])


class Rows(unittest.TestCase):
    def test_every_held_out_row_is_generated_and_in_its_track(self):
        """Held-out rows run in this campaign by design (#975) and are built by `--generate`."""
        for t in ('G', 'M'):
            self.assertEqual(len(campaign.ROWS[t]['held-out']), 2)
            for r in campaign.ROWS[t]['held-out']:
                self.assertIn(r, campaign.GENERATED)
                self.assertEqual(campaign.set_of(t, *r), 'held-out')


class GateD(unittest.TestCase):
    def _gv(self, dev, held):
        win = bs.win_verdict(dev)
        return {('wide64', 'eco-12'): (dev, win), ('wide64', 'katsura-12'): (held[0], bs.win_verdict(held[0])),
                ('wide64', 'mq-random-10-s1'): (held[1], bs.win_verdict(held[1]))}

    def test_win_confirmed_only_when_every_held_out_row_is_within_the_bar(self):
        """A development win confirms only if each held-out row is ≤ its ratio + 0.15."""
        _, res = summarize.gate_d(self._gv(ci(0.9, 0.85, 0.95), [ci(1.0, 0.9, 1.1), ci(1.04, 1.0, 1.1)]), {})
        self.assertEqual(res['G', 'wide64', 'eco-12', 1], (True, True))
        _, res = summarize.gate_d(self._gv(ci(0.9, 0.85, 0.95), [ci(1.0, 0.9, 1.1), ci(1.06, 1.0, 1.1)]), {})
        self.assertEqual(res['G', 'wide64', 'eco-12', 1], (True, False))

    def test_a_loss_is_not_a_confirmed_win(self):
        """A development row that does not win here is not confirmed whatever the held-out rows read."""
        _, res = summarize.gate_d(self._gv(ci(1.3, 1.2, 1.4), [ci(1.0, 0.9, 1.1), ci(1.0, 0.9, 1.1)]), {})
        self.assertEqual(res['G', 'wide64', 'eco-12', 1][0], False)


if __name__ == '__main__':
    unittest.main()
