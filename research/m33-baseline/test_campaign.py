import json
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parents[1] / 'tools'))
import campaign  # noqa: E402
import summarize  # noqa: E402

CASE = dict(modulus='7', variables=['x', 'y'], digest='d')


class CampaignTest(unittest.TestCase):
    # Every solver's output reaches one digest for the same basis, and a failed Zeebra run has none.
    def test_digest_of_agrees_across_solvers(self):
        msolve = b'#header\n[1*x^1+6*y^1,\n1*y^2+1]:\n'
        grobx = json.dumps(dict(basis='[x-y, y^2+1]')).encode()
        grs = json.dumps(dict(basis=['x-y', 'y^2+1'])).encode()
        digests = {campaign.digest_of('msolve', msolve, CASE), campaign.digest_of('grobx155', grobx, CASE),
                   campaign.digest_of('groebner-rs', grs, CASE)}
        self.assertEqual(len(digests), 1)
        self.assertIsNotNone(digests.pop())
        self.assertIsNone(campaign.digest_of('entry', b'{"status":"timeout"}', CASE))
        self.assertEqual(campaign.digest_of('sigf4', b'{"status":"complete","basis_m33":"ab"}', CASE), 'ab')

    # Arms are attributed to their solver by name: Zeebra engines, grobx pins, msolve.
    def test_solver_of(self):
        self.assertEqual([campaign.solver_of(a) for a in ('entry16', 'sigf4', 'grobx073', 'msolve')],
                         ['zeebra', 'zeebra', 'grobx073', 'msolve'])

    # The cut to win is zero when the row already wins, None when no cut can, and otherwise puts the upper bound below 1.
    def test_cut_to_win(self):
        c = [100.0 + i for i in range(9)]
        self.assertEqual(summarize.cut_to_win([50.0 + i for i in range(9)], c, 's'), 0.0)
        d = summarize.cut_to_win([150.0 + i for i in range(9)], c, 's')
        self.assertTrue(45 < d < 60, d)
        z = [150.0 + i - d for i in range(9)]
        self.assertLess(summarize.bs.independent_ratio(z, c, seed='s').hi, 1)
        self.assertIsNone(summarize.cut_to_win([], c, 's'))


if __name__ == '__main__':
    unittest.main()
