import importlib.util
import json
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent


def _module(name):
    spec = importlib.util.spec_from_file_location(f'm32baseline_{name}', HERE / f'{name}.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


pins = _module('pins')
campaign = _module('campaign')


def records(row, walls_ms, status='complete'):
    return [dict(row=row, process_wall_ns=int(w * 1e6), report=dict(status=status, call_ns=int(w * 1e6)))
            for w in walls_ms]


class AdmissionTest(unittest.TestCase):
    def verdict(self, walls_ms, status='complete'):
        return pins.admission(records('goldilocks/cyclic-6', walls_ms, status))['goldilocks/cyclic-6']

    def test_inside_the_window_is_kept(self):
        """A complete row whose median process wall is inside 20 ms-60 s is kept."""
        self.assertEqual(self.verdict([25, 30, 900])['verdict'], 'kept')

    def test_too_fast_is_dropped(self):
        """A median under 20 ms drops the row, even when one repetition is slower."""
        read = self.verdict([12, 15, 40])
        self.assertEqual(read['verdict'], 'dropped')
        self.assertIn('outside 20 ms-60 s', read['reason'])

    def test_too_slow_is_dropped(self):
        """A median over 60 s drops the row."""
        self.assertEqual(self.verdict([61_000, 62_000, 59_000])['verdict'], 'dropped')

    def test_an_incomplete_repetition_drops_the_row(self):
        """Any repetition that did not complete drops the row, whatever its wall."""
        read = pins.admission(records('goldilocks/cyclic-6', [30, 30]) +
                              records('goldilocks/cyclic-6', [30], 'stopped: wall'))['goldilocks/cyclic-6']
        self.assertEqual(read['verdict'], 'dropped')

    def test_an_unread_row_is_not_judged(self):
        """A candidate with no records is reported as not read rather than kept or dropped."""
        self.assertEqual(pins.admission([])['m31/eco-11'],
                         dict(verdict='not read'))


class PinTest(unittest.TestCase):
    def test_committed_pins_reproduce(self):
        """pins.json is exactly what pins.py writes from the catalog, the code pins and the admission read."""
        self.assertEqual(pins.pins(), json.loads((HERE / 'pins.json').read_text()))

    def test_admission_suite_is_the_held_out_set_at_sixteen_workers(self):
        """The admission suite reads every held-out candidate once per repetition, F4 at 16 workers only."""
        self.assertEqual([r for r, _ in campaign.SUITES['admission']], [f'{f}/{n}' for f, n, _ in pins.HELD_OUT])
        self.assertTrue(all(a == ['f4:16'] for _, a in campaign.SUITES['admission']))


class CampaignTest(unittest.TestCase):
    BINS = dict(sig=Path('B'), ref=Path('R'), split=Path('S'))

    def test_walls_cover_every_development_row(self):
        """The walls suite runs every pinned development row, each with all twenty arms."""
        dev = [f"{r['field']}/{r['name']}" for r in json.loads((HERE / 'pins.json').read_text())['development']]
        self.assertEqual(sorted(r for r, _ in campaign.SUITES['walls']), sorted(dev))
        self.assertTrue(all(len(a) == 20 for _, a in campaign.SUITES['walls']))

    def test_prefixes_pick_the_build(self):
        """`r` arms run the reference build, `s` arms the split build, unprefixed arms the suite's own."""
        self.assertEqual(campaign.command(self.BINS, 'wide64/eco-12', 'ren:16')[1][:1], ['R'])
        self.assertEqual(campaign.command(self.BINS, 'wide64/eco-12', 'scl:8')[1][0], 'S')
        argv = campaign.command(self.BINS, 'wide64/eco-12', 'cl:8')[1]
        self.assertEqual((argv[0], argv[-1], argv[argv.index('--engine') + 1]), ('B', '--claim', 'sigf4'))
        self.assertEqual(campaign.command(self.BINS, 'wide64/eco-12', 'en:1')[1][6], 'entry')

    def test_small_controls_repeat_the_call(self):
        """The #934 suite appends `--repeat` to every child and runs at least 31 processes per cell."""
        argv = campaign.command(self.BINS, 'wide64/katsura-4', 'en:16', campaign.EXTRA['small'])[1]
        self.assertEqual(argv[-2:], ['--repeat', '21'])
        self.assertGreaterEqual(campaign.REPS['small'], 31)


if __name__ == '__main__':
    unittest.main()
