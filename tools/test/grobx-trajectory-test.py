#!/usr/bin/env python3
"""Validate that retained grobx reports preserve abandoned runs and their work."""
import gzip
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location('grobx_trajectory', ROOT / 'tools/external/grobx-trajectory.py')
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def fixture():
    with gzip.open(ROOT / 'research/competitive/results/grobx-683.json.gz', 'rt') as stream:
        return json.load(stream)


def report_at(index):
    return json.loads(fixture()['attempts'][index]['artifacts']['raw_output'])['report']


class TrajectoryTests(unittest.TestCase):
    # Both abandoned signature work and the restarted conventional run contribute to totals.
    def test_all_runs_and_coefficient_charges_are_retained(self):
        parsed = MODULE.parse_report(report_at(10))
        self.assertEqual([r['config']['engine'] for r in parsed['runs']], ['signature', 'plain'])
        self.assertEqual([len(r['rounds']) for r in parsed['runs']], [9, 10])
        self.assertEqual(parsed['runs'][0]['summary']['outcome'], 'handover')
        self.assertEqual(parsed['runs'][1]['config']['reduce'], 'rows')
        self.assertEqual(parsed['totals']['rounds'], 19)
        self.assertEqual(parsed['totals']['subtracted_entry_charges'], 83_846_548 + 294_668_951)
        self.assertEqual(parsed['totals']['added_entry_charges'], 101_798)
        self.assertEqual(parsed['totals']['input_echelon_subtracted_entry_charges'], 470)
        self.assertEqual(parsed['totals']['interreduction_subtracted_entry_charges'], 93_201)
        self.assertEqual(parsed['runs'][0]['summary']['syzygy'], 34_187)
        self.assertEqual(parsed['runs'][1]['rounds'][0]['density'], 40 / (5 * 23))
        self.assertEqual(parsed['runs'][0]['rounds'][-1]['dropped'], 589)

    # Large-prime combinations and the one eligible band are observable without tracing.
    def test_active_reduction_modes_and_bands_are_preserved(self):
        parsed = MODULE.parse_report(report_at(22))
        self.assertEqual(parsed['read']['field'], 'gf31')
        self.assertEqual(parsed['runs'][1]['config']['reduce'], 'combinations')
        self.assertEqual(parsed['runs'][1]['totals']['subtracted_entry_charges'], 36_826_594)
        self.assertEqual(parsed['runs'][1]['totals']['added_entry_charges'], 5_390_520)
        self.assertEqual([r['number'] for r in parsed['runs'][1]['rounds'] if r['bands']], [5])
        self.assertFalse(any(r['bands'] for r in parsed['runs'][0]['rounds']))

    # All six existing verified raw MQ10 attempts retain matching degree and work trajectories.
    def test_complete_retained_cohort(self):
        parsed = MODULE.parse_cohort(fixture())
        self.assertEqual(len(parsed['attempts']), 6)
        for attempt in parsed['attempts']:
            trajectory = attempt['trajectory']
            self.assertEqual(trajectory['totals']['rounds'], 19)
            self.assertEqual([r['degree'] for r in trajectory['runs'][0]['rounds']], [2, 3, 4, 4, 5, 6, 7, 8, 9])
            self.assertEqual([r['degree'] for r in trajectory['runs'][1]['rounds']], [2, 3, 4, 5, 6, 6, 6, 7, 7, 8])
            self.assertEqual(trajectory['runs'][-1]['summary']['elements'], 247)
            self.assertEqual(attempt['digest'], attempt['input']['digest'])

    # Truncated reports cannot publish partial trajectories as complete computations.
    def test_missing_end_and_missing_summary_are_rejected(self):
        text = report_at(10)
        for changed in ['\n'.join(text.splitlines()[:-1]),
                        '\n'.join(line for line in text.splitlines() if ' ran number=1 ' not in line)]:
            with self.subTest(changed=changed[-80:]), self.assertRaises(ValueError):
                MODULE.parse_report(changed)

    # Counter corruption and missing rounds are rejected instead of understating work.
    def test_bad_counts_and_numbering_are_rejected(self):
        text = report_at(10)
        for changed in [text.replace('rounds=9 reduced=659', 'rounds=8 reduced=659'),
                        text.replace('rounds=9 reduced=659', 'rounds=9 reduced=660'),
                        text.replace('rounds=9 reduced=659 zero=250', 'rounds=9 reduced=659 zero=249'),
                        text.replace('round number=3 degree=4', 'round number=4 degree=4', 1)]:
            with self.subTest(changed=changed[-80:]), self.assertRaises(ValueError):
                MODULE.parse_report(changed)

    # A handover must restart from the same reported original-generator shape.
    def test_changed_restart_input_is_rejected(self):
        text = report_at(10)
        changed = text.replace('0.084160 inputs generators=10 nonzero=10 terms=95',
                               '0.084160 inputs generators=11 nonzero=10 terms=95')
        with self.assertRaisesRegex(ValueError, 'restart input'):
            MODULE.parse_report(changed)

    # Future passive events remain visible without changing reduction-mode interpretation.
    def test_unknown_passive_events_are_retained(self):
        text = report_at(10).replace('0.084153 run number=2',
                                   '0.084150 work pivot-applications=10 tail-products=20\n0.084153 run number=2')
        parsed = MODULE.parse_report(text)
        self.assertEqual(parsed['runs'][0]['events'][-1]['kind'], 'work')
        self.assertEqual(parsed['runs'][0]['events'][-1]['fields']['tail-products'], 20)


if __name__ == '__main__':
    unittest.main()
