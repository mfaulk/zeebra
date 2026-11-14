#!/usr/bin/env python3
import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location('study', Path(__file__).resolve().parents[1] / 'external/multirow-study.py')
study = importlib.util.module_from_spec(spec)
spec.loader.exec_module(study)


def matrix(**overrides):
    row = dict(rows=8, columns=9, first=0, target_entries=20, bands=2, partial_bands=0,
               pivot_applications=6, pivot_reads=3, entries_applied=30, entries_read=15,
               lane_products=40, reads_by_lanes=[0, 1, 1, 1, 0], intra_band_pivots=1,
               new_pivots=5, zero_rows=3, scratch_bytes=144)
    row.update(overrides)
    return row


class Plan(unittest.TestCase):
    # Every arm runs once per cell and repetition, and no arm is always first.
    def test_plan_is_balanced_and_rotated(self):
        cells = list(study.plan('native'))
        self.assertEqual(len(cells), 5 * 3 * 2 * 4)
        firsts = {cells[r * 24][3] for r in range(4)}
        self.assertEqual(firsts, set(study.ARMS))

    # Every arm except the stock control selects its multirow mode explicitly.
    def test_command_names_the_arm(self):
        binary = Path('/bin/true')
        self.assertNotIn('--multirow=stock', study.command(binary, 'cyclic-5', 13, 'stock'))
        self.assertIn('--multirow=lanes4', study.command(binary, 'cyclic-5', 13, 'lanes4'))
        self.assertIn('--stages', study.command(binary, 'cyclic-5', 13, 'stock'))


class Acceptance(unittest.TestCase):
    # A complete answer plus the selected mode is accepted; a wrong basis or mode is not.
    def test_answer_and_mode(self):
        ref = dict(digest='d', modulus=13, basis=['x+2*y'])
        raw = dict(ref, problem='cyclic-5', multirow=dict(mode='band4', matrices=[matrix()]))
        study.validate(raw, ref, 'cyclic-5', 'band4')
        for key, value in [('basis', ['x+3*y']), ('digest', 'e'), ('multirow', None),
                           ('multirow', dict(mode='lanes4', matrices=[matrix()])),
                           ('multirow', dict(mode='band4', matrices=[]))]:
            with self.subTest(key=key), self.assertRaises(ValueError):
                study.validate(dict(raw, **{key: value}), ref, 'cyclic-5', 'band4')

    # The single-row arm must not reach the band kernel, and stock must not report a mode.
    def test_controls(self):
        ref = dict(digest='d', modulus=13, basis=['x'])
        study.validate(dict(ref, problem='p', multirow=dict(mode='single', matrices=[])), ref, 'p', 'single')
        study.validate(dict(ref, problem='p', multirow=None), ref, 'p', 'stock')
        with self.assertRaises(ValueError):
            study.validate(dict(ref, problem='p', multirow=dict(mode='single', matrices=[matrix()])), ref, 'p', 'single')
        with self.assertRaises(ValueError):
            study.validate(dict(ref, problem='p', multirow=dict(mode='single', matrices=[])), ref, 'p', 'stock')

    # Totals sum every matrix and derive eligible rows from the split.
    def test_census_totals(self):
        raw = dict(multirow=dict(mode='band4', matrices=[matrix(), matrix(first=2, scratch_bytes=200)]))
        totals = study.census_totals(raw)
        self.assertEqual(totals['entries_read'], 30)
        self.assertEqual(totals['eligible_rows'], 14)
        self.assertEqual(totals['reads_by_lanes'], [0, 2, 2, 2, 0])
        self.assertEqual(totals['max_scratch_bytes'], 200)
        self.assertIsNone(study.census_totals(dict(multirow=None)))


if __name__ == '__main__':
    unittest.main()
