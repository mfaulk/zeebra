#!/usr/bin/env python3
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location('residual_model', ROOT / 'research/residual-backward/model.py')
model = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(model)


class ResidualModel(unittest.TestCase):
    # Amdahl ceilings use the eligible duration and total from the same attempt.
    def test_per_attempt_ceiling(self):
        self.assertAlmostEqual(model.ceiling(100, 20, 2), 100 / 90)
        self.assertAlmostEqual(model.ceiling(100, 20, None), 1.25)
        self.assertEqual(model.ceiling(100, 0, 64), 1)
        for total, backward, workers in [(0, 0, 2), (10, 11, 2), (10, -1, 2), (10, 1, 0)]:
            with self.subTest(total=total, backward=backward, workers=workers), self.assertRaises(ValueError):
                model.ceiling(total, backward, workers)

    # Product and target distributions must not silently accept missing or inconsistent batches.
    def test_census_rejects_incomplete_or_drifted_batches(self):
        batch = dict(completed=True, columns=10, rank=2,
                     backward=dict(rows_loaded=1, coefficient_products=5, pivot_applications=2,
                                   dense_load_entries=3, dense_gather_entries=2))
        result = model.census([batch])
        self.assertEqual(result['targets'], 1)
        self.assertEqual(result['largest_batch_product_fraction'], 1)
        self.assertEqual(result['batches'][0]['source_fanout_upper_bound'], 1)
        for bad in [[], [dict(batch, completed=False)], [dict(batch, columns=0)],
                    [dict(batch, rank=0)],
                    [dict(batch, backward=dict(batch['backward'], coefficient_products=-1))]]:
            with self.assertRaises(ValueError):
                model.census(bad)

    # A larger worker count increases reserved scratch even when products and output stay fixed.
    def test_parallel_workspace_and_entry_reservation(self):
        self.assertEqual(model.reservation(100, 20, 10, 4), 160)
        self.assertEqual(model.workspace(10, 4, 4), 250)
        self.assertEqual(model.workspace(10, 8, 1), 170)
        for p in [0, -1]:
            with self.assertRaises(ValueError):
                model.reservation(100, 20, 10, p)

    # Dispatch estimates require every physical-core warm empty-job cell from the retained runtime.
    def test_dispatch_grid_is_complete(self):
        rows = [dict(phase='floor', backend='parked', workers=p, case=['0']) for p in model.WORKERS]
        self.assertEqual(model.dispatch_rows(rows), rows)
        for bad in [rows[:-1], rows + rows[:1], []]:
            with self.assertRaises(ValueError):
                model.dispatch_rows(bad)


if __name__ == '__main__':
    unittest.main()
