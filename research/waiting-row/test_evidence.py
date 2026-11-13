import unittest
from evidence import diagnostic, timing


class EvidenceTests(unittest.TestCase):
    # Failed publications mark subsequent products without proving they are avoidable.
    def test_diagnostic_keeps_retry_products_separate(self):
        batch = dict(products=100, inherited_products=40, discovered_products=60,
                     retry_products=25, retries=2, rows=6, split=2, worker_rows=[2, 2],
                     worker_ns=[10, 20], scheduling_ns=7, publication_ns=3,
                     peak_reserved_entries=100, workspace_bytes=80)
        result = diagnostic([batch])
        self.assertEqual(result['post_loss_product_fraction'], .25)
        self.assertEqual(result['worker_duration_balance'], .75)
        self.assertEqual(result['scheduling_worker_sum_ns'], 7)
        self.assertNotIn('avoidable_elapsed_ns', result)

    # Inconsistent worker totals must fail instead of producing plausible evidence.
    def test_incomplete_worker_aggregation_is_rejected(self):
        with self.assertRaises(ValueError):
            diagnostic([dict(products=100, inherited_products=40, discovered_products=60,
                             rows=6, split=2, worker_rows=[1], worker_ns=[10])])

    # Negative worker clocks cannot masquerade as balanced scheduling evidence.
    def test_negative_worker_clock_is_rejected(self):
        batch = dict(products=100, inherited_products=40, discovered_products=60,
                     retry_products=25, retries=2, rows=6, split=2, worker_rows=[2, 2],
                     worker_ns=[-10, 20], scheduling_ns=7, publication_ns=3,
                     peak_reserved_entries=100, workspace_bytes=80)
        with self.assertRaises(ValueError):
            diagnostic([batch])

    # The ideal whole-forward ceiling uses wall time from the same timed attempt.
    def test_same_attempt_forward_ceiling(self):
        result = timing(1000, [dict(forward_ns=200)])
        self.assertEqual(result['remove_all_forward_ceiling'], 1.25)
        self.assertEqual(result['required_forward_saving_for_10pct'], .5)

    # Unavailable or impossible stage boundaries cannot become numerical ceilings.
    def test_invalid_timer_boundary_is_rejected(self):
        for wall, forward in [(0, 0), (100, 101), (100, 100), (100, -1)]:
            with self.assertRaises(ValueError):
                timing(wall, [dict(forward_ns=forward)])


if __name__ == '__main__':
    unittest.main()
