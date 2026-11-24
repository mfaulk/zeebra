import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import summarize as s  # noqa: E402

VALUES = {
    "variables": 3,
    "generators": 3,
    "nonzero_generators": 3,
    "max_degree": 2,
    "terms": 9,
    "homogeneous": False,
    "linear_generators": 0,
    "components": 1,
    "unused_variables": 0,
    "constant_generators": 0,
    "elimination_width": 2,
    "linear_rank": 0,
    "linear_consistent": True,
    "scalar_substitutions": 0,
    "univariate_generators": 0,
    "binomial_generators": 0,
    "monomial_generators": 0,
    "duplicate_generators": 0,
    "divisible_leading": 0,
    "sampled_pairs": 3,
    "coprime_pairs": 0,
    "overlapping_pairs": 3,
    "top_degree_terms": 6,
    "homogeneous_capacity": 18,
}


def record(id, cheapest, cost=100, **values):
    return {
        "id": id,
        "wall_s": 60,
        "feature_costs": {f: {"median_ns": cost, "cold_ns": 3 * cost} for f in s.FEATURES},
        "features": {**VALUES, **values},
        "entry": {
            "route": "Shipping",
            "status": "complete" if cheapest else "stopped",
            "calls_ns": [cheapest or 5_000_000],
        },
        "f4": {"status": "complete" if cheapest else "stopped", "calls_ns": [cheapest or 8_000_000]},
        "cheapest_arm": None if cheapest is None else "entry",
        "cheapest_ns": cheapest,
    }


class Summary(unittest.TestCase):
    # A feature costing 1% of the solve passes and one costing more fails, per small record.
    def test_threshold_is_inclusive_per_feature(self):
        rows = s.feature_rows([record("a", 10_000), record("b", 9_000)])
        first = rows[0]
        self.assertAlmostEqual(first["worst_ratio"], 100 / 9_000)
        self.assertEqual(first["verdict"], "FAIL")
        self.assertEqual(first["worst_id"], "b")
        self.assertEqual(first["over"], 1)
        rows = s.feature_rows([record("a", 10_000)])
        self.assertEqual(rows[0]["verdict"], "pass")

    # The set is the sum of the seven features, held to its own fraction.
    def test_set_sums_every_feature(self):
        rows = s.feature_rows([record("a", 100_000)])
        whole = rows[-1]
        self.assertEqual(whole["feature"], "all seven")
        self.assertEqual(whole["median_ns"], 700)
        self.assertAlmostEqual(whole["worst_ratio"], 0.007)
        self.assertEqual(whole["verdict"], "pass")

    # Unsolved and slow records are never small, so they cannot decide a verdict.
    def test_only_small_records_decide(self):
        rows = s.feature_rows(
            [record("slow", 2 * s.SMALL_NS, cost=10**9), record("none", None, cost=10**9)]
        )
        self.assertEqual(rows[0]["verdict"], "no small input")
        self.assertEqual(rows[0]["small"], 0)
        self.assertEqual(rows[0]["max_ns"], 10**9)

    # Coverage counts each structural property once per record.
    def test_coverage_counts(self):
        cov = s.coverage(
            [
                record("a", 1, components=2, homogeneous=True),
                record("b", None, variables=5, linear_rank=1, scalar_substitutions=1),
            ]
        )
        self.assertEqual(cov["split_components"], 1)
        self.assertEqual(cov["homogeneous"], 1)
        self.assertEqual(cov["variables"], (3, 5))
        self.assertEqual(cov["linear_part"], 1)
        self.assertEqual(cov["substitutions"], 1)
        self.assertEqual(cov["solved"], 1)
        self.assertEqual(cov["under_determined"], 1)

    # An unsolved record's ratio is bounded by the shortest call that stopped, not the wall.
    def test_render_bounds_unsolved_records(self):
        text = s.render([record("a", 10_000), record("b", None)])
        self.assertIn("stopped ≥ 5.0 ms", text)
        self.assertIn("< 0.014%", text)

    # Failures are located by the slowest solve they occur on, and cold calls are reported apart.
    def test_failing_solves_and_cold_ratio(self):
        rows = s.feature_rows([record("a", 5_000), record("b", 8_000), record("c", 50_000)])
        self.assertEqual(rows[0]["failing_below_ns"], 8_000)
        self.assertAlmostEqual(rows[0]["worst_cold_ratio"], 300 / 5_000)
        self.assertEqual(rows[0]["over"], 2)

    # The repeat session gets its own verdict table.
    def test_repeat_session_is_rendered(self):
        text = s.render([record("a", 10_000)], [record("a", 5_000)])
        self.assertIn("## Repeat session", text)
        self.assertIn("| `system_shape` | 2.000% | 1 / 1 | FAIL |", text)

    # A process that failed is named and kept out of every table.
    def test_failed_process_is_excluded(self):
        text = s.render([record("a", 10_000), {"id": "dead", "status": "failed: exit 124"}])
        self.assertIn("Failed processes, excluded: `dead`", text)
        self.assertIn("(1 records)", text)


if __name__ == "__main__":
    unittest.main()
