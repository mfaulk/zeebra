#!/usr/bin/env python3
"""bench_stats must replay published M31/M32 intervals exactly: the bootstrap is seeded, so any
drift in resampling order, index convention or seed derivation shows up as a changed digit."""
import gzip
import importlib.util
import json
import pathlib
import statistics
import unittest
import zlib

ROOT = pathlib.Path(__file__).resolve().parents[2]


def _module(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


bs = _module("bench_stats", "tools/bench_stats.py")


def ci(median, lo, hi, n=9):
    return bs.Interval(median, lo, hi, n, n)


def fmt(c):
    return f"{c.median:.3f} [{c.lo:.3f}, {c.hi:.3f}]"


class Replay(unittest.TestCase):
    def test_m32_gate_q_t3_cell(self):
        """The M32 Gate Q T3 cell gf32003/mq-random-10 at 1 worker (ad ÷ f4, paired, seed 941) reprints as published."""
        cells = {}
        with gzip.open(ROOT / "research/m32-qualification/dev.jsonl.gz", "rt") as handle:
            for line in handle:
                r = json.loads(line)
                label, workers = r["arm"].split(":")
                label = label.partition(".")[0]
                ok = r["returncode"] == 0 and (r.get("report") or {}).get("status") == "complete"
                if r["row"] == "gf32003/mq-random-10" and workers == "1" and label in ("ad", "f4") and ok:
                    cells.setdefault(r["rep"], {})[label] = r["process_wall_ns"] / 1e6
        ad = {k: v["ad"] for k, v in cells.items() if "ad" in v}
        f4 = {k: v["f4"] for k, v in cells.items() if "f4" in v}
        c = bs.paired_ratio(bs.paired_ratios(ad, f4), seed=941)
        self.assertEqual(c.n, 9)
        self.assertEqual(fmt(c), "0.432 [0.424, 0.443]")
        self.assertIn(f"| {fmt(c)} | {100 * bs.relative_half_width(c):.1f}% |",
                      (ROOT / "research/m32-qualification/tables.md").read_text())

    def test_m31_competitive_grobx_cell(self):
        """The M31 MQ11/Goldilocks equal-worker cell (Zeebra en:1 ÷ grobx raw, independent) reprints as published."""
        row, label = "goldilocks/mq-random-11", "grobx (raw randomized)"
        zeebra = {}
        with gzip.open(ROOT / "research/m31-final/walls.jsonl.gz", "rt") as handle:
            for line in handle:
                r = json.loads(line)
                ok = r["returncode"] == 0 and (r.get("report") or {}).get("status") == "complete"
                if (r["row"], r["arm"]) == (row, "en:1") and ok:
                    zeebra[r["rep"]] = r["process_wall_ns"] / 1e9
        z = [v * 1e3 for v in zeebra.values()]
        passes = json.loads((ROOT / "research/m31-final/wide-attempts.json").read_text())
        grobx = [a["solver_process_wall_ns"] / 1e6 for p in passes for a in p["attempts"]
                 if (a["field"], a["name"], a["engine"], a["status"]) == ("goldilocks", "mq-random-11", "grobx", "complete")]
        c = bs.independent_ratio(z, grobx, seed=f"{row} {label} {len(z)}")
        self.assertEqual(fmt(c), "1.711 [1.624, 1.814]")
        self.assertIn(fmt(c), (ROOT / "research/m31-final/tables.md").read_text())


class Equivalence(unittest.TestCase):
    VALUES = [1.02, 0.97, 1.11, 0.99, 1.04, 1.00, 0.95, 1.07, 1.01]
    OTHER = [2.1, 1.9, 2.4, 2.0, 2.2, 1.8, 2.05, 2.3, 1.95]

    def test_paired_matches_m31_baseline(self):
        """paired_ratio returns exactly what research/m31-baseline's median_interval returned for one seed."""
        old = _module("m31summary", "research/m31-baseline/summarize.py")
        c = bs.paired_ratio(self.VALUES, seed=901)
        self.assertEqual((c.median, c.lo, c.hi), old.median_interval(self.VALUES, 901))

    def test_independent_matches_m29_verdicts(self):
        """independent_ratio returns exactly what research/m29-final's verdicts.interval returned for one seed."""
        old = _module("verdicts", "research/m29-final/verdicts.py")
        c = bs.independent_ratio(self.VALUES, self.OTHER, seed=7)
        self.assertEqual((c.lo, c.hi), old.interval(self.VALUES, self.OTHER, 7))
        self.assertEqual(c.median, statistics.median(self.VALUES) / statistics.median(self.OTHER))
        self.assertEqual((c.n, c.n_ref), (9, 9))

    def test_string_seed_is_crc32(self):
        """A string seed is the CRC-32 of its UTF-8 bytes, as the M31 summaries derived theirs."""
        self.assertEqual(bs.paired_ratio(self.VALUES, seed="row a b"),
                         bs.paired_ratio(self.VALUES, seed=zlib.crc32(b"row a b")))

    def test_paired_ratios_intersects_repetitions(self):
        """Paired ratios use only repetitions both arms completed, in repetition order."""
        self.assertEqual(bs.paired_ratios({2: 4.0, 0: 2.0, 1: 9.0}, {0: 1.0, 2: 2.0}), [2.0, 2.0])

    def test_empty_sample_is_refused(self):
        """A bootstrap over no samples raises rather than inventing an interval."""
        with self.assertRaises(ValueError):
            bs.paired_ratio([], seed=1)


class Precision(unittest.TestCase):
    def test_relative_rule(self):
        """Relative half-width 2% passes a 1.05 bound (allowance 2.5%) and fails a 1.03 bound (1.5%)."""
        c = ci(1.0, 0.98, 1.02)
        self.assertTrue(bs.precise(c, 1.05))
        self.assertFalse(bs.precise(c, 1.03))

    def test_threshold_below_one(self):
        """A threshold below 1.0 (Gate C's 0.97) measures its distance from 1.0 the same way."""
        self.assertTrue(bs.precise(ci(0.9, 0.89, 0.91), 0.97))
        self.assertFalse(bs.precise(ci(0.9, 0.85, 0.95), 0.97))

    def test_absolute_rule(self):
        """The absolute variant (m32-gate-s) compares the raw half-width, not half-width ÷ median."""
        c = ci(0.5, 0.48, 0.52)
        self.assertFalse(bs.precise(c, 1.05))
        self.assertTrue(bs.precise(c, 1.05, relative=False))


class Verdicts(unittest.TestCase):
    def test_regression(self):
        """Upper bound over the bound is a regression; at or under it is no-regression."""
        self.assertEqual(bs.regression_verdict(ci(1.06, 1.055, 1.065), 1.05).outcome, "regression")
        self.assertEqual(bs.regression_verdict(ci(1.0, 0.99, 1.01), 1.05).outcome, "no-regression")

    def test_imprecise_regression_extends_once(self):
        """An imprecise read asks for the one extension, then is inconclusive without asking again."""
        first = bs.regression_verdict(ci(1.0, 0.9, 1.1), 1.05)
        self.assertEqual((first.outcome, first.extend), ("inconclusive", True))
        final = bs.regression_verdict(ci(1.0, 0.9, 1.1, n=21), 1.05, extended=True)
        self.assertEqual((final.outcome, final.extend), ("inconclusive", False))

    def test_too_few_repetitions_is_stopped(self):
        """Fewer than the minimum repetitions reads as stopped, never as a pass."""
        self.assertEqual(bs.regression_verdict(ci(1.0, 0.99, 1.01, n=5), 1.05).outcome, "stopped")
        self.assertEqual(bs.win_verdict(ci(0.5, 0.4, 0.6, n=8)).outcome, "stopped")

    def test_win_rule(self):
        """§8.4: median and upper bound below 1 is a win; lower bound above 1 is a loss."""
        self.assertEqual(bs.win_verdict(ci(0.9, 0.85, 0.95)).outcome, "win")
        self.assertEqual(bs.win_verdict(ci(1.2, 1.1, 1.3)).outcome, "loss")

    def test_spanning_one_extends_then_inconclusive(self):
        """An interval spanning 1 gets the one extension at n = 9, then is inconclusive."""
        self.assertEqual(bs.win_verdict(ci(0.98, 0.9, 1.02)), bs.Verdict("inconclusive", True, "interval spans 1"))
        v = bs.win_verdict(ci(0.98, 0.9, 1.02, n=21), extended=True)
        self.assertEqual((v.outcome, v.extend), ("inconclusive", False))

    def test_anomaly_and_small_rows_never_win(self):
        """A win at an msolve anomaly is reported as anomaly; a sub-300 ms row cannot win."""
        self.assertEqual(bs.win_verdict(ci(0.5, 0.4, 0.6), anomaly=True).outcome, "anomaly")
        self.assertEqual(bs.win_verdict(ci(0.5, 0.4, 0.6), small=True).outcome, "inconclusive")
        self.assertEqual(bs.win_verdict(ci(1.5, 1.4, 1.6), anomaly=True).outcome, "loss")

    def test_outcomes_are_declared(self):
        """Every outcome a verdict can return is in the published vocabulary."""
        self.assertEqual(set(bs.OUTCOMES),
                         {"win", "loss", "inconclusive", "regression", "no-regression", "stopped", "anomaly"})


class Anomaly(unittest.TestCase):
    WALLS = {1: [1000, 1010, 990], 4: [400, 410], 8: [467, 470], 16: [430, 440]}

    def test_msolve_anomaly(self):
        """A count whose median is over 1.10x msolve's own best is anomalous; within it is not."""
        self.assertTrue(bs.msolve_anomaly(self.WALLS, 8))
        self.assertFalse(bs.msolve_anomaly(self.WALLS, 16))
        self.assertFalse(bs.msolve_anomaly(self.WALLS, 4))
        self.assertFalse(bs.msolve_anomaly(self.WALLS, 8, tolerance=1.20))

    def test_missing_count_is_refused(self):
        """Asking about a worker count with no samples raises instead of returning not-anomalous."""
        with self.assertRaises(KeyError):
            bs.msolve_anomaly(self.WALLS, 2)


class Contamination(unittest.TestCase):
    def test_partition_counts_every_attempt(self):
        """Contaminated attempts are separated and counted, never silently dropped, and the void rule applies."""
        attempts = [{"wall": 1, "contaminated": False}, {"wall": 2, "contaminated": True}, {"wall": 3}]
        clean, dirty = bs.partition_contaminated(attempts)
        self.assertEqual(([a["wall"] for a in clean], [a["wall"] for a in dirty]), ([1, 3], [2]))
        self.assertTrue(bs.session_void(len(clean), len(dirty)))
        self.assertFalse(bs.session_void(9, 1))
        self.assertFalse(bs.session_void(0, 0))


class WarmCall(unittest.TestCase):
    def test_warm_median_skips_first_call(self):
        """The warm-call figure is the median over calls after the first (cold) one."""
        self.assertEqual(bs.warm_median([900, 10, 12, 11]), 11)


if __name__ == "__main__":
    unittest.main()
