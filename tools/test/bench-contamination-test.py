#!/usr/bin/env python3
"""Unit tests for tools/bench_contamination.py; run: python3 tools/test/bench-contamination-test.py"""

import json
import os
import pathlib
import subprocess
import sys
import tempfile
import unittest

TOOLS = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(TOOLS))
import bench_contamination as bc  # noqa: E402


def snap(at, bench, sibs, rest=(0, 1000, 4), khz=4000000, **extra):
    """A cpu-context snapshot: bench/sibs map cpu -> (busy, total) jiffies."""
    d = {
        "at": at, "load1": 1.0, "compilers": 0, "runner_workers": 0, "benchlock_open": [],
        "clock": "boost", "rapl_uj": None, "rapl_max_uj": None,
        "cpus": [{"cpu": c, "khz": khz} for c in bench],
        "stat": [{"cpu": c, "role": "bench", "busy": b, "total": t} for c, (b, t) in bench.items()]
        + [{"cpu": c, "role": "sibling", "busy": b, "total": t} for c, (b, t) in sibs.items()],
        "rest_stat": {"busy": rest[0], "total": rest[1], "cpus": rest[2]},
    }
    d.update(extra)
    return d


T0, T1 = "2026-11-21T00:00:00.000Z", "2026-11-21T00:00:10.000Z"


def pair(sib_busy=0, bench_busy=1000, rest_busy=0, khz=4000000, **extra):
    """Ten seconds on bench CPU 8 (sibling 72) and four rest CPUs, 1000 jiffies each."""
    before = snap(T0, {8: (0, 0)}, {72: (0, 0)}, rest=(0, 0, 4), khz=khz)
    after = snap(T1, {8: (bench_busy, 1000)}, {72: (sib_busy, 1000)},
                 rest=(rest_busy, 4000, 4), khz=khz, **extra)
    return before, after


class AttemptTest(unittest.TestCase):
    def test_idle_sibling_and_own_bench_time_is_clean(self):
        """A fully busy bench CPU whose busy time is all the child's own is not contaminated."""
        m = bc.attempt_metrics(*pair(), own_cpu_s=10.0)
        self.assertEqual(m["bench_foreign"], 0.0)
        self.assertFalse(bc.attempt_verdict(m)["contaminated"])

    def test_busy_sibling_contaminates(self):
        """A sibling above 5% busy over the attempt contaminates it, whatever the child did."""
        m = bc.attempt_metrics(*pair(sib_busy=60), own_cpu_s=10.0)
        v = bc.attempt_verdict(m)
        self.assertTrue(v["contaminated"])
        self.assertIn("sibling cpu 72 busy 6.0%", v["reasons"])

    def test_sibling_at_threshold_is_clean(self):
        """Exactly 5% is not above the threshold."""
        m = bc.attempt_metrics(*pair(sib_busy=50), own_cpu_s=10.0)
        self.assertFalse(bc.attempt_verdict(m)["contaminated"])

    def test_foreign_time_on_bench_cpus_contaminates(self):
        """Bench busy beyond the child's own CPU time is foreign; above 5% it contaminates."""
        m = bc.attempt_metrics(*pair(bench_busy=1000), own_cpu_s=9.0)
        self.assertAlmostEqual(m["bench_foreign"], 0.10)
        self.assertTrue(bc.attempt_verdict(m)["contaminated"])

    def test_bench_unjudged_without_own_time(self):
        """Without the child's CPU time, bench CPUs are not judged and the verdict says so."""
        m = bc.attempt_metrics(*pair(bench_busy=1000))
        self.assertIsNone(m["bench_foreign"])
        v = bc.attempt_verdict(m)
        self.assertFalse(v["contaminated"])
        self.assertIn("bench_foreign unjudged: no own_cpu_s", v["notes"])

    def test_frequency_deviation_contaminates(self):
        """A bench median clock more than 3% off the session median contaminates the attempt."""
        m = bc.attempt_metrics(*pair(khz=3800000), own_cpu_s=10.0)
        self.assertTrue(bc.attempt_verdict(m, session_median_khz=4000000)["contaminated"])
        m = bc.attempt_metrics(*pair(khz=3900000), own_cpu_s=10.0)
        self.assertFalse(bc.attempt_verdict(m, session_median_khz=4000000)["contaminated"])

    def test_rest_load_and_publication_rules(self):
        """Publication adds rest load < 4, no compiler, no runner worker, no foreign benchlock."""
        m = bc.attempt_metrics(*pair(rest_busy=4000), own_cpu_s=10.0)
        self.assertAlmostEqual(m["rest_load"], 4.0)
        self.assertFalse(bc.attempt_verdict(m, mode="dev")["contaminated"])
        self.assertIn("rest load 4.00 >= 4", bc.attempt_verdict(m, mode="publication")["reasons"])
        b, a = pair(compilers=2, runner_workers=1,
                    benchlock_open=[{"owner": "me", "pid": 1}, {"owner": "zb-9", "pid": 2}])
        v = bc.attempt_verdict(bc.attempt_metrics(b, a, own_cpu_s=10.0), "publication", owner="me")
        self.assertEqual(v["reasons"], ["2 compiler process(es)", "1 Runner.Worker process(es)",
                                        "other benchlock owner(s): zb-9"])

    def test_rapl_power_with_wraparound(self):
        """Package power is the energy delta over the interval, across a counter wrap."""
        b, a = pair()
        b.update(rapl_uj=900, rapl_max_uj=1000)
        a.update(rapl_uj=100, rapl_max_uj=1000)
        self.assertAlmostEqual(bc.attempt_metrics(b, a)["package_w"], 200e-6 / 10)


class SessionTest(unittest.TestCase):
    def test_void_above_twenty_percent(self):
        """A session with more than 20% contaminated attempts is void; 20% exactly is not."""
        clean = bc.attempt_metrics(*pair(), own_cpu_s=10.0)
        dirty = bc.attempt_metrics(*pair(sib_busy=500), own_cpu_s=10.0)
        self.assertFalse(bc.session_verdict([clean] * 4 + [dirty])["void"])
        s = bc.session_verdict([clean] * 3 + [dirty] * 2)
        self.assertTrue(s["void"])
        self.assertEqual(s["contaminated"], 2)

    def test_frequency_median_per_group(self):
        """The frequency rule compares an attempt with its own group's median, not across groups."""
        serial = bc.attempt_metrics(*pair(khz=4540000), own_cpu_s=10.0)
        wide = bc.attempt_metrics(*pair(khz=3990000), own_cpu_s=10.0)
        s = bc.session_verdict([serial, wide, serial, wide], groups=[1, 16, 1, 16])
        self.assertEqual(s["contaminated"], 0)
        s = bc.session_verdict([serial, wide, serial, wide, wide])
        self.assertGreater(s["contaminated"], 0)


class PublicationCheckTest(unittest.TestCase):
    def test_refusals_from_a_snapshot(self):
        """Publication refuses to start with load1 >= 4, a compiler or another benchlock owner."""
        ok = snap(T0, {8: (0, 0)}, {})
        self.assertEqual(bc.publication_refusals(ok), [])
        bad = snap(T0, {8: (0, 0)}, {}, load1=5.0, compilers=1,
                   benchlock_open=[{"owner": "zb-1", "pid": 3}])
        self.assertEqual(bc.publication_refusals(bad), [
            "load1 5.00 >= 4", "1 compiler process(es)", "other benchlock owner(s): zb-1"])

    def test_cli_refuses_with_a_synthetic_compiler(self):
        """`check --mode publication` exits 1 over a synthetic /proc holding rustc; dev exits 0."""
        with tempfile.TemporaryDirectory() as root:
            r = pathlib.Path(root)
            cpu = r / "sys/cpu8"
            for sub, val in [("cache/index3/shared_cpu_list", "8-15"), ("topology/core_id", "8"),
                             ("topology/thread_siblings_list", "8")]:
                (cpu / sub).parent.mkdir(parents=True, exist_ok=True)
                (cpu / sub).write_text(val + "\n")
            (r / "proc/9").mkdir(parents=True)
            (r / "proc/loadavg").write_text("0.10 0.10 0.10 1/1 1\n")
            (r / "proc/stat").write_text("cpu8 1 0 0 9 0 0 0 0 0 0\n")
            (r / "proc/9/comm").write_text("rustc\n")
            env = dict(os.environ, ZEEBRA_CPU_CONTEXT_SYS=str(r / "sys"),
                       ZEEBRA_CPU_CONTEXT_PROC=str(r / "proc"),
                       ZEEBRA_CPU_CONTEXT_CLASS=str(r / "class"),
                       ZEEBRA_BENCHLOCK_DIR=str(r / "bl"))
            cmd = [sys.executable, str(TOOLS / "bench_contamination.py"), "check", "--cpus", "8"]
            pub = subprocess.run(cmd + ["--mode", "publication"], env=env, capture_output=True,
                                 text=True)
            self.assertEqual(pub.returncode, 1, pub.stderr)
            self.assertIn("1 compiler process(es)", json.loads(pub.stdout)["refusals"])
            dev = subprocess.run(cmd + ["--mode", "dev"], env=env, capture_output=True, text=True)
            self.assertEqual(dev.returncode, 0, dev.stderr)
            (r / "proc/9/comm").write_text("bash\n")
            pub = subprocess.run(cmd + ["--mode", "publication"], env=env, capture_output=True,
                                 text=True)
            self.assertEqual(pub.returncode, 0, pub.stdout + pub.stderr)


if __name__ == "__main__":
    unittest.main()
