#!/usr/bin/env python3
"""Unit tests for tools/bench_contamination.py; run: python3 tools/test/bench-contamination-test.py"""

import gzip
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

    def test_per_arm_groups_leave_foreign_and_sibling_rules_unchanged(self):
        """Grouping per arm moves only the clock median: a busy sibling still contaminates its attempt."""
        steady = [bc.attempt_metrics(*pair(khz=k), own_cpu_s=10.0) for k in (2670000, 4540000) * 3]
        groups = ["a", "b"] * 3
        self.assertEqual(bc.session_verdict(steady, groups=groups)["contaminated"], 0)
        busy = bc.attempt_metrics(*pair(khz=2670000, sib_busy=500), own_cpu_s=10.0)
        s = bc.session_verdict(steady + [busy], groups=groups + ["a"])
        self.assertEqual(s["contaminated"], 1)
        self.assertIn("sibling cpu 72 busy 50.0%", s["attempts"][-1]["reasons"])


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


def psi(some, full=None):
    return {"some_us": some, "full_us": full}


def telemetry(compilers_on_bench=0, compilers_elsewhere=0, psi_cpu=0, pgscan=0, mbm=0,
              ccd=(0, 0), running=()):
    """The #1105 snapshot fields, as tools/cpu-context.sh prints them."""
    return dict(telemetry=1, compilers_on_bench=compilers_on_bench,
                compilers_elsewhere=compilers_elsewhere, runner_workers_on_bench=0,
                psi={"cpu": psi(psi_cpu), "memory": psi(0, 0), "io": {"unavailable": "no pressure/io"}},
                psi_bench_slice={"unavailable": "no zbbench.slice"},
                vmstat={"pswpin": 0, "pswpout": 0, "pgscan": pgscan, "pgsteal": 0, "pgmajfault": None},
                mbm_bytes=mbm, ccd_stat=[{"l3": "8-15,72-79", "busy": ccd[0], "total": ccd[1], "cpus": 2}],
                bench_running=[{"pid": 9, "comm": c, "cpu": 72} for c in running])


class TelemetryTest(unittest.TestCase):
    """Interference telemetry (#1105) is metrics, not rules: it never changes a verdict."""

    def pair(self, **after):
        before = snap(T0, {8: (0, 0)}, {72: (0, 0)}, rest=(0, 0, 4), **telemetry())
        a = snap(T1, {8: (1000, 1000)}, {72: (0, 1000)}, rest=(0, 4000, 4), **telemetry(**after))
        return before, a

    def test_deltas_over_the_attempt(self):
        """Pressure is a fraction of the attempt's wall, counters are deltas, load is per domain."""
        m = bc.attempt_metrics(*self.pair(psi_cpu=1_000_000, pgscan=40, mbm=5_000_000,
                                          ccd=(1000, 2000), running=("rustc",)), own_cpu_s=10.0)
        self.assertEqual(m["telemetry"], 1)
        self.assertEqual(m["psi"]["cpu"], {"some": 0.1, "full": None})
        self.assertEqual(m["psi"]["memory"], {"some": 0.0, "full": 0.0})
        self.assertEqual(m["vmstat"]["pgscan"], 40)
        self.assertIsNone(m["vmstat"]["pgmajfault"])
        self.assertEqual(m["mbm_bytes_per_s"], 500_000.0)
        self.assertEqual(m["ccd_load"], {"8-15,72-79": 1.0})
        self.assertEqual(m["bench_running"], ["rustc"])

    def test_placement_counts_take_the_larger_snapshot(self):
        m = bc.attempt_metrics(*self.pair(compilers_on_bench=2, compilers_elsewhere=5))
        self.assertEqual((m["compilers_on_bench"], m["compilers_elsewhere"]), (2, 5))

    def test_unavailable_is_never_a_value(self):
        """An unavailable source stays unavailable through the deltas, and `available` says so."""
        m = bc.attempt_metrics(*self.pair())
        self.assertEqual(m["psi"]["io"], {"unavailable": "no pressure/io"})
        self.assertEqual(m["psi_bench_slice"], {"unavailable": "no zbbench.slice"})
        for value in (None, m["psi"]["io"], m["psi_bench_slice"]):
            self.assertFalse(bc.available(value))
        self.assertTrue(bc.available(0))

    def test_old_snapshots_record_nothing(self):
        """A snapshot from before #1105 has no telemetry: every new metric is None, not zero."""
        m = bc.attempt_metrics(*pair(), own_cpu_s=10.0)
        for key in bc.TELEMETRY_METRICS:
            self.assertIsNone(m[key], key)

    def test_verdicts_ignore_telemetry(self):
        """Placement does not yet excuse a compiler elsewhere: publication still counts them all."""
        before, after = self.pair(compilers_on_bench=0, compilers_elsewhere=2)
        after["compilers"] = 2
        m = bc.attempt_metrics(before, after, own_cpu_s=10.0)
        bare = {k: v for k, v in m.items() if k not in bc.TELEMETRY_METRICS}
        for mode in bc.MODES:
            self.assertEqual(bc.attempt_verdict(m, mode), bc.attempt_verdict(bare, mode))
        self.assertIn("2 compiler process(es)", bc.attempt_verdict(m, "publication")["reasons"])


def retained_attempts():
    """(job, mode, exit metadata) for every attempt in the repository's retained bench-job journals."""
    for journal in sorted(TOOLS.parent.glob("research/*/journals/*/journal.jsonl.gz")):
        header = json.loads((journal.parent / "header.json").read_text())["header"]["bench_job"]
        for line in gzip.decompress(journal.read_bytes()).splitlines():
            r = json.loads(line)
            c = r.get("metadata", {}).get("contamination") or {} if r["kind"] == "exit" else {}
            if c.get("metrics") and all("stat" in (r["metadata"].get(s) or {}) for s in ("before", "after")):
                yield header["job_id"], c["mode"], r["metadata"]


class ReplayTest(unittest.TestCase):
    """Old snapshots give the metrics and verdicts on record (#1105's bit-identity requirement)."""

    def test_retained_journals_replay_identically(self):
        n = 0
        for job, mode, md in retained_attempts():
            stored = md["contamination"]["metrics"]
            khz = [stored["median_khz"]] if stored["median_khz"] else None
            m = json.loads(json.dumps(bc.attempt_metrics(md["before"], md["after"], khz_samples=khz)))
            for key in set(stored) - {"bench_foreign"}:  # own CPU time is not journaled on its own
                self.assertEqual(m[key], stored[key], f"{job} {md['attempt_id']} {key}")
            merged = dict(stored, **{k: m[k] for k in bc.TELEMETRY_METRICS})
            self.assertEqual(bc.attempt_verdict(merged, mode, owner=f"bench-job-{job}"),
                             md["contamination"]["verdict"], f"{job} {md['attempt_id']}")
            n += 1
        self.assertGreater(n, 100, "the retained journals should hold the M33 sessions")


if __name__ == "__main__":
    unittest.main()
