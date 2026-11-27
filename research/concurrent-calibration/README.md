# #1107 concurrent-benchmark calibration

**Measured at:** `C` = `5451e9f853c8f24bafed6875218a175de441e3f0` for every Zeebra binary. Harness:
`tools/bench-job` with `arms[].instances` (`93f96542`), and this directory's driver as committed on
the PR branch (tagged `measured/1107-concurrent-calibration` once merged). Binaries:
`sig_f4_study` `6ffc1e88…`, `m29_cost_model` `cb2c17ce…`, `sweep` `7b48f39b…`, `stream` `bc0bf4ac…`,
`grobx-driver` 0.155.1 `fdd6aeec…`, and `msolve` 0.11.0 `557470de…`. Full hashes are in `calib.py`'s
`SIGNED`; `prepare.py` refuses any other binary. Clock: boost (#954 open). Reservation: §5.3's
fallback, CCDs 1–2.

This runs the protocol in
[`docs/research/concurrent-benchmark-calibration-protocol.md`](../../docs/research/concurrent-benchmark-calibration-protocol.md)
as the owner signed it on 2026-11-25 (#1106). The same day the owner decided two things about the
budget: it is counted as reservation wall-hours, and the optional W6 is dropped. The pilot is in
[`pilot/`](pilot/README.md).

## Files

| Path | What |
|---|---|
| `calib.py` | the protocol as code: cells (§3–§4.5), manifests, §6 gates, §8.4 fit, extraction. `test_calib.py` covers it (CI) |
| `prepare.py` | sets up `$W` = `/buildcache/cargo-target/zeebra-1107`: binaries checked against the signed hashes, the `s5`/`m5` wrappers, comparand inputs, the workloads' `git archive C` and warm builds |
| `session.py`, `run.sh` | one session (W0, the shuffled loaded workloads, W0; both cohorts each), or one (cohort, workload) job. Applies §7.3's stops |
| `chain.sh` | starts a later session unattended on its day, announcing its heavy windows on #1107 |
| `references.json` | the basis digest per instance; every arm, grobx and msolve included, agreed on it in a smoke repetition |
| `extract.py`, `fit_limits.py`, `summarize.py` | §8.6's interfaces |
| `throughput.py` | §8.3's development-throughput measurement |
| `sweep.c` | §4.2's DRAM sweep (`m5`) |
| `limits.json` | the §8.4 limit, fitted on calibration only; SHA-256 `283ba430…41f4`, posted on #1107 before the summary |
| `tables.md`, `throughput.json` | every result table, and §8.3's build walls. The write-up is [`docs/research/concurrent-benchmark-calibration.md`](../../docs/research/concurrent-benchmark-calibration.md) |
| `data/` | per-attempt records and event logs for both sessions, the bench-job journals (gzipped, without stdout blobs) and the harness-bug stop |

## Reproduce

```bash
python3 -I research/concurrent-calibration/prepare.py --pilot-dir <dir with the C binaries> --grobx <grobx-driver> --msolve <msolve>
python3 -I research/concurrent-calibration/session.py session s1-YYYYMMDD --seed YYYYMMDD
python3 -I research/concurrent-calibration/fit_limits.py --records $W/sessions/*/records-*-calibration-*.jsonl.gz --out research/concurrent-calibration/limits.json
python3 -I research/concurrent-calibration/throughput.py throughput-YYYYMMDD
python3 -I research/concurrent-calibration/summarize.py --records research/concurrent-calibration/data/s*/records-*.jsonl.gz \
    --limits research/concurrent-calibration/limits.json --limits-sha <posted> \
    --throughput research/concurrent-calibration/throughput.json --out research/concurrent-calibration/tables.md
```

## Log

- **2026-11-25, session 1.** At 17:00 it stopped on an idle A/A "failure" in C-P16. That was a
  harness bug: the m29 A/A was paired `distinct2`/`every`, which is the real effect, instead of
  `distinct2`/`distinct`. The fix has a test (`1420417d`). The stop is recorded in
  `harness-bug-stops.json`, not counted toward §7.3, and the session resumed at 17:01, reusing the
  finished W0 job.
- **2026-11-25, W2 is lighter than its name.** A clean `cargo build -j48 --tests` of this crate spends
  most of its wall in one `rustc --crate-name zeebra` at about 2 CPUs. Load average under W2 was
  4–8 (under W5, which adds `stream 16`, 15–19). The command is the protocol's (§2), and #985's, so
  it stays. But W2's row in the decision table speaks for "a Zeebra rebuild", not for a parallel
  multi-crate build of 48 jobs.
- **2026-11-26, done.** Session 2 ran 08:00–16:08 with no stop; throughput ran until 19:32. The
  preregistered verdict is no-go for #1108, decided by H1's width clause, which fails idle against
  idle about as often as under load. The owner chose to publish it as is; the follow-up is #1180.
  While summarizing, H5 turned out to pass vacuously when a rule set emptied its cells. That is
  fixed, with a test, before the tables were committed.
