# #1106 pilot (exploratory: decides nothing)

**Measured at:** `C` = `5451e9f853c8f24bafed6875218a175de441e3f0`. `sig_f4_study` and
`m29_cost_model` were built from `git archive C`, `--locked`, release, fat LTO, 1 CGU, with
`RUSTC_WRAPPER="" CARGO_INCREMENTAL=0`. `sweep` (this directory's `../sweep.c`, not in `C`) and
`stream` (`research/m33-calibration/stream.c`) were built with `cc -O2 -pthread`. SHA-256s are in
`session-1/summary.md`. Run 2026-11-25, 13:44:20–13:52:57 and 13:53:32–14:08:57 EST: 24 minutes of
reserved CCDs 1–2 against the 1 h budget, released cleanly. The fallback reservation of
[protocol](../../../docs/research/concurrent-benchmark-calibration-protocol.md) §5.3 was in force
(#1104's 1-CCD policy has not landed) and the clock mode was boost. Every attempt is a dev-mode
`bench-job` attempt, labeled `pilot` in its manifest's `context`. Per §7.1 it is excluded from every
decision.

## What it found

| Protocol item | Result |
|---|---|
| §7.2 n | **30 for every calibration cell: the cap binds.** At n₀ = 9 the A/A 95% CI half-widths are 1.0–5.8% (`session-1/summary.md`), and C-P16 and C-M16 are the widest at 5.8% and 5.1%, idle. Scaling by √(9/30) predicts ±3.1% and ±2.8% at n = 30. That is wider than the proposed A/A gate's CI band of [0.975, 1.025], so the 16-worker cells would likely fail H1 *idle*, which §7.3 treats as an instrument failure that stops the campaign. |
| §4.3 held-out small pair | **H-S16 = `cyclic7-wide64`** (16 workers): `distinct/every` 0.965 [0.953, 0.973] idle, the first candidate in order. `katsura11-wide64` and `katsura11-m31` are 0.89, too large an effect to qualify. C-P16's own idle effect is 0.968 [0.956, 1.010], whose CI does not exclude 1 at n = 9. |
| §4.2 `m5` tuning | **Tuned on 1 of 6 cells.** Eco-12 1w: 32 MiB, 13 passes, validated at 1.043. On every sub-second cell, allocation and first touch alone exceed the 5% budget even at 32 MiB: t₀ = 58 ms for 1 thread and 256 ms for 16, against budgets of 12–23 ms. So `m5/a` reads 1.20 (1w) and 1.55–2.12 (16w) and the cells are untuned. As specified, H2's and H6's contention-sensitive control exists only on C-E1, which is a calibration cell, so no held-out cell has one. |
| Binaries | `C` and the four SHA-256s are in `session-1/summary.md`; `grobx-driver` and `msolve` were not needed by the pilot. |

## Decisions this hands the owner (before signing §6)

1. **The A/A CI band versus n ≤ 30.** Options are to widen the band for 16-worker cells, to lift
   the cap (n = 60 would predict about ±2.2% for C-P16), or to accept that 16-worker cells cannot
   pass H1. The protocol should fix this before #1107, not after.
2. **`m5` on sub-second cells.** As written, it cannot be tuned there. Options: keep the allocation
   out of the timed region (have the wrapper allocate before the binary runs, then sweep after);
   use one sweep thread whatever the worker count; or drop `m5` from cells under about 1.5 s and
   let H2/H6's positive control rest on Eco-12 and H-P1. Each one is a protocol amendment.

## Files

| Path | What |
|---|---|
| `pilot.py`, `launch.sh` | the driver: waits for the machine, reserves, runs each job below, tunes and validates `m5`, releases. A finished job is reused on resume (`job-<label>`) |
| `summarize.py` | §7.2 n, §4.3 qualification, §4.2 table → `session-1/summary.md` |
| `session-1/manifest-*.json`, `job-*`, `run-*.log`, `events.log`, `results.json` | each job's manifest, id, runner log, the timeline, and the tuning record |
| `session-1/journals/*.jsonl.gz` | every attempt of every job (§10 retention) |

Jobs: `S1`/`S16` = `sig_f4_study` `a`, `a2` on the 1- and 16-worker cells (held-out cells idle only).
`P` = `m29_cost_model` `every`, `distinct`, `distinct2`. `SW` = `sweep` at 0 and 1 passes, 64 and
32 MiB. `V*-try*` = `a` vs `m5` validation. `-W4` = the same under W4-32 (`stream 32` on
`0-7,24-71,88-127`), calibration cells only.

**Defect in session 1's loaded steps.** The loader was started as `setsid taskset … stream 32` in a
new session. `setsid`, already a group leader, forked, so `stream` landed outside the group that
`killpg` stopped, and every loader outlived its step. `S1-W4` ran under one W4-32 loader, `S16-W4`
under two, `P-W4` under three. The three were killed by pid at 15:38, after running ~1.5 h with the
machine otherwise released; `benchlock.log` shows no other bench run in that window. So the W4 rows
of `summary.md` are W4-32, W4-64 and W4-96 respectively, not W4-32. n is unaffected, because every
cell's larger half-width is its idle one. `pilot.py` now launches the loader without `setsid`.

Side finding: `bench_running` (#1105) lists the snapshot's own `cat`/`awk` in 343 of 1,049
snapshots. Its self-exclusion skips children of the script, but these are grandchildren, so the
field reports the harness as foreign work. Noted on #1148.
