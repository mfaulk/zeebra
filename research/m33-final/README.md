# #975 M33-I: publication-mode competitive campaign

Plan: [`docs/MILESTONE-COMPETITIVE-BENCHMARKING.md`](../../docs/MILESTONE-COMPETITIVE-BENCHMARKING.md)
§§8, 9.10, 11, 16; the report is that document's §17.

**Measured at:** F3 = F2 = `db181c51` (tag `measured/975-f3`; `sig_f4_study` SHA-256 `beecc346…`)
and F0 `31e334bd`, built from `9d6f16e4` (tag `measured/975-f0-harness`; `f8c844ee…`). Comparands
are #966's pins. Sessions on 2026-11-22: Track G, jobs `92e26e267f3d`, `7fa0250e1309` and
`d5db6121722d`; Track M, jobs `ea52bc970e59` (interrupted and resumed) and `b5a15591d188`. The
predeclaration below was committed before any timed attempt; the results are in
[tables.md](tables.md) and §17 of the plan.

## Predeclaration

**Freezes.** F3 = F2 = `db181c51` (tag `measured/974-f2`): `git log db181c51..origin/main --numstat --
src/grobner src/linalg src/fields src/poly` is empty at pin time. F0 = `31e334bd` (tag
`measured/966-f0`), rebuilt beside it from `git archive 9d6f16e4` exactly as M33-0 built it
(`src/`, `Cargo.toml`, `Cargo.lock` identical to F0; its `sig_f4_study` predates F3's added
statistics). Both: `--features research-sigf4`, release, fat LTO, one codegen unit, x86-64-v3,
`RUSTC_WRAPPER=""`, `CARGO_INCREMENTAL=0`. Comparands at #966's pins (`research/m33-baseline/pins.json`).

**Jobs.** `tools/bench-job` in publication mode (exclusive benchlock, CPUs 8–23, siblings idle),
n = 9, arms rotated per repetition, a fresh process per attempt, 180 s and 8 GiB caps.

| Job | Rows | Arms | Workers |
|---|---|---|---|
| G | Track G development, control and held-out (11) | F3 and F0 × {sigf4 1 w, entry 1 w, entry 16 w}; grobx 0.155.1 raw; groebner-rs | 1; entry 16 w |
| Gc | wide64 / Eco-12 (the Track G primary) | grobx 0.155.1 certified, 600 s / 32 GiB (M31's declared cap) | 1 |
| M | Track M development, control and held-out (10) | F3 and F0 entry; msolve 0.11.0 | 1, 4, 8, 16 |

Jobs G and Gc form the Track G session and run in one window. The session cap is 3 (plan §13): one
per track plus one spare. A session over 20% contaminated is void; it is dropped whole and re-run
whole, and the re-run is the session of record. Every attempt is retained.

**Scoring (fixed before reading).**
- Track G: F3 `sigf4` at 1 w ÷ grobx raw at 1 w, as M33-0 scored it; F3 `entry` is reported beside
  it. Zeebra entry at 16 w ÷ grobx at 1 w is the best-supported row, kept separate, never scoring.
- Track M: F3 `entry` ÷ msolve at the same count. A count where msolve's median is more than
  1.10× its own best over {1, 4, 8, 16} in this session is an anomaly and cannot score T-M.
- Ratio = median ÷ median of process wall, 95% percentile bootstrap, 20,000 draws, each side
  resampled independently (`tools/bench_stats.py`). Win: median < 1 and upper < 1. A spanning row
  that could score (development or held-out, not small, not anomalous) gets the one n = 12
  extension, pooled and read once.
- Small rows (M33-0's rule: competitor median < 300 ms on Track G; either median < 300 ms on
  Track M) are reported, never scored.
- An attempt counts only if it is `ok`, uncontaminated, and its `m33-basis-v1` digest equals the
  row's independent reference ([references.json](references.json)).
- Gate D confirmation (§8.4): a development-row win scores only if it wins again here **and** each of
  that track's held-out rows at the same worker count reads ≤ that development ratio + 0.15. Where a
  reading the plan admits would change the verdict, the verdict is left to the owner.
- F3 ÷ F0 is paired per repetition and reported beside each row; it does not re-run Q's gates.

**Amendment, 16:40Z, after job `92e26e267f3d` completed (valid, 65/792 contaminated, every flag the
per-arm clock rule).** Contaminated attempts left cells short of 9 clean attempts (as few as 4),
which `bench_stats.win_verdict` reads as `stopped`, not a row class. As Q's session 2 did, each
track's main job is followed in the same reservation window by one **top-up job** of the same arms
and rows at n = 5 (the largest shortfall), and its clean attempts are pooled with the main job's
and read once. The top-up belongs to the track's session. Track G's main-job ratios were seen before
this amendment; no development row's interval reaches 1 there.

## Outcome

Two of the three allowed sessions ran, both valid: 2,913 attempts, 279 contaminated (all by the
per-arm clock rule), and every digest equal to its reference. One grobx certified attempt was
completed and the job was then refused on output size (#1020). `campaign.py inputs` now writes Track
Gc's request with `digest_only: true`, so its reply carries the basis digest and not the 1.70 GB of
certified text; a re-run is therefore a new input and a new job id, and job `d5db6121722d`'s record
is the full-reply run.

**Track Gc digest-only re-run (#1065), 2026-11-23, job `16693d8f6a58`: void.** The same input with
`digest_only: true` and the same manifest, at F3 = `db181c51`. The grobx 0.155.1 driver was built
from `main` `28df047f` with `grobx-pin.sh`'s recipe (SHA-256 `e2572de9…`). Publication mode, CCDs 1–2
reserved, 16:21–17:05Z. All 9 attempts were `ok`, digest-equal to the reference and under the
600 s / 32 GiB caps, with process wall 272.6–299.1 s (median 296.4 s) and peak RSS 8.7 GiB. All 9
were contaminated, though: other sessions' compilers, rest load ≥ 4 on 4 attempts, and the clock rule on
3. Over 20% contaminated makes the session void, so it is not of record (`sessions.json`, `void`) and
no certified-grobx timing is scored from it. The walls are reported here only to show that the
job now completes n = 9. The job no longer stops on output size: the retained journal is 56 KB,
against 1.70 GB for `d5db6121722d`.

**Track Gc of record: job `577f983483fb`, 2026-11-24 02:39–03:20Z.** This is a quiet-window re-run of
the same manifest (only `context.session` = `rerun` differs, so it gets a new job id), at F3 =
`db181c51` with grobx 0.155.1 `8005a2a1` (driver SHA-256 `e2572de9…`, built from `main` `28df047f`).
- **Valid.** All 9 attempts are `ok`, certified, and digest-equal to the reference, and **0 of 9 are
  contaminated**.
- **Figures.** Process wall median 267,723.8 ms (range 265.7–272.0 s), peak RSS 8.7 GiB.
- **Of-record list.** `sessions.json` now lists it as Track Gc's record. `d5db6121722d` is
  `superseded`: a single full-reply attempt on a different input, which must not be pooled with the
  digest-only attempts. `tables.md`'s certified reference row reads this job alone.
- **Scoring.** It is still a reference row, never scoring (predeclaration). `history.json` is
  append-only, so it is not re-appended here.

No row qualified for the n = 12
extension: every inconclusive row is small or short of n, not spanning. No third session was run.

Verdicts (plan §17.8): Minimum met. **T-G missed**: no development row wins against grobx raw.
**T-M missed (not confirmed at Gate D, owner decision 16 on #965)**: Katsura-11 wins again at 8 w
(0.452 [0.449, 0.453] on GF(2³¹−1), 0.536 on GF(32003)), and held-out Katsura-12 reads 0.453, but
held-out mq-random-10-s1 reads 1.689 against the 0.602 bar. T-B, T-Q, T-R, S-4 and S-5 met; S-1,
S-2 and S-3 missed.

## Reproducing the tables

```bash
python3 research/m33-final/summarize.py           # regenerate tables.md from the retained records
python3 research/m33-final/summarize.py --check   # fail if tables.md is stale
python3 -m unittest research/m33-final/test_final.py
python3 research/m33-final/campaign.py board      # print the CompetitiveRecord rows (--append writes history.json)
```

Re-running a session needs the builds and inputs (`campaign.py inputs`, `references`, `manifest
--track G|Gc|M`) and `session.sh <track-label> <job-id>…` under `tools/bench-job` in publication mode.
