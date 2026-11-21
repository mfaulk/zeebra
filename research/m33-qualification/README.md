# #974 M33-Q: correctness, resource safety and held-out qualification

Plan: [`docs/MILESTONE-COMPETITIVE-BENCHMARKING.md`](../../docs/MILESTONE-COMPETITIVE-BENCHMARKING.md)
§§8.4, 11.4, 12, 13. **Status: prepared, not run.** F2 is not pinned yet, because #971 (G2) is still
in Gate C. Nothing here has timed Zeebra, and nothing has read a held-out row.

F0 is `31e334bd` (tag `measured/966-f0`). Both arms are built from `git archive` of their commit
with this directory's harness laid over it, [`examples/m33_qualify.rs`](../../examples/m33_qualify.rs).
The harness uses only public API that F0 already had, so the two binaries differ only in `src/`.

## Files

| File | What |
|---|---|
| [`examples/m33_qualify.rs`](../../examples/m33_qualify.rs) | One fresh-process solve. It covers GF(2), GF(32003), GF(2³¹−1), 2⁶⁴−59, 2⁶⁴−353 and Goldilocks under grevlex, graded-lex or lex, with `--engine entry` (`f4_signature_reported`) or `f4`. It reports the typed outcome, the route, the `m33-basis-v1` digest (made monic at the grevlex leading term, as `basis_digest.py` is), the thread high-water and the warm calls. |
| [campaign.py](campaign.py) | `build` (F0 or F2 plus the harness), `manifest` (one bench-job manifest per suite), `inputs` and `references` |
| [summarize.py](summarize.py) | `correctness`, `regression` and `gate-d` verdicts from job directories |
| [references.json](references.json) | Complete for all 71 correctness rows. One independent `m33-basis-v1` per correctness row, untimed, on CPUs 24–39. Below 2³¹ (GF(2) included) it is Singular `std` with `redSB` in `dp`, `Dp` or `lp`; on wide fields it is groebner-rs at one worker. Grevlex rows that the F0 cohort already referenced reuse `research/m33-baseline/references.json`. |
| [test_qualification.py](test_qualification.py) | Tests for the Gate D refusals, the held-out guard and the verdict rules. They run in CI. |
| [`tests/m33_safety.rs`](../../tests/m33_safety.rs), [`tests/m33_thread_cap.rs`](../../tests/m33_thread_cap.rs) | The safety suite (deliverable 3) |

## Suites

The correctness suites use 3 repetitions at 1 and 16 workers. The others use the plan's n.

| Suite | Rows | Arms | Workers | n | Attempts |
|---|---|---|---|---:|---:|
| `grevlex` | 44: the 17 F0 development and control rows, plus Katsura-8, Eco-9, Cyclic-6, Noon-7 and MQ9-s2 at all six fields (no Noon at GF(2)) | F0 and F2 × entry and f4 | 1, 16 | 3 | 1,056 |
| `grlex` | 12: every instance in #961's table, plus GF(2) Katsura-7 and Cyclic-6 | F0 f4, F2 entry, F2 f4 | 1, 16 | 3 | 216 |
| `lex` | 15: Katsura-4 and Eco-6 at all six fields, Cyclic-5 below 2³¹ (groebner-rs does not finish lex Cyclic-5 or Katsura-5 in 600 s) | F0 and F2 × entry and f4 | 1, 16 | 3 | 360 |
| `regression-G` / `-M` | Track G / M controls of at least 300 ms in the F0 cohort | F0 and F2 × entry and f4 | G 1, 16; M 1, 4, 8, 16 | 9 | 144 / 144 |
| `small-G` / `-M` | the controls under 300 ms, read by warm calls (22 calls per process, the cold one dropped) | as above | as above | 31 | 992 / 1,488 |
| `gate-d-G` / `-M` | the four held-out rows of `research/m33-baseline/held-out.json` | F0 and F2 entry | G 1, 16; M 1, 4, 8, 16 | 9 | 72 / 144 |

Goldilocks MQ11 under graded-lex is a typed `TooManyLiveNonzeros` stop on the shipping F4 at the
default budget (#961's table). There the check is that F0 and F2 stop the same way; the reference
is recorded but nothing is compared to it.

The `grlex` suite has no F0 entry arm. On F0, graded-lex takes the signature route, which is #961
itself (> 8 GiB). Under F2 the entry point must report `Shipping(Order)` and return F0 f4's digest.

### What each verdict checks

**Correctness** (§12.1). A row fails unless all of the following hold:
- Every complete attempt, across arms, workers and repetitions, has one digest, and it equals the
  reference.
- Under lex, the entry point gives a typed `Unsupported` refusal.
- Under graded-lex, F2's entry point routes to F4 by rule.
- F2 keeps every typed outcome F0 had per engine and worker count (for example, a
  `TooManyLiveNonzeros` stop stays a `TooManyLiveNonzeros` stop).
- No attempt reports more threads than requested.

**Regression** (§12.2). Each cell is paired F2 ÷ F0 per repetition, using `bench_stats.paired_ratio`
and `regression_verdict`. The rules:
- Wall: the upper bound must be ≤ 1.05.
- A row under 300 ms is read only from the warm-call suite.
- Peak RSS ≤ 1.25×. Growth above 1.10× is flagged for explanation.
- Contaminated attempts are excluded under the dev rule (per-arm clock, #998).

**Gate D** (§13). The held-out read uses the same statistic and must pass with every upper bound
≤ 1.05. Rules:
- `manifest --suite gate-d-*` and `summarize.py gate-d` each refuse unless `--gate-d --f2 <commit>`
  are given.
- The summarizer also refuses a job whose manifest is not a Gate D job pinned at that F2.
- It writes `gate-d.md` and refuses to run again once that file exists.
- Every other suite refuses a held-out row by name and by input digest.
- The Gate D manifests default to publication mode.

## Safety suite (deliverable 3)

The rows are Katsura-11, at 2⁶⁴−353 and 2³¹−1. At 16 workers the signature route runs a 16-worker
parallel cascade there: eleven variables are past both the small-team and the worker-crossover
bands. Each test was shown to bite by disabling its budget in `src/` (temporarily, then reverted)
and running it.

| Test | Asserts | Disabled by | Result disabled |
|---|---|---|---|
| wall, 1 and 16 w | typed `TimeBudgetExceeded` or `InterreductionTimeBudgetExceeded`, route `Signature`, back within budget + 20 s | `signature_options` passes `max_wall_time: None` | `1 workers: expected a typed time stop, got Ok(..)` |
| matrix rows, 1 and 16 w, two fields | `Shipping(Fallback(TooManyRows))`, result equal to the shipping F4's typed refusal | the engine's `rows.len() > max_matrix_rows` check made `false` | route assertion fails |
| live bytes, 1 and 16 w, two fields | `Shipping(Fallback(TooManyLiveBytes))`, result equal to the shipping F4's | the serial cascade's `LiveBudget::charge` (#986) never fails; separately, the parallel cascade's `live_limit: None` | `1 workers: Signature`; `16 workers: Signature` |
| cancellation, 1 and 16 w | an observer stop returns `StoppedByObserver` after exactly the allowed batches, with counters | the `should_stop` check before elimination made `false` | `1 workers`: `Ok(..)` |
| thread cap 3 and 16, both routes | ≤ 1% of parallel-phase samples have more than `cap` threads running (state `R`), and no worker outlives a budget-stopped call | the signature team given `workers + 1`; separately, `auto_workers` capped at `max_workers + 1` | 10,159 of 10,313 samples over; 26,983 of 28,449 over (unmodified: 0 and ≤ 7 of tens of thousands) |

The 1% allowance in the thread test covers a caller that is still runnable while it spawns or joins
its team. #941's adverse-schedule suite is `sigf4::cascade_tests`, in the library, and Q runs it
unchanged.

## Run at F2

```sh
export M33Q_BUILD=/buildcache/cargo-target/zeebra-974 TMPDIR=$M33Q_BUILD/tmp ZEEBRA_BENCH_JOBS=$M33Q_BUILD/jobs
F2=<pinned commit>; git tag measured/974-f2 $F2
Q=research/m33-qualification
python3 $Q/campaign.py build --commit 31e334bd --harness 895879c8   # F0 binary
python3 $Q/campaign.py build --commit $F2 --harness 895879c8        # F2 binary
cargo test --test m33_safety --test m33_thread_cap && cargo test --features research-sigf4 --lib cascade_tests  # at F2
python3 $Q/campaign.py references --study $F2BIN          # fills any row references.json lacks
A="--f0-study $F0BIN --f2-study $F2BIN --f2 $F2 --agent $(scripts/agent/zb-claim.sh id)"
for s in grevlex grlex lex regression-G regression-M small-G small-M; do
  python3 $Q/campaign.py manifest --suite $s $A > $M33Q_BUILD/$s.json
  tools/bench-job submit $M33Q_BUILD/$s.json              # then: tools/bench-job run <id> (reserved CCDs)
done
python3 $Q/summarize.py correctness <grevlex job> <grlex job> <lex job>
python3 $Q/summarize.py regression <regression-G job> <regression-M job> --small <small-G job> <small-M job>
# Only after every suite above passes, once:
python3 $Q/campaign.py manifest --suite gate-d-G --gate-d $A > $M33Q_BUILD/gate-d-G.json   # likewise -M
python3 $Q/summarize.py gate-d --gate-d --f2 $F2 <gate-d-G job> <gate-d-M job>   # post the raw table on #965 first
```

## Run at F2 `db181c51`

`results/` holds the summarizer output of the 2026-11-21 session (`correctness.md`, `regression.md`,
`jobs.txt`). The write-up is [`docs/research/m33-qualification.md`](../../docs/research/m33-qualification.md):
Q did not pass and Gate D was not run. Repetitions pool across jobs, so a top-up job for cells
short of n is passed beside the first job.

## Dry run (pipeline proof, not a measurement)

Run on 2026-11-21 with n = 1 on CPUs 24–39 (off the CCD 1–2 reservation, which another campaign
held), through a pass-through reserve shim (as `tools/bench-job-smoke.sh` does). F0 was
`31e334bd`, and the stand-in for F2 was `e13fa7fd`, whose `src/` is main `577266dc`'s. This was not
a measurement session; its walls are not results.

- **Correctness:** 8 of 8 rows pass. The rows were `grevlex` w59/Katsura-8, GF(2)/Cyclic-6,
  wide64/Katsura-4 and m31/Eco-11; `grlex` m31/Eco-11 and GF(2)/Katsura-7; `lex` GF(2)/Katsura-4
  and wide64/Eco-6. Every digest equals its Singular or groebner-rs reference. Lex was refused,
  typed, on the entry point, and graded-lex went to `Shipping(Order)` at the stand-in.
- **Warm calls:** `small-M` gf32003/Katsura-4 ran 22 calls per process, and the pipeline produced
  paired ratios. Every verdict reads `stopped: n = 1 < 31`, as intended. Four 16-worker attempts were
  contaminated by foreign load, so the session read as **void**, which the summarizer reports.
- **Gate D:** `summarize.py gate-d` without `--gate-d --f2` exited 2 with the refusal.
