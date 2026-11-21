# M33-Q: qualifying F2 against F0

**Measured at:** F2 `db181c51` (tag `measured/974-f2`) against F0 `31e334bd`, both built with the
harness `examples/m33_qualify.rs` at `dd57bc4e` (content identical to `895879c8`) by
`research/m33-qualification/campaign.py build`. Binary sha256 prefixes: F0 `fe8fe83cb14a861b`, F2
`b14b4680e3221daa`. One bench-job session, 2026-11-21 17:58Z–23:01Z, CPUs 8–23 under the CCD 1–2
reservation (`tools/bench-reserve.sh`), dev mode, clock rule per arm (#998).

Result: **Q did not pass.** The safety suite passes, correctness fails on 6 of 71 rows, regression
has no failing row but 24 of 56 cells end short of n, and Gate D was therefore **not run**: the
held-out rows were never timed. Nothing was reverted; the decision is the orchestrator's (#965).

## Safety (at F2)

| Suite | Result |
|---|---|
| `tests/m33_safety.rs` (wall, row, byte budgets and observer stop; 1 and 16 w) | 4 / 4 pass |
| `tests/m33_thread_cap.rs` (caps 3 and 16) | 1 / 1 pass |
| `sigf4::cascade_tests` (`--features research-sigf4`) | 9 / 9 pass |

## Correctness: 65 of 71 rows pass

Full table: `research/m33-qualification/results/correctness.md`. The six failures are of two kinds.

| Row | Verdict |
|---|---|
| grevlex/gf32003/katsura-11 | f2-f4 at 16 w: 18 threads |
| grevlex/gf32003/noon-7 | f0-f4 at 16 w: 21 threads |
| grevlex/wide64/cyclic-7 | f2-entry at 16 w: 21 threads |
| grevlex/wide64/noon-8 | f0-f4 at 16 w: 17 threads |
| grlex/wide64/eco-12 | f2-f4 at 16 w: 17 threads |
| grlex/gf2/cyclic-6 | f2 entry under graded-lex took `Shipping(DegreeSpread)`, not `ShippingReason::Order` |

Every digest matches its reference, and every lex entry call refuses.

**Thread peaks.** Of 1,632 sampled attempts, 5 attempts peaked above the cap, one apiece in the 5 rows: 2 at F0 and 3 at F2,
all at 16 workers, each in one repetition of three. The harness sampler (`sampled()` in
`examples/m33_qualify.rs`) counts *alive* entries of `/proc/self/task`, not running threads. The
safety test `tests/m33_thread_cap.rs` counts threads in state R and passes. Since F0 shows the excess
too, this is probably a team's exiting threads still listed while the next team starts. That is
unverified.

**Route.** `src/grobner/sigf4/dispatch.rs` tests degree spread before order. Cyclic-6 (degrees 1–6)
therefore takes `Shipping(DegreeSpread)`, which is still a shipping route with the reference digest.
The summarizer requires the reason to be `Order` exactly. katsura-7 at gf2 routes `Order` as expected.

## Regression: no failing row, 24 of 56 cells inconclusive on n

Full tables: `research/m33-qualification/results/regression.md`. The largest wall upper bound is
1.046 (m31 eco-11, f4, 4 w, n = 4), and the largest peak-RSS ratio is 1.025. Contamination was
9.7%, 11.1%, 8.1% and 4.2% of attempts in the regression-G, regression-M, small-G and small-M jobs.
Every flag came from the clock-deviation rule. No session is void (> 20%). The flags cluster by
cell, so 24 cells keep fewer clean pairs than the plan's n (9 for process wall, 31 for warm calls).
Those cells need a top-up job; `summarize.py` now pools repetitions across jobs.

## Gate D

Not run. The plan reads it only after safety, correctness and regression all pass.

## Raw data

Jobs live under `/buildcache/cargo-target/zeebra-974/jobs/`; the ids are in
`research/m33-qualification/results/jobs.txt`.
