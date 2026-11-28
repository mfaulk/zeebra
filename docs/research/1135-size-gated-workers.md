# #1135: a size-gated worker count for `GradedEngine::Adaptive` (laptop stage)

**Measured at:** `36fd4137` for the development figures (tag `measured/1012-matrix`, bench host,
re-read, not re-measured). The laptop read is pending; this section is the predeclaration, committed
before any fresh row was timed.

**Status:** laptop stage. No default changes. **Classification:** hypothesis.

**Parent:** #1003. **Found by:** #1015 (`docs/research/m34-selection-findings.md` §7.3, §8 item C).
**Related:** #978 and #1141 (the `WorkerCrossover` band), #1009 (feature extraction must be cheap
on sub-millisecond inputs).

Records and harness: [`research/1135-size-gated-workers/`](../../research/1135-size-gated-workers/).

## 1. Question

In Gate H's development matrix, `GradedEngine::Adaptive` at one worker (P8-w1) is the
leave-one-family-out best fixed arm in 16 of 17 families. On the larger ladder rows the same dispatch
at 16 workers (P8-w16) is 1.5–2.2× cheaper. Can a cheap size predicate, fixed in advance, choose
between them: one worker below it, the caller's workers at or above it?

## 2. What a laptop stage can and cannot say

The machine is an Apple M4 Pro with 10 performance and 4 efficiency cores and 48 GB, under macOS.
Nothing is pinned, and another agent was building on it during the session. That limits the read:

- **Worker count.** The issue's arm is 16 workers, which this machine does not have. The read uses
  **10**, the performance-core count. Efficiency cores in a barrier-synchronised team make every
  batch wait for the slowest worker, so 14 is not the sensible maximum.
- **Noise.** Unpinned figures on a shared laptop are development figures. A 1.5–2× effect is larger
  than that noise, so the read can show whether the gate points the right way on unseen rows. It
  cannot place a threshold for the bench host to within 10%, and it does not qualify anything.
- **What remains for the bench host.** The same read at 16 workers, pinned to the reserved CCDs,
  with more rows where the gate is closed. Section 6 lists what it needs.

## 3. The gate (predeclared)

**Definition.** Let `n` be the number of variables that appear in some nonzero generator, and
`d_1 ≤ d_2 ≤ …` the degrees of the nonzero generators. Let

    B = d_1 · d_2 · … · d_k,   k = min(#generators, n),

with `B = 0` if some generator is a nonzero constant. **Run `Adaptive` on one worker when
`B < 2^11 = 2048`, and on the caller's workers when `B ≥ 2048`.** Linear generators contribute 1.

`B` is the Bézout number of the `k` least-degree generators. For a zero-dimensional complete
intersection, it bounds the number of solutions, and so the quotient dimension, which drives the
size of F4's matrices. Here it is used only as a predictor. It costs one pass over each generator's
degree, which `signature_route` already computes (`degrees` in `src/grobner/sigf4/dispatch.rs`),
plus a sort of `m` integers. It needs none of #1009's allocated feature extractors, so it is cheap
on sub-millisecond inputs. The implementation the read uses is `bezout_bound` in
`research/1135-size-gated-workers/study.py`, with unit tests in `test_study.py`.

**Where it comes from.** The gate was fitted on the 118 development records that have both P8 cells
(`research/1135-size-gated-workers/dev.md`). Those rows fitted the gate, so they are not evidence
for it:

| Development records | gate agrees (within 10%) | worst regret under the gate | geo-mean regret: gate / always 1 w / always 16 w |
|---|---:|---:|---:|
| all 118 | 94 | 1.53 (`gen-phosphorylation-5`, a 9 ms solve) | 1.078 / 1.054 / 1.207 |
| 18 with the faster median in 100 ms – 300 s | 18 | 1.08 (`zb-col-grid-4x5`) | 1.011 / 1.300 / 1.045 |

Two weaknesses were visible before the read:

- **The threshold sits on one boundary.** It falls between `gen-chandrasekhar-h-10` (B = 1,024,
  16 workers 0.73× as fast) and `gen-chandrasekhar-h-11` (B = 2,048, 1.21× faster). On quadratic
  systems it reads "at least 11 variables". Nothing in the development data places it more
  tightly.
- **Overdetermined and binomial inputs open the gate on small solves.** Graph colourings and
  phosphorylation networks have B in the thousands to millions and solve in 6–20 ms, where 16 workers
  cost 1.3–1.5×. Twenty-two of the 24 development disagreements are rows of this kind, all under
  25 ms. The other two are `sd-fourbodyproblem` at both fields (B = 1,000, 26–28 ms), where 16
  workers are 1.10–1.11× faster. The issue's band excludes all of them, and so does the read below.
  A shipped gate would need a second condition for the small rows.

## 4. Fresh rows and protocol (predeclared)

**Rows.** Thirteen problems over GF(2³¹−1), none of them read by Gate H and none in its sealed
validation or untouched cohorts (`research/m34-gate-h/s0/cohorts.json`; families there are
excluded wholesale, because #1005 groups by family). They are new rungs of development families,
built with `tools/m34_structural_corpus.py`'s own generators (`study.py catalog` →
`catalog.json`). The ladder rungs are exposed in earlier milestones (M29–M33), but not to this
gate.

| row | variables | generators | B | gate predicts |
|---|---:|---:|---:|:-:|
| `zb-katsura-10` | 10 | 10 | 512 | 1 worker |
| `zb-katsura-11` | 11 | 11 | 1,024 | 1 worker |
| `zb-katsura-13` | 13 | 13 | 4,096 | 10 workers |
| `zb-eco-10` | 10 | 10 | 13,122 | 10 workers |
| `zb-eco-11` | 11 | 11 | 39,366 | 10 workers |
| `zb-eco-13` | 13 | 13 | 354,294 | 10 workers |
| `zb-cyclic-8` | 8 | 8 | 40,320 | 10 workers |
| `zb-noon-8` | 8 | 8 | 6,561 | 10 workers |
| `zb-noon-9` | 9 | 9 | 19,683 | 10 workers |
| `zb-reimer-7` | 7 | 7 | 40,320 | 10 workers |
| `zb-col-grid-4x6` | 24 | 62 | 16,777,216 | 10 workers |
| `zb-col-gnm-16-28-s1` | 16 | 44 | 65,536 | 10 workers |
| `zb-col-ktree2-16-s1` | 16 | 45 | 65,536 | 10 workers |

Only two rows have the gate closed, because a slow row with small B is rare in these families. The
read therefore tests mainly whether the open side is right. It has little power to show a missed
gain, and only `zb-katsura-11` can show one. None of the rows is in the `WorkerCrossover` band
(10 variables, quadratic, with a solution at infinity): katsura-10 has every square in its top
forms. So 10 workers changes the team here, not the engine.

**Arms.** `examples/m34_matrix --engine adaptive` (the #1012 arm P8) at `--workers 1` and
`--workers 10`, built `--release --features research-sigf4` at this branch. Each attempt is a fresh
process. Its process wall is timed by the controller, with a 120 s solve budget (`--wall-s 120`).
There are 5 repetitions per arm and row. Each repetition runs the rows in a fixed order, and the
order of the two arms alternates between rows and between repetitions. The controller makes one
untimed warm-up call first. The 1-minute load average is recorded at each attempt's start.

**Scoring.**

- A row is scored when both arms complete and the faster arm's median lies in **100 ms – 300 s**.
  Other rows are dropped and recorded, not replaced.
- Every completed attempt of a row must report the same `basis_sha256`.
- A row **agrees** when the arm the gate picks is within 10% of the other arm's median.
- Regret is the picked median over the faster median.

**Criterion.** The gate is **supported at the laptop stage** if it agrees on at least 80% of the
scored rows and no scored row has regret above 1.25. Otherwise it is **not supported**, and no
threshold is moved on this data. Either way no default changes, and the geometric-mean regrets of
the gate, always-1 and always-10 are reported as description.

## 5. Result

Pending.
