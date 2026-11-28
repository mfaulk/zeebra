# #1135: a size-gated worker count for `GradedEngine::Adaptive` (laptop stage)

**Measured at:** `68ed9b14` for the laptop read (source tree of `main` `f77dc563`; the commit adds
only research Python, documents and a CI step), Apple M4 Pro, unpinned, 2026-11-28
(`research/1135-size-gated-workers/provenance.txt`). The development figures are from `36fd4137`
(tag `measured/1012-matrix`, bench host), re-read and not re-measured. Sections 3 and 4 were
committed at `68ed9b14` and posted on #1135 (issue comment 7242437140) before any fresh row was
timed.

**Status:** laptop stage. No default changes. **Verdict: not supported** (§5).
**Classification:** hypothesis. The gate is refuted on this machine, and the bench-host question
is open.

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

## 5. Result: not supported

The session ran 2026-11-28 17:10–17:15 UTC: 130 attempts, all completed. Every row's bases agree
across all ten of its attempts. Tables are in `research/1135-size-gated-workers/tables.md`, and every
attempt is in `attempts.jsonl.gz`.

| row | B | gate | 1 w (ms) | 10 w (ms) | 1 w ÷ 10 w | scored | agrees |
|---|---:|:-:|---:|---:|---:|:-:|:-:|
| `zb-katsura-10` | 512 | 1 | 108.5 | 76.1 | 1.42 | no (76 ms) | – |
| `zb-katsura-11` | 1,024 | 1 | 622.4 | 320.9 | **1.94** | yes | **no** |
| `zb-katsura-13` | 4,096 | 10 | 25,163.5 | 7,139.5 | 3.52 | yes | yes |
| `zb-eco-10` | 13,122 | 10 | 49.0 | 46.9 | 1.04 | no (47 ms) | – |
| `zb-eco-11` | 39,366 | 10 | 257.0 | 197.0 | 1.30 | yes | yes |
| `zb-eco-13` | 354,294 | 10 | 10,045.9 | 7,187.2 | 1.40 | yes | yes |
| `zb-cyclic-8` | 40,320 | 10 | 2,938.8 | 781.3 | 3.76 | yes | yes |
| `zb-noon-8` | 6,561 | 10 | 256.5 | 256.8 | 1.00 | yes | yes |
| `zb-noon-9` | 19,683 | 10 | 1,716.3 | 1,683.3 | 1.02 | yes | yes |
| `zb-reimer-7` | 40,320 | 10 | 1,716.3 | 513.7 | 3.34 | yes | yes |
| `zb-col-grid-4x6` | 16,777,216 | 10 | 784.0 | 739.5 | 1.06 | yes | yes |
| `zb-col-gnm-16-28-s1` | 65,536 | 10 | 30.0 | 34.0 | 0.88 | no (30 ms) | – |
| `zb-col-ktree2-16-s1` | 65,536 | 10 | 22.9 | 26.4 | 0.87 | no (23 ms) | – |

Medians are of 5 fresh processes per arm, process wall. The 1-minute load at attempt start was
3.2–5.7. The repetitions are tight: katsura-13 at one worker spans 25.09–25.22 s, and cyclic-8 at
10 workers 758–801 ms.

**Pre-declared read.** Nine rows are scored. The gate agrees on 8 of 9 (89%, criterion ≥ 80%),
but its worst regret is **1.94** on `zb-katsura-11`, against a bound of 1.25. **The gate is not
supported.** No threshold is moved on this data.

What the read shows, descriptively:

- **In the band, 10 workers never lost.** Always-10 has geometric-mean regret 1.000 over the nine
  scored rows. The gate's is 1.076 and always-1's is 1.769. Ten workers gain 1.3–3.8× on six rows
  and tie on three: noon-8 and noon-9, which the signature route's small team holds to 8 workers,
  and col-grid-4x6.
- **The gate's closed side is wrong on both of its rows.** katsura-10 and katsura-11 run the
  signature engine on the full team, and 10 workers are 1.42× and 1.94× faster. On the bench host
  the matching development row went the other way: `gen-chandrasekhar-h-10` (10 variables,
  quadratic, signature route, no `WorkerCrossover`) was 0.73× as fast at 16 workers. That
  boundary is what put the threshold at 2,048, and it does not reproduce here. Whether it is a
  16-worker effect, a Zen cross-CCD effect or a property of chandrasekhar-h is not separable on a
  laptop.
- **Where one worker wins, the row is under 100 ms.** The only rows that 10 workers slow down are
  the two 16-vertex colourings (0.87–0.88×, 23–34 ms), the case §3 flagged. The gate opens on both.
  On this evidence a worker-count gate earns its keep below the issue's band, if anywhere, and
  input size does not pick out those rows.

So on this machine the gate does no better than passing the caller's workers through, and on one
row it is 1.94× worse. The development finding behind #1135, "P8-w1 is the best fixed arm", holds
because the development cohort is 87.5% small problems. It does not carry over to rows of
100 ms – 300 s.

## 6. Classification and next stage

- **Refuted at the laptop stage:** the predeclared Bezout gate at 2^11. **Distribution-specific:**
  fresh rungs of five ladder families and the colouring family over GF(2³¹−1), on one machine at 10
  workers.
- **Hypothesis, still open:** whether *any* static size gate helps on the bench host at 16
  workers. The only development evidence for a closed side above 100 ms is chandrasekhar-h-9 and
  -10. A bench-host stage should:
  1. re-read katsura-10 and katsura-11 (both fresh to the bench host) and chandrasekhar-h-10 at 1,
     8 and 16 workers, pinned, to see whether the loss at 16 workers is a team-size effect;
  2. widen the rows with small B and 100 ms – 300 s solves before any gate is fitted again. These
     families have almost none.
- **Not recommended:** fitting a new threshold on these rows. The read was spent on this gate.
- **Worth a separate issue if pursued:** a gate that reads elapsed time rather than input size.
  Start on one worker and widen the team at a batch boundary once a wall-clock threshold passes.
  The rows that lose on many workers are the ones that finish within milliseconds, which input
  size does not identify (§3, and the colourings here). A wall-clock gate would identify them. It
  needs both engines to accept a team change between batches, which neither does today.
