# M29 — Verified Competitive F4

**Status:** planning, 2026-11-16 (revised proposal).
**Predecessor:** M28 — Competitive Multicore Algebra and Wide-Field Frontier
([`MILESTONE-MULTICORE-COMPETITIVENESS.md`](MILESTONE-MULTICORE-COMPETITIVENESS.md), §18).
**Planning base:** `main` at `7834aa04`.
**Measured at:** not measured here — every figure is quoted from #820, #821, #827, PR #829 and the
#831 exploratory runs, which carry their own commits. No timings were taken for this plan.
**Tracking issue:** [#833](https://github.com/mfaulk/zeebra/issues/833).
**Project:** [Zeebra #7](https://github.com/users/mfaulk/projects/7); label `M29`. Priority is the
Project field (P0 → High, P1 → High/Medium, P2 → Low); no native milestone object.

**Focus:** reduce necessary Gröbner-basis computation enough to challenge the leading open-source
solvers.

## 1. Executive summary

M29 retains two quantitative goals:

1. **Goal A — msolve parity.** Bring Zeebra within 1.5× of the fastest exact-mode msolve
   configuration under a common budget of at most 16 physical cores, on MQ10 over both GF(32003)
   and GF(2³¹−1).
2. **Goal B — grobx victory.** Achieve a verified, reproducible speed lead of at least 10% against
   grobx on one substantial Gröbner-basis computation over Goldilocks or 2⁶⁴−353.

The milestone's central question is no longer whether Zeebra can implement competitive multicore
F4; M28 established that it can. The question is now:

**Can Zeebra remove enough additional algebraic work, data movement and serial overhead to become
competitive with the best existing implementations?**

The latest investigations change the execution strategy:

- Promote exact duplicate pair-multiple elimination (#831) to the first production candidate.
- Treat serial Faugère–Lachartre reduction (#816 / PR #829) as an evaluated, noncompetitive
  alternative to the shipping parallel backend.
- Test parallel Faugère–Lachartre reduction (#828) as a separate conditional experiment.
- Defer parallel symbolic preprocessing (#832) until deduplication is integrated and remeasured.
- Prioritize current-revision grobx work attribution (#835) before selecting a larger algorithmic
  redesign.

Do not expand M29 into FGLM optimization, generalized symbolic algebra refactoring or hardware
acceleration.

## 2. Current evidence and numerical targets

### 2.1 MQ10 versus exact-mode msolve

Current fresh-process medians from [#820](https://github.com/mfaulk/zeebra/issues/820):

| Instance | Zeebra, 16 workers | Best exact msolve ≤16 cores | Required Zeebra time | Improvement needed |
|---|---:|---:|---:|---:|
| MQ10 / GF(32003) | 340.7 ms | 116.8 ms | ≤175.2 ms | ≥1.95× |
| MQ10 / GF(2³¹−1) | 314.1 ms | 167.0 ms | ≤250.5 ms | ≥1.25× |

These are complete reduced-basis tasks, not whole-point-solving tasks.

For final acceptance, both engines are remeasured on the same host, with the same mathematical
inputs, process timing boundaries and resource limits. Zeebra and msolve may each select their
fastest measured configuration within the 16-physical-core limit; results at fixed 1, 4, 8 and 16
workers are also retained.

The GF(32003) target is the harder gate and is prioritized when ranking potential optimizations.

### 2.2 Wide-field targets versus grobx

Current candidates from [#821](https://github.com/mfaulk/zeebra/issues/821):

| Instance | Zeebra, 16 workers | grobx, 1 worker | Required Zeebra time for ≥10% lead |
|---|---:|---:|---:|
| Eco-12 / 2⁶⁴−353 | 3.880 s | 1.619 s | ≤1.457 s |
| MQ11 / Goldilocks | 9.230 s | 3.326 s | ≤2.993 s |

**Eco-12 is the initial preferred target**, but both remain in the frozen benchmark corpus. Other
hard instances may be evaluated, provided the selection criteria and the complete candidate set are
declared before the final measurement.

The comparison permits Zeebra up to 16 physical cores and grobx its fastest supported configuration
within that budget. It is reported explicitly as a **common-budget**, not equal-worker, comparison.
No startup-dominated or trivial planted instance qualifies.

A qualifying answer must be independently certified as a complete reduced Gröbner basis for the
original ideal. Agreement between two solvers is useful but is not, by itself, a proof of ideal
equality.

Two performance categories stay distinct: raw complete outputs checked independently after
execution, and solvers that include exact certification inside their measured execution. Identical
randomized-versus-deterministic guarantees are never implied.

## 3. Reconciliation with completed work

| Existing issue / PR | Status at planning | M29 disposition |
|---|---|---|
| [#803](https://github.com/mfaulk/zeebra/issues/803) / [PR #817](https://github.com/mfaulk/zeebra/pull/817) | Complete | Historical residual study; its original batch speedup is corrected by #829. No new implementation task. |
| [#816](https://github.com/mfaulk/zeebra/issues/816) / [PR #829](https://github.com/mfaulk/zeebra/pull/829) | PR open | Finish review and integration of the opt-in serial route; do not adopt as default. |
| [#827](https://github.com/mfaulk/zeebra/issues/827) / [PR #830](https://github.com/mfaulk/zeebra/pull/830) | Merged | Use its CPU-frequency, placement and symbolic-cost findings; do not repeat the investigation. |
| [#831](https://github.com/mfaulk/zeebra/issues/831) | Open | P0 production candidate: exact duplicate pair-multiple elimination. |
| [#828](https://github.com/mfaulk/zeebra/issues/828) | Open | P1 conditional: parallel Faugère–Lachartre reduction. |
| [#832](https://github.com/mfaulk/zeebra/issues/832) | Open | P2 research, dependent on #831 and a new opportunity calculation. |
| [#809](https://github.com/mfaulk/zeebra/issues/809) | Open | Optional Faugère Simplify investigation, only if the wide-field cost model justifies it (a C2 option). |
| [#808](https://github.com/mfaulk/zeebra/issues/808) | Open | Deferred: mainly final-interreduction memory, not a proven speed bottleneck. Not labelled M29. |
| [#826](https://github.com/mfaulk/zeebra/issues/826) | Open | Deferred to whole-solving optimization; outside M29's reduced-basis objectives. Not labelled M29. |

M28's generic investigation of the 16-worker serial-stage slowdown is retired: #827 resolved the
principal causes.

### Key correction: Faugère–Lachartre

The first study counted 579 candidate-finishing rows on MQ10, whereas production F4 finishes only
eight. That overstated the production backward pass and made the new reduction order look
substantially more attractive than it is.

Corrected measurements from PR #829:

| Task | Serial forward order | Serial FL order | Shipping 16-worker order |
|---|---:|---:|---:|
| MQ10 complete F4 | 1,139 ms | 992 ms | 291 ms |
| Katsura-11 complete F4 | 10,062 ms | 8,024 ms | 1,738 ms |
| Cyclic-7 complete F4 | 285 ms | 270 ms | 140 ms |

The FL route is faster than serial forward reduction but slower than the production parallel route
by about 1.9–4.6×. No M29 success criterion may rely on the earlier 1.8–2.1× claim; parallel FL
requires its own end-to-end evidence.

## 4. M29-0 — Freeze the current competitive baseline

**Owner:** [#834](https://github.com/mfaulk/zeebra/issues/834). **Priority:** P0. **Dependencies:** none.

**Status: baseline frozen and cost model published**
([report](research/m29-baseline-cost-model.md), measured on a quiet machine at `7251e775`,
production source `60e99587`; the first pass at `847c4030` is kept as superseded evidence). It
shows the following:

- At 16 workers the F4 call is 63–76% serial. Forward elimination already scales 10.7–14.1×.
- Serial candidate finishing is 14–28% of process wall, the largest single opportunity on both wide
  targets, and is [#845](https://github.com/mfaulk/zeebra/issues/845).
- #843's parallel FL (#828) measured 1.145× on Eco-12 and 1.272× on MQ11 at 16 workers (F4 call;
  1.134× / 1.243× process wall). Its gain is that it removes serial finishing, not that it cuts
  forward work, so the report's original −4 to −5% prediction for #828 is withdrawn. #843 and
  #845 act on the same stage.
- #831 measured 0.84–0.97× at 16 workers.
- Distances: msolve 2.77× (32003) and 1.93× (2³¹−1); grobx 2.21× (Eco-12) and 2.53× (MQ11).

The measurement policy below is §3 of the report, and `tools/cpu-context.sh` implements it.

### Tasks

1. Freeze the current `main` source and executable identities for Zeebra, msolve, grobx and other
   relevant capable comparands.
2. Reproduce the two MQ10 benchmarks and the preferred wide-field targets.
3. Retain the complete current worker curves at 1, 4, 8 and 16 workers.
4. Publish performance-stage attribution using the current adaptive parallel implementation.
5. Add a post-M28 CPU/topology measurement policy informed by #827.

The protocol must distinguish serial-phase clock changes from changes in useful algorithmic work. A
16-worker burst keeps the 5995WX near all-core boost for about 200–500 ms, and placement across
CCDs can affect serial-stage timings.

Log worker affinity, CPU placement, effective clocks where available, machine load and compiler
activity. Do not compensate for these effects with inferred clock-normalized results; the actual
process-wall measurement remains authoritative.

### Cost-model deliverables

A table for each target containing:

- full F4 wall and process wall
- symbolic preprocessing and matrix construction
- reducer-sweep and newly discovered-pivot work
- candidate finishing and interreduction
- coefficient products, row applications, matrix sizes and fill
- peak RSS, live-entry reservations and temporary memory
- measured serial/parallel fractions

Predict a maximum recoverable improvement for every proposed mechanism.

**Gate:** no new performance implementation is approved solely on an older serial result if the
current 16-worker cost model cannot support its claimed benefit.

## 5. M29-A — Ship exact symbolic work reduction

**Owner:** [#831](https://github.com/mfaulk/zeebra/issues/831). **Priority:** P0.
**Dependencies:** current baseline (#834) and existing #753/#827 evidence.

This is the first production optimization candidate.

### Existing evidence

On Katsura-11 / GF(2³¹−1), exploratory measurements found that deduplicating exact pair multiples
reduced the complete F4 call from about 1,645 ms to 1,485–1,491 ms without changing the
537-element reduced basis — about 10%, with savings in both symbolic work and subsequent forward
elimination. These were two exploratory repetitions outside the benchmark lock, not accepted
production measurements.

### Implementation

Move the exact duplicate-multiple policy out of research-only thread-local scope and into
production symbolic preprocessing. For every batch, retain at most one occurrence of each
mathematically identical `(basis_index, multiplier)` multiple, while preserving the span and pair
relations required for F4 correctness.

1. Document the equality and span-preservation argument, including duplicate origins, proportional
   generators and pair LCM coverage.
2. Remove feature/scope overhead from the production implementation.
3. Account for the deduplication set's capacity, allocations and lifetime.
4. Validate every supported monomial order, field width and relevant backend.
5. Rerun complete F4 on MQ10, Katsura-11, Cyclic, Eco, Noonburg and held-out examples.
6. Compare both serial and adaptive-16-worker paths against the same shipping baseline.

### Acceptance

Ship only if:

- complete reduced bases agree coefficient for coefficient, including independent references;
- at least one named substantial task improves by at least 10% in a controlled benchmark;
- other supported controls do not regress materially beyond 5%;
- retained allocation overhead causes no material memory regression (investigate any RSS increase
  above 1.15×);
- existing cancellation and budget semantics remain intact.

If it passes, integrate before the parallel FL experiments and update every remaining Amdahl
estimate.

The #753 combined ordering experiment is not reopened. Initial-generator ordering stays separately
gated: it did not help Katsura-11 in #827 and previously incurred integration overhead.

## 6. M29-B — Parallel Faugère–Lachartre feasibility

**Owner:** [#828](https://github.com/mfaulk/zeebra/issues/828). **Priority:** P1, conditional.
**Dependencies:** PR #829 merged; #831's production decision and updated baseline.

The serial FL order remains an opt-in research alternative, not a production default.

### Hypothesis

Reducing each pair row against an immutable reducer block may permit an efficient parallel sweep,
followed by parallel elimination of the residual block D′. This could remove unnecessary arithmetic
and exploit multicore resources simultaneously — but the route must compete with a 16-worker
production algorithm that is already much faster than serial FL.

### Implementation experiment

1. Extend the existing concurrent dispatch capability with an independently budgeted reducer sweep.
2. Preserve immutable reducer publication and isolated worker scratch.
3. Use the existing concurrent elimination machinery for the residual D′ where applicable.
4. Reuse the existing FL candidate-finishing and remapping logic.
5. Include conservative reservations for the reducer block, residual storage, worker buffers, pivot
   metadata and thread stacks.

Do not build a second general-purpose scheduling runtime.

### Controlled factorial benchmark

| Route | 1 worker | 4 workers | 8 workers | 16 workers |
|---|---|---|---|---|
| Shipping forward order | Required | Required | Required | Required |
| FL order | Required | Required | Required | Required |

Evaluate MQ10 at both primes, Katsura-11, Cyclic-7/8, Eco-12 and a bounded MQ14 batch. Include
64-bit fields after the first small-prime gate. Record the cost of the sweep, residual echelon,
candidate finishing, representation conversion and peak process memory.

### Stop/go gate

The parallel FL route advances toward production only with:

- at least 15% complete-F4 improvement on one substantial case against the shipping parallel
  baseline;
- evidence on a held-out family that the gain is not specific to one MQ matrix;
- no material regression on small controls;
- no new budget refusals or unsupported mathematical outcomes;
- peak RSS at most 1.25× baseline, unless a separately demonstrated fixed-budget frontier gain
  justifies the exception.

If it fails the bounded comparison, close #828 with a negative verdict; do not tune worker counts
indefinitely. **Improving serial FL against serial forward reduction does not satisfy this gate.**

## 7. M29-C — Attribute and reduce the grobx gap

**Owners:** C1 [#835](https://github.com/mfaulk/zeebra/issues/835) (P0 research); C2/C3
[#836](https://github.com/mfaulk/zeebra/issues/836) (P1, conditional, labelled `blocked` on #835).
**Dependencies:** M29-0; incorporate successful A/B changes.

The 64-bit win is the highest-risk objective. Eco-12 needs about a 2.66× Zeebra improvement to
establish a 10% lead; MQ11 / Goldilocks needs about 3.09×. A handful of low-level arithmetic
optimizations is unlikely to achieve this; the investigation must find a sufficiently large
reduction in total work.

### C1 — Reattribute the gap on current code

Reuse the original [grobx trajectory attribution](research/grobx-trajectory.md), but repeat the
relevant counting on current Zeebra, not the pre-M28 implementation. Measure:

- critical-pair and reducer trajectories
- row admissions and exact zero reductions
- reducer/pair work versus newly discovered pivots
- total coefficient products, including discarded work
- row width, density and coefficient storage
- copied versus borrowed coefficient data
- memory traffic and the cost of row materialization
- time per useful rank increase and per necessary candidate
- the differing work contracts of the randomized and deterministic algorithms

Compare Zeebra's necessary computation against grobx's actual computation for identical inputs. Do
not read larger or smaller Macaulay matrices as direct evidence of more or less arithmetic.

#714 is a constraint: grobx's random combinations substantially reduce work, but the
straightforward exact audit erased that advantage. Do not repeat the rejected proof strategy.

### C2 — Choose one algorithmic improvement

Select no more than one substantial new algorithmic/data-layout implementation from the
attribution. Candidate directions, in preference order:

1. **Work-avoiding exact row reduction.** A deterministic route that removes a measurable fraction
   of pair-row, reducer or discovered-pivot updates.
2. **Reduced-row reuse across batches.** #809 (Faugère Simplify), only if the current work ledger
   shows substantial repeated reducer computation.
3. **Less row materialization.** Borrow immutable coefficients and share reducer storage rather
   than rebuilding large sparse rows; reuse #268's research where appropriate.
4. **Field-width-specialized kernels.** Only when measurements establish that operation cost,
   rather than avoidable operations, is sufficiently dominant.

An algorithm may be rejected after a bounded prototype. A fast kernel with unchanged total F4 time
is not progress toward Goal B. No full signature-F4/F5 implementation or Monte Carlo row-skipping
scheme is authorized merely because grobx uses one.

### C3 — Competitive qualification

Rerun both 64-bit primes on the full frozen corpus after any accepted change. Prioritize Eco-12 and
MQ11; retain Katsura, Cyclic and Noonburg outcomes as regression and generality checks.

Use a separate exact verification step establishing that the output is a reduced Gröbner basis of
the original input ideal. Verification time is reported outside raw solver wall, with certified
execution comparisons separately identified. A speed win is measured on complete process runs,
without raising time or memory budgets or omitting unsuccessful results.

## 8. M29-D — Conditional parallel symbolic preprocessing

**Owner:** [#832](https://github.com/mfaulk/zeebra/issues/832). **Priority:** P2.
**Dependencies:** #831 and a reprofiled symbolic stage.

#827 measured level-parallel symbolic closure. On Katsura-11, 16 workers reduced the symbolic stage
from about 482 ms to 348 ms — 1.38× on the stage, only about 8% of the complete F4 call before
integration overhead. It is bounded by roughly 300–325 ms of serial commit and monomial interning,
and the research prototype costs substantially more than serial preprocessing at one worker. Do not
ship it in its present form.

After #831 merges or is rejected, remeasure the remaining symbolic opportunity. Proceed only if at
least one is established:

- parallel interning removes a substantial portion of the serial commit cost while preserving
  deterministic handle assignment;
- a persistent per-batch worker strategy materially reduces scheduling overhead;
- a held-out whole-F4 task shows enough residual symbolic work to support at least a 10% gain.

Otherwise close or defer #832. Do not build a new parallel monomial-interner subsystem solely for a
projected 8% result on one family.

## 9. M29-I — Competitive validation and integration

**Owner:** [#837](https://github.com/mfaulk/zeebra/issues/837). **Priority:** P0 closeout.
**Dependencies:** accepted production candidates and completed research decisions.

### Final benchmark protocol

Threadripper PRO 5995WX and the existing benchmark lock (`tools/benchlock.sh`). For every final
target comparison:

- one frozen source revision and documented binary identity per engine;
- same canonical polynomial system and field;
- fresh processes, full input/output and identical task definitions;
- the fastest validated configuration within the common 16-core limit;
- unchanged child wall and memory limits, normally 60 s and 2 GiB;
- at least nine interleaved measurements per primary target;
- retained refusals, compiler interruptions, raw responses and provenance;
- exact mathematical verification outside the raw timed region;
- an explicit paired-ratio distribution or uncertainty interval.

**Goal A:** both Zeebra/msolve ratios have medians ≤1.5 and a declared uncertainty interval whose
upper end stays below 1.5.

**Goal B:** Zeebra's median is at most 0.90× grobx's and the uncertainty interval establishes a
speed lead. If the evidence is too noisy, one preregistered confirmation cohort is allowed; do not
resample until a favorable result appears.

Never pool sessions that used different revisions, input identities, correctness modes or timing
boundaries.

### Scoreboards

One compact primary leaderboard:

| Task | Field | Zeebra | Best exact comparand | Fastest checked-output comparand | Ratio | RSS | Verification |
|---|---|---:|---:|---:|---:|---:|---|

supplemented by worker-scaling curves and instance-by-instance failures. Distinguish exact-mode
msolve, grobx's randomized raw mode, and independently checked outputs. A solver's missing external
adapter or field capability is not a performance loss.

Preserve all negative experiments: serial FL, symbolic parallelism, rejected randomization
approaches and failed fixed-budget completions.

### Final milestone acceptance

**Minimum — research and integration complete**

- M29-0 baseline/cost model complete (#834).
- #831 evaluated and integrated or rejected with evidence.
- #829/#816 reconciled; #828 evaluated, or explicitly deferred after a failed feasibility gate.
- #832 priced after deduplication.
- Current grobx attribution completed (#835).
- All attempted optimization routes scored.
- Boards, tests and final report complete (#837).

Minimum means M29's research is finished. It does not mean the competitive targets succeeded.

**Target — both performance goals met**

1. Zeebra ≤1.5× exact-mode msolve on both required MQ10 fields.
2. At least one ≥10% independently verified win against grobx on a substantial 64-bit instance.

**Stretch — broader reproducible superiority**

- Wins on at least two independent hard instances or problem families.
- A speed lead across both 64-bit primes.
- A meaningful fixed-budget frontier advance, with independent exact verification.
- Demonstrated equal-worker improvements, not only common-core-budget wins.

The milestone may close after documented negative results, but keeps an explicit **target missed**
status for any unmet goal.

## 10. Issue ownership and implementation queue

All rows are native sub-issues of #833 and carry the `M29` label.

| Work package | Issue | Priority (board) | Status at planning | Immediate action |
|---|---|---|---|---|
| M29-0 — baselines and cost model | [#834](https://github.com/mfaulk/zeebra/issues/834) | P0 (High) | Published ([report](research/m29-baseline-cost-model.md)) | Use its §6 ceilings to approve or decline each mechanism |
| Parallel candidate finishing | [#845](https://github.com/mfaulk/zeebra/issues/845) | Medium | Shipped (default order) | Measured −13.9% / −22.6% process wall on Eco-12 / MQ11 and −8 to −11% on MQ10, ahead of #843's opt-in FL on both wide targets with no RSS growth ([report §6b](research/m29-baseline-cost-model.md)) |
| M29-A — production symbolic dedup | [#831](https://github.com/mfaulk/zeebra/issues/831) | P0 (High) | Open | First production candidate |
| Serial FL order (opt-in) | [#816](https://github.com/mfaulk/zeebra/issues/816) / PR #829 | P0 review (High) | PR open | Review/merge the corrected opt-in route; default unchanged |
| M29-B — parallel FL order | [#828](https://github.com/mfaulk/zeebra/issues/828) | P1 (Medium) | Open | Bounded parallel feasibility only, after #829 and #831 |
| M29-C1 — current grobx attribution | [#835](https://github.com/mfaulk/zeebra/issues/835) | P0 (High) | Done ([note](research/m29-grobx-attribution.md)) | 93% of Zeebra's products are on pairs that reduce to zero; grobx avoids them by signature criteria (MQ11) and randomized combinations (Eco-12). Recommends no C2 in M29 |
| M29-C2/C3 — one exact-work improvement | [#836](https://github.com/mfaulk/zeebra/issues/836) | P1 (Medium) | New, `blocked` | Start only after #835 justifies a candidate |
| C2 option — Faugère Simplify | [#809](https://github.com/mfaulk/zeebra/issues/809) | Optional (Low) | Open | Only if #835's ledger shows repeated reducer work |
| M29-D — parallel symbolic | [#832](https://github.com/mfaulk/zeebra/issues/832) | P2 (Low) | Open | Defer until #831's post-adoption cost model |
| M29-I — comparison and integration | [#837](https://github.com/mfaulk/zeebra/issues/837) | P0 closeout (High) | New | Publish the two target verdicts |

#827 and #803 are completed prerequisites and are not recreated. #753 remains closed. #808 and
#826 are deferred and not labelled M29.

## 11. Parallel development and dependencies

These can start independently:

- **Agent A:** baseline protocol, current source and external solver measurements (#834).
- **Agent B:** #831 exact symbolic dedup implementation and correctness proof.
- **Agent C:** #828 parallel FL design, matrix-level tests and resource model.
- **Agent D:** read-only current grobx work attribution and algorithm literature study (#835).

Only one agent owns shared elimination and symbolic interfaces (`src/grobner/f4/`, `src/linalg/`)
at a time. All benchmark campaigns stay serialized under `benchlock`, even when implementation runs
concurrently.

Integration sequence:

1. Establish source and benchmark baselines.
2. Merge only validated production changes.
3. Reprofile after each change, rather than multiplying independent expected gains.
4. Advance or reject parallel FL.
5. Select at most one additional wide-field algorithmic implementation from current measurements.
6. Run final independently checked competitive cohorts.
7. Publish the M29 report and scorecard.

## 12. Scope exclusions and stop rules

M29 does not undertake:

- general FGLM operator optimization (#826);
- GPU or out-of-core elimination;
- a generic new execution runtime;
- unbounded signature-F4 development;
- uncertified randomized zero skipping;
- general public polynomial representation redesign;
- cosmetic scoreboard improvements without new measurements.

A new performance line must identify its full-task opportunity and resource model before
implementation. For an expensive line, stop after at most two bounded designs fail the predeclared
performance or memory gates. The milestone does not expand indefinitely if the goals prove harder
than expected.

## 13. Recommended next actions

1. **Finish review of PR #829** and record the corrected Faugère–Lachartre evidence. Its opt-in
   route can support #828 but does not displace the production default.
2. **Prioritize #831.** Its measured 10% Katsura-11 reduction is a stronger near-term adoption
   candidate than parallel symbolic preprocessing.
3. **Run current-revision Eco-12/MQ11 attribution (#835)** while implementation proceeds. It
   determines whether there is a credible route to the required 2.7–3.1× improvement.
4. **Evaluate #828** after the deduplicated production baseline stabilizes. Do not invest in
   another large elimination framework unless its multicore performance beats the existing backend.
5. **Recompute the remaining distance to both goals.** Decide whether further implementation is
   justified by measured work reductions and their cost, not by the attractiveness of the
   underlying algorithm.

## Milestone conclusion

M29 is an experiment in **competitive algorithm economics**, not a general optimization campaign.

Completed work has already eliminated two weak assumptions: serial Faugère–Lachartre's apparent 2×
advantage was partly a benchmark error, and the multicore serial-stage slowdown was largely CPU
behavior rather than a software defect.

The strongest immediate priorities:

1. Ship exact duplicate pair-multiple elimination if its controlled results hold.
2. Establish whether parallel FL can beat the existing parallel algorithm.
3. Identify and remove a large, demonstrably unnecessary portion of the wide-field work that makes
   grobx faster.
4. Measure both competitive goals on equal process boundaries with independently verified output.

The success criteria are demanding by intent: M29 should produce either genuine competitive results
or a precise, reproducible explanation of what still prevents them.
