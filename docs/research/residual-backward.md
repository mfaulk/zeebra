# Residual backward parallelism after candidate selection (#730)

**Measured at:** not measured here — timer cohorts are #269 build `0ed4fe332e3a6bcb51f9502b8f39e75c34b055dc`, controller `c148058bba3f65f794666394db1689835d4c4ada`;
production work is #749 build `a9f86ec00f8040618b26372073ba43ee5240f384`, controller `36f792a142efcaea6fee2252cf1800359972337d`;
dispatch is #592 source `6360904ab06f9ed773a530da3314ecfaef3d5837`.
**Source audit:** `b9898c9a` (includes production candidate-only reduction, #757).
**Decision:** reject a new per-pivot full-RREF scheduler for ordinary F4; defer a separate
candidate-target scheduler until current integrated measurements clear the opportunity gate below.
This is a completed conditional feasibility decision, not a parallel implementation or a measured
current-production backward speedup. No new solver measurements were run.

## What remains necessary

The [candidate-only contract](candidate-only-f4.md) supersedes the old assumption that F4
needs every inherited pivot tail reduced. `src/grobner/f4/reduction.rs` first computes echelon
form and then calls `candidate::finish` only for new leading columns. Public RREF, final matrix
interreduction and resource fallback still retain their full-row contract. They are separate
callers; optimizing them cannot be credited as ordinary candidate-pass acceleration.

`src/grobner/f4/candidate.rs` scans each selected target left to right using original later
echelon pivots. Its increasing-target order keeps those sources unchanged until no earlier target
needs them. There are no reverse-pivot barriers or mutable incidence lists in this route.
Consequently, adding threads to `back_substitute_pivots_tracked` would principally accelerate
work which ordinary F4 no longer performs. Reinstating full RREF to obtain its parallel fanout
would restore removed work and is rejected.

## Measured opportunity, with boundaries kept separate

The [#269 native cohort](../../research/selective-backward/native.json.gz) has five fresh-process
repetitions per cell, instrumentation counters off, and an observer timing the selected-row
backward call separately from forward elimination. That backward timer includes its pivot-index
and dense-row allocation, target substitution and output gathering. It excludes the selection-mask
construction before the call. The complete F4 timer includes all F4 stages and final interreduction;
input parsing, answer rendering and independent checking are outside it. The
[original study](elimination-kernels.md#candidate-only-backward-feasibility-269) and [reproduction guide](../../research/selective-backward/README.md)
retain campaign, machine, executable, independent basis checks and overhead controls.

| Historical selected-row cell | Complete F4 median | Backward median [min,max] | Median same-attempt fraction | Largest same-attempt ideal speedup |
|---|---:|---:|---:|---:|
| MQ10 / 32003 | 1321.362 ms | 42.265 [41.343,43.183] ms | 3.233% | 1.03379x |
| MQ10 / 2147483647 | 1476.386 ms | 46.904 [46.172,52.725] ms | 3.348% | 1.03629x |
| Cyclic-5 / 32003 | 0.596 ms | 0.020 [0.019,0.028] ms | 3.279% | 1.03517x |
| Cyclic-5 / 2147483647 | 0.620 ms | 0.020 [0.019,0.023] ms | 3.155% | 1.03328x |
| Katsura-6 / 32003 | 1.048 ms | 0.021 [0.020,0.034] ms | 2.006% | 1.02838x |
| Katsura-6 / 2147483647 | 1.213 ms | 0.026 [0.022,0.027] ms | 2.159% | 1.02232x |

For each attempt separately, with complete duration `T` and eligible backward duration `B`,
the zero-overhead model is `T / (T-B+B/p)`, or `T/(T-B)` for unlimited workers. The table takes
the largest of the five unlimited-worker ceilings; it does not divide independent medians or
combine snapshots. Every observed ceiling is below the M28 default 10% complete-task gain gate.
Even removing this entire timed region cannot meet that gate on these matched serial controls.
The sub-millisecond controls provide only bounded negative/correctness evidence, not precise
performance predictions. Per-worker model values for 1–64 workers are retained in
[summary.json](../../research/residual-backward/summary.json); these are analytical ceilings,
not measured parallel scaling.

The [#749 production campaign](../../research/candidate-adoption/) subsequently measured complete
F4 medians 1251.183/1336.917 ms on MQ10 and verified every complete basis independently. Its
elimination timer combines forward and backward. **There is no separate production backward
timer in that campaign.** The historical 3.2–3.5% fractions must not be assigned to those newer
production times, or to a whole point-solving route. Equal products do not establish equal time.
This limitation bounds the decision's scope: it rejects investment on the available serial
evidence and requires a new elapsed profile before reconsidering the integrated parallel route.

## Production work and batch skew

The offline model revalidates all retained complete answers through the existing #269/#749
validators and compares every backward batch census across five production work diagnostics and
five historical selected-row work diagnostics at each prime. All censuses match: 250 targets,
23,566,622/23,567,093 products and 471,831/471,840 pivot applications. Those are useful logical
operations, not elapsed shares or physical bandwidth. Work-on elapsed times are excluded from the
native ceiling calculation. No production full-RREF fallback occurs in these measured cells.

| MQ10 batch | Columns | Selected targets | GF(32003) products | Source fanout bound |
|---|---:|---:|---:|---:|
| 0 | 40 | 5 | 213 | ≤5 |
| 1 | 196 | 14 | 4,846 | ≤14 |
| 2 | 658 | 35 | 291,617 | ≤35 |
| 3 | 1695 | 62 | 2,765,823 | ≤62 |
| 4 | 4169 | 64 | 6,497,169 | ≤64 |
| 5 | 6292 | 44 | 8,773,962 | ≤44 |
| 6 | 6027 | 18 | 3,516,178 | ≤18 |
| 7 | 12020 | 8 | 1,716,814 | ≤8 |
| 8 | 10738 | 0 | 0 | 0 |
| 9 | 11851 | 0 | 0 | 0 |

Batch 5 carries 37.2305% of residual products but only 44 targets. The widest nonempty batch has
eight targets; the two final batches have none. At 64 workers those batches cannot provide
64-way target concurrency. This is a census of cross-batch work skew, not a claim that the 44
targets cost equally or that 44 workers are optimal. Both primes' complete batch tables, loads,
gathers and application counts remain in the generated summary.

Each source can be applied at most once to any target, because the scan advances strictly right
and no pivot introduces a term to its left. Its fanout is therefore bounded by the selected-target
count in the table. **Exact per-source fanout and per-target time/product distributions were not
recorded** by these cohorts: aggregate application totals cannot recover them. They are unnecessary
to reject the historical complete-task opportunity even under perfect balance, but are required
before designing a scheduler if the elapsed gate reopens. The old full-RREF incidence census is
not a substitute for these selected-row quantities.

## Dependency and ownership argument

For full RREF, a finalized pivot's tail must be cleared of later pivot columns before earlier
consumers use it. Distinct target updates from one immutable pivot are independent; overlapping
updates to one target are not. Preserve descending pivot order, and finish the current pivot's
consumers before mutating any row a later barrier can read. An arbitrary pivot panel is not
independent: its pivots may depend on one another. `PivotColumnRows` is built once and remains
valid precisely because subtraction cannot introduce an earlier column. Concurrent mutation or
changing traversal direction invalidates that argument. Per-target scratch ownership and per-pivot
barriers are the simplest correct model; panel/wavefront execution requires a new dependency proof.

Candidate reduction has a cheaper mathematical decomposition. Freeze the **original entire
echelon matrix**, let each worker own one selected target's dense row and result, and defer all
matrix replacements until workers complete. Later source columns strictly increase during
substitution, proving termination; every selected result has its original leading column and no
other pivot columns. Uniqueness of RREF gives coefficient-for-coefficient equality with serial
candidate outputs. Zero/nonselected rows create no jobs; duplicate or nonmonic pivots violate
the existing echelon precondition. Workers never read another worker's partial output.

This independence does **not** make concurrent in-place calls to today's `finish` safe. That
function replaces selected rows as it goes. A later target might replace a source an earlier
worker is still reading; it also updates shared statistics. Immutable borrowed sources plus
owned deferred outputs avoid those hazards. Commit outputs only after every worker succeeds;
on cancellation, panic or refusal discard all outputs, join workers and leave original rows intact.
Aggregate worker-local work and capacity explicitly, since `linalg::work` scopes are thread-local.
The proof concerns candidate coefficients; any prototype still needs schedule/refusal/reuse tests
and independent complete-basis checks before integration.

## Dispatch and memory bounds

[#592](worker-pool.md) measures a persistent static pool's complete warm empty-job pipeline,
not a portable barrier primitive: 8.34/18.68/16.89/27.44/53.49/103.46 microseconds at
2/4/8/16/32/64 requested workers. Constructor and first dispatch are separate. Applying those
historical pipeline medians to eight nonempty candidate batches costs approximately
0.067/0.149/0.135/0.220/0.428/0.828 ms before useful work. This is a planning estimate, not
a lower bound or an F4 timing. It suggests that one coarse dispatch per candidate batch can be
affordable inside the backward region. It does not overcome the complete-task ceiling.

A dispatch per pivot/application would multiply that pipeline cost instead; useful active-pivot
counts are not known, so no numerical barrier impossibility is claimed. One task per coefficient
or scalar application is rejected as the wrong granularity. #592's synthetic and FGLM findings
do not establish an F4 crossover. There is no measured panel cost to justify a second scheduler.

For the immutable-source/deferred-output design let `R` be resident original entries, `C` width,
`Q=sum(C-leading_column_i)` over selected targets, and `p` worker scratch rows. A conservative
mathematical entry reservation is `R + Q + p*C` before dispatch. This charges all retained
originals and all output suffixes simultaneously. It differs from serial positive-growth
reservation; copying the entire source matrix instead of borrowing it adds another `R`.
Use checked arithmetic and fall back on the untouched input if reservation cannot be admitted.

Sharing the column index/selection mask yields a minimum modeled dense/index/mask allocation
`C*(p*sizeof(F)+sizeof(usize)+sizeof(bool))`, excluding output-vector headers, capacities, worker
descriptors and allocator/runtime overhead. On this 64-bit target at `C=12020`, the formula
is 156,260→3,185,300 bytes for 4-byte fields at p=1→64 and 204,340→6,262,420 bytes for
8-byte fields. At 32-byte field width, p=64 requires 24,725,140 bytes before output storage.
These are layout models, not RSS or a new workspace allowance. Wider configured matrices can
cross the existing 64-MiB scratch limit; generic fallback must remain. Do not multiply serial
mathematical peaks or silently treat the serial reservation as sufficient for concurrent outputs.
Exact-support output buffers must be allocated independently; never install shared high-water
scratch capacity in every row (#554).

## Decision, acceptance and reopening

**Reject** parallelizing the old full-RREF pass as the default F4 optimization: it addresses the
wrong caller contract after #749. **Defer** a candidate-target prototype: the measured selected-row
serial controls cannot reach the 10% whole-F4 improvement gate even with free, perfectly balanced
backward execution. No additional runtime, pivot-panel protocol or worker scratch is justified by
this evidence. This is not a universal rejection of parallel back-substitution or larger fields.

| #730 area | Disposition |
|---|---|
| Required-output proof and selected policy | Implemented prerequisite #749; audited serial selection and untouched full-RREF fallback |
| Residual time/work and skew | Historical same-attempt elapsed ceilings, exact production batch reconciliation at two primes; per-target/per-source details explicitly unavailable |
| Dependency/dispatch/memory analysis | Full-RREF ordering and immutable-source candidate decomposition above; runtime measurements separately pinned and modeled |
| Scheduling prototype and 1–64-worker measured scaling | Not built: opportunity gate fails on available matched serial controls; modeled ceilings are labeled separately |
| Correctness and complete independent outputs | Existing #269/#749 offline validators rerun; no changed algebra or concurrency requiring new solver tests |
| Adoption verdict | Reject old-contract scheduler; defer target scheduling with numerical reopening condition |

Reopen after #752's integrated forward work or a named large/wide task has **current same-run**
backward wall attribution. For the ordinary 10% complete-task speedup gate, even an infinitely fast
eligible stage must exceed `1-1/1.10 = 9.091%` of that complete task. A finite-worker proposal needs
more headroom after dispatch, snapshot/deferred-output storage and skew. Declare no more than 5%
material control regression and 1.25x RSS unless a separately reviewed fixed-budget frontier
tradeoff justifies another limit. Current forward parallelism can raise backward's fraction, so
the old serial 3% ceiling does not bound the future integrated configuration.

At reopening, first add opt-in per-target elapsed/product and source-use diagnostics; measure their
overhead with counters off, then test only one coarse immutable-target prototype if the complete
task opportunity survives. Preserve supported fields, exact complete output, cancellation/panic/
refusal cleanup, reservations and generic fallback. Full-RREF callers need their own elapsed
profile and incidence distribution before any barrier/panel proposal. Larger/wider attempts and
new point-solving boundaries require their own bounded plan; this report authorizes no campaign.

## Reproduction and documentation checks

The [offline model guide](../../research/residual-backward/README.md) gives exact commands.
It revalidates existing raw evidence and regenerates the report's arithmetic without invoking
solvers or acquiring the benchmark lock. Tests were added first and failed because the model was
absent, then passed after implementation; they cover same-attempt ceilings, invalid/incomplete
censuses, dispatch-grid completeness and concurrent reservation formulas. Existing CI runs those
tests and checks the derived summary. README links, source paths and commands were reviewed.
No Rust production code or source-file headers change; no new measurement is presented as current.
