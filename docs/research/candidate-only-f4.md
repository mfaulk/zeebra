# Candidate-only production F4 backward reduction (#749)

**Measured at:** Rust/build `a9f86ec00f8040618b26372073ba43ee5240f384`; controller `36f792a142efcaea6fee2252cf1800359972337d`.
No library, Cargo or profiling-example content differs between the build and final publication
commits; test/controller/report changes are pinned separately. Baseline: current-main
`778e1dc94fbb963a9a1970dde526393ffbf5bdfe`, after #747/#746/#755 merged, with unchanged production
full batch RREF. This report uses only its own matched cohort for numerical adoption claims.

## Contract and correctness

F4 now fully reduces only pivot rows whose leading columns were absent from the input leading
set. Public matrix RREF and final matrix interreduction retain full RREF. `reduce_batch_rows=false`
retains its existing echelon behavior. Scheduling, arithmetic, field interfaces and concurrency
bounds do not change.

Forward elimination provides monic rows with distinct leading columns. Process selected targets
in increasing leading-column order. A pivot used to clear a later column has no entries to its
left, so substitution only introduces entries strictly later in the scan. Later source pivots
remain original echelon rows: already-reduced selected rows have earlier leading columns and
cannot be used by a later target. Every selected row ends with only its own pivot and free columns,
hence equals its unique full-RREF row. Each replacement is an elementary span-preserving reduction;
unused rows retain their echelon tails. Candidate leading columns never change. Exact candidate
polynomials therefore match the previous policy, inductively preserving subsequent basis elements,
pair/degree trajectories and final reduced basis. Rank/leading-term agreement alone is not used
as verification.

The algorithm uses generic `FiniteField` operations and safe owned storage, independently adapted
from Zeebra's reviewed #269 research. GPL implementation sources remain algorithm references only.

## Budget and memory behavior

Let `R` be the echelon matrix's resident mathematical entries, `C` the number of columns and
`q_i=C-leading_column_i` the maximum support of selected target `i`. Before changing any target,
reserve `R + sum(max(q_i-original_nnz_i,0)) + C`, with checked arithmetic. This covers all positive
output growth across the pass, retained originals, and the currently live dense/output support.
Gathering moves coefficients out of the dense row into the sparse output, so their live support
union fits one row. No late selective refusal can force fallback from partially changed targets.

Total additional workspace is `C*(size_of(F)+size_of(usize)+size_of(bool))`, checked against 64 MiB
**before selection-mask allocation**. Overflow, insufficient workspace or insufficient whole-pass
entry reservation selects the old full-RREF pass on the untouched echelon matrix. This preserves
old admission/error behavior instead of refusing an otherwise supported computation. No-candidate
batches allocate no selection mask, dense row or pivot index. No existing F4 budget is widened.

`peak_nonzeros` is mathematical replacement-row support, excluding retained-original copies.
`candidate_reduction` separately reports selected targets/products, conservative reservations,
sparse output/row capacity, workspace and fallback counts. Passive counters include actual
coefficient operations and scratch/index storage. `estimated_bytes` is a conservative model that
can sum noncoincident phase maxima; it is not measured RSS. Each output owns its exact-support
buffer; shared high-water scratch is not installed into persistent rows.

Cancellation remains the existing F4 observer/time policy at batch boundaries. An error still
returns no successful partial basis. No new claim of mid-row cancellation is made.

## Matched measurement protocol

Machine: Ryzen Threadripper PRO 5995WX, affinity CPU 3 (one physical core, no SMT), rustc 1.99.1, release/fat LTO/one
codegen unit/x86-64-v3, mold and system allocator. All builds explicitly clear `RUSTC_WRAPPER`;
`CARGO_INCREMENTAL=1` is inherited and recorded for every arm. Exact source, executable SHA256,
Cargo fingerprints, full topology and commands are retained in
[build metadata](../../research/candidate-adoption/build-metadata.json) and the raw cohorts.

The single benchmark lock window is **2026-11-13 16:02:52–16:05:40 America/New_York**, 168 seconds,
`status=0 end=exited`, load 0.57→1.61. No compiler overlaps, resource refusals, interrupted or
excluded attempts, retries or budget extensions occurred. Pre/post-child compiler gates remain
in every attempt. The campaign used one 900-second aggregate watchdog, 60-second/2-GiB child caps
and the existing 185-second nested watchdog. Retained campaign scratch was 95 MiB under its
predeclared 256-MiB output allowance; publication uses content-addressed full answers and is about
2.6 MiB before this report. [The protocol and commands](../../research/candidate-adoption/README.md)
predeclare the plan and gates.

Five interleaved fresh processes per cell: 90 native attempts cover three arms (old shipping
stock, feature-absent production, feature-present/counters-off production), three families and two
primes. Twenty separate work diagnostics compare full research RREF with ordinary production;
20 additional MQ10 controls disable stage clocks. Every one of the **130 complete answers** equals
its retained independently Singular-verified full reduced basis, with exact field/input identity.
Raw answers, CPU/wall/RSS, stages, pair/degree/shape/basis-growth trajectory and all work counters
remain in the [retained cohorts](../../research/candidate-adoption/). The memory peak's associated
as-built denominator is not an algebraic trajectory invariant: a changed reduction can cause a
different batch to peak. That statistic remains visible rather than being used to reject a valid
trajectory or silently held constant.

### Complete F4 adoption result

Times below are complete **F4-call** medians in milliseconds with five-run [min,max]; parsing,
answer rendering and independent checking are outside that timer. Process wall includes startup,
input generation and complete output encoding. RSS is the maximum self high-water across each
arm's five runs, measured through basis rendering; sampled process-tree RSS is retained separately.
These are matched current-source results, not ratios to #747 or another historical session.

| Family / prime | Stock F4 ms [min,max] | Production F4 ms [min,max] | Speedup | Stock → production RSS MiB |
|---|---:|---:|---:|---:|
| MQ10 / 32003 | 3173.462 [3150.298,3254.021] | 1251.183 [1247.926,1285.268] | 2.536x | 134.40 → 33.82 |
| MQ10 / 2147483647 | 3406.818 [3402.979,3410.713] | 1336.917 [1329.239,1368.610] | 2.548x | 136.33 → 34.46 |
| Cyclic-5 / 32003 | 0.989 [0.742,1.109] | 0.588 [0.570,0.663] | control only | 3.88 → 3.79 |
| Cyclic-5 / 2147483647 | 0.770 [0.758,0.771] | 0.613 [0.604,0.694] | control only | 3.91 → 3.86 |
| Katsura-6 / 32003 | 1.503 [1.493,1.722] | 1.027 [1.013,1.180] | control only | 4.48 → 4.36 |
| Katsura-6 / 2147483647 | 1.540 [1.525,1.554] | 1.027 [1.022,1.070] | control only | 4.26 → 4.14 |

All control medians improve and all maxima satisfy the predeclared 1.25x RSS ceiling. Their
sub-two-millisecond duration makes them bounded regression/correctness controls, not broad precise
speed claims. MQ10 clears the predeclared ≥10% full-call improvement gate at both primes with
nonoverlapping complete-call ranges. Final interreduction remains charged: production medians
are 12.386/12.732 ms, inside the complete-call gains above.

| MQ10 boundary | 32003 stock → production | 2147483647 stock → production |
|---|---:|---:|
| Process wall median, ms | 3205.123 → 1279.787 | 3439.942 → 1367.550 |
| Process-tree CPU median, ms | 3000.569 → 1198.251 | 3223.320 → 1281.173 |
| Stage-clock-disabled F4 median, ms | 3164.441 → 1249.315 | 3404.743 → 1334.372 |

Feature-present/counters-off production F4 medians are 1274.733/1401.162 ms, versus
1251.183/1336.917 ms feature-absent. Work-on production diagnostics are 1283.560/1417.126 ms;
they retain exact counters but are not pooled into native speedup medians. The stage-off cohort
confirms the result without stage clocks. Small differences between staged and unstaged medians
are not optimization claims. No internal time is substituted for process wall or complete point
solving; this experiment computes complete reduced bases only.

### Work removal and storage

The separately observed MQ10 counts are identical across five diagnostics per cell. Direct
production product counts agree exactly with passive counters. Forward work stays unchanged;
backward products fall by about 24.6x. Candidate-only work does not create new final-interreduction
debt because its extracted polynomials are coefficient-for-coefficient full-RREF candidates.

| MQ10 prime | Forward products, both | Full backward products | Production backward products | Complete batch products, full → production |
|---|---:|---:|---:|---:|
| 32003 | 585,166,982 | 579,721,912 | 23,566,622 | 1,164,888,894 → 608,733,604 |
| 2147483647 | 585,195,178 | 579,751,105 | 23,567,093 | 1,164,946,283 → 608,762,271 |

Only 250 target rows are reduced. Production loads 210,902/210,910 dense nonzeros, scans 629,935
columns and gathers 71,088/71,089 output entries. The full policy copies back 610,222,599 /
610,252,491 sparse entries. These are modeled logical operations, not allocator calls, physical
DRAM traffic or a measured bandwidth roofline.

| Peak quantity | 32003 | 2147483647 |
|---|---:|---:|
| F4 mathematical live entries, full → production | 3,932,926 → 1,164,536 | 3,933,045 → 1,164,559 |
| Candidate-pass conservative reserved entries | 1,119,821 | 1,119,843 |
| Candidate-pass sparse row/output capacity, entries | 1,066,897 | 1,066,920 |
| Candidate dense/index/selection workspace, bytes | 156,260 | 204,340 |
| Production full-RREF fallback batches | 0 | 0 |

These maxima describe different phases and moments. In particular, the total F4 mathematical
peak can exceed the later candidate-pass reservation because forward elimination already peaked
before that reservation was made. They must not be added, divided as simultaneous footprints or
used as a substitute for the process RSS measurements. Physical memory-controller bandwidth is
not measured here.

## Validation and decision

Behavioral Red first failed on exact selected rows, full-RREF fallback and separate reservation
accounting; Green passed after implementation. At the initial adoption source the complete library
passed 2,800 tests, 27 ignored. The final preflight source passes 282 focused F4 tests, 5 ignored,
and seven candidate-kernel tests. An external integration test covers all three ordinary order
kinds plus representative weighted and product orders: 18 two-block configurations (both split
positions, all 3×3 block suborders), all three weighted tie breaks, six fields including GF(2),
GF(2^8), 32-bit, 64-bit and BN254, every elimination backend and structured/unstructured reduction.
Candidate outputs equal public full RREF; complete small bases equal independent Buchberger output.

No-selection, rank-deficiency/empty rows, reversed physical row order, tight-budget/fill-in fallback,
whole-pass growth and overflow/total-workspace preflight are covered. Existing cancellation, budget,
allocator-capacity and independent fixture regressions remain in the F4/library suite. Default and
research/no-default builds are checked. Protocol tests reject missing production metadata, research
overrides disguised as production, wrong input/full coefficients, trajectory drift, incomplete
plans, invalid timers/RSS, missing executable identities and compiler contamination. A Red–Green
supervisor regression kills/reaps owned process groups on interruption; cleanup also handles a
natural-exit race safely. Existing CI verifies retained data without measuring.

**Adopt the serial candidate-only contract with unchanged full-RREF fallback.** The isolated
correctness/budget gate and the predeclared complete-task, control and memory gates pass on these
named inputs. This is approximately 2.54x complete serial F4 acceleration on the two pinned MQ10
small-prime tasks, with exact independent output checks and substantially lower measured RSS.
It is not a general solver or field-width performance claim.

| #749 acceptance area | Disposition |
|---|---|
| Tests first and exact candidates/complete outputs | Met by the Red–Green kernel tests, full-RREF/Buchberger comparisons and 130 independent complete-reference checks |
| Supported fields/orders/backends | Correctness covered by ordinary, weighted and block-order controls, prime/binary/extension/64-/254-bit fields; wide performance remains separate |
| Budget admission, mathematical versus reserved counts | Checked whole-pass/total-workspace preflight, untouched fallback and tight-limit/overflow regressions; no widened defaults |
| Cancellation/refusal/reuse and capacity safeguards | Existing batch-stop guarantees retained; refusal/retry tests and exact-output owned buffers; no mid-row cancellation promise |
| Instrumented versus native full-task measurements | Five matched repeats, separate feature/counter/stage-clock controls, all failures retained (none occurred) |
| README/source/CI/provenance | Updated contract/counter documentation and offline CI revalidation; exact source/compiler/executable identities retained |

Reproduce by building baseline `778e1dc9` and production `a9f86ec0`, using the controller at
`36f792a1` and the [retained launch script](../../research/candidate-adoption/run-adoption.sh).
Offline verification executes no solver:

```sh
python3 tools/test/selective-backward-study-test.py
python3 tools/test/candidate-adoption-summary-test.py
python3 research/candidate-adoption/summary.py --check
```

No production parallel policy, wider-field performance or new fixed-budget
frontier completion is claimed. The separate adaptive parallel integration remains #752; matrix-only
scaling and the historical #747 experimental headline are not this report's result.
