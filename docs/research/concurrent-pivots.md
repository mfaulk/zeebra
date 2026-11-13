# Concurrent F4 pivot discovery (#728)

Source audit: Zeebra `e22b9b58`; serial census **measured at `65a02699`** with Rust
instrumentation from `8e971167`. [Protocol and reproduction](../../research/concurrent-pivots/README.md).
The post-prefix #713 census is reused, not relabelled as a new timing result.

## Reference mechanisms

| Reference and immutable revision | Publication and scheduling | Implication for Zeebra |
|---|---|---|
| [msolve `la_ff_common.c`](https://github.com/algebraic-solving/msolve/blob/c5a41f0a842c126d669676c041bd3fc4675cf7e7/src/neogb/la_ff_common.c), `c5a41f0a842c126d669676c041bd3fc4675cf7e7`, exact sparse routines | OpenMP dynamic row/group scheduling, worker-private `int64_t` dense storage, CAS installing a completed sparse pivot; losers resume reduction. The shared file invokes width-specific reduction/normalization callbacks. | Separate the scheduling/publication idea from grouped arithmetic and field width. Audit the final-reduction path's thread selection; do not extrapolate every OpenMP loop to every task. |
| [Groebner.jl threaded backend](https://github.com/sumiya11/Groebner.jl/blob/509ed7c38338608c25c9c86713ed7a57bb78f5ba/src/f4/linalg/backend_threaded.jl), `509ed7c38338608c25c9c86713ed7a57bb78f5ba` | Reservation changes sentinel 0 to 1; normalization, coefficient storage and support initialization precede release-publishing sentinel 2. Consumers acquire ready pivots. Rows are assigned to round-robin task chunks. | Reservation is not readiness. Its deterministic threaded path is independent of randomized row skipping. [Dispatch](https://github.com/sumiya11/Groebner.jl/blob/509ed7c38338608c25c9c86713ed7a57bb78f5ba/src/f4/linalg/linalg.jl) uses lower-row/task and column gates; these are upstream policy, not Zeebra crossover evidence. |
| [Monagan–Pearce, PASCO 2015, §2.2](https://www.cecm.sfu.ca/CAG/papers/RomanPasco2015.pdf) | Private dense work rows and atomic sparse-pivot installation; a failed claim requires further reduction. | Redundant work is possible; historical speedups do not predict present workloads or efficiency. |
| [Rust comparand](https://github.com/sdiehl/groebner/blob/c3e1d630fba9b2155a4c389d9022f13e0ba09218/src/f4/eliminate.rs), `c3e1d630fba9b2155a4c389d9022f13e0ba09218` | A column-indexed `OnceLock` table stores owned completed pivots, separate from borrowed known rows. Failed installation returns ownership to the losing row for reduction. | A safe standard-library publication mechanism avoids custom raw-pointer reclamation. Its [scheduler](https://github.com/sdiehl/groebner/blob/c3e1d630fba9b2155a4c389d9022f13e0ba09218/src/par.rs) and coefficient layout are separate choices. |

The GPL sources are algorithm references only. The initial instrument modifies
Zeebra's own serial observer and uses no imported elimination implementation.
No comparand source is vendored into the MIT library.

The pinned msolve trace/application sparse routines explicitly choose one thread
in final reduction; the ordinary exact sparse routine takes `st->nthrds`.
Groebner.jl's dispatch requires at least twice as many lower rows as tasks and at
least 1000 columns. These policies are not Zeebra crossover measurements.

## Initial serial census and prototype gate

The retained [complete cohort](../../research/concurrent-pivots/census.json.gz)
contains 40 verified attempts: five repetitions of four arms on each MQ10 field.
Every complete reduced basis equals the retained independently Singular-verified
answer coefficient-for-coefficient. Input digests, degree sequences, pairs and
algebraic counters are unchanged by observation. The earlier
[interrupted cohort](../../research/concurrent-pivots/census-interrupted.json.gz)
retains seven completed attempts followed by a load-gate refusal; it is not pooled
into the complete cohort. The complete lock window is 2026-11-13 00:25:09–00:30:40
America/New_York, `end=exited status=0`; load at its boundaries is 2.25/1.48.

| Field | Stock wall median [min,max], ms | Feature/off | Aggregate work | Discovery |
|---|---:|---:|---:|---:|
| 32003 | 3130.08 [3106.49,3137.79] | 3256.53 [3225.50,3298.21] | 3288.24 [3268.82,3317.26] | 3304.37 [3300.07,3393.94] |
| 2147483647 | 3462.92 [3437.34,3501.92] | 3510.72 [3504.26,3597.26] | 3534.78 [3485.27,3622.65] | 3569.37 [3512.11,3600.86] |

These are fresh-process spawn-to-reap times including full answer encoding;
verification follows timing. Per-process RSS and all per-row elapsed observations
are retained in the cohort. Detailed forward row clocks occupy within-run median
37.93%/38.04% of the observed F4 call. This is a measured elapsed fraction of the
instrumented path, **not an exact stock stage fraction**. Feature/off versus stock
and discovery/off expose compilation and observation costs. Even assigning their
whole observed difference to forward work leaves ample margin over the declared
10% investigation threshold. The observed Amdahl model saturates near 1.61x;
crediting all elimination time to forward discovery would be invalid.

Inherited pivots account for 307650953/307661703 products, newly discovered pivots
for 277516029/277533475. This refines #713's existing total of
585166982/585195178 forward products. The dominant batch has 1468 candidates,
579 new pivots, 889 zeros and 12020 columns. Its serial first-claim groups have at
most six rows. Dependency counts and weighted DAG lengths describe this serial
trajectory; concurrent winners may change work, so neither proves concurrent
critical-path length or retry count.

At the largest width, 64 dense accumulators require about 2.94 MiB for GF(32003)
and 5.87 MiB for GF(2147483647), below the declared 256 MiB scratch gate.
Publication tables, live entries, reservations and thread stacks cost extra.
The gates justify **one bounded prototype**, not an adoption or scaling claim.

## Correctness and resource requirements for a possible prototype

Known reducer rows remain read-only. A private candidate accumulator starts as an
input row and changes only by subtracting multiples of published pivots and by
nonzero normalization. Hence every live residual remains in the input row span.
Publish a fully initialized monic sparse row only in the slot of its leading
column. A single-assignment slot gives distinct leading columns. On losing a
claim, keep the owned losing row, load it again, and eliminate with the winner:
its lead strictly advances or the row becomes zero. There are finitely many
columns, so each row terminates without waiting for an unpublished future pivot.

Every consumed input is represented by a published residual plus the pivots used
to reduce it, or reduces to zero. Both span inclusions follow; matching ranks alone
would not establish them. Winners can have unreduced tails. Freeze all winners
until every worker joins, then run the existing backward pass separately. Do not
mutate a pivot while a reader can still borrow it. This preserves the linalg RREF
contract and the F4 candidate-selection contract without making inherited reducers
an identity first. The rejected #50 decomposition remains rejected.

Prefer `OnceLock<SparseRow<F>>` with ordinary Rust borrows over an empty/reserved/
ready raw pointer protocol. Fully initialize and normalize before `set`; `get`
returns only initialized storage. A failed `set` returns ownership. Scoped joins
end every reader before extraction/destruction, so no ABA or reclamation protocol
is needed. Cancellation and worker panics must join everyone and discard the whole
partial result. Failure must leave no successful partial basis or lingering claim
state, and subsequent calls must work normally. `Send + Sync` belongs only on the
experimental entry, never on the public `FiniteField` trait.

Concurrent resource checks must precede growth. One simple conservative ledger
retains all original input entries, charges every published pivot, and reserves
up to two full row widths per active candidate (dense mathematical support plus
temporary sparse materialization). Replace the reservation with the winner's
actual entries only after publication. Count all simultaneous losers/reservations;
do not reuse the serial peak as a concurrent bound. A separate workspace-byte
limit covers worker dense capacities and publication/index arrays; process RSS
and input/output capacities remain separately reported. Checked arithmetic must
refuse overflow. This ledger may reject a serially affordable matrix; report that
restriction rather than silently raising the shipped budget.

The source design is independent of #269's output-necessity experiment and #592's
pool. Any timed prototype needs a measured dispatch floor, dynamic versus static
controls, explicit worker-local product/retry aggregation, and the full correctness
and adversarial scheduling tests described in #728. Serial thread-local counters
in a parent scope cannot observe worker work. No custom atomics or unsafe code are
necessary for publication; synchronization-library guarantees do not replace forced
race, panic, cancellation, reservation-refusal and reuse tests.

## Native prototype results and verdict

**Measured prototype source: `cf92a3cb`; resumption runner: `1e16ac90`.** The
[310-attempt cohort](../../research/concurrent-pivots/parallel.json.gz),
[300 classical controls and four budget probes](../../research/concurrent-pivots/controls.json.gz),
[source/build recovery stamps](../../research/concurrent-pivots/evidence/provenance.json)
and [benchmark lock log](../../research/concurrent-pivots/evidence/benchlock.log)
retain every attempt, exact answer and verification outcome. Together with the
40 serial census attempts, **650 completed final-cohort answers verify**. Seven
additional verified answers remain in the separately retained interrupted census.
CI rechecks them too. The four
MQ14 probes are incomplete resource refusals and are excluded from that count.
No completed MQ10 solve used the serial budget fallback.

Machine: Threadripper PRO 5995WX, 64 physical cores/128 logical CPUs; Rust 1.99.1,
release/fat LTO/one codegen unit, x86-64-v3. Each child uses one logical CPU per
physical core, selected from actual topology, starting with CPU 2. The exact sets,
cache/node IDs, binary/lock hashes, limits and load readings are retained. No SMT
arm was selected. Scratch is first touched by its worker; immutable inputs are
built by the main thread. No separate NUMA-placement experiment was performed.

Five interleaved fresh processes per arm/field compare stock serial, the new
feature-present serial controls, and the same concurrent algorithm at
1,2,4,8,16,32,64 workers under both schedules, counters off/on. A load-gate refusal
at 5.826 interrupted the fourth repetition. The resumption preserved the exact
verified prefix and the frozen binary hashes and ran only the missing samples;
no sample was discarded or repeated to improve a result. Its runner commit and
the original refusal remain in `resumptions`. Ranges include all five samples.

The following are **uninstrumented-counter process walls**, including input,
complete F4 and full output encoding. Stock controls in this cohort are
3080.07 [3048.29,3190.00] ms / 135.57 MiB and
3380.86 [3340.75,3563.92] ms / 136.28 MiB respectively. No historical timing is a
denominator. Efficiency uses the new algorithm's own p=1 wall, not stock wall.

| Workers | GF(32003) wall median [min,max], ms | Stock speedup | Same-algorithm efficiency | GF(2147483647) wall median [min,max], ms | Stock speedup | Same-algorithm efficiency |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 3206.90 [3059.13,3276.88] | 0.96x | 100% | 3386.01 [3243.44,3716.23] | 1.00x | 100% |
| 2 | 2590.93 [2535.20,2671.70] | 1.19x | 61.9% | 2803.05 [2655.50,3069.85] | 1.21x | 60.4% |
| 4 | 2375.01 [2298.46,2410.79] | 1.30x | 33.8% | 2486.42 [2431.59,2603.03] | 1.36x | 34.0% |
| 8 | 2214.04 [2159.22,2310.79] | 1.39x | 18.1% | 2354.14 [2317.44,2389.50] | 1.44x | 18.0% |
| 16 | 2109.88 [2065.57,2216.31] | 1.46x | 9.5% | 2297.42 [2276.78,2397.81] | 1.47x | 9.2% |
| 32 | 2178.91 [2131.04,2249.99] | 1.41x | 4.6% | 2348.80 [2330.04,2445.97] | 1.44x | 4.5% |
| 64 | 2207.93 [2106.86,2234.88] | 1.40x | 2.3% | 2302.87 [2287.59,2325.66] | 1.47x | 2.3% |

Exact ranges and both schedules are in [parallel.csv](../../research/concurrent-pivots/parallel.csv).
Four to sixteen workers are a useful MQ10 range; the experiment does not establish
a unique optimum between overlapping high-worker ranges. At p=16, same-algorithm
full-task speedups are 1.52x/1.47x. At p=64 extra cores do not produce a persuasive
complete-task gain over p=16, while CPU time rises. Dynamic p=16 is faster in median
than static p=16 (2225.77/2402.34 ms), but their full-task ranges overlap on the
larger field; the data do not calibrate a universal scheduler crossover.

The dominant **same-input matrix** scales much further: its forward phase changes
from 843.74/901.88 ms at p=1 to 18.57/19.90 ms at p=64, about 45.4x/45.3x and 71%
matrix-stage efficiency. Every observed arm has identical pre-elimination matrix
digests, checked using the existing corpus fingerprint routine. These are matrix
stage results, not 45x complete-basis speedups. All per-batch curves and active
worker counts are retained in [matrix-scaling.csv](../../research/concurrent-pivots/matrix-scaling.csv).
Some matrix ratios slightly exceed linear scaling; work differences and noise
prevent interpreting that as hardware superlinearity.
The serial backward phase still takes 1830.19/2011.88 ms at dynamic p=16.

| Field/arm | Process CPU median, s | Process RSS median [min,max], MiB |
|---|---:|---:|
| 32003 stock | 3.062 | 135.57 [135.49,135.58] |
| 32003 dynamic p=16 | 3.225 | 135.84 [135.47,136.07] |
| 32003 dynamic p=64 | 3.539 | 138.43 [137.99,140.75] |
| 2147483647 stock | 3.360 | 136.28 [136.15,136.38] |
| 2147483647 dynamic p=16 | 3.514 | 136.38 [136.20,136.81] |
| 2147483647 dynamic p=64 | 3.723 | 140.53 [140.29,140.87] |

The p=16 wall and RSS gates pass on MQ10. Workspace maxima at p=64 are 3750240 /
6827360 bytes, including dense buffers and pivot/index arrays; reservation peaks
stay below three million entries on these inputs. Observed p=16 sparse live peaks
are 3928801/3929819 entries and sparse capacity maxima 6840008/6843659 slots, in
the later backward phase. These are separate boundaries, not quantities to sum
as a simultaneous peak. Allocator events and physical memory bandwidth were not
measured. Nonzero sparse materializations are counted by successful plus failed
publications; dense allocations are one per active worker per batch. Additional
report, thread and allocator allocations are outside that count.
The legacy F4 per-backend dense-buffer statistic still describes one Adaptive row;
the experimental workspace ledger reports worker capacity for this hook.

### Work, contention, skew and overhead

Counters-on p=1 reproduces the serial control's 585166982/585195178 forward
products with zero lost publications. At dynamic p=16 the product medians are
578354208/576824272, with 569/750 failed publications; at p=64 they are
560401051/554372312, with 928/1475 failures. Thus changed pivot winners alter work;
the strong-scaling rows are not an equal-instruction experiment. Products executed
after a lost claim are 34391960/40254066 at p=16 and 75939650/92012623 at p=64.
They are not all provably redundant work: baseline pivot trajectories also require
reductions, and total work can decrease despite more retries.

Static p=16 loses fewer claims (168/322 medians) but performs more products
(622277258/614764387). In the dominant matrix, median min/max worker durations are
54.17/56.06 ms and 58.81/60.77 ms for dynamic p=16, versus 16.93/89.77 ms and
20.26/98.45 ms for static. This supports dynamic scheduling as the smaller useful
prototype; it does not justify implementing weighted scheduling or another queue.
Worker durations/row counts, actual dense loads/scans/gathers, normalization work,
scheduling and publication clocks remain available in each complete response.

Observed p=16 sums of scheduling/reservation clocks are 0.84/0.37 ms, and sums of
publication clocks 0.32/0.39 ms. These sums span workers and are neither independent
elapsed shares nor pure lock-wait times. There is no custom unsafe/atomic pivot
protocol: `OnceLock` and scoped joins provide publication/lifetime synchronization;
relaxed cancellation flags carry no data ownership.

Observation is material. Dynamic p=16 counters-on process medians are
2461.91/2768.01 ms versus 2109.88/2297.42 ms off. These arms additionally hash
matrices and collect worker/parent diagnostics; they establish work and identity,
not the timing speedup. Feature-present serial/off controls are
3145.47/3360.47 ms; ranges overlap stock on the larger field. Do not turn a
compiler/layout or observation difference into a threading result.

Five fresh processes per worker count measure sixteen empty scoped dispatches
each. Median floors in microseconds are 42.36, 65.73, 78.84, 127.43, 299.64,
600.13, 1334.20 at 1,2,4,8,16,32,64 workers; [dispatch.csv](../../research/concurrent-pivots/dispatch.csv)
retains min/max. This is spawn/join wall cost, not a persistent-pool measurement
or a decomposition of enqueue/wake/barrier CPU cost. #592 remains the runtime
comparison; no predicted nanosecond pool floor is assumed here.

### Classical controls, fixed budget and decision

All 300 classical-control answers verify. Cyclic uses the retained full independent
reference. Each Katsura field additionally retains a fresh Singular computation
and complete coefficient-set comparison, outside timing. At dynamic p=8, whole
process serial/new speed ratios are 0.696/0.710 on Cyclic-5 and 0.695/0.704 on
Katsura-6: about 41–44% slower. F4-call ratios are separately retained; they are
not substituted for process-wall adoption criteria. The [control table](../../research/concurrent-pivots/controls.csv)
includes every worker count and both schedules. **Unconditional dispatch fails
the predeclared 5% regression gate.**

The public MQ14 probes keep the default 32000000-entry cap. Both serial and
dynamic p=4 return `TooManyNonzeros` in both fields, with no accepted partial
basis. Times to refusal are 31.72/21.53 seconds at 32003 and 31.55/22.64 seconds
at 2147483647; peak RSS is 765–773 MiB. These are resource outcomes, not speedups.
No completed larger rung or fixed-budget frontier improvement is established.
The separately gated 24843682-entry corpus case uses a 64-million-entry preset;
that larger-budget replay was not enabled or represented as covered by this run.

**Verdict: retain the opt-in prototype and evidence; reject unconditional
dispatch; defer production integration.** Concurrent discovery is useful on the
tested MQ10 tasks, with a measured full-task gain and affordable memory. Its
maintenance cost is a research-only hook, safe pivot ownership, strict reservation
logic and failure tests; serial remains the default and the generic fallback.
The new tests cover forced pivot races, rectangular/rank-deficient inputs, binary
and 254-bit fields, mid-run budget refusal, cancellation, worker panic and reuse.
A digest-pinned live corpus matrix also matches an independent sparse RREF
coefficient-for-coefficient under both schedules at every measured worker count.

A later integration proposal needs a validated dispatch gate for small batches,
a completed independently checked larger target under fixed resources, and the
selective-backward × parallel-forward 2×2 after #269 supplies its policy. #269 and
#592 were still open at this audit; neither result is invented here. The new
worker evidence can inform #729, but claim counts alone do not establish a
waiting-queue opportunity. Removing backward work may change both the eligible
fraction and the best worker count: do not multiply separately measured gains.
