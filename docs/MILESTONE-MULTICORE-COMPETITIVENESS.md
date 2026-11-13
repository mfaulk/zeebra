# M28 — Competitive Multicore Algebra and Wide-Field Frontier

**Status:** planned; no M28 implementation or benchmark campaign authorized by this document alone.
**Planning date:** 2026-11-13.
**Source audit:** current `main`, `ae489ca33c00d49d906d33ee73e9dfea853b82a2` (#748).
**Measured at:** not measured here. Numerical evidence below is attributed to its original
source/control revision and computational boundary; no timings were taken for this plan.
**Tracking issue:** [#750](https://github.com/mfaulk/zeebra/issues/750).
**Project:** [Zeebra #7](https://github.com/users/mfaulk/projects/7).
**Planning branch:** `docs/m28-multicore-plan`; planning PR recorded on #750.

## 1. Executive summary and vision

Can Zeebra combine lower algebraic work, efficient finite-field kernels and multicore execution
to compete with the strongest capable algebra systems on substantial, independently verified
polynomial systems, especially over large prime fields?

Two primary objectives organize M28: competitive multicore F4, and a hard wide-prime-field
competitive frontier. Block Krylov conversion is subordinate, conditional research. Complete
reduced-basis computation is the principal F4 task; complete solving has a separate boundary
including operator construction, conversion, recovery and verification. A basis is not a point.

The first investment is removing unnecessary backward work, followed by adaptive use of the
existing concurrent-pivot algorithm. Arithmetic and storage proposals must be repriced after work
removal. External multiworker baselines and hard 64-bit inputs determine what is worth shipping.
No victory is promised: a reproducible, costed negative decision can satisfy Minimum. Strong
requires a full-task achievement. Stretch requires a narrow certified competitive or resource
frontier advance. Historical matrix scaling cannot satisfy either tier by itself.

## 2. Inherited M26/M27 results and limits

Read the [M26 integration report](MILESTONE-ALGORITHMIC-ELIMINATION.md#14-integration-report-2026-11-11)
and [M27 integration report](MILESTONE-COMPETITIVE-MQ-SOLVING.md#15-integration-report-2026-11-11),
including their unfulfilled criteria. Published integration reports do not mean every original
milestone requirement was met. Neither old tracker bodies nor old `Status: planned` passages
override these reports.

M26/M27 delivered faster resultant computation, budget diagnostics, batch-tail reduction and
matrix final interreduction. M27 also delivered certified scalar Wiedemann conversion with
classical fallback. These are prerequisites, not new implementation assignments.

M27 §15.3 transcribes the `3d0e3759` paired interreduction cohort: complete MQ10 reduced-basis
time changes from 27,536.2 ms to 4,695.7 ms (5.86x), with Singular at 7,371.9 ms in that cohort.
That establishes a selected task-equivalent lead over Singular at that revision, with increased
memory cost. It does not describe audited-main timing, msolve parity or a multicore lead.
Do not restore the pre-M27 interreduction route as an optimization control except as an explicitly
named historical ablation.

[M27 §15.6](MILESTONE-COMPETITIVE-MQ-SOLVING.md#156-m28-recommendation-and-the-original-hypotheses)
requires repeating weak Katsura measurements and obtaining a bounded current-default public-MQ
profile covering basis construction, operators, conversion, recovered points, verification,
fallback and attributable RSS. M28-0 owns this missing evidence alongside #739's comparand curves.
An F4-only profile cannot silently satisfy this whole-route requirement.

## 3. Current competitive position and provenance

The [generated competitive board](../research/competitive/COMPETITIVE.md) is a collection of
pinned attempts, not a single current-main experiment. Its `unchecked`, failed, unsupported and
limit-stop rows remain visible. Do not pool sessions or divide Julia warmed solve time by another
engine's process wall. The [external-engine guide](guide/external-engines.md) defines supported
tasks, startup screening and current adapter restrictions.

| Evidence | Revision and boundary | Finding and applicability |
|---|---|---|
| [Current-default MQ10 profile](research/mq10-current-profile.md) | `5409f2bf`, native; sampling `a7a11368`; F4-call stages | Elimination including backward reduction is 96.66%/97.01% at GF(32003)/GF(2147483647); final interreduction about 0.3%. Historical post-M27 profile, not a timeless stage share. |
| [Matched msolve attribution](research/msolve-gap.md) | Zeebra `99a81844`, unchanged instrument content at `47161ee1`; msolve 0.11.0; single worker, process wall | GF(32003): about 13.9x wall gap, 4.14x batch products, 4.77x elimination ns/product. The last quantity averages different forward/backward mixtures and is not an isolated arithmetic-kernel ratio. GF(2^31−1) reports 13.7x/4.14x/4.86x separately. |
| Same work study | Zeebra counts from `ff65d2b4`, applicability reconciled to row counts at the timing pin | About 579.7 M backward products versus msolve 0.64 M. Main opportunity: inherited reducer tails need not all be backward reduced. |
| [Symbolic attribution](research/symbolic-attribution.md) | `575f59d9` frozen replay; `f80adee9` complete sorted-input check | Ordering plus duplicate-multiple removal changes forward products from 585.17 M to 486.42 M in replay. Combined live policy and end-to-end time were not measured. |
| [Kernel study](research/elimination-kernels.md) | Prefix result `dd36652e`; delayed pilot `6578c0ab` with overlay hash retained there | Generic prefix merge shipped. Delayed small-prime pilot fails broader full-solve regression gates. Read-side fill counts are not measured physical controller bandwidth. |

The [Groebner.jl gap](research/groebner-jl-gap.md) and
[grobx trajectory](research/grobx-trajectory.md) explain older algorithm/work comparisons. Their
interreduction and compiler boundaries must not replace current controls. Widely different
per-product averages motivate experiments; they do not identify one independently recoverable
factor. #739 still lacks a completed current multiworker competitive curve at this audit.

## 4. Completed parallel studies and newly discovered in-flight work

### 4.1 Completed prerequisites

- [#728 / #741](https://github.com/mfaulk/zeebra/pull/741),
  [concurrent-pivot report](research/concurrent-pivots.md): prototype source `cf92a3cb`, resumption
  runner `1e16ac90`. At 16 workers, MQ10 process-wall speedups against matched stock serial are
  1.46x/1.47x across the two primes. Dominant-matrix forward scaling at 64 workers is about 45x;
  serial backward work remains large. Unconditional small-control dispatch fails the declared
  5% regression gate. MQ14 refuses at the entry budget; no frontier completion is established.
  `OnceLock`, immutable pivots, private scratch and joined workers already exist experimentally.
- [#592 / #735](https://github.com/mfaulk/zeebra/pull/735),
  [worker-pool report](research/worker-pool.md): source `81aaa1be`, controller `6360904a`.
  Warm persistent dispatch is much cheaper than scoped spawning; small default FGLM border
  batches still often lose. Production runtime integration was deferred. Do not repeat an empty
  dispatch study or assume that a pool creates profitable algebraic work.
- [#737 / #743](https://github.com/mfaulk/zeebra/pull/743) and
  [#742 / #745](https://github.com/mfaulk/zeebra/pull/745) supply work attribution above.
  Their instrumentation is not a production policy change.

### 4.2 Audit correction: selective reduction is already under review

[PR #747](https://github.com/mfaulk/zeebra/pull/747) is open against #269 at planning time.
Its [candidate-only report on the branch](https://github.com/mfaulk/zeebra/blob/feat/269/docs/research/elimination-kernels.md#candidate-only-backward-feasibility-269)
and [retained artifacts](https://github.com/mfaulk/zeebra/tree/feat/269/research/selective-backward)
were inspected. Treat its verdicts as reported research pending review/merge, not shipping behavior.
Serial source `0ed4fe33`, controller `c148058b`: MQ10 complete F4 medians are 3.28/3.32 s stock
versus 1.32/1.48 s selected, with about 135 MiB versus 36 MiB process RSS and 579.7 M versus
23.6 M backward products. Fields are GF(32003)/GF(2147483647), five interleaved repetitions on
the 5995WX. The rejected dense-all-target alternative grows work to about 7.08 B products.

The requested 2×2 already has bounded research evidence in #747: combined Rust `ff15a0af`,
controller `1bf48baa`, complete F4-call medians, not process-wall competitive ratios:

| Backward policy | Serial forward, ms (32003 / 2147483647) | Four-worker forward, ms |
|---|---:|---:|
| Existing full reduction | 3200.824 / 3309.431 | 2332.214 / 2438.262 |
| Selected candidates | 1300.425 / 1383.567 | 494.656 / 513.758 |

The same concurrent algorithm's one-worker selected controls are 1274.008/1367.392 ms. Combined
four-worker versus matched serial-full is 6.47x/6.44x, measured together, not multiplied from
independent speedups. Small classical controls still regress and MQ14 still refuses. Wider-field
performance, production contracts/statistics and a larger verified completion remain unproved.
Do not declare M28 Strong achieved by adopting this planning snapshot's experimental headline.

Existing [#749](https://github.com/mfaulk/zeebra/issues/749), a native child of #269, owns serial
production adoption after #747. M28-A reuses both. No new selective-backward or duplicate 2×2
research issue is needed; M28-B must confirm the crossing after integration on its own pinned build.

### 4.3 Audit correction: wide-field ladder is already in flight

[#738](https://github.com/mfaulk/zeebra/issues/738) has draft
[PR #746](https://github.com/mfaulk/zeebra/pull/746): 39 proposed pinned identities across dense
unplanted MQ, Katsura, zero-dimensional Cyclic, Eco and Noonburg, two 64-bit primes and capability-only
BN254. Its body says the serialized measurement campaign is pending. Neither proposed catalog
size nor existing easy planted rows establish a hard competitive win. M28-D follows that owner.

## 5. Principal bottlenecks, goals and non-goals

Prioritize necessary output over full matrix normalization, then forward coefficient work,
per-update arithmetic/data movement, and adaptive concurrency. Recompute the ranking after #749;
removing a bottleneck changes both the Amdahl bound and the profitable representation.

Preserve generic `FiniteField`, safe Rust where practical, supported orders/backends, exact
mathematical results, cancellation and resource enforcement. No global `Send + Sync` requirement
on `FiniteField`; put concurrency bounds at the actual dispatch boundary. No weakened randomized
correctness to imitate another engine. Account for exact checking and deterministic fallback.

Non-goals: generic new parallel F4, another worker-pool feasibility study, a new benchmark framework,
GPU purchases, distributed attacks, NVMe elimination, universal SIMD or field-independent density
thresholds. No algorithm code, default change, expensive experiment or merge belongs in this PR.

## 6. Issue reconciliation and ownership

P0 maps to board **High**, P1 normally **High** or **Medium** by the existing queue; P2 maps to
**Medium**. Priority is a Project field, not a new priority label. M28 is a milestone label;
native GitHub milestone objects are unused (none returned by the audit) and none is created.
The 351-item Project snapshot was read completely. Recheck leases and open linked PRs at pickup.

| Issues | Disposition for M28 | Priority / stream | Dependencies / status at planning |
|---|---|---|---|
| [#256](https://github.com/mfaulk/zeebra/issues/256) | Existing and sufficient overarching research epic | High / shared | Open; preserve all existing parent relationships |
| [#751](https://github.com/mfaulk/zeebra/issues/751) | New narrow full-route baseline owner | P0 / 0 | M27 §15.6; #739 supplies comparands |
| [#739](https://github.com/mfaulk/zeebra/issues/739) | Existing and sufficient scaling owner | P0 / 0 | Open; wide extension after #738 identities |
| [#269](https://github.com/mfaulk/zeebra/issues/269), [#749](https://github.com/mfaulk/zeebra/issues/749) | Existing research plus sufficient adoption follow-up | P0 / A | #269 open with live #747; #749 waits for #747 |
| [#752](https://github.com/mfaulk/zeebra/issues/752) | New adaptive production follow-up to #728 | P0 gate, P1 implementation / B | #749, [#751](https://github.com/mfaulk/zeebra/issues/751), #739; no unconditional dispatch |
| [#729](https://github.com/mfaulk/zeebra/issues/729) | Existing and sufficient conditional queue decision | P1 / B2 | Reprice post-selection retries/skew; no automatic scheduler build |
| [#730](https://github.com/mfaulk/zeebra/issues/730) | Existing and sufficient residual-backward decision | P1 conditional / B | Post-#749 serial share; may close with a negative study |
| [#268](https://github.com/mfaulk/zeebra/issues/268), [#270](https://github.com/mfaulk/zeebra/issues/270), [#715](https://github.com/mfaulk/zeebra/issues/715) | Existing and sufficient storage/arithmetic/reuse owners | P1 / C | Read-only ranking now; shared-file implementation after A contract |
| [#753](https://github.com/mfaulk/zeebra/issues/753) | New narrow live ordering/dedup follow-up | P1 / C | Completed #742; profile; serialize with #749 changes |
| [#738](https://github.com/mfaulk/zeebra/issues/738) | Existing and sufficient hard-corpus owner | P0 / D | Draft #746 in progress; no competing issue |
| [#87](https://github.com/mfaulk/zeebra/issues/87), [#731](https://github.com/mfaulk/zeebra/issues/731) | Existing and sufficient conditional block research | P2 / E | Full conversion profile and measured operator density first |
| [#273](https://github.com/mfaulk/zeebra/issues/273) | Existing and sufficient adaptive policy owner | P1 conditional / B/E | Successful measured route; no planner rewrite in advance |
| [#754](https://github.com/mfaulk/zeebra/issues/754) | New integration/report owner | P0 closeout / I | All required decisions, provenance and final comparisons |
| [#728](https://github.com/mfaulk/zeebra/issues/728), [#592](https://github.com/mfaulk/zeebra/issues/592), [#737](https://github.com/mfaulk/zeebra/issues/737), [#742](https://github.com/mfaulk/zeebra/issues/742) | Completed prerequisites | Reference only | Closed; do not reopen or rewrite historical research |
| [#272](https://github.com/mfaulk/zeebra/issues/272), [#716](https://github.com/mfaulk/zeebra/issues/716), [#225](https://github.com/mfaulk/zeebra/issues/225) | Deferred or out of scope | No primary M28 commitment | Reopening conditions in §13 |

New native children belong to #750. Shared research issues gain M28 associations and links, not a
replacement parent. In particular #749 stays under #269 and #87 retains its hardware-research
ownership. Do not change #269's live claim (`zeebra-269@feat/269`) or rewrite #738 while #746 is
under development. Historical closed labels/statuses are left intact.

## 7. Workstreams and decision gates

### 7.1 M28-0 — current baseline and competitive algorithmic cost model

Owners: [#751](https://github.com/mfaulk/zeebra/issues/751) and #739. Freeze audited-main serial F4, opt-in concurrent-pivot F4 and,
later, integrated candidate-only/parallel routes as distinct configurations. Repeat the weak
Katsura cells named in M27's report with the same input identities. Include public MQ10, an
affordable next MQ rung and the largest bounded Cyclic control. Refusals are retained.

Extend existing examples/runners rather than replacing them. Profile symbolic preprocessing,
matrix construction, forward elimination, backward reduction, extraction, final interreduction
and scheduling/normalization overhead. Separate work-on diagnostics from timing controls.
Count coefficient products, row visits, logical entry traffic, peak mathematical entries,
reservations/capacities and attributable process RSS. Build a whole-route profile for basis,
operator construction, conversion including certification/retries/fallback, recovery and original
equation substitution. Use separate one-route processes for RSS; process high waters cannot be
subtracted to manufacture stage peaks.

#739 evaluates msolve at 1/2/4/8/16/32 workers; use 64 where useful. Groebner.jl, grobx,
groebner-rs and the remaining relevant roster get only supported configurations, with randomized
versus exact backends explicit. Record actual active workers/CPU and affinity, not just requested
threads. Capability refusals count; silently relabeling a serial engine multicore does not.
Deliver current baseline and scaling reports with 8- and 16-worker targets, matched-core and
best-under-common-core-budget tables. State every timer boundary and which numbers cannot compare.

Compute workload/revision-specific `S(p)=T(1)/T(p)`, `E(p)=S(p)/p`, and Amdahl bounds
`1/((1-f)+f/p)` only for an identified parallelizable elapsed fraction `f`. Re-establish `f`
after selection. Changed pivot work is valid task acceleration, not equal-work strong scaling.

### 7.2 M28-A — necessary backward output, then safe adoption

Owners: #269/#747 research, #749 adoption. Review the existing proof: candidate eligibility is
fixed by leading columns after forward elimination; reduce every selected row exactly against
later immutable echelon pivots, without materializing unneeded inherited reduced tails. Unique
candidate RREF rows imply identical polynomials and subsequent F4 trajectory under the serial
schedule. Rank or pivot agreement alone is insufficient. Evaluate dependency closure and lazy
substitution costs using the retained products, materializations, scans and final-interreduction
cost; do not replace the proof with analogy to msolve.

#749 owns a private F4 output contract, keeping public full-matrix RREF unchanged. Test supported
orders/backends, empty/partial candidate sets, rank deficiency, characteristic two, extension,
64-bit and 254-bit fields before integration. Reconcile conservative retained-original/temporary
copy reservations with mathematical peaks, sparse capacities and byte ledgers. A previously
supported call must preserve admission/error semantics or have a tested full-RREF fallback.
Cancellation, panic/refusal/retry and allocator-capacity safeguards remain required.

Adopt only with exact independent complete-basis agreement, material MQ10 product reduction,
repeatable complete F4 improvement, RSS accounting and no material Katsura/Cyclic/public controls
regression. Preserve M27 batch-tail and final-matrix behavior. Rejection or deferral must name the
failed contract/cost gate; the already rejected all-target replacement is not a fallback proposal.

### 7.3 M28-B — adaptive production parallel F4

Owner: [#752](https://github.com/mfaulk/zeebra/issues/752), coordinated with #273. Extend #728's safe publication, do not implement
parallel pivot discovery again. Begin design review alongside A; production edits follow #749's
output/statistics contract and the baseline targets. Confirm the four complete 2×2 configurations
on the integrated revision, retaining serial-forward and concurrent-one-worker controls.

Calibrate a dispatch gate from actual lower-row work, width/density, scratch budget and worker
count; validate on held-out public controls rather than fitting only MQ10. Static/dynamic or a
bounded scheduler is chosen from work/skew evidence. Reuse #592 dispatch measurements; integrate
a persistent runtime only if constructor, warm dispatch, retention/nesting and complete-task
measurements justify it. Declare a supported serial fallback and avoid oversubscription.

Retain immutable published pivots, per-worker scratch and `Send + Sync` at the dispatch boundary.
Use standard safe synchronization; workers join/drain after cancellation, budget refusal or panic.
No partial basis becomes success and deterministic error guarantees remain explicit. Charge
simultaneous publication losers, dense scratch, pivot/index storage and stacks appropriately.

Evaluate 1/2/4/8/16/32/64 physical workers where useful; stop high-worker arms if the declared
cost/resource gate rules them out. Unconditional dispatch is already rejected. Require held-out
small controls within a predeclared 5% material-regression gate (noise assessed using repeated
matched runs), named large-task improvements and explicit memory/concurrency limits before adoption.
A more expensive runtime must beat the simpler bounded route on complete calls.

**B2, #729:** first inspect #728's failed claims, products after lost claims, worker skew and
publication/scheduling clocks. Those summed worker clocks are not elapsed serial fractions;
retry-attributed products are not all provably redundant. Recompute opportunity after A. If no
material recoverable full-task share exists, reject/defer without a queue prototype. Otherwise
compare one bounded waiting-row design against the existing strategy. Do not ship two schedulers
without distinct winning workloads. **#730:** only price threading the necessary residual backward
work after A; avoid parallelizing work already removed.

### 7.4 M28-C — arithmetic, layout and symbolic source work

Owners: #268 storage, #270 arithmetic, #715 reuse/SIMD, [#753](https://github.com/mfaulk/zeebra/issues/753) live symbolic policy.
Rank candidate savings against post-A full-task time and RSS before selecting at most one kernel
prototype at a time. Existing Adaptive dense target/sparse source machinery, shipped prefix merge
and rejected delayed pilot are starting points. An invented generic matrix representation is not
itself a deliverable.

Investigate narrower indices/entries with checked overflow/fallback; dense temporary targets with
sparse sources; widened delayed modular reduction with a proved field-specific accumulation bound;
multirow source reuse; then SIMD against an equal-work scalar multirow control. Compare equal
field widths/layouts when isolating arithmetic, and equal arithmetic when isolating storage. Use
31-bit and 64-bit fields; treat BN254 separately. Count conversion, packing, workspace and index
costs. Physical bandwidth remains uncertain where counters are unavailable; logical traffic is
not a substitute.

[#753](https://github.com/mfaulk/zeebra/issues/753) measures live original/ordered × duplicate/unique-multiple policies, including
changed pair trajectories, on complete bases. #742's replay is a feasibility prior, not an
end-to-end result. Preserve pair relations, column/covered-lead invariants, order/field support
and refusal contracts. Compare against the production route chosen by A and isolate interaction
with concurrency before adopting both. No production rewrite of general polynomial storage or
caller-visible normal-form divisor order is authorized by a single MQ10 result.

Ship only a complete-task benefit or a demonstrated fixed-budget memory-frontier advantage,
with controls and correctness. Predeclare time/RSS/regression gates and implementation maintenance
cost; an attractive arithmetic microbenchmark with a complete-solve regression is rejected.

### 7.5 M28-D — hard wide-field competitive frontier

Owner: #738/#746, scaling through #739. Primary fields: `2^64-353` and Goldilocks
`2^64-2^32+1`; 31-bit controls connect the competitive baseline. BN254 scalar is a secondary
capability target. The current external characteristic interchange is u64-limited: no invented
254-bit cross-engine ratio. Reassess capabilities at the pinned campaign revision.

Freeze unplanted dense random MQ, Katsura, zero-dimensional Cyclic and selected public Eco,
Noonburg/Reimer rungs. Keep source/license and canonical full input digests; include unfavorable
families and all attempted rungs. For each family/field record:

| Rung | Required meaning |
|---|---|
| Small | Fast complete independent correctness control; no competitive victory |
| Competitive | Fastest capable comparand clears startup/noise gates, preferably at least one second |
| Stress | Bounded attempt approaching practical time/memory limits |
| Frontier | Explicit next fixed-budget target whose verified completion would extend reach |

Rung sizes come from #738's bounded ladder, not arbitrary variable-count promises. A failed search
for an above-floor competitive rung must name the capabilities/resource barriers. Random planted
solutions are controls, not evidence of hard MQ. Positive-dimensional/unit-ideal outcomes must
be identified before interpreting runtime as the intended zero-dimensional task.

Prioritize capable grobx, Groebner.jl and groebner-rs at 64 bits; check Singular, msolve, Sagebrush,
Giac and Sylvester capabilities rather than extrapolating small-field support. Magma is optional
only with available licensed access and reproducible local measurements. Unsupported fields are
capability outcomes. Multiworker comparisons use matched cores and best observed under a common
physical-core budget, with exact/randomized verification cost explicit.

Claim a lead only after repeat runs with matching field, order, input, task, concurrency and
compiler/ISA provenance, full wall/CPU/RSS, above-floor separation and independent mathematical
verification. The corpus investigation can close without a win if its negative result is precise.

### 7.6 M28-E — conditional sparse/block Krylov

Owners: #87 then #731; independent of the F4 source interface, optional for M28. Existing
[certified scalar Wiedemann](research/certified-wiedemann.md) supplies the scalar reference and
independent quotient-algebra certificate. Do not replace it with an uncertified recurrence.

Use affordable pinned quotient dimensions and actual operator density/cache footprint. #87 prices
batched sparse matrix-block products, storage formats and data reuse. #731 studies shorter Krylov
depth versus block reconstruction, polynomial-matrix cost, rank deficiency, non-shape position,
retries, certification and fallback. Compare complete conversion including operator construction,
not matvec alone; track peak RSS and retained scratch. First bound the fraction of full conversion
that block application can save. Stop before a polynomial-matrix subsystem if that bound or pilot
cost fails the declared economic gate. A certified useful pilot can justify a later milestone;
production block integration is not required here. [XL history](research/xl-block-wiedemann.md)
does not make block Wiedemann a replacement for F4 echelonization.

### 7.7 M28-I — integration, scoreboards and report

Owner: [#754](https://github.com/mfaulk/zeebra/issues/754). Maintain issue/decision matrix, ensure successful branches compose,
regenerate final comparisons from retained accepted records and score every original criterion
in §11. Preserve failed, refused, unsupported and deferred outcomes. Use existing generated
scoreboards, not manually curated winner tables. Review README, guides, changed source comments,
commands, CI references, source and artifact identities, and the M28 tracker before closure.
Do not close shared research issues simply because M28 has enough evidence to finish.

## 8. Dependencies, execution order and development concurrency

```text
#751 + #739 (current baseline and external targets)
          |                              |
#269/#747 -> #749 (A adoption)      #738/#746 (D corpus)
          |                              |
#752 (B adaptive integration)             |
          |                              |
          +------------- #754 -----------+

#268 / #270 / #715: read/rank alongside A; shared kernel edits after A
#753: isolated design now; live F4 edits after A interface stabilizes
#87 -> #731: optional independent conversion research; never blocks core F4 closure
```

Start immediately: [#751](https://github.com/mfaulk/zeebra/issues/751), #739, #738 (continue existing #746 owner), and review #747
before starting #749. A fifth independent assignment is #268's read-only post-selection memory
model, coordinated with the adoption owner. [#752](https://github.com/mfaulk/zeebra/issues/752) design can proceed, but production
implementation waits for A and baseline targets. Do not assign #269's live work to another agent.

| Source/interface | Single owner at a time | Safe concurrent work |
|---|---|---|
| `src/linalg/sparse/elimination.rs`, `row.rs`, `src/linalg/dense/accumulator.rs`, `src/linalg/pivots.rs` | A (#749) first, then B or one C implementation | Mathematical review, external source study, offline analysis |
| `src/grobner/f4/structured.rs`, `reduction.rs` | A output contract, then B; symbolic owner rebases after it | Corpus design with existing public interfaces |
| `src/grobner/f4/options.rs`, `statistics.rs`, research-work counters | A owns selected-output accounting; B owns subsequent concurrency policy | Baseline owner proposes required counters before edits; no competing schema |
| `src/grobner/f4/symbolic.rs`, pair/macaulay interfaces | Symbolic-policy owner after A contract | Ordering/dedup proof and fixture specification |
| `src/grobner/fglm/{multiplication,wiedemann,conversion}.rs` | E, coordinating #273 for routing | Independent of F4 code changes |
| Existing external adapters, competitive records and renderers | #739 scaling; #738 catalog; I integration schema review | Disjoint source studies; coordinate shared runner changes |

Use issue leases via `scripts/agent/zb-claim.sh`; one real worktree/branch and private
`/buildcache/cargo-target/zeebra-<issue>` plus `TMPDIR` per writer. Never let two agents redesign
row ownership or pivot publication independently. No shared checkout writers. Source reading,
proof work and disjoint harness tests can run concurrently; benchmark campaigns on the 5995WX
are serialized through `tools/benchlock.sh`. Builds/tests must not contaminate timed windows.

## 9. Measurement protocol and reproducibility

Follow [external comparison protocol](research/external-comparison-protocol.md),
[external engines](guide/external-engines.md) and [benchmarking](guide/benchmarking.md).
Reuse existing runners, work observers, matrix corpus and independent verification. #748's
[native matrix archives/SMS export](guide/f4-matrix-files.md) permit offline replay; capture or
replay timing is not a complete solve and large opt-in captures are not part of this planning task.

Primary host: AMD Ryzen Threadripper PRO 5995WX, 64 physical/128 logical cores, 512 GB installed
memory. Record observed topology, actual usable memory and affinity mask; choose one logical CPU
per physical core. Worker sweep is 1/2/4/8/16/32/64; 128 is a separately named optional SMT cohort.
Record requested and observed active concurrency, nested engine/BLAS/OpenMP settings and CPU time.
No CLI thread count alone proves multicore use.

Pin source commit, dirty/overlay identities, executable hash, compiler, dependency lock, allocator,
release/LTO/codegen options and effective ISA flags. Rust and external builds need matched effective
architecture settings, not merely the same environment variable. Private build/scratch directories
live on `/buildcache`; build/test before the measurement lock and retain load/compiler gates.

Each accepted or refused attempt records input's full canonical digest, field/order/task, exact
algorithm configuration, requested/observed workers, source/executable identities, affinity,
complete process wall/CPU and RSS, applicable stages and counters, budget/termination outcome,
output identity and verification status. Missing/unavailable counters say so. Use at least five
interleaved fresh-process repetitions for adoption, ranges plus medians and instrumentation-off
controls; predeclare thresholds and stopping rules. Preserve interrupted/excluded evidence and
reasons separately. No post-hoc repeated campaign to choose a favorable sample.

| Quantity | Permitted comparison |
|---|---|
| Engine-internal F4 / Julia warmed solve | Same explicitly matched internal boundary; not a process-wall ratio |
| Spawn-to-reap process wall and CPU | Whole process including startup/output; apply per-engine startup floor |
| Complete solve including certification/recovery | Same delivered mathematical object and charged verification/fallback |
| Process RSS high water | Separate attributable one-route process; not sum/difference of stage high waters |
| Work counters / modeled entry traffic | Explain algorithm/traversal work; not physical bandwidth or elapsed fractions |
| Refusal time / unsupported engine | Resource/capability outcome; no successful-computation speedup |

Retain current F4 live-entry and byte budgets. Start bounded pilots using the existing
60-second/2-GiB child policy where suitable and the instrument's existing process-tree watchdog
(often 185 seconds); whole-route pilots retain M27 #457's specific limits. State scope explicitly.
Lifting an entry allowance does not bound RSS. Larger frontier attempts require a recorded time,
memory, retry and output-storage estimate and decision before execution; no new blanket 512-GB
authorization follows from available hardware. Use `tools/rss-guard.sh` and external process-tree
supervision, cancellation and terminal-cause logging. Do not acquire the benchmark lock to build.

Require coefficient-for-coefficient complete reduced-basis equality against an independently
verified reference where available. For new inputs retain exact two-inclusion/cofactor evidence
or an appropriate independent exact certificate; simple agreement on rank, dimension, leading
terms or two randomized outputs is insufficient. Independently substitute recovered points into
original equations. Record basis, certified reduced basis, eliminant, recovered point, verified
point and incomplete resource-limited computation as distinct achievements. Include certification
cost in exact-mode adoption decisions even when separately timed for attribution.

## 10. Performance hypotheses and falsification

| Hypothesis | Supporting evidence required | Refutation or limiting result |
|---|---|---|
| Selected backward work materially reduces F4 cost | #747 proof survives #749 contracts; products and full-call time fall without final debt | Backend/budget correctness failure, shifted interreduction cost, or no matched end-to-end benefit |
| Coefficient updates can narrow residual per-product cost | Equal-work/layout/width controls, fewer cycles/update and faster complete tasks | Conversion/scratch/control overhead erases gains; original 4.8x mixture disappears after A |
| Concurrent forward becomes more valuable after selection | Integrated 2×2, same-algorithm p=1 control, held-out adaptive crossover, full-task curves | Serial stages, retries or dispatch dominate; small-case gate cannot validate |
| Hard wide fields offer competitive differentiation | Above-floor task-equivalent repeated matched-core result with exact independent checking | Capable comparand wins, no hard rung completes or verification costs dominate |
| Block Krylov can improve large sparse conversion | Operator application dominates, batched reuse wins and complete certified conversion improves | Reconstruction/certification/fallback dominates or block memory exceeds the fixed budget |

## 11. Acceptance criteria

The report labels each item **measured**, **implemented**, **certified**, **refused**, **deferred**,
or **not met**, with evidence. These statuses are not interchangeable. A deferred optional backend
does not count as implemented. Historical prerequisites alone do not earn new implementation claims.

### Minimum — completed evidence and decision gates

1. Current-default and complete-route MQ/Katsura profiles retained, weak Katsura repeated or its
   precise resource/capability blocker documented; #739 curves and 8/16-worker targets recorded,
   or each unavailable comparand/configuration has an explicit capability blocker.
2. Necessary-backward correctness analysis and work/materialization model reviewed, with a named
   adopt/reject/defer decision. #747 may satisfy research evidence after review; #749's shipping
   status is reported separately, never implied by that verdict.
3. Existing concurrent prototype compared with pinned current default and selected backward policy
   through four complete configurations; existing #747 evidence is identified and production
   replication or an explicit integration blocker is reported. No multiplied speedup estimates.
4. Hard wide-field ladder with full input identities and independent verification, or explicit
   retained resource/capability refusals per attempted rung. A fabricated win is not required.
5. Arithmetic/layout/source-work and queue/residual-threading alternatives ranked against current
   measured opportunity. Each has an adopt/reject/defer gate; no implementation required merely
   to reject an uneconomical direction. E receives an optional go/no-go decision.
6. Raw artifacts, verification, source/executable identities and rejected/refused attempts retained.
7. I report scores every criterion here and the five hypotheses, with regenerated truthful
   comparisons, README/guide consistency, remaining gaps and a next-milestone recommendation.
8. Negative results, regressions, unsupported tasks and uncertified outcomes remain visible.

Minimum requires completed research decisions, not every shared epic closed. Deferred production
adoption must state the binding correctness, budget or economic obstacle and reopening condition;
an unexplained postponed experiment is not a completed gate.

### Strong — Minimum plus a substantial full-task achievement

At least one newly integrated and independently verified result:

- At least 2x complete F4 time improvement on a named nontrivial MQ input against a pinned
  current-default serial control, same machine/input and matched measurement boundaries.
- Material reduction of total coefficient operations with a resolved end-to-end gain and
  acceptable measured memory, including final interreduction and verification costs.
- Production adaptive parallel F4 with realistic large-task gains and validated small controls.
- Measurable narrowing of the gap to a leading capable comparand at equivalent concurrency,
  clear of startup/noise, including exact-output certification cost.
- A larger independently verified fixed-budget completion where the pinned control refused.

The pre-integration #747 experiment supports investing; it does not by itself meet this tier.
Declare the numerical gates before measuring. Default starting gates for a new adoption pilot are
at least 10% named full-task gain, no more than 5% material control regression and at most 1.25x
RSS unless a separately justified memory/frontier tradeoff is predeclared. These are decisions,
not performance predictions. If two bounded designs fail the complete-task or maintenance gate,
stop that implementation line, retain the evidence, and close at Minimum when all its gates hold.
Do not chase Strong by extending budgets until a favorable result appears.

### Stretch — demonstrated competitive advance

Any one certified and reproducible achievement: a speed lead over the strongest capable open-source
comparand on a substantial hard wide-prime-field task at matched concurrency; a meaningful
multicore lead on a representative Gröbner task; a new fixed-budget completed instance; improved
resource scaling enabling substantially larger systems; or a new parallel/block algebra algorithm
winning on a complete constrained task. State exact scope, e.g. the pinned input/field/task and
16-worker budget. No universal “fastest Gröbner solver” claim, kernel-only win or faster refusal.

## 12. Risks, uncertainties and expected cost

| Risk / uncertainty | Response and cost gate |
|---|---|
| In-flight #747/#746 change before merge | Keep audit snapshot explicit; review final diffs/provenance and update status at integration |
| Candidate-only budget/accounting stricter than full route | #749 reservations/fallback tests before default; preserve admission and error contracts |
| Arithmetic opportunity shrinks after work removal | Reprofile first; #270 pilot already has a negative full-solve result |
| Pivot order changes work and memory | Charge retries/work/scratch; task acceleration separate from equal-work scaling |
| Adaptive threshold overfits MQ10 | Hold out public controls/fields; serial fallback; no global default from one cell |
| Hard 64-bit instances refuse before a useful timing | Keep ladder and refusals; resource model before larger rung; no unsupported-engine ratio |
| 254-bit comparisons lack adapter/engine support | Capability-only result; no representation-based performance claim |
| Independent verification is expensive | Retain exact certificates, charge their time/memory and bound output storage |
| Physical controller counters unavailable | Name limitation; do not infer DRAM saturation from modeled traffic/read fills |
| Shared files/workstation cause contamination | Single interface owner, worktrees/private build dirs, serialized measurement and compiler gates |
| Block reconstruction becomes a subsystem | #87/full-conversion opportunity gate before #731 expands scope |

Planning estimates, not commitments: baseline/corpus reconciliation and bounded profiling are
medium effort; #749 contract/budget adoption is medium to high; adaptive parallel integration is
high; one arithmetic/layout or symbolic pilot is medium; full block reconstruction is high and
conditional. The scarce resource is serialized measurement plus independent verification, not
agent count. Every campaign issue declares cell counts, repetitions and worst-case aggregate
wall/output cost before launch. Begin with controls and one bounded competitive rung, review
the gate, then authorize the wider sweep; this plan supplies no expensive campaign authorization.

## 13. Deferred alternatives and reopening conditions

- GPU F4: #69/#86/#225 remain research-gated. Need an identified real matrix, CPU baseline,
  arithmetic-intensity/transfer model, device memory budget and a full-task opportunity first.
- Out-of-core/NVMe (#88): reopen only after necessary work and compact storage fail a demonstrated
  resource barrier and an I/O model is competitive; no hardware purchases scheduled.
- Generic multicore NTT (#732): caller-level transform share and dispatch crossover required;
  independent butterflies alone do not justify a backend.
- GF(2)/GF(2^e), #272: separate bit-packed algorithm family; integrate only for a named competitive
  benchmark whose full-route profile makes it a primary M28 opportunity.
- Signature F4, #716: retain bounded feasibility under #256, not a new signature implementation
  or reopening of closed #223. Need measured avoided work and affordable exact checking.
- Randomized row skipping: do not weaken exactness; charge independent span/ideal certification
  and deterministic fallback before a new policy proposal.
- Distributed cryptanalysis, specialization campaigns and challenge orchestration remain in
  `mfaulk/cryptanalysis`; Zeebra contributes reusable algebraic primitives only.
- General runtime, public polynomial representation and multiple production schedulers: require
  a successful caller and separate full-task benefit/maintenance justification.

## 14. Research references and licensing boundaries

Research papers explain mechanisms, not predicted speedups on this machine. References checked
2026-11-13; implementation links are immutable research pins, not claims of latest upstream HEAD.
New campaigns must pin their actual provisioned versions and reevaluate supported code paths.

1. Faugère–Lachartre, *Parallel Gaussian Elimination for Gröbner Bases Computations in Finite
   Fields*, PASCO 2010, pp. 89–97, in the
   [proceedings](https://www.csd.uwo.ca/~mmorenom/Publications/pasco2010.pdf): structured block
   elimination. Zeebra already has a reducer-first triangular split; an identity-first split
   was measured and rejected. Do not present the principle as a missing implementation.
2. Monagan–Pearce, [*A Compact Parallel Implementation of F4*](https://www.cecm.sfu.ca/CAG/papers/RomanPasco2015.pdf),
   PASCO 2015 §2.2: private work rows and sparse pivot installation. Supports B's mechanism,
   not a forecast of Zeebra scaling.
3. Boyer et al., [*GBLA — Gröbner Basis Linear Algebra Package*](https://arxiv.org/abs/1602.06097),
   2016, and [matrix/library site](https://hpac.imag.fr/gbla/): multiline/block storage and
   operation scheduling. #729 must distinguish scheduler benefit from storage/arithmetic.
4. Faugère–Mou, [*Sparse FGLM Algorithms*](https://arxiv.org/abs/1304.1238): sparse multiplication
   operators, recurrence and shape-position limits; see the existing certified-scalar report.
5. Coppersmith, [*Solving Homogeneous Linear Equations over GF(2) via Block Wiedemann Algorithm*](https://doi.org/10.1090/S0025-5718-1994-1192970-7),
   Math. Comp. 62 (1994), 333–350: block sequences/reconstruction motivation. Publisher PDF was
   access-blocked during planning; bibliographic/algorithm context also retained in #731 and
   the existing XL research. This is not a new prime-field performance measurement.
6. msolve [common F4 code at `c5a41f0a`](https://github.com/algebraic-solving/msolve/blob/c5a41f0a842c126d669676c041bd3fc4675cf7e7/src/neogb/la_ff_common.c):
   row scheduling, private dense targets, pivot publication and selected new-pivot finishing.
   #737 instead instruments provisioned 0.11.0 (archive hash in its report); keep the pins distinct.
7. Groebner.jl [threaded backend at `509ed7c3`](https://github.com/sumiya11/Groebner.jl/blob/509ed7c38338608c25c9c86713ed7a57bb78f5ba/src/f4/linalg/backend_threaded.jl):
   reservation/readiness publication and task chunks. Its randomized backend and dispatch gates
   are separate policies, not measured Zeebra thresholds.
8. grobx [multirow tests at `1854835d`](https://github.com/code1-de/grobx/blob/1854835dbc25f24dc9a9ba017024d5030e99da1c/src/band_tests.rs)
   and [Zeebra trajectory report](research/grobx-trajectory.md): source reuse, scalar-equivalent
   controls and randomized-versus-certified work. #715 isolates reuse before SIMD.
9. MIT Rust comparand [elimination at `c3e1d63`](https://github.com/sdiehl/groebner/blob/c3e1d630fba9b2155a4c389d9022f13e0ba09218/src/f4/eliminate.rs):
   safe owned-pivot `OnceLock` reference; existing subprocess driver remains the measurement path.
10. [Magma Gröbner handbook](https://magma.maths.usyd.edu.au/magma/handbook/text/1314): direct versus
    conversion strategies and exact reduced-basis contracts. Documentation access does not imply
    a licensed benchmark installation or source access (#439).

GPL/LGPL engines are algorithmic references only: independently implement in Zeebra's MIT core;
do not copy implementation code or bundle incompatible instrumentation. Preserve licensing and
fixture provenance. M4RI/M4RIE belong to #272's deferred characteristic-two investigation.
The [matrix corpus](research/f4-matrix-corpus.md), [worker pool](research/worker-pool.md),
[msolve attribution](research/msolve-gap.md), [symbolic attribution](research/symbolic-attribution.md),
[current profile](research/mq10-current-profile.md), [kernel report](research/elimination-kernels.md),
[Groebner.jl gap](research/groebner-jl-gap.md), [scalar certificate](research/certified-wiedemann.md)
and [XL history](research/xl-block-wiedemann.md) retain detailed local evidence and caveats.

## 15. Planned integration report and scoreboard requirements

Append an integration report at closure with a measurement/publication header and source snapshot.
Required tables: every §11 criterion scored; every issue's research/shipping disposition; every
§10 hypothesis supported/refuted/unresolved; per-task/current-default and comparand fixed-core
and common-budget curves; full-route stage/work/RSS decomposition; integrated 2×2; wide ladder
including refusals/capabilities; previous versus new fixed-budget frontier; maintenance/resource
cost and cost-model prediction error. Keep old reports and numerical controls traceable.

Use the existing non-measuring competitive renderer after accepted records are integrated:

```sh
cargo run --release --example competitive -- --write
```

Build before any measurement campaign; this command renders stored records and launches no solver
measurements. The old `scoreboard` example moved out with cryptanalysis in #668 and is absent
from this source tree; do not copy its historical render command into M28 instructions.
Review resulting diffs rather than changing generated Markdown by hand. A library
version table or generated board's `complete` row is not by itself independent certification.

## 16. Documentation and closeout checks

Before closing #750: reconcile plan/tracker/Project #7 and final source; audit README, guide paths,
commands, CI and changed source comments; record Red–Green evidence for behavior changes and
offline provenance/certificate checks. This planning PR changes documentation only, so no new
algorithm tests, source file headers or CI workflow are needed. Existing documentation/provenance
checks and link/path review validate it; implementation issues require focused Red–Green tests
and updates to existing CI. No solver benchmarks are used as documentation validation.

## 17. Recommended directions after M28

If A+B ship and forward work remains dominant, invest in the winning field-width/source-reuse
design, not the removed backward phase. If symbolic live policy wins across families, integrate
its measured selection rule through #273. If wide-field arithmetic dominates after work reduction,
fund a width-specific follow-up with exact overflow and full-task gates. If memory binds the next
verified rung, use #268's measured layout opportunity before out-of-core or hardware work.
If block application dominates certified conversion and E succeeds, plan a separate bounded block
reconstruction/integration milestone. If comparands still lead decisively, publish the exact gap
and algorithmic cause; defer uneconomical integration and select the next milestone from evidence.
