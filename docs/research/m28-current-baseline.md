# M28 current whole-route baseline (#751)

**Status:** current cohort at `2ec9d3af` retained: pilot 6/6, native 61/75 (four complete repetitions
of every cell). The fifth native repetition is a precise deferral to #788. The historical 70/75 is unchanged.
**Measured at:** current cohort: Rust/example source and executable `2ec9d3af362b1331c8118c7ce0e0505a391b4b49`
(binary SHA-256 `cb7d3d475e586701…`), controllers `b241475b` (pilot) and `680a8a12` (native).
Historical cohort: Rust/example source `657344357a9cee9fb8d9c8409005f32ac950a2c4` (full source identity
is authoritative in the retained compilation provenance); initial native controller `9e2017806b95cbf88a904ad9213d324c2a1f5b0e`,
amended implementation `5e2bf3d8`, launch controller `9dafa38271b39f24496119df4b164e47175d1ba1`.
**Production baseline:** current cohort `2ec9d3af` (after #749/#757, #763, #772 and #774); historical
cohort `b9898c9a`. Production algorithms, defaults and admission limits are unchanged. The profiling
instrument adds explicit fixed-route composition and passive clocks. A later import-only
compilation correction to the historical build is recorded below.

The [current cohort](#current-cohort-at-2ec9d3af) below supersedes the historical figures as the
shipping baseline. The historical sections after it are retained unchanged as superseded evidence
and are never pooled with it. The historical cohort preserves **70 distinct accepted native processes
and four distinct accepted pilot processes**. Original-prefix archives are retained copies of those
same records, not additional measurements. The
[protocol](../../research/m28-current-baseline/README.md),
[unchanged native archive](../../research/m28-current-baseline/native-completed.json.gz),
[derived summary](../../research/m28-current-baseline/summary.json) and
[external watchdog ledger](../../research/m28-current-baseline/native-amendment-stop.json)
keep the measured boundaries and missing cells explicit.

## Current cohort at `2ec9d3af`

**Identity and budget.** Threadripper PRO 5995WX (`ZEEBRA_MACHINE=trpro-5995wx`), affinity CPU 3,
Rust 1.99.1 (`58cf8f9c3`), release/fat LTO/one codegen unit/x86-64-v3/mold/system allocator,
`research-work`, `CARGO_INCREMENTAL=0`, empty `RUSTC_WRAPPER`. The executable was copied out of the
Cargo target before launch. The
[protocol](../../research/m28-current-baseline/README.md#fresh-current-cohort-at-2ec9d3af-751-completion)
declared the budget before launch: the reviewed six-cell pilot (480 s aggregate) and 75-cell native
grid (900 s aggregate). Each child was capped at 60 s, 2 GiB and 128 MiB of output, with 256 MiB
per cohort. Every window ran under `tools/benchlock.sh` with the existing process-tree guard, zero
solver retries and no raised limit. The journaled controllers (#764/#770) published every window
without loss.

**Windows, in order.** Pilot windows 1 and 2 refused before any child and hold no sample. In
window 1, an idle `rust-analyzer` matched the old build gate. In window 2, another session's link
storm pushed the load to 1,242. Pilot window 3 accepted **6/6**. Native window 1 accepted **60/75**
and native window 2 accepted **61/75**. Each stopped at the unchanged one-minute load gate (4.48 and
4.09, with no build process running) immediately after repetition 3's Katsura-11 child. Every
accepted child is independently verified, and none failed. The protocol allows one further window
after a sampled refusal, so the native campaign stops here. Window 2 is the retained cohort
([archive](../../research/m28-current-baseline/current/native-2ec9d3af.json.gz),
SHA-256 `45860857b39ff48816eb843e371cc1e79be51b4923d4e75053265de6afec6fa1`). Window 1 is retained
outside the repository (SHA-256 `f6c432e5405a87d42df5b0f9dce2973d5632d55eecf40a8ea11ed64de4b45a09`,
68 MB) as an independent replicate. It is never pooled, and its MQ10 and Katsura-11 medians agree
with window 2 to within 1.3%. **Deferral:** the fifth repetition is missing for every cell except
the first MQ10/GF(32003) stage-off. [#788](https://github.com/mfaulk/zeebra/issues/788) owns a single
complete window. The figures below use four repetitions; none is presented as a five-repeat median.

**Pilot outcomes** ([archive](../../research/m28-current-baseline/current/pilot-2ec9d3af.json.gz)).
The direct-lex MQ10/GF(32003) control, which was never attempted in the historical cohort, is now
measured. Shipped lex F4 **refuses** at the 200,000-column Macaulay cap after 9,180 ms of process
wall, with a sampled process-tree peak of 1,086 MiB. The grevlex+FGLM route finishes in about 1.7 s
at 52 MiB. This is a measured negative for direct lex on this input, not a solver failure. The other
five pilot cells match the native medians below.

| MQ10 prime | Stage-off process ms | Stage-on process ms | Stage-on whole-route ms | Stage-on F4 ms | Stage-on conversion ms | Self RSS MiB | Outcome |
|---|---:|---:|---:|---:|---:|---:|---|
| 32003 | 1705.130 [1670.302,1774.574] (n=5) | 1703.760 [1668.377,1710.084] | 1689.078 | 1347.983 | 284.218 | 51.92 | no base-field point |
| 2147483647 | 1938.946 [1932.420,2028.635] | 1909.365 [1888.642,1938.668] | 1893.544 | 1425.318 | 402.793 | 53.36 | verified point |

Values are medians [min,max] over four repetitions unless marked. The stage-off and stage-on ranges
overlap at both primes, so no instrumentation overhead is resolved. MQ10's quotient dimension is
354. Adaptive conversion takes Classical with `DenseOperator` and makes zero scalar attempts. Every
M31 point is substituted into the original equations in Rust and again, independently, in Python.

| Stage-on median, ms | Symbolic | Construction | Forward | Backward | Extraction | Interreduction | Operators | Quotient | Dependence | Recovery | Checkpoint |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| MQ10 / 32003 | 87.894 | 18.581 | 1159.798 | 45.319 | 8.330 | 13.865 | 265.315 | 1.811 | 16.422 | 0.751 | 2.291 |
| MQ10 / M31 | 86.920 | 18.453 | 1239.308 | 51.541 | 8.149 | 12.790 | 300.544 | 1.746 | 99.842 | 19.021 | 2.963 |

The six F4 stage medians sum to 1333.8 and 1417.1 ms, against F4-call medians of 1348.0 and 1425.3 ms.
That leaves roughly 14 and 8 ms of unattributed scheduling, materialization and pair bookkeeping.
Stage medians are not an exact additive partition; the ceilings below use clocks from the same attempt.

| Control (stage-on, n=4) | Process ms | Whole-route ms | F4 ms | Conversion ms | Recovery ms | Self RSS MiB | Outcome |
|---|---:|---:|---:|---:|---:|---:|---|
| Katsura-6 / 32003 | 7.729 | 1.654 | 0.850 | 0.352 | 0.052 | 8.26 | verified point |
| Katsura-6 / M31 | 8.674 | 2.221 | 0.988 | 0.455 | 0.305 | 8.81 | verified point |
| Cyclic-5 / 32003 | 7.139 | 1.287 | 0.624 | 0.387 | 0.032 | 7.83 | no base-field point |
| Cyclic-5 / M31 | 7.725 | 1.582 | 0.705 | 0.456 | 0.099 | 8.44 | no base-field point |

Process startup dominates these small controls: about 7–9 ms of process wall against a whole route
under 2.3 ms. They establish correctness and keep refusals visible, but they show no parallel
opportunity.

**Weak Katsura-11/M31 repeat.** All four runs produced a complete reduced grevlex basis matching the
independent 537-element Singular basis. Process wall was **12,582.089 ms [12,513.433,12,669.965]**,
with an F4 call of 12,400.829 ms, 11,804 ms of CPU and 117.6 MiB of self RSS. The M27 single attempt
(29,769.4 ms at `3d0e3759`) and the historical four-repeat median (13,055.5 ms) keep their own
builds and windows, and no cross-cohort ratio is claimed.

**Work diagnostics** (four work-on processes per prime, kept separate from the timing figures). The
logical counts are exact and identical across repetitions (GF(32003) / M31):

- forward coefficient products: 585,166,982 / 585,195,178
- candidate-backward products: 23,566,622 / 23,567,093, from 250 candidate targets in 10 batches,
  with no full-RREF fallback
- peak sparse capacity: 1,066,897 / 1,066,920 entries; reserved: 1,119,821 / 1,119,843 entries
- workspace: 156,260 / 204,340 bytes

The archive also holds row visits, scans, gathers, per-batch capacities and trajectories. These are
logical models, not allocator counts or DRAM traffic. Conversion has no product-level counters, so
those are reported as unavailable rather than zero.

### Post-selection cost model and ranked serial terms

Shipping F4 already uses candidate-only backward finishing (#749), so this is the post-selection
model. For a stage of duration `S` inside the same attempt's whole route `T`, removing the stage
entirely bounds the speedup at `T/(T−S)`. Spreading it over `p` ideal workers gives `T/(T−S+S/p)`.

| Term (MQ10 stage-on, ranked) | Share of whole route, 32003 / M31 | Zero-cost ceiling | Ideal 8 / 16 workers on this term alone |
|---|---:|---:|---:|
| F4 forward elimination | 68.7% / 65.4% | 3.23x / 2.88x | 2.51x / 2.81x at 32003; 2.34x / 2.59x at M31 |
| FGLM multiplication operators | 15.7% / 15.9% | 1.19x / 1.19x | — |
| F4 symbolic preprocessing | 5.2% / 4.6% | 1.05x | — |
| FGLM dependence (classical) | 1.0% / 5.3% | 1.01x / 1.06x | — |
| F4 candidate backward | 2.7% / 2.7% | 1.028x / 1.028x | — |
| Construction, interreduction, extraction, unattributed F4 | 3.2% / 2.5% combined | <1.04x | — |
| Recovery, substitution, checkpoints | <1.2% | <1.02x | — |

The forward and backward ceilings are medians of per-attempt values from `summary.json`; the others
are computed from medians. After an ideal 8-worker forward phase, operators become 39% (32003) and
37% (M31) of the remaining whole route, and symbolic preprocessing becomes 13% and 11%.

Compare these with #739's ≤8- and ≤16-core complete-basis targets: 0.1168 s for MQ10 at GF(32003)
and 0.1670 s at M31. Even a free forward phase leaves F4 at about 188 and 186 ms, above both
targets. **Forward parallelism alone cannot meet #739's MQ10 targets.** Symbolic preprocessing and
candidate backward, about 133–138 ms together, would also have to shrink. This comparison sets F4-call
time against basis-only targets; it does not divide a whole-route wall by a basis wall.

### Decisions from the current cohort

| Investment | Decision | Measured basis |
|---|---|---|
| Concurrent forward / #752 | **Adopt as first priority** | 65–69% of the whole route, ceiling 2.9–3.2x; production adoption still needs #752's full-task, control and RSS gates |
| Residual backward threading / #730 | **Reject** for these serial MQ inputs | free removal is ≤1.028x; reopen only if forward work changes its fraction |
| Operator construction / #87, then #731 | **Keep as the second term; defer the prototype until after #752** | 265–301 ms: 16% now, 37–39% after an 8-worker forward phase |
| Live symbolic policy / #753 | **Defer to #753's matched controls** | 87–88 ms: 5% now, 11–13% after forward parallelism; also needed to reach #739's targets |
| Block/scalar reconstruction / #731 | **Defer** | adaptive selection made zero scalar attempts on these dense operators |
| Arithmetic/layout / #268, #270, #715 | **Defer to isolated matched controls** | coefficient products alone do not price elapsed gains |
| Direct lex route for MQ10 | **Reject** | refuses at the column cap after 9.2 s and 1.09 GiB; grevlex+FGLM completes in 1.7 s at 52 MiB |
| Study publication / #764 | **Done** (#765, #770) | journaled windows published 6, 60 and 61 cells without loss; the binding limit is now the shared-machine load gate (#788) |

## Historical cohort (superseded, retained unchanged)

The subsections below describe the earlier `65734435` cohort as it was published in PR #762. Their
statements of incompleteness refer to that cohort.

### Timer and task audit

The preexisting `mq10_profile` measured complete F4 calls and F4 symbolic/construction/elimination/
extraction/final-interreduction stages. Production elimination did not split forward from candidate
finishing. Existing FGLM statistics split quotient enumeration, operators and dependence, but the
scalar sequence, reconstruction and exact certificate shared that dependence timer. The ordinary
solve API exposes counters and outcomes but lacks these whole-route call walls.

The extended instrument composes the existing public APIs for one explicit fixed route:
`f4_reported` under grevlex, `fglm_to_lex_with_options` with default adaptive options, and
`solve_from_lex_basis` for the first base-field point. It performs the same dimension classification
before conversion. Direct mode uses lex F4 and the same recovery. These are explicit strategies,
not the automatic planner or enumeration of every point. Default F4 and FGLM options, resource
admission and failure behavior stay intact.

| Boundary | Included | Excluded / limitation |
|---|---|---|
| Process wall/CPU/RSS | Input construction/parsing, all selected stages, checkpoint and final output; supervisor startup | Independent known-basis comparison in controller; RSS is an attributable process high water |
| Complete F4 call | Shipped F4 and final interreduction; work-scope aggregation only in diagnostics | Input parsing and basis rendering |
| F4 forward/backward | Production forward elimination; candidate selection, allocation, finishing and full-RREF fallback | Refinements of elimination, never added twice; observer overrides leave production refinements zero |
| Conversion call | Public FGLM call including algebra drop and selected fallback | Record formatting; public API supplies no partial FGLM statistics on refusal |
| Quotient/operators/dependence | Existing FGLM stage clocks; dependence includes scalar retries before classical fallback | Inner stages do not cover the full conversion call by definition |
| Scalar sequence/reconstruction/certificate | All attempted scalar projections, including unsuccessful reconstruction and exact certificates | Refinements of dependence; zero when the adaptive screen makes no scalar attempt |
| Recovery call | Classification, root finding, first-point search and the solver's built-in original-equation checks | Separate additional substitution and output |
| Additional substitution | Every original equation evaluated at the returned point | Never executed when no point is returned |
| `whole_route_ns` | F4 through recovery, classification, source/lex rendering and checkpoints, extra substitution | Input parsing and final JSON encoding; `checkpoint_ns` measures direct emission, not its allocator/cache perturbation |

The whole timer is not the sum of inner clocks. Construction refinements, elimination refinements
and scalar refinements overlap their parent stages intentionally. No process high waters are
subtracted and no retained work ratio is called an elapsed share.

### Campaign identity, bounds and terminal cause

Machine: Threadripper PRO 5995WX, one physical-core affinity CPU 3, Rust 1.99.1,
release/fat LTO/one codegen unit/x86-64-v3/mold/system allocator. The raw archives retain executable,
Cargo/configuration, compiler and topology identities. Every accepted native response has empty
pre/post compiler snapshots and matches its complete independent source basis. Every recovered
point is independently substituted into the original equations in Python as well as Rust.

The original native window accepted two samples and stopped at a pre-child compiler gate. One
explicit amendment preserved that exact archive/refusal/prefix and appended only unexecuted cells.
Its 2026-11-13 19:59:29–20:14:10 America/New_York lock window ended with **status 124, end=budget**.
The original nine-second window is conservatively charged 20 seconds; the amended watchdog is
880 seconds under the original 900-second allowance. No limit was raised or accepted sample rerun.

The final amended archive is byte-for-byte preserved, SHA-256
`577344c995b23dbae63f4d7567a6c20db16813254e70f199ffda564e26240667`.
The controller exhausted aggregate time while handling publication; this is **not a solver timeout
or solver resource refusal**. About 100.591 seconds of durable accepted child process wall occurred
inside the amended 881-second logged window. The remaining controller elapsed includes independent
checking, JSON serialization, compression and other work; it is not an isolated gzip timing.
Full growing cohorts were rewritten after each response. Follow-up
[#764](https://github.com/mfaulk/zeebra/issues/764), linked under #751/#750 with Project #7 High
priority, scopes incremental/content-addressed durable publication. No implementation or new
measurement of that follow-up occurs here.

The watchdog interrupted controller publication outside a child guard, so the archive has no
in-band refusal marker. The separate hash-bound external-stop ledger binds its exact 70-record
prefix, lock log, launcher output and unaccepted row-70 files. That row's stdout/stderr/usage
survived, but complete process-wall/exit/guard metadata did not become durable; it supplies no
reconstructed timed sample. Offline replay attaches only the external termination fact in memory.
The measured archive is not rewritten. Total retained native scratch and both native archives
were 184,998,092 bytes, below the original 256-MiB cumulative output allowance.

### Coverage and repeated whole-route results

All 70 durable native attempts are independently source-basis verified. MQ10, Katsura-6 and
Cyclic-5/GF(32003) have five stage-off and five stage-on fresh-process repetitions. Cyclic-5/M31
has four of each; MQ work diagnostics have four per prime; Katsura-11/M31 has four staged
basis-only repetitions. Five cells remain unaccepted:

| Repetition | Input / prime | Route | Arm |
|---:|---|---|---|
| 4 | Cyclic-5 / 2147483647 | conversion/recovery | stage-off |
| 4 | Cyclic-5 / 2147483647 | conversion/recovery | stage-on |
| 4 | MQ10 / 32003 | conversion/recovery | work diagnostic |
| 4 | MQ10 / 2147483647 | conversion/recovery | work diagnostic |
| 4 | Katsura-11 / 2147483647 | reduced grevlex basis | stage-on |

The two original pilot tail cells (Katsura-11/M31 basis-only and MQ10/GF(32003) direct lex) remain
separate and unattempted; native Katsura observations do not complete that pilot. The pilot has
one independently checked M31 MQ point and three no-base-field-point outcomes. Its four accepted
samples are never pooled with native medians.

The following MQ10 process walls include input and output. Five repetitions per arm; milliseconds
are median [min,max]. Self RSS is the median process high water in MiB, without subtraction.

| Prime | Stage-off process ms | Stage-on process ms | Stage-on F4 ms | Stage-on conversion ms | Self RSS MiB | Outcome, both arms |
|---|---:|---:|---:|---:|---:|---|
| 32003 | 1656.653 [1626.338,1795.889] | 1647.553 [1629.409,1730.846] | 1313.947 | 282.771 | 49.25 | no base-field point |
| 2147483647 | 2061.503 [1939.301,2080.516] | 1973.159 [1927.020,2031.248] | 1509.652 | 385.983 | 51.67 | verified point |

Stage-off/on ranges overlap, including the M31 median difference; the data do not resolve a
positive clock-overhead estimate or justify crediting instrumentation with a gain. Work-on
observations remain separate diagnostics. MQ10's quotient dimension is 354 at both primes,
not 354 base-field points. Adaptive conversion takes Classical with `DenseOperator` and zero
scalar attempts; Cyclic-5/Katsura-6 take Classical with `SmallQuotient`. No scalar certificate
or block-Krylov performance result is inferred from zero scalar subphase clocks.

| MQ10 prime | Forward ms | Candidate backward ms | Operator construction ms | Classical dependence ms | Recovery ms | Direct checkpoint emission ms |
|---|---:|---:|---:|---:|---:|---:|
| 32003 | 1133.908 | 44.237 | 264.405 | 16.010 | 0.710 | 2.344 |
| 2147483647 | 1316.341 | 50.237 | 284.661 | 98.784 | 19.149 | 2.712 |

These are stage medians, not an additive partition of a process median. Direct checkpoint time
excludes construction of its JSON values and cannot bound cache/allocator perturbation. The
whole-route timer includes source/lex rendering and checkpoint work as documented.

The four retained Katsura-11/M31 processes all match the independent 537-element Singular basis.
Their process median is **13,055.548 ms [12,910.347,13,335.830]**, and F4-call median is
12,865.848 ms [12,709.734,13,142.479]. Self RSS spans 115.66–116.02 MiB. This repeats the old weak
single attempt four times, but the declared fifth repetition remains missing. The M27
29,769.4-ms observation at `3d0e3759` keeps its original 600-second envelope, flags and load
caveats; no cross-cohort speed ratio or new comparand lead is published.

### Work, cost model and scoped decisions

The four MQ work diagnostics per prime agree on exact logical counts:

| Prime | Forward products | Candidate backward products | Candidate targets | Full-RREF fallback batches | Candidate workspace bytes |
|---|---:|---:|---:|---:|---:|
| 32003 | 585,166,982 | 23,566,622 | 250 | 0 | 156,260 |
| 2147483647 | 585,195,178 | 23,567,093 | 250 | 0 | 204,340 |

The archives separately retain row visits, scans, gathers, capacities, conservative reservations,
mathematical peaks, and full stage/trajectory statistics. They are logical work/storage models,
not allocator counts, physical DRAM bandwidth or measured process RSS. Work scopes here cover F4;
conversion product-level counters are unavailable and are not silently reported as zero.

The model uses each staged attempt's own whole-route duration `T` and stage duration `S` for the
ideal zero-cost ceiling `T/(T-S)`. Median forward ceilings are 3.179x/3.010x; median candidate
backward ceilings are 1.028x/1.026x, with maximum backward ceilings below 1.029x. These are
analytical ceilings, not parallel forecasts. They use current production pass clocks, rather than
assigning historical work percentages to elapsed time.

| Investment | Scoped decision from this evidence |
|---|---|
| Concurrent forward / #752 | Prioritize a bounded matched-control experiment: forward remains the dominant named MQ term; production adoption still requires its full-task/control/memory gates |
| Residual backward scheduling / #730 | Reject as a 10% whole-route optimization on these serial MQ inputs: even free removal is below 3%; reopen only after integrated forward work changes its measured fraction |
| Operator construction / #87 and conversion planning | Keep as a measured secondary opportunity; 264–285 ms is material, with explicit construction ownership and a complete-route gate before a prototype |
| Block/scalar reconstruction / #731 | Defer investment from this cohort: adaptive selection rejects scalar on these dense operators; no successful scalar hot phase was measured |
| Arithmetic/layout/symbolic changes | Defer policy selection pending their isolated matched controls; coefficient products alone do not price elapsed gains |
| Study controller publication / #764 | Fix before any new long cohort: aggregate publication cost is the demonstrated completion blocker |

The separate [#739 targets](comparand-scaling.md#targets-for-zeebra-at-8-and-16-workers) remain
complete-basis process targets. Exact-mode ≤8/≤16-core MQ10 targets are 0.1168 s at GF(32003)
and 0.1670 s at M31; M31 Katsura-11 is 0.7155 s. Those pinned observations, raw randomized
checked-answer targets and certification costs keep their own boundaries. No whole-point-solving
wall is divided by a basis-only comparand wall. No current wide-field frontier measurement is
supplied by this narrow-prime campaign.

### Acceptance, compilation correction and reproducibility

| #751 deliverable | Disposition |
|---|---|
| Current complete-route MQ profile and timer audit | Implemented; five native timing repetitions per MQ arm, independently checked M31 points and explicit GF(32003) no-point outcomes |
| Complete declared 75-cell grid and all five-repeat controls | **Incomplete: 70/75**; Cyclic-5/M31 fifth pair, both fifth work diagnostics and fifth Katsura repetition are unaccepted |
| Weak Katsura repeat | Four independently checked completions retained; declared fifth absent; aggregate controller budget binds, not a solver refusal |
| Current post-selection cost model and ranked terms | Implemented for the named MQ route with same-attempt elapsed ceilings; broad production policies remain gated |
| External 8/16-worker targets | Linked to #739 with separate exact/raw/task boundaries |
| Raw outcomes, refusals and publication interruption | Retained without rewriting accepted prefixes or inventing lost clocks |
| Full milestone/issue acceptance | **Not complete**; #751 remains open; merging PR #762 does not complete the study |

CI found one default-feature compilation issue after measurement: `FiniteField` became used only
by the research observer, leaving its unconditional import unused under warnings-denied default
builds. The post-measurement correction moves only that import behind `research-work`. The exact
[patch](../../research/m28-current-baseline/provenance/post-measurement-import.patch), SHA-256
`0cfbcad370601a2739930238778f3631c8f051513e26cffceaec50525c6ee036`,
[checks/provenance](../../research/m28-current-baseline/provenance/post-measurement-import.json)
and 315-file frozen-source hash manifest retain this compilation-only exception. The measured
release executable and response archives are unchanged. Offline replay checks the retained
[source snapshot](../../research/m28-current-baseline/provenance/frozen-source.json.gz) against
the measured manifest and verifies the patch's exact before/after blobs; subsequent source changes
are independent of historical validation. Replay works without Git history or network access.
Both default/research example builds pass `cargo rustc ... -- -D warnings`.

Tests preceded behavior changes. Nine example/integration tests and 15 Wiedemann tests across
supported fields passed before measuring. Eight protocol and four model tests now cover exact
prefixes, one-time cumulative amendments, modular substitution, missing/invalid cells, terminal
causes and hash-bound external publication stops. Existing CI runs those checks and deterministic
archive/source/point replay. README commands, local paths and source documentation comments were
reviewed. No additional solver launch, retry or budget extension is authorized.

Run the [documented offline commands](../../research/m28-current-baseline/README.md).
The two originally unattempted pilot tail cells remain separate from this native evidence.

## #751 acceptance

| Deliverable | Disposition |
|---|---|
| Timer-boundary audit and table | Done (historical audit above; the boundaries are unchanged at `2ec9d3af`) |
| Repeated timing controls, separate work-on and overhead controls | Four fresh interleaved repetitions per cell at `2ec9d3af`, plus an off-repository replicate. The fifth repetition is a **precise deferral** (load-gate refusal after 60 and 61 verified cells) owned by #788 |
| F4 attribution: symbolic, construction, forward, backward, extraction, interreduction, residual | Done; residual is reported as unattributed F4-call time |
| Work counters: products, row visits, entries, reservations, capacities, workspace | Done for F4; conversion product counters are unavailable, and the report says so rather than recording zero |
| Whole route: basis, operators, conversion, recovery, substitution, wall/CPU/RSS | Done with one-route processes; the direct-lex refusal is visible and is not a failure |
| Independent exact checks | Every basis matches its independent reference; every point is substituted in Rust and Python |
| Repeated/superseded MQ10 and Katsura figures | Current figures above; historical figures are retained as superseded |
| Post-selection Amdahl model and ranked serial terms | Done |
| Link to #739 targets without duplicating its campaign | Done |
| Adopt/reject/defer each next investment | Done (decision table) |

The historical pilot's two tail cells are now superseded by the complete current pilot. #751's
gates are met by measurement or by a named, precise deferral (#788).
