# M28 current whole-route baseline (#751)

**Status:** instrumentation and 70/75 native responses retained; acceptance remains incomplete.
**Measured at:** Rust/example source `657344357a9cee9fb8d9c8409005f32ac950a2c4` (full source identity
is authoritative in the retained compilation provenance); initial native controller `9e2017806b95cbf88a904ad9213d324c2a1f5b0e`,
amended implementation `5e2bf3d8`, launch controller `9dafa38271b39f24496119df4b164e47175d1ba1`.
**Production baseline:** `b9898c9a`, after candidate-only F4 #749/#757. Production algorithms,
defaults and admission limits are unchanged. The profiling instrument adds explicit fixed-route
composition and passive clocks. A later import-only compilation correction is recorded below.

This report preserves **70 distinct accepted native processes and four distinct accepted pilot
processes**. Original-prefix archives are retained copies of those same records, not additional
measurements. The [protocol](../../research/m28-current-baseline/README.md),
[unchanged native archive](../../research/m28-current-baseline/native-completed.json.gz),
[derived summary](../../research/m28-current-baseline/summary.json) and
[external watchdog ledger](../../research/m28-current-baseline/native-amendment-stop.json)
keep the measured boundaries and missing cells explicit. PR #762 integrates the instruments and
retained partial evidence; #751 stays open until its remaining acceptance requirements are met.

## Timer and task audit

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

## Campaign identity, bounds and terminal cause

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

## Coverage and repeated whole-route results

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

## Work, current cost model and scoped decisions

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

## Acceptance, compilation correction and reproducibility

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
