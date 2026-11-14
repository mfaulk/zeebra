# M28 current whole-route baseline (#751)

**Status:** instrumentation, four accepted pilot processes and a two-process native prefix retained; repeated baseline incomplete.
**Measured at:** `657344357a9cee9fb8d9c8409005f32ac950a2c4` (Rust instrumentation and profiling example);
controller `72c2a2c6` for the accepted pilot prefix; controller `807547b6` for the refused continuation.
**Production baseline:** `b9898c9a`, after candidate-only F4 #749/#757; the measurement changes
passive timing and the profiling example, not an algebra algorithm or solver default.
**Machine:** Threadripper PRO 5995WX, one physical-core affinity CPU 3, Rust 1.99.1,
release/fat LTO/one codegen unit/x86-64-v3/mold/system allocator. Complete source, binary,
Cargo/ISA configuration, toolchain and topology identities are retained in the raw archives.

This is an **incomplete investigation**, not a completed M28-0 acceptance claim. No single pilot
observation is promoted to a repeated current baseline, precise speedup or adoption decision.
The [protocol](../../research/m28-current-baseline/README.md),
[raw accepted prefix](../../research/m28-current-baseline/pilot.json.gz),
[refused continuation](../../research/m28-current-baseline/pilot-completed.json.gz) and
[native prefix](../../research/m28-current-baseline/native.json.gz) and
[derived summary](../../research/m28-current-baseline/summary.json) preserve the distinction.

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

## Pilot outcomes and environmental stops

The first lock window, 2026-11-13 19:21:43–19:21:54 America/New_York, accepted four processes.
Their pre/post compiler snapshots are empty. Before Katsura-11 could launch, an unrelated compiler
appeared; the driver retained the exact accepted prefix and refused the next cell. The sole
bounded continuation then refused before either remaining child for the same reason. The original
prefix and both compiler identities remain retained; no accepted sample was discarded or repeated.
A controller path-normalization defect caused a separate preflight failure before any child;
its log and Red–Green regression are retained too.

The following are **one accepted pilot per cell**, not medians or comparative measurements.
All source bases match independently verified complete reduced bases coefficient for coefficient.

| Input / prime | Process ms | F4 call ms | Forward ms | Backward ms | Conversion ms | Recovery ms | Self RSS MiB | Outcome |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| mq-random-10 / 32003 | 1615.844 | 1276.425 | 1096.150 | 43.517 | 279.738 | 0.712 | 49.42 | no-base-field-point |
| cyclic-5 / 32003 | 8.159 | 0.639 | 0.107 | 0.031 | 0.379 | 0.035 | 5.79 | no-base-field-point |
| mq-random-10 / 2147483647 | 1908.830 | 1446.367 | 1263.499 | 48.337 | 382.823 | 18.745 | 51.71 | verified-point |
| cyclic-5 / 2147483647 | 8.090 | 0.652 | 0.128 | 0.024 | 0.454 | 0.109 | 6.02 | no-base-field-point |

MQ10 has quotient dimension 354 at both primes, not 354 base-field points. Adaptive FGLM takes
Classical with `DenseOperator`, with zero scalar attempts; Cyclic-5 has dimension 70 and takes
Classical with `SmallQuotient`. No zero-valued scalar clock is interpreted as a fast certificate.
The M31 MQ point is independently substituted into all original generators in Python as well
as Rust. The other outcomes report no base-field point; exact source-basis checking is distinct
from an independent proof of that root-search outcome.

The two pilot tail cells—Katsura-11/M31 basis-only and MQ10/GF(32003) direct lex—remain
**unattempted**. Native measurements must not be silently counted as completing that pilot.
The exact frozen Katsura identity is
`03bf44d5d614a21cc8f56462aa873b7961641a2341892e3b2ef52b6cfec86a13`.
Its 537-element independent Singular reference is reused from #739 with retained archive hash
`d52ca65cbdc2a088e42da3faeb58305cbfa614dc2e6740de09fd2b6d13c133c1`;
no redundant external oracle campaign is run.

## Repeated native baseline and post-selection model

The native window ran 2026-11-13 19:36:12–19:36:21 America/New_York. It accepted exactly two
fresh processes: repetition 0, MQ10/GF(32003), stage-off and stage-on. Both source bases verify
exactly, both report no base-field point, and their pre/post compiler snapshots are empty. A new
unrelated compiler appeared before the M31 cell; the driver retained its identities and stopped.
The archive preserves the exact **2/75 prefix**, leaving 73 cells unattempted. No native retry or
resumption is authorized. Its paired observations cannot establish clock overhead or a repeated
performance estimate. Pilot and native observations are never pooled into five-run medians.

There are six distinct accepted solver processes across the two cohorts; the pilot continuation
copies its original four accepted records unchanged and adds no new measurement. The external
compiler workload is the binding measurement blocker. #751 stays open and its PR stays draft.

Pending: five interleaved stage-off/on fresh-process repetitions of MQ10, Katsura-6 and Cyclic-5
at both primes; five separate work diagnostics at each MQ prime; five staged Katsura-11/M31
basis-only repetitions. The exact 75-process plan has a 900-second aggregate hard cap, 60-second/
2-GiB child caps limited by remaining aggregate time, and 256-MiB cumulative output allowance.
There is no authorized automatic native retry or resumption. Compiler/load refusals stop the grid
and preserve the prefix. Work diagnostics never join native timing distributions.

The offline model computes each eligible-stage ceiling from that attempt's own full-route duration
`T` and stage duration `S`: `T/(T-S)`. It neither divides unrelated medians nor assigns historical
backward fractions to production clocks. Pilot forward work is the largest observed term, with
operator construction also material, but the repeated grid and perturbation controls are required
before ranking investments or making an adaptive dispatch decision. No current whole-route
wide-field or larger-frontier result is supplied by the two narrow-field inputs.

Katsura's M27 single-attempt 29,769.4-ms result at `3d0e3759` remains historical, with its original
600-second envelope and load caveats. The new five-attempt 60-second envelope must retain any
refusal; a faster stop cannot replace the old completed-basis timing or establish a speedup.

## External targets and decision status

[#739's report](comparand-scaling.md#targets-for-zeebra-at-8-and-16-workers) supplies independently
checked complete-basis process targets at fixed/common core budgets. At both ≤8 and ≤16 cores,
the named exact-mode MQ10 targets are 0.1168 s at GF(32003) and 0.1670 s at M31; M31 Katsura-11
is 0.7155 s. They are pinned observations from that separate cohort, not ratios to this pilot.
Raw randomized checked-answer targets and certificate/checking costs remain separate in that report.
A whole point-solving route must not be divided by a comparand's basis-only process wall.

| #751 deliverable | Current disposition |
|---|---|
| Current explicit whole-route instrument and timer-boundary audit | Implemented; focused tests and fixed-route functional control pass |
| Five-repetition native baseline and stage/work perturbation controls | 2/75 native prefix retained; five-repetition coverage and diagnostics incomplete |
| Weak Katsura repeat or exact resource/capability blocker | All five native Katsura attempts and both pilot tail cells unattempted after compiler refusals |
| Complete independent source bases and original-equation point checks | Four pilot and two native source bases validated; one M31 pilot point independently substituted |
| Post-selection Amdahl model and ranked remaining terms | Reproducible same-attempt model implemented; repeated verdict pending |
| External 8/16-worker targets | Linked to #739 with separate boundaries and exact/raw distinction |
| Adopt/reject/defer next investments | Pending repeated baseline; no policy selected from single pilot cells |

## Validation and reproduction

Tests preceded changes: missing refinement fields, absent route implementation and protocol/model
functions failed first; implementation then passed nine example/integration tests and 15 focused
Wiedemann tests across supported prime/binary/extension/wide fields. Protocol tests also cover
relative continuation paths, strict frozen-prefix identity, invalid clocks, missing cells, point
substitution and unexpected failure versus resource stop. Existing CI runs these offline checks.
The documentation and command audit covers the published partial result. Repeated-native acceptance remains open; no environmental stop is treated as completion of the issue.

Run the [documented build and offline commands](../../research/m28-current-baseline/README.md).
Archive replay rechecks exact full source coefficients and points without launching a solver.
It does not turn a retained status label into a new external certificate, or turn an interrupted
prefix into a complete campaign. README paths and commands have been checked against this source.
