# External worker scaling and the target for parallel F4 (#739)

**Measurement sources:** native prefix controller `d7d2bc8f043eead4add57e03d6d6b835c2646a4c`,
controller-only continuation `2f661626` (full identities in the retained metadata),
AMD Threadripper PRO 5995WX, one logical CPU per physical core, requested workers
1/2/4/8/16/32. Inputs come from `competitive_sweep` built at
`e131a0829a94d9d4bfeff1bc2404c56f2a175e1e` and the merged #738 wide corpus.
The debug exporter only constructs inputs, outside measured regions. Measured native engines
are optimized executables; executable/build/source hashes, commands and affinity are retained.

Retained evidence and protocol: [research/comparand-scaling](../../research/comparand-scaling/README.md).
The generated per-worker [BOARD](../../research/comparand-scaling/BOARD.md) separates complete,
independently checked, limited, unsupported and unattempted cells. Julia uses controller
`55f513492f565f59aadd4d9b30b5f5a8b2039929`; its bounded stage does not change the native instrument. No Zeebra solver algorithm or production default changes in this study.

## Native result

The native campaign covers 1,296 distinct grid identities: three repetitions, 18 inputs, six
worker counts and four engine entries. There are 234 checked completions, 246 completions
without an independent exact reference, 10 resource stops, 96 gated records, 656 capability
refusals and 54 shipping-serial entries deliberately left unmeasured for #751's current-default
profile. Zeebra multiworker refusals remain visible; the experimental concurrent-pivot route
is not relabeled as a shipping backend. Grobx's pinned driver supports one worker only.

The anticipated expansion of a single-worker gap into a uniformly much larger multicore gap
is not supported by these pinned native inputs. More requested workers do not monotonically
improve complete task time. This is evidence about these engines, fields and inputs, not a
claim that larger matrices cannot scale. All completed answers used for ratios agree with
independently retained exact reduced bases, coefficient for coefficient.

Selected medians below are **fresh process wall**, including input/output. Each has three
interleaved observations. See the full board for ranges, RSS, CPU time, startup gates and
all intermediate worker counts. Rust's backend is randomized; msolve uses exact sparse
linear algebra (`-g2 -l2`). These are measured alternatives, not equal-work strong scaling:
pivot choices and coefficient work can change with concurrency.

| Field/input | Engine | 1 worker s | 8 workers s | 16 workers s | Best observed worker count through 32 |
|---|---|---:|---:|---:|---:|
| GF(32003) MQ10 | msolve | 0.2121 | 0.1168 | 0.6581 | 8 |
| GF(32003) MQ10 | groebner-rs | 0.1169 | 0.0882 | 0.1006 | 8 |
| GF(2^31−1) MQ10 | msolve | 0.2384 | 0.4615 | 0.4621 | 4 |
| GF(2^31−1) MQ10 | groebner-rs | 0.1552 | 0.0970 | 0.1077 | 8 |
| GF(2^31−1) Katsura-11 | msolve | 1.5328 | 0.7155 | 2.7126 | 8 |
| GF(2^31−1) Katsura-11 | groebner-rs | 0.8100 | 0.3603 | 0.3794 | 8 |

Grobx's one-worker M31 Katsura-11 process median is 0.1504 seconds. It is an important raw
performance target even though the pinned driver has no multicore entry. A best observation
within this finite grid is not a validated adaptive policy or proof of saturation beyond it.
Cyclic-7 has a particularly shallow curve; small differences within its repeated ranges should
not be promoted to a precise optimal worker count. Cyclic-10 refuses both serial and bounded
16-worker rescue probes under the declared limits; no refusal is a completed instance.

Higher-worker regressions do not establish oversubscription: requested workers have matching
physical-core affinity. Synchronization, cache effects, scheduling and changed coefficient work
are possible causes requiring separate attribution. Native process CPU/wall greater than one
establishes overlapping CPU execution, not a count of algebra workers. Rust's pool-size report
alone establishes capacity; separate hot-region observations address actual participation.

## Targets for Zeebra at 8 and 16 workers

These native process targets are pinned complete-basis observations, not predictions.
The ordinary deterministic Julia process grid was also measured; none of its matched process
observations improves the exact-mode targets below. Its hot-call timers cannot join this boundary. The first bar is the
best **tested exact-mode** engine under a common physical-core budget; fixed-worker values
remain visible so a slower 16-worker comparand cannot be selected opportunistically.

| Input | Exact-mode target with ≤8 cores s | Exact-mode target with ≤16 cores s | Raw checked-answer target with ≤8/≤16 cores s |
|---|---:|---:|---:|
| GF(32003) MQ10 | 0.1168 (msolve, 8) | 0.1168 (msolve, 8) | 0.0882 (Rust, 8) |
| GF(2^31−1) MQ10 | 0.1670 (msolve, 4) | 0.1670 (msolve, 4) | 0.0970 (Rust, 8) |
| GF(2^31−1) Katsura-11 | 0.7155 (msolve, 8) | 0.7155 (msolve, 8) | 0.1504 (grobx, 1) |

The randomized raw rows have checked answers on these frozen inputs. They do not justify
weakening Zeebra's exact algorithmic guarantees. The separate Python equality oracle costs
about 0.59–0.63 seconds on MQ10 and 3.90–3.99 seconds on M31 Katsura-11 in this campaign.
Those costs are outside process wall and retained per observation. They presuppose an already
known exact basis and are **not** a general production certification route or a measurement
of arbitrary-input certificate construction. Do not add them to raw wall and label the sum a
production-certified solver. Actual certified grobx reference runs, including witnesses and
refusals, are separate retained experiments.

A go/no-go comparison for #728/#730's successors must use the same canonical input, resource
limits and task boundary. Report the same-algorithm one-worker control, shipping-current control,
fixed 8/16-worker result, and best result under the matching core budget. A faster matrix stage
or a faster refusal cannot meet these whole-task targets. #751 owns complete current-default
Zeebra profiling; these external measurements do not silently supersede that prerequisite.

## Exact references, failures and wide-field limits

Historical #683 artifacts supply independently Singular-checked MQ10/Katsura-4 bases at both
small prime widths. The reference loader actually finds their retained `artifacts.basis`, rather
than assuming an unavailable result. A bounded exact/cofactor grobx attempt supplies C7/32003:
its native mathematical check completed, but an unrelated compiler appeared at the post-child
gate. Its original timing remains excluded. Only its checked mathematical answer is reused.
Offline replay checks retained input/response hashes, format and full coefficient equality;
it does not rerun all native cofactor identities or claim independent certificate replay.

The initial K11/32003 cofactor attempt refused at its resource limit. A later bounded Singular
attempt completed through the existing adapter, but an artifact-retention defect deleted its
native answer. Its capture failure and logs remain visible; it supplies neither a reference nor
a published complete-basis timing. It was not retried. The adapter retention flag was fixed and
validated on a cheap control before the distinct, unattempted K11/M31 oracle, which retains a
complete exact Singular answer. Consequently K11/32003 and C7/M31 remain complete-unverified
observations; no ratios are published from them.

The merged wide64/Goldilocks inputs have complete native worker grids, including dense random
MQ10, Katsura-9, Cyclic-7 and startup controls. Their canonical inputs differ from the narrow
historical MQ fixture. The original native observations lacked exact references and retain their
complete-unverified statuses. A separate post-campaign trusted deterministic Julia agreement
layer now checks 63 native and eight Julia answers for wide64 K4/C7/MQ10, without rewriting
historical statuses or clocks. This is independent exact-engine agreement, not a witness/cofactor
certificate. Goldilocks and wide64 Katsura-9 remain outside that new attestation. No verified
wide-field competitive lead or frontier advance is claimed. msolve's
characteristic limitation is an unsupported comparison, not inferior performance. These gaps
are explicit priorities for a subsequent bounded exact-reference campaign, not hidden wins.

## Measurement, storage and audit boundaries

Each solver has the original 60-second/2-GiB/128-MiB process-tree/output guard. Resource stops
seed a serial-refusal gate and one bounded 16-worker rescue; higher repeats remain explicit
skips. The native prefix, continuation and Julia timing windows use the existing workstation lock, matching affinity and compiler
refusal checks. msolve's provisioned O2/AVX2 build and Rust's x86-64-v3/fat-LTO/system allocator
are identified separately; identical effective instruction flags are not claimed. Full source,
executable and Julia package identities are retained.

The first native window ended after 1,161 seconds with a declared dispatch cutoff and 222
records. Whole-cohort checkpoint rewrites were costly: 391.91 seconds of child wall and 70.83
seconds of equality checking leave the rest for parsing, serialization, compression and other
controller work. That residual is not an isolated compression measurement. One explicitly
approved controller-only continuation retains all accepted/refused prefix identities, never
reruns them, and completes the remaining 1,074 records in a 529-second lock window
(controller elapsed 527.55 seconds). Of this, child wall is 154.95 seconds and equality checking
140.03 seconds; other controller work accounts for about 232.58 seconds. Solver timers exclude
these archival/checking costs, but campaign budgets include them.

The continuation writes static metadata once and one hash-bound row payload once using the
existing flushed-journal pattern. Final publication uses the existing bounded chunk loader and
content-addressed proof-response helper; repeated basis literals are shared without dropping raw
answers. Exact round-trip and tamper tests cover native JSON, flat basis copies, textual outputs,
refusals and interruption boundaries. Original archive hashes and controller identities remain
in the publication metadata. The continuation changes no solver binary, input, affinity,
arithmetic/backend setting or measurement region.


## Julia and actual CPU participation

All 108 ordinary deterministic Julia observations complete and match independently retained exact
bases: three repetitions, workers 1/2/4/8/16/32, GF(32003) K4/MQ10/C7 and M31 K4/MQ10/K11.
Its 819.47-second controller stage stays inside the 900-second watchdog. The startup-screened
board withholds ordinary process-wall scaling ratios on these small tasks. For example, M31
Katsura-11 process medians are 9.617/7.136/7.174 seconds at 1/8/16 workers, while tiny-warmup
internal calls are 2.954/0.807/0.845 seconds. These are distinct boundaries. Ordinary internal
calls can still contain target-specific threaded JIT and GC; they are not compilation-free timings.

A separate copied-full-input-prewarm diagnostic completes all three planned M31 Katsura-11
observations within 42.07 controller seconds. These processes each contain two complete solves
and are excluded from external process-wall comparisons. Their hot calls are 2.927/0.610/0.564
seconds at 1/8/16 requested workers, with zero reported compilation/recompilation and
39.6/57.9/25.1 ms GC. CPU-active OS-thread participation is 1/11/23, respectively. Counts above
requested algorithm workers can include GC/runtime threads; these are tick-resolution lower
bounds on participation, not simultaneous algebra-worker counts. One diagnostic observation
per cell does not establish a production adoption speedup.

Rust's 15-second diagnostic stage retains a complete p=1 record. The p=8 native response
completed but its parent's known-reference comparison was interrupted before journal commit.
The retained request/stdout/usage files bind the executable, input and eight CPU-active hot-call
participants; a separate offline exact basis comparison succeeds. Its native timer is retained,
but whole-process wall and exit metadata are missing. No completed process row or ratio is
invented. P=16 hot diagnostics were not attempted. The new regression fixes specifically this
coefficient/reference-check interruption boundary for future runs; it does not claim universal
metadata durability across every possible JSON parsing or archival signal. The original failed
record remains unchanged and was not rerun.

The wide Julia stage captures eight of nine planned cells before its dispatch cutoff (69.51
controller seconds): K4/C7 at 1/8/16 and MQ10 at 1/8. MQ10 p=16 is explicitly unattempted. The
post-campaign agreement layer binds actual retained scripts, field, ordered generators, grevlex,
explicit deterministic linear algebra, full output and pinned source. Its trusted finite-field F4
backend exhaustively processes deterministic row chunks; `certify=false` remains disclosed and
no separate `isgroebner`/witness check is claimed. The single-repeat wide observations support
input-specific agreement, not a robust performance-win claim or extrapolation to Goldilocks/BN254.

## Acceptance and integration scoreboard

| #739 deliverable | Result |
|---|---|
| Per-worker board cohorts | Generated experimental board with every native grid cell, 108 ordinary Julia rows, diagnostics and explicit omissions. Shipping board rows are not relabeled. |
| msolve/Rust scaling through 32 | Complete three-repeat native grids, work/task boundaries, CPU/RSS, startup gates and observed best worker counts retained. No claim beyond the tested grid. |
| Groebner.jl scaling | Installed `tasks` API verified; 108 deterministic process observations, separately qualified hot-call curves and full-case-prewarm diagnostics retained. Startup limits whole-process ratio claims. |
| grobx threaded setting | Pinned driver is serial; unsupported worker counts remain visible. |
| Actual concurrency | Native CPU/wall and phase-specific participation retained with stated limits; Rust p=8 is a partial diagnostic and p=16 is missing, rather than inferred from pool size. |
| Zeebra 8/16-worker targets | Exact-mode process and raw checked-answer targets stated separately, including best performance under the common core budget. |
| Wide extension | Both fields' native grids retained; separate exact-engine agreement covers three completed wide64 inputs. Remaining gaps and omitted Julia p=16 MQ remain visible. |
| Shipping Zeebra row | Serial p=1 profiling remains #751; p>1 refuses. A production parallel backend must explicitly update the existing adapter capability and rerun a matched cohort before publication. |
| Reproducibility | Original source/executable identities, independent references, failures, resource stops, stage manifests, bounded payloads and offline board replay retained. |

The experimental board is necessary because the shipping Groebner.jl adapter selects its own
backend and cannot honestly label these explicitly deterministic or two-solve diagnostic calls
as default adapter measurements. A narrow future adapter extension can expose the algorithm
configuration before importing corresponding rows into the main competitive board. This report
already supplies concrete per-worker cohorts; main-board integration is not represented as done.

Final integration merges current main, including #749, without rebasing or relabeling measured
ancestors. Required installed-adapter coverage runs with `ZEEBRA_REQUIRE_MSOLVE=1`: 339/339
external-library tests pass after that merge. The optional native driver tests/Clippy, exporter
and retention protocol tests, focused Python guards and generated artifact replay cover this
study's changed interfaces. No new solver algorithm or production parallel default is added.
