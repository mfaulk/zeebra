# Comparand worker scaling (#739)

The study extends the existing competitive corpus export, wide-corpus canonical parser/native
identity checks, exact references and process-tree guard. It changes no algebra algorithm.
`tools/external/comparand-scaling.py` creates bounded fresh-process worker cohorts; each attempt
retains the frozen complete input, command/affinity, source/executable identities, stdout/stderr,
whole-process wall/CPU/RSS, status and exact full-basis comparison. Native full-basis timing and
independent exact-reference/certificate construction are separate costs.

## Predeclared budget and gates

Workers: 1,2,4,8,16,32 physical cores, one logical CPU per distinct topology core. Initial cells:
GF(32003)/GF(2^31−1) published MQ10, Katsura-11 and Cyclic-7, with Cyclic-10 as the next-rung
bounded probe; Katsura-4 startup controls. Merged #738 supplies wide64/Goldilocks MQ10, Katsura-9
and Cyclic-7 plus Katsura-4. Dense wide MQ is a different pinned input from historical narrow MQ.

Each child is externally guarded at 60 seconds, 2 GiB and 128 MiB input/output storage. Each
campaign also has a declared aggregate wall limit and is launched inside `tools/benchlock.sh`.
A serial resource refusal gates repetitions and smaller-worker cells but receives one 16-worker
rescue before omitting larger-worker repeated cells. Skips and refusals stay in the archive;
a faster refusal is never a speedup. No budget is lifted to obtain a completion. Five repetitions
are the adoption standard; three bounded repetitions here establish comparative targets, with
ranges and startup boundaries stated rather than a production adoption decision.

For inputs lacking an already independently verified reference, `--certify` runs one bounded
serial grobx exact/cofactor checker. Its construction/verification attempt, source identities,
cofactors and failures are retained separately. A missing certificate/reference prevents timing
ratios; independent engine agreement alone does not establish reverse ideal inclusion.

## Build and validate before acquiring the measurement lock

```sh
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-m28-739
export TMPDIR="$CARGO_TARGET_DIR/tmp"
export RUSTC_WRAPPER=''
mkdir -p "$TMPDIR"
. tools/external/env.sh
cargo test --example competitive_sweep
python3 tools/test/comparand-scaling-test.py
cargo build --example competitive_sweep
```

The input-only exporter uses a debug build outside all measured regions; its complete canonical
identities are asserted against the frozen corpus. Every measured native solver uses the pinned
optimized build. Build the optional diagnostic driver privately, without replacing the installed driver:

```sh
cd tools/external/groebner-driver
CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-m28-739-driver \
TMPDIR=/buildcache/cargo-target/zeebra-m28-739/tmp RUSTC_WRAPPER='' \
RUSTFLAGS='-C target-cpu=x86-64-v3' CARGO_PROFILE_RELEASE_LTO=fat \
CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1 cargo build --release --locked
cd ../../..
export ZEEBRA_GROEBNER_RS_DRIVER=/buildcache/cargo-target/zeebra-m28-739-driver/release/groebner-rs-driver
```

Commit clean source before measurement. The study discovers actual affinity and topology and
sets each child to the first `p` available physical cores. Set `ZEEBRA_MACHINE` explicitly.
Use fresh output paths for distinct grids and diagnostic arms; no silent continuation/pooling:

```sh
ZEEBRA_MACHINE=5995wx tools/benchlock.sh comparand-739 \
  python3 tools/external/comparand-scaling.py \
  --binary "$CARGO_TARGET_DIR/debug/examples/competitive_sweep" \
  --input-source "$(git rev-parse HEAD)" \
  --scratch "$CARGO_TARGET_DIR/native" --output "$CARGO_TARGET_DIR/native.json.gz" \
  --fields 32003,2147483647 --rows katsura-4,mq-random-10,katsura-11,cyclic-7 \
  --repeats 3 --campaign-wall 1200
```

`--certify --workers 1 --repeats 1` retains exact reference construction; use its output with
`--references PATH` in later timing campaigns. `--diagnostic --repeats 1` enables hot-region
thread CPU snapshots in Julia/Rust and must remain separate from counters-off medians.
`--summarize --output PATH` regenerates a campaign table from retained records without solving.

For bounded narrow-field oracle alternatives, `--reference-only --engines singular --workers 1
--repeats 1 --wall 55` drives the existing Singular adapter through the input-export executable;
its generated script, ordered generator echoes and complete native answer are retained. Adapter
native solvers can own a separate process group: cancellation kills those leaves first and lets
the wrapper reap them before terminating the wrapper. The aggregate hard watchdog remains
separate from the controller's before-next-cell wall cutoff. Launcher signals retain the current
interrupted attempt before propagating their exit status.

`--references PATH...` can reuse multiple pinned reference cohorts. An exact native-checker answer
whose timing was excluded for compiler overlap may supply mathematics after input/checker/output
validation; its original status is preserved and its clocks/RSS never enter timing medians.
Pre/post-child compiler snapshots refuse or exclude a cell and halt the cohort, retaining process
identities instead of silently retrying a favorable sample.

Final artifacts use `--replay research/comparand-scaling` to check archive/source/executable
identity consistency, full input binding, complete coefficients against retained exact references,
and generated board equality. This offline check does **not** rerun the native cofactor checker:
original mathematical certification is the pinned external checker's successful execution, with
its full witness/output retained. Hash/format checks and full-basis equality are distinct evidence.

## Concurrency and comparison boundaries

The installed Groebner.jl 0.10.11 uses `tasks=N` and `threading_enabled()`, not `threaded=:yes`.
The study explicitly enables the supported global switch, asserts it, and requests deterministic
linear algebra at every worker count. Its internal call excludes setup/input/output but the tiny warmup can leave target-specific
threaded JIT compilation and GC inside it. The published wall column includes the complete fresh Julia process. Do not compare its warmed timer
with another engine's process wall. Hot user+system CPU tick deltas are a lower bound on observed
OS-thread participation, may include JIT/GC, and cannot resolve sub-tick or exited-thread work.

The Rust driver normally reports Rayon pool capacity, not actual solver participation. Optional
`ZEEBRA_RESEARCH_THREAD_TICKS=1` adds before/after snapshots immediately around its existing F4
call. This observer is absent from timing arms; the backend remains randomized with returned
bases checked against independent exact references. Native msolve process CPU/wall can establish
actual overlapping CPU execution (no JIT) but is not a count of active elimination workers.
Grobx's pinned driver and production Zeebra refuse multiworker requests explicitly.

These experimental cohort tables are retained research evidence, not new shipping Zeebra board
rows. Final main-board integration must use existing CompetitiveRecord contracts and exact
configuration/provenance gates; unsupported Zeebra multiworker rows remain capability refusals.

## Bounded controller continuation

The first native campaign stopped at its declared 1150-second before-next-cell cutoff after
222 grid records. Whole-cohort gzip checkpointing consumed substantial controller time:
391.91 seconds of child wall time and 70.83 seconds of exact coefficient checking leave about
687 seconds of the declared window for input/output parsing, archival and other controller work.
This residual is not a measurement of compression alone. Its 250,212,529-byte compressed
checkpoint retains the accepted prefix, refusals and all original controller identities.

The continuation changes archival behavior only: following the existing #592 journal pattern,
write static metadata once, each gzip attempt payload once, and append a flushed/fsynced
hash/path descriptor. A small status sidecar records termination. An incomplete descriptor is
an explicit recovery blocker; committed payload changes are rejected. Existing `wide.pack`
provides lossless bounded publication chunks after timing. `--resume PATH` requires identical
inputs, executable hashes, compiler/package provenance, affinity, effective environment and
solver policy. Version-probe RSS is retained as runtime telemetry and excluded only from the
immutable version-identity comparison; executable/build hashes remain exact. Every previous complete, refused, unsupported or gated identity is skipped.
Original attempts retain their original controller commit. There is one declared continuation,
not repeated sampling until a favorable result. The new aggregate storage ceiling is 16 GiB
for newly retained payloads plus measured child output; each original child cap remains intact.

The continuation has a 1150-second dispatch cutoff and an external **1200-second hard wall
limit**. Pending cells remain unattempted if the bound is reached. Julia is a separately declared
stage with its own at-most-1200-second hard cap, including diagnostics. No claim of saturation
or a scaling knee is made from a single unresolved repetition.

## Julia stage protocol

One Julia stage has a hard aggregate limit of 1200 seconds, including every child startup,
full-case warmup, tick diagnostic and artifact write. No new native reference attempts are
included. Ordinary timing keeps the existing tiny same-ring warmup; hot-call curves are labeled
**tiny-warmup calls, possibly containing threaded JIT and GC**. They are diagnostic observations,
not claims of compilation-free steady state. The installed 0.10.11 explicitly selects threaded
linear algebra only when `tasks > 1`, lower-row count is at least `2*tasks`, and total columns
are at least 1000 (`src/f4/linalg/linalg.jl`, pinned source hashes in the cohort).

Separate `--diagnostic --julia-full-warmup` processes first solve a `deepcopy(zb_sys)`, then time
the original input. Their whole-process time contains two complete solves and never enters an
external process-wall comparison. Julia 1.11's `@timed` exposes compilation, recompilation and
GC times for the hot call; these are retained with CPU-tick participation. `@timed` also enables
runtime accounting/lock profiling, so those arms remain separate from ordinary timers. Positive
hot tick deltas may still include JIT/GC work; a participant count alone does not prove simultaneous
algebra workers. Full-case warmup is not assumed to eliminate all compilation without checking
the reported telemetry. `--case-pairs field/input,...` declares a narrow exact-reference subset
within the regular rows/fields grid.

The exact [Julia stage launcher](julia-stage.sh) declares 900 seconds ordinary timing,
15 seconds Rust diagnostics, 165 seconds Julia diagnostics and 120 seconds wide observations.
Ordinary timing selects only these exact-reference inputs: GF(32003) K4/MQ10/C7 and
GF(2^31−1) K4/MQ10/K11, three repetitions at all six worker counts (108 planned records).
Both diagnostic stages use M31 Katsura-11 at 1/8/16 workers, one repetition. Wide64 K4/MQ10/C7
gets one observation at 1/8/16 workers (nine planned records), with missing independent exact
references still blocking ratios. Every stage has a before-next-cell cutoff, a separate hard
watchdog and no automatic retry. All stages together run under a 1200-second outer watchdog.
`timeout --foreground` keeps the inner controller in the outer process group; its existing signal
handler kills and reaps separately grouped solvers. An environment/failure exit stops the whole
sequence. Omitted/remainder cells stay explicit in the generated board.

Set `ZEEBRA_739_EXPORTER`, `ZEEBRA_739_EXPORTER_SOURCE`, `ZEEBRA_739_REFERENCE_A` and
`ZEEBRA_739_REFERENCE_B` to the pinned executable/archives and exact exporter build commit.
Then, after clean-source/quiet gates, use the existing lock:

```sh
ZEEBRA_MACHINE=5995wx tools/benchlock.sh comparand-739-julia \
  timeout --signal=TERM --kill-after=3s 1200 \
  bash research/comparand-scaling/julia-stage.sh "$CARGO_TARGET_DIR/julia-stage-fresh"
```


## Published result and audit

See the [report](../../docs/research/comparand-scaling.md) and generated [BOARD](BOARD.md).
`inventory.json` binds cohorts, original reference archives, publication provenance and separate
post-campaign attestations. The 222-row native prefix is retained separately and not counted
twice in the 1,296-row completed grid. Ordinary Julia has 108 verified observations; its full-case
warm diagnostic has three. The Rust 15-second stage has one complete row and one separately
retained native response interrupted during parent reference checking; p=16 is unattempted.
The wide Julia stage has eight of nine planned records. No omitted cell is silently filled.

`trusted-exact-attestations.json` records 71 input-specific agreements with a separately audited,
trusted deterministic Julia finite-field F4 answer (63 native plus eight Julia responses).
This is not witness/cofactor certification; original complete-unverified statuses and clocks stay
immutable. Offline replay rechecks actual script/input bindings and all listed full coefficients.
Goldilocks and wide64 Katsura-9 are not extrapolated into that attestation.

`rust-postprocessing-interruption.json.gz` retains the p=8 native request/stdout/usage and hot
participant evidence without fabricating lost process wall/exit metadata. Future controller runs
retain guarded metrics if a deadline interrupts the coefficient/reference-check phase; this
specific fix is covered by a regression. Other signal boundaries retain their stated limitations.
`offline-validation-pause.json` records the owned validator pause during Julia timing. Its paused
wall is never used as a checker-cost measurement; published checker costs are original unpaused
per-attempt observations.

CI runs `python3 tools/external/comparand-scaling.py --replay research/comparand-scaling`.
It launches no solver and validates retained bytes, inputs, complete coefficients, continuation
identity and generated-board equality. It does not rerun native cofactor identities or reconstruct
an independently certified ideal-membership proof from a successful native checker flag.
