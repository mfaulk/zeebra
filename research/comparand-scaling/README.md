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
  --scratch "$CARGO_TARGET_DIR/native" --output "$CARGO_TARGET_DIR/native.json.gz" \
  --fields 32003,2147483647 --rows katsura-4,mq-random-10,katsura-11,cyclic-7 \
  --repeats 3 --campaign-wall 1200
```

`--certify --workers 1 --repeats 1` retains exact reference construction; use its output with
`--references PATH` in later timing campaigns. `--diagnostic --repeats 1` enables hot-region
thread CPU snapshots in Julia/Rust and must remain separate from counters-off medians.
`--summarize --output PATH` regenerates a campaign table from retained records without solving.

## Concurrency and comparison boundaries

The installed Groebner.jl 0.10.11 uses `tasks=N` and `threading_enabled()`, not `threaded=:yes`.
The study explicitly enables the supported global switch, asserts it, and requests deterministic
linear algebra at every worker count. Its warmed internal solve excludes setup/JIT/output; the
published wall column includes the complete fresh Julia process. Do not compare its warmed timer
with another engine's process wall. Hot user+system CPU tick deltas are a lower bound on observed
OS-thread participation, may include GC, and cannot resolve sub-tick or exited-thread work.

The Rust driver normally reports Rayon pool capacity, not actual solver participation. Optional
`ZEEBRA_RESEARCH_THREAD_TICKS=1` adds before/after snapshots immediately around its existing F4
call. This observer is absent from timing arms; the backend remains randomized with returned
bases checked against independent exact references. Native msolve process CPU/wall can establish
actual overlapping CPU execution (no JIT) but is not a count of active elimination workers.
Grobx's pinned driver and production Zeebra refuse multiworker requests explicitly.

These experimental cohort tables are retained research evidence, not new shipping Zeebra board
rows. Final main-board integration must use existing CompetitiveRecord contracts and exact
configuration/provenance gates; unsupported Zeebra multiworker rows remain capability refusals.
