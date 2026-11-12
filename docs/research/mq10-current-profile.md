# Current-default MQ10 profile (#709)

This experiment profiles the same public digest-pinned instances used by the grobx and sylvester
comparands, at GF(32003) and GF(2147483647), with the field representations used by `ZeebraSolver`.
`examples/mq10_profile.rs` changes only `F4Options::measure_stages`; the library and shipped
strategies are unchanged. Each process computes one reduced basis. Timers cover the F4 call,
not input generation/parsing or basis serialization. Process wall includes those boundaries.

Five alternating repetitions with and without stage clocks measure instrumentation overhead.
Every complete answer must match the full retained Singular-verified grobx basis, with the same
input digest and field; matching leading monomials alone is insufficient. All attempts and full
answers are retained. Construction sub-timers refine construction and never add to the stage sum.

A separate Callgrind run counts instructions in the clocks-disabled executable. Its simulated
wall clock and RSS are profiler costs and cannot become benchmark timings or engine memory figures.
Whole-process instruction counts include setup and serialization; source/function attribution is
used to locate code for investigation, not to equate instruction shares with elapsed-time shares.

## Reproduce

Build and test before acquiring the benchmark lock. Use a private target/scratch directory on
`/buildcache`; substitute a real machine name and an available CPU set. Commit the instrument
before running the campaign so retained provenance identifies the actual source.

```sh
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-mq10-profile
export TMPDIR="$CARGO_TARGET_DIR/tmp"
export RUSTC_WRAPPER=''
mkdir -p "$TMPDIR"
cargo test --example mq10_profile
python3 tools/test/mq10-profile-test.py
CARGO_PROFILE_RELEASE_DEBUG=1 cargo build --release --example mq10_profile

ZEEBRA_MACHINE=my-machine ZEEBRA_AFFINITY=0,1,2,3 \
  tools/benchlock.sh mq10-profile taskset -c 0-3 \
  python3 tools/external/mq10-profile.py \
  --binary "$CARGO_TARGET_DIR/release/examples/mq10_profile" \
  --scratch "$CARGO_TARGET_DIR/native" \
  --output "$CARGO_TARGET_DIR/mq10-profile-native.json.gz"

ZEEBRA_MACHINE=my-machine ZEEBRA_AFFINITY=0,1,2,3 \
  tools/benchlock.sh mq10-callgrind taskset -c 0-3 \
  python3 tools/external/mq10-profile.py --callgrind --repeats 1 \
  --binary "$CARGO_TARGET_DIR/release/examples/mq10_profile" \
  --scratch "$CARGO_TARGET_DIR/callgrind" \
  --output "$CARGO_TARGET_DIR/mq10-profile-callgrind.json.gz"
```

Keep outputs outside the checkout until both campaigns finish, then copy the two cohorts and
Callgrind sidecars into `research/competitive/results/`; the runner refuses a dirty source tree.

The native guard allows 120 seconds and 2 GiB per process. Callgrind gets 1800 seconds and 4 GiB.
A guard stop or nonzero exit is retained and fails the campaign. The binary hash, compiler, source
commit, options, field type, actual CPU affinity and complete statistics are recorded. The build
uses release fat LTO, one codegen unit and x86-64-v3, with line tables for instruction attribution.
No profiling row enters the competitive board, and no cross-engine ratio pools it with old runs.
