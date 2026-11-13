# Concurrent F4 pivot feasibility (#728)

This study reuses the complete MQ10 inputs, independent full-basis reference answers,
descendant RSS guard and machine-wide lock from [#713](../grobx-trajectory/README.md).
The current control is `e22b9b58`; historical timings are context only.

`linalg::work::measure_discovery` adds candidate-row clocks, inherited/new pivot
products, first non-inherited claim columns and serial pivot dependencies. It leaves
row order and arithmetic unchanged. `mq10_profile --discovery` enables this mode;
`--work` keeps the existing aggregate counters. Both require `research-work`.
An incomplete row remains explicitly incomplete after a budget refusal. Panic
cleanup restores disabled observation. This is a serial observer, not worker
aggregation or a parallel performance result.

Build/test before taking the lock, using private paths on `/buildcache`:

```sh
export RUSTC_WRAPPER=''
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-728-observed
export TMPDIR=/buildcache/cargo-target/zeebra-728-tmp
mkdir -p "$TMPDIR"
cargo test --features research-work --lib linalg::work
cargo test --features research-work --example mq10_profile
python3 tools/test/pivot-discovery-study-test.py
cargo build --release --features research-work --example mq10_profile
CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-728-stock \
  cargo build --release --example mq10_profile
```

Commit instruments before measuring. Unset `RUSTFLAGS` to retain the repository's
`x86-64-v3` flags. The runner records compiler, source commit, lock/config, binary
hashes, topology, actual affinity and load inside the lock. Substitute the actual
available CPU and declared affinity together:

```sh
ZEEBRA_MACHINE=trpro-5995wx ZEEBRA_AFFINITY=2 \
  tools/benchlock.sh pivot-discovery-728 taskset -c 2 \
  python3 tools/external/pivot-discovery-study.py \
    --stock /buildcache/cargo-target/zeebra-728-stock/release/examples/mq10_profile \
    --observed /buildcache/cargo-target/zeebra-728-observed/release/examples/mq10_profile \
    --scratch /buildcache/cargo-target/zeebra-728-census \
    --output /buildcache/cargo-target/zeebra-728-census.json.gz
```

Five interleaved fresh-process repetitions per field/arm: feature-absent control,
feature-present/off, aggregate work and detailed discovery. Each child is limited
to 60 seconds/2 GiB. All attempts and complete answers are retained; every completed
answer must equal the independently Singular-verified reference, with unchanged
input digest and F4 structural counters. The default ambient-load gate is 4.
No timing is inferred from a refusal. Verification is outside process timing.

Declared before this campaign: investigate one safe bounded prototype only if
measured forward discovery occupies at least 10% of the complete F4 call and the
64-worker dense scratch estimate is below 256 MiB on the initial MQ10 inputs.
Detailed row clocks include observation overhead; compare the four arms before
using their elapsed fraction, and report ambiguity rather than treating coefficient
ratios as elapsed shares. The weighted dependency DAG is specific to the serial
pivot trajectory; it is not a bound on concurrent pivot winners. First-claim
overlap is potential contention, not measured failed publication.

A later prototype must meet the issue's safe-publication, strict reservation,
cancellation, worker-failure, row-space and complete-basis checks before measuring.
Use workers 1,2,4,8,16,32,64, five interleaved fresh processes at matched settings,
dynamic versus static contiguous rows, and explicit worker-local counter totals.
Adoption requires at least 1.15x complete-task speedup at some p<=16 versus the
current serial control, no more than 1.5x RSS, and no >5% median wall regression
on completed public Katsura/Cyclic controls. Compare same-algorithm p=1 separately.
Any apparent success needs a larger MQ rung and the separate #269 policy crossing;
it does not authorize a production default. Failure of the initial gate ends the
prototype experiment with a scoped reject/defer verdict.
