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

## Bounded prototype

The opt-in `linalg::concurrent::reduce` uses safe `OnceLock` publication and scoped
threads. It reuses one dense accumulator per active worker, supports dynamic or
static contiguous row scheduling, and commits matrix changes only after every
worker succeeds. Its bounds apply only at this experimental entry. Ordinary F4
and `FiniteField` keep their existing generic signatures.

The `research-work` observer hook connects this entry to the existing F4 loop;
`mq10_profile --workers=4 --schedule=dynamic` selects it. `--work` collects actual
worker-local dense-operation counters, products after failed claims, scheduling
and publication clocks. Parent thread-local counters alone omit forward work.
Without `--work`, worker product/operation observation is off; algebraic statistics
and publication counts remain available. Entry/workspace refusals retain the input
and explicitly fall back to serial; worker failure never accepts partial output.

The experimental `statistics.peak_nonzeros` is a **conservative reservation upper
bound**, also exposed as `peak_reserved_entries`, rather than a sampled actual
mathematical high water. It charges original input copies and concurrent pending
reservations in addition to published rows. The ordinary serial statistic retains
its existing meaning. `workspace_bytes` bounds dense buffers and pivot/index
arrays separately; thread stacks, allocator overhead, sparse capacity and process
RSS are not inferred from it. A stricter reservation refusal is not a serial
budget failure or evidence that the mathematical matrix exceeds the limit.

Build the new observed binary with the commands above. For the parallel phase,
launch the runner with a parent affinity containing all 64 physical cores and
set `ZEEBRA_AFFINITY` to that exact inherited CPU set (comma-separated CPU IDs).
It maps topology to one logical CPU per physical core, records each child CPU set,
and pins every child independently:

```sh
ZEEBRA_MACHINE=trpro-5995wx \
ZEEBRA_AFFINITY="$(python3 -c 'import os; print(",".join(map(str, sorted(os.sched_getaffinity(0)))))')" \
  tools/benchlock.sh concurrent-pivots-728 \
  python3 tools/external/pivot-discovery-study.py --phase parallel \
    --stock /buildcache/cargo-target/zeebra-728-stock/release/examples/mq10_profile \
    --observed /buildcache/cargo-target/zeebra-728-observed/release/examples/mq10_profile \
    --scratch /buildcache/cargo-target/zeebra-728-parallel \
    --output /buildcache/cargo-target/zeebra-728-parallel.json.gz
```

Controls plus both schedules at 1,2,4,8,16,32,64 workers, counters on/off, each get
five fresh processes per field. The same processes retain per-batch forward and
backward elapsed times; observed arms hash pre-elimination matrices with the
existing matrix-corpus fingerprint routine and require identical inputs across
schedules. CPU time is the change in child user+system resource usage. Empty
scoped dispatch is measured in five fresh processes per worker count, 16 samples
each, with actual affinity. This scoped runtime is a bounded experiment; #592
owns any persistent-pool comparison and production runtime decision.

The runner losslessly packs repeated complete bases using the existing
`study_artifacts`/`proof_artifacts` storage. Always decode with
`tools/external/study_artifacts.py`'s `load_study` or `iter_attempts`, which verify
payload hashes and restore exact stdout. Census archives use the same packing;
their parsed response key was renamed from `report` to `raw` outside timing.
Keep interrupted
cohorts separately and report why each stopped; never pool them into the final
five-repetition summary.

For a parallel campaign stopped by the ambient-load gate, rerun the identical
command with `--resume` after the machine is quiet. This accepts only an intact
verified prefix of the predeclared five-repetition plan, unchanged binaries,
limits and physical affinity. It retains the refusal in `resumptions` and executes
only missing samples; it cannot discard failures, duplicate a sample or select a
new repetition count. The runner commit used for each resumption is recorded.

## Controls, frontier probe and retained verification

The same instrument accepts `--problem=cyclic-5`, `--problem=katsura-6` and
`--problem=mq-random-14`; MQ10 remains the default. Katsura names here count
variables, so `katsura-6` is the literature's Katsura-5. Run the classical controls
and the fixed-budget frontier probe under a separate lock, after the main sweep:

```sh
tools/benchlock.sh concurrent-pivots-728-controls \
  python3 research/concurrent-pivots/controls.py \
    --binary /buildcache/cargo-target/zeebra-728-observed/release/examples/mq10_profile \
    --scratch /buildcache/cargo-target/zeebra-728-controls \
    --output /buildcache/cargo-target/zeebra-728-controls.json.gz
```

Each classical field/arm gets five fresh processes: serial control and both
schedules at all seven worker counts. Cyclic uses the existing independent full
reference. Katsura's complete reduced coefficient list is checked against a fresh
Singular reduced basis of the independently written defining equations, outside
solver timing; its script and full oracle output are retained and digest-bound.

The public MQ14 probe is predeclared at 60 seconds/2 GiB per child, default F4
entry/byte budgets, one serial and one dynamic four-worker attempt per field.
It tests reachability/refusal only and cannot establish scaling or a speedup.
Its exact input digests are `4e440cfac84262260736a2368f43c7a96181986ca5bc108517299520d56f8795`
at 32003 and `029def705543e29b9f0648d3fa21a87be32358b79c3e64bb6dd222fa432c439d`
at 2147483647. A completed probe still needs an independent reference before any
performance adoption claim. Stops remain explicit unverified outcomes.

`python3 research/concurrent-pivots/summarize.py` restores/hash-checks payloads,
rechecks every complete answer and regenerates CSV/JSON summaries. CI runs this
alongside the hand-matrix, forced-race and observation tests. Frozen source patches,
source archive hashes, Cargo fingerprints and binary hashes live under `evidence/`;
apply the named decompressed patch to its recorded base to recover the measured
source after a squash. The prototype measurement source is distinct from the later
feature-disabled lint cleanup, which changes no elimination algorithm.
