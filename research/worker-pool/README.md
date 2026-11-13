# Persistent-worker dispatch study (#592)

This experiment compares scoped OS threads, a safe persistent pool with one bounded mailbox per
worker, and Rayon 1.12.0 (MIT/Apache-2.0), already present transitively through Criterion and now
an explicit **dev dependency only**. It changes no solver default or required dependency.

`examples/support/worker_pool.rs` accepts owned, bounded batches, preserves result order, retains
worker-local scratch, drains failures, and joins workers on drop. Cancellation is cooperative
between jobs; a running algebra operation is not preempted. Panicking scratch is reset before
reuse. A mutable owner submits one batch at a time; there is no global pool, recursive dispatch,
implicit nesting, spin loop, affinity setting or work stealing. Clients must budget all pools
and avoid outer/inner oversubscription. This research code is not an endorsed production runtime.

The `research-work`-gated `measure_border_reduction_with` hook owns each task's references with
`Arc`; it shares the original reduction loop and keeps `Send + Sync` off conversion APIs. Active
scratch is refused before dispatch above an explicit cell allowance; this does not redefine the
existing closure budgets or bound retained capacity/RSS. Scratch is cleared before every group,
including a new closure or shrinking/growing buffer. Retained capacities and the process high
water are reported separately. Unit tests compare exact coefficients across both prime widths,
GF(2), and GF(2^8), and check cancellation, panic recovery, result completeness and refusals.

## Predeclared protocol and decision gates

- Freeze source/build/lockfile/input/source-basis identities before measuring. All arms use the
  same release/fat-LTO/one-codegen-unit/x86-64-v3 executable and exact mathematical workload.
- Five fresh processes per cell, rotating backend order across repetitions, inside `benchlock`.
  Workers 1/2/4/8/16/32/64 are the physical-core sweep; 128 is a separate SMT diagnostic. The
  runner selects one logical CPU per physical core before SMT siblings and records topology.
- Dispatch: each process records construction, first dispatch and 32 repeated dispatches, with
  zero, 256 and 65,536 **total** synthetic integer updates divided across tasks. Each batch submits
  one task per requested worker. The static pool visits every worker; Rayon can execute multiple
  tasks on fewer workers. Active-worker counts expose that difference: this is task dispatch,
  not an assertion that Rayon wakes every worker. Scratch/queue/result ownership costs are included.
- Border: the existing eight Katsura/Cyclic/planted fixtures, batch size 64 and unbounded, same
  fixed contiguous groups in all arms. Preserve complete polynomial text and SHA-256 identities;
  check all remainder digests against the existing scalar entry point in every process. Record
  cold and warm whole-border, closure and reduction times, cells zeroed and capacities. The second
  run is the warm primary; keep both. Scoped groups allocate fresh scratch; pools reuse it.
- A 60-second/2-GiB descendant guard per child and an outer 900-second timeout bound the campaign.
  Unsuccessful attempts remain in the cohort and stop it. Start load must be below eight inside
  the lock; every attempt records load, CPU time, full process wall and process peak RSS.
- Treat median warm dispatch at least 4x below scoped dispatch at 2/8/32 workers as a material
  infrastructure result. This is not a solver speedup. For a border follow-up, require at least
  10% warm **whole-border** improvement versus that backend's own one-worker arm, consistent
  median/ranges and no >25% process-RSS regression; also compare against the existing scalar
  entry point to expose owned-dispatch overhead. A tiny-target or microkernel-only win is insufficient.
- No production integration or reopening of #50/#51/#52/#167 follows automatically. Default-batch
  and unbounded regimes must be reported independently; the latter's larger closure can erase
  target-loop gains. A future integration would need complete conversion/F4 evidence, worker
  budgets, API design and measured adaptive thresholds. An explicit negative verdict is complete.

This measures border reduction, **not a parallel FGLM conversion**. Whole-process time includes
source F4, reference checking, construction and two border passes, so do not label its ratio a
conversion speedup. Stage and whole-border ratios use matched regions instead. CPU time and RSS
include all of that setup. Default NUMA policy/first-touch is recorded, not claimed optimized;
there is no bandwidth/NUMA-causation claim without a targeted follow-up. Task-count bounds are not
byte budgets. No thread-local F4 work scope is inherited by workers or misreported as full work.

## Reproduce

Build and test before taking the benchmark lock. Keep artifacts off the system disk. Commit the
instrument first: the runner refuses a dirty tree. Choose an available CPU set after inspecting
`lscpu -p=CPU,CORE,SOCKET,NODE`; the example below uses all 128 logical CPUs of the 5995WX.

```sh
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-592
export TMPDIR="$CARGO_TARGET_DIR/tmp"
export RUSTC_WRAPPER=''
mkdir -p "$TMPDIR"
unset RUSTFLAGS
cargo test --features research-work --example worker_pool_study
cargo test --features research-work --lib grobner::fglm
python3 tools/test/worker-pool-study-test.py
cargo build --locked --release --features research-work --example worker_pool_study -j16

ZEEBRA_MACHINE=5995wx ZEEBRA_AFFINITY="$(seq -s, 0 127)" \
  tools/benchlock.sh worker-pool-592 timeout --signal=INT --kill-after=30s 900 \
  taskset -c 0-127 python3 tools/external/worker-pool-study.py \
  --binary "$CARGO_TARGET_DIR/release/examples/worker_pool_study" \
  --phase all --systems katsura-5,katsura-6,katsura-7,cyclic-5,cyclic-6,planted-6,planted-8,planted-10 \
  --output "$CARGO_TARGET_DIR/worker-pool.json.gz"
```

Use `--phase floor` or `--phase border` to split campaigns. `--workers` and `--systems` narrow a
smoke run; they do not stand in for the declared full sweep. A quick correctness invocation is
`worker_pool_study border parked 2 katsura-7 64`; it is not publication evidence.

After completion copy retained cohorts into this directory and run `python3 research/worker-pool/summarize.py`.
Keep benchmark-lock windows and provenance with the report in `docs/research/worker-pool.md`.
