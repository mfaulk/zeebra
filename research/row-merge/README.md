# Sparse row-merge experiment

`examples/row_merge_study.rs` captures pinned matrices before timing the production forward and
backward elimination stages. Capture cost is outside those stage timers but inside the guarded
process. `--mode work` repeats back-substitution with counters and asserts exact equality with
production; its extra clone and diagnostic pass mean its timings must not be pooled with native
matrix timings. Target roles identify inherited reducer **pivot columns**, not original row
provenance after backend row reordering.

`tools/external/row-merge-study.py` alternates baseline/candidate executables in fresh processes,
checks complete bases against independently verified retained references, and compares complete
RREF hashes across arms and backends. Public-family binaries check their frozen Singular
references internally. Its snapshot mode binds source revision, compiler and executable hashes.
The runner retains every process exit, resource stop and verification failure and exits nonzero
if any attempt fails; a failing cohort is not a performance result.

## Reproduce

Use a separate worktree and private target directory for each revision. Build before acquiring
the machine-wide lock. At each clean revision containing the runner:

```sh
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-row-merge
export TMPDIR="$CARGO_TARGET_DIR/tmp"
export RUSTC_WRAPPER=''
mkdir -p "$TMPDIR"
cargo build --release --example row_merge_study --example public_corpus --example mq10_profile
python3 tools/external/row-merge-study.py --snapshot "$CARGO_TARGET_DIR/frozen" \
  --target "$CARGO_TARGET_DIR"
```

Then, from the candidate checkout, supplying the two frozen directories:

```sh
ZEEBRA_MACHINE=my-machine ZEEBRA_AFFINITY=0,1,2,3 \
  tools/benchlock.sh row-merge taskset -c 0-3 \
  python3 tools/external/row-merge-study.py \
  --baseline /buildcache/cargo-target/baseline/frozen \
  --candidate /buildcache/cargo-target/candidate/frozen \
  --phase solves --repeats 5 \
  --scratch "$CARGO_TARGET_DIR/solves" --output "$CARGO_TARGET_DIR/solves.json.gz"
```

Use `--phase matrices --repeats 3` for eight small matrices with three backends each plus the large
MQ10 Adaptive case; `--phase work --repeats 1` collects diagnostic counts. Every process has a
185-second/2-GiB tree watchdog; source F4 captures and public/classical solves additionally have a 60-second solver
limit; MQ10 uses its existing shipped-default instrument with the outer watchdog. Matrix entry allowances remain those of the pinned preset. Native matrix measurements
exclude capture; RSS covers capture, replay and output. Explicit dense-buffer size is reported
separately from sparse tuple payload. These are neither identical memory boundaries nor measured
DRAM traffic. Do not infer physical bandwidth from logical tuple counts.

The historical `grobx-683` and corrective `grobx-683-small` cohorts supply independently verified
full bases for MQ10 and Cyclic-5/Katsura-4 at both 32003 and 2147483647. The corrected small-prime
Katsura record is used rather than the earlier failed grobx attempt. No historical record is edited.

Offline checks:

```sh
cargo test --example row_merge_study
python3 tools/test/row-merge-study-test.py
```

For separate user-mode hardware observations, use `--phase counters --repeats 3 --perf /path/to/perf`.
This runs only the two MQ10 full solves under `perf stat` and retains raw event output. Acceptance
requires positive counts for `cycles:u`, `instructions:u`, `cache-references:u`, and `cache-misses:u`,
with at least 99% running time for each event; unavailable or multiplexed events fail explicitly.
These whole-child observations include parsing and output and are not pooled with unprofiled F4
elapsed times. No memory-controller counters or physical DRAM bandwidth are measured.
