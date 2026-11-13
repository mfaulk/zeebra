# Selective F4 backward reduction (#269)

This is an opt-in research experiment. The production full-RREF path remains the control.
The prototype keeps forward pivots/arithmetic/scheduling fixed and uses one generic dense
row to clear later echelon pivots from selected targets, left to right. It never discards
an inherited pivot before a candidate has used it. No public RREF contract changes.

Predeclared gate: five interleaved fresh-process repetitions at both 32003 and 2147483647,
one worker, CPU 3, release/fat LTO/one codegen unit/x86-64-v3. Initial MQ10 arms are stock,
observed full sparse back-substitution, dense all targets and dense candidate targets.
The last two separate row-major materialization from target selection. Work-on repeats
are separate from native timings. Build and test before taking `tools/benchlock.sh`.
Use the existing 60-second/2-GiB child and 185-second parent guards and unchanged F4 limits;
every failure/refusal stays in the artifacts. No build may overlap measurement.

Acceptance: all completed answers must match the existing complete independently checked
reduced bases and input digests. For further consideration, selected reduction must improve
MQ10 complete F4 median by at least 10% at both primes, use at most 1.25x peak RSS, and not
regress Cyclic-5 or Katsura-6 complete medians by more than 5%. Five repetitions establish
only a bounded feasibility verdict, not a production shipping decision. Any apparent win
also gets the existing MQ14 60-second fixed-budget probe; stops are not speedups.
No repeated extension is planned if noise obscures the sign. A later production proposal
requires its own review. Parallel-forward crossing follows the isolated verdict and does
not change this experiment's serial forward schedule.

The correctness argument, exact commands, retained attempts and scoped decision are recorded
in `docs/research/elimination-kernels.md`. H2 marked scanning is a separate factor: no scan
heuristic is bundled into this prototype.

## Reproduce

```sh
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-269
export RUSTC_WRAPPER=''
export TMPDIR="$CARGO_TARGET_DIR/tmp"
mkdir -p "$TMPDIR" "$CARGO_TARGET_DIR/frozen"
cargo test --features research-work --lib linalg::selective
cargo test --features research-work --example mq10_profile
python3 tools/test/selective-backward-study-test.py
cargo build --release --example mq10_profile
cp "$CARGO_TARGET_DIR/release/examples/mq10_profile" "$CARGO_TARGET_DIR/frozen/stock"
cargo build --release --features research-work --example mq10_profile
cp "$CARGO_TARGET_DIR/release/examples/mq10_profile" "$CARGO_TARGET_DIR/frozen/observed"
```

Commit the instruments before measuring. With matching machine identity and actual affinity:

```sh
ZEEBRA_MACHINE=trpro-5995wx ZEEBRA_AFFINITY=3 \
  tools/benchlock.sh selective-backward-269 taskset -c 3 \
  python3 tools/external/selective-backward-study.py \
  --stock "$CARGO_TARGET_DIR/frozen/stock" --binary "$CARGO_TARGET_DIR/frozen/observed" \
  --scratch "$CARGO_TARGET_DIR/native" --output "$CARGO_TARGET_DIR/native.json.gz"
```

Use separate outputs and scratch directories with `--phase work` for passive-work overhead
controls, or `--phase probe` for the larger MQ14 fixed-budget probe. `--resume` only continues
a verified prefix stopped by the ambient-load gate, with unchanged source, binaries and limits.
The work cohort has five fresh processes each for full-off, full-on, dense-all-on and
selected-on, separately from the 120 native attempts. It checks every complete coefficient
and the complete F4 pair/degree/shape trajectory. Source inputs remain the existing public
corpus; independent reference files are hashed into every cohort.

The research entry charges the retained original target plus the live dense copy against the
existing live-entry allowance, so it can refuse earlier than the ordinary algorithm. It separately
bounds dense cells plus the column index to 64 MiB. Reported sparse capacities include the
output buffer before replacement. They exclude allocator metadata, observer masks, thread
stacks and source polynomials; process RSS includes the whole child. Two scratch/index
allocations plus one output allocation per nonzero selected target replace repeated sparse
merge/copyback operations. No buffer capacity is transferred between target rows.

Decode packed answers with `tools/external/study_artifacts.py`'s `load_study` or `iter_attempts`.
The content-addressed payload hashes are checked during decoding. Native whole-process wall,
self peak RSS and F4 stages are separate quantities; work-on and probe times are not native
performance samples. Logical field products and scanned cells are not physical DRAM bandwidth.
