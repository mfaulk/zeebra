# Remaining H13 kernel experiments

This study extends the [prefix-merge report](../../docs/research/elimination-kernels.md).
`elimination_kernel_study FIELD SHAPE EIGHTHS BACKEND` replays structured elimination plus
production back-substitution. Fields are `m31`, `p64`, `bn254`, and the pilot `p15` (32003).
Shapes are `k7` (Katsura-7 grevlex, batch 4), `c6` (Cyclic-6 grevlex, batch 7) and `k6lex`
(Katsura-6 lex baseline preset, batch 21). M31/p64 source fingerprints must match H6.
BN254/p15 captures retain their full fingerprints and must agree across attempts.

`EIGHTHS` in 1..8 deterministically thins only tails, with nested masks and every leading entry
retained. Eight means the unmodified capture. Lower levels are synthetic corpus derivatives,
not F4 batches from an equivalent ideal. The reducer-block invariant survives. Compare backends
at one mask using the complete canonical RREF, rank, zero rows and work counters; do not compare
bases across masks or treat a masked matrix as a full-solve performance result.

`--arithmetic` compares the generic GF(32003) accumulator with the scalar delayed pilot over the
same row, fixed factor and passes, asserting every final coefficient equal. Its logical update
throughput includes exact modular-zero bookkeeping. It does not measure physical DRAM bandwidth.

## Isolated pilot

`delayed.patch` changes **only a disposable build**: it adds private research conversion hooks to
`FiniteField`, implements them only for `PrimeFieldElement64<32003>`, and intercepts Adaptive
elimination there. Other primes and binary/extension/wide fields use the original generic path.
The committed library API and production dispatch are unchanged. `examples/support/h13_delayed.rs`
contains the one scalar prototype shared by the arithmetic instrument and overlay.

The pilot stores canonical pivot coefficients as split u16 arrays and working cells as u64
nonnegative sums. Pivot decisions and support counts always use residues mod 32003. Each row
operation adds at most `(p-1)^2` per cell; folds occur after at most
`floor((u64::MAX-(p-1))/(p-1)^2)` operations. Tests force frequent folds and cover cancellation,
reactivation, column boundaries, stale scratch and exact mid-operation entry-budget refusals.
No SIMD kernel or general field dispatch is added.

The pilot duplicates pivot storage. `ZEEBRA_H13_METRICS=1` adds conversion-time and cache-capacity
lines to stderr; keep those diagnostic runs separate from native timing. The F4 live-entry
allowance is unchanged, but the extra pivot cache is **outside its byte accounting**. Therefore
this is a feasibility experiment, not a shippable backend or a capacity improvement. Every process
has an independent 2-GiB/185-second tree guard, and source captures have a 60-second solver limit.

## Build and freeze

Use one private target directory on the buildcache drive. Build before holding benchlock:

```sh
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-269-kernels
export TMPDIR="$CARGO_TARGET_DIR/tmp"
export RUSTC_WRAPPER=''
mkdir -p "$TMPDIR"
cargo build --release --example elimination_kernel_study --example row_merge_study \
  --example public_corpus --example mq10_profile
python3 tools/external/elimination-kernel-study.py --freeze "$CARGO_TARGET_DIR/baseline" \
  --target "$CARGO_TARGET_DIR"
git apply research/elimination-kernels/delayed.patch
cargo test --example elimination_kernel_study
cargo build --release --example elimination_kernel_study --example row_merge_study \
  --example public_corpus --example mq10_profile
python3 tools/external/elimination-kernel-study.py --freeze "$CARGO_TARGET_DIR/candidate" \
  --target "$CARGO_TARGET_DIR"
git apply -R research/elimination-kernels/delayed.patch
```

Freeze requires a committed instrument and either a clean tracked tree or the exact research
patch. Metadata retains source revision, overlay SHA-256, compiler identity and all binary hashes.
Always remove the overlay before committing or running ordinary development checks.

## Run

```sh
ZEEBRA_MACHINE=my-machine ZEEBRA_AFFINITY=3 tools/benchlock.sh h13-curves taskset -c 3 \
  python3 tools/external/elimination-kernel-study.py --phase curves --repeats 5 \
  --baseline "$CARGO_TARGET_DIR/baseline" --scratch "$CARGO_TARGET_DIR/curves" \
  --output "$CARGO_TARGET_DIR/curves.json.gz"
```

Use `--phase arithmetic --repeats 7` for the scalar feasibility gate. If useful, follow with
`--phase pilot --candidate "$CARGO_TARGET_DIR/candidate" --repeats 5` and then the
[existing full-solve runner](../row-merge/README.md) using these same frozen directories. It checks
all complete bases against retained independent references. Fresh processes alternate arms and
backend order; every failure remains in the compressed output and fails the campaign.

Offline checks, also run by CI:

```sh
cargo test --example elimination_kernel_study
python3 tools/test/elimination-kernel-study-test.py
```

Physical DRAM counters require a working memory-controller event. A failed or unavailable event
must remain a limitation; logical byte counts and cache misses do not substitute for bandwidth.
