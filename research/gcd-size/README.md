# Multivariate GCD intermediate-size campaign

Issue [#652](https://github.com/mfaulk/zeebra/issues/652); the
[research note](../../docs/research/multivariate-gcd.md#6-intermediate-size-profiles-652)
defines phase boundaries, local determinant degree bounds and the fixed campaign.

Build both configurations from the same clean, committed source before acquiring
`tools/benchlock.sh`. The two copies preserve the feature-absent and feature-present
binary identities even though Cargo uses the same output filename.

```sh
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-652
export TMPDIR="$CARGO_TARGET_DIR/tmp"
export RUSTC_WRAPPER=''
mkdir -p "$TMPDIR" "$CARGO_TARGET_DIR/bin"
cargo test --features research-work --test gcd_profile
cargo test --features research-work --lib gcd_profile
python3 tools/test/gcd-size-study-test.py
cargo build -j4 --release --example gcd_routes
cp "$CARGO_TARGET_DIR/release/examples/gcd_routes" "$CARGO_TARGET_DIR/bin/gcd_routes-stock"
cargo build -j4 --release --features research-work --example gcd_routes
cp "$CARGO_TARGET_DIR/release/examples/gcd_routes" "$CARGO_TARGET_DIR/bin/gcd_routes-observed"
```

Use an available CPU and declare its actual affinity. The runner refuses dirty
source, output overwrite, excess ambient load, mismatched input digests, missing
profiles/RSS, violated degree bounds and disagreeing complete GCDs. It preserves
all child stops and refuses the next child after the aggregate campaign ceiling.

```sh
ZEEBRA_MACHINE=trpro-5995wx ZEEBRA_AFFINITY=2 \
  tools/benchlock.sh gcd-size-652 taskset -c 2 \
  python3 tools/external/gcd-size-study.py \
    --stock "$CARGO_TARGET_DIR/bin/gcd_routes-stock" \
    --observed "$CARGO_TARGET_DIR/bin/gcd_routes-observed" \
    --scratch /buildcache/cargo-target/zeebra-652/campaign-scratch \
    --output /buildcache/cargo-target/zeebra-652/campaign.json.gz \
    --max-load 4 --campaign-seconds 600
```

Use a fresh scratch/output path for each declared campaign. Never overwrite or
silently rerun a stopped/noisy attempt. All raw JSON, stdout/stderr, process wall,
RSS, stop reasons and binary/compiler/input identities stay in the gzip cohort.
All new figures must name the measured source commit; do not quote these commands
as measurements before the campaign has run.
