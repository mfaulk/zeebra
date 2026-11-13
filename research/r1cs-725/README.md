# Bounded R1CS adapter gate and pilot (#725)

The gate precedes the Rust parser/converter: a pinned public R1CS example and an independently
compiled BN254 multiplier round-trip through the external `r1csfile` reader, while all 343
GF(7)^3 assignments agree between original rows and an independent polynomial prototype.
The typed Rust integration suite repeats the semantic comparison without that reader.

`manifest.json` pins the binary producer, source tags, reader source/package lock, circuit
source, generated R1CS/symbols/witness, and schema scope. `gate.json` and `oracle.json` retain
all coefficients, counts, mappings and canonical identities. The upstream reader and producer
are external reference programs; their implementations and generated JavaScript/WASM runtimes
are not dependencies of the Rust crate and are not copied into its source.

## Recreate the gate

Use private scratch outside the worktree. This example names the build-cache drive used for
the retained run; another writable private directory is suitable.

```sh
scratch=/buildcache/cargo-target/r1cs-reproduction
mkdir -p "$scratch"
git clone https://github.com/iden3/r1csfile.git "$scratch/r1csfile"
git -C "$scratch/r1csfile" checkout d82959da1f88fbd06db0407051fde94afbf8824a
(cd "$scratch/r1csfile" && npm ci --ignore-scripts --no-audit --no-fund)
python3 research/r1cs-725/gate.py --reader-repo "$scratch/r1csfile" \
  --output "$scratch/gate" > "$scratch/gate.json"
```

`gate.py` invokes our `reader-oracle.mjs` subprocess wrapper around the pinned external reader,
reconstructs canonical binary files, rereads them with that independent implementation, and
compares all header counts, coefficients and wire-label mappings. It also checks 1,029 GF(7)
row/assignment pairs and the independent producer witness with an invalid perturbation.
No external implementation is transcribed into the Rust parser.

## Regenerate the producer fixture

The compiler is the official Circom 2.2.3 Linux x86-64 release asset, pinned by SHA-256 in
`manifest.json`; its release tag names source commit
`ad44e915a12bb047b05745c2884aad9cc8326bc6`. The binary is pinned directly; no assertion of a
reproducible compiler build from that tag is made.

```sh
gh release download v2.2.3 --repo iden3/circom --pattern circom-linux-amd64 --dir "$scratch"
sha256sum "$scratch/circom-linux-amd64"
chmod +x "$scratch/circom-linux-amd64"
"$scratch/circom-linux-amd64" tests/fixtures/r1cs/multiplier.circom \
  --r1cs --sym --wasm --O0 -o "$scratch"
printf '%s\n' '{"a":"3","b":"5"}' > "$scratch/input.json"
node "$scratch/multiplier_js/generate_witness.js" \
  "$scratch/multiplier_js/multiplier.wasm" "$scratch/input.json" "$scratch/multiplier.wtns"
node research/r1cs-725/producer-witness.cjs "$scratch/multiplier_js" "$scratch/input.json" \
  > "$scratch/producer-witness.json"
```

The committed binary and symbols must retain the hashes in the manifest. The witness order is
`[1,15,3,5]`, produced by Circom's generated witness calculator and retained separately in
`producer-witness.json`. The circuit and both example input values are synthetic and public. `PrivateInput` describes
the R1CS declaration of `b`; it does not identify confidential input data in this fixture.

## Run the bounded pilot

Build/test first, outside the measurement lock. The ten declared cases include three complete
imports and seven explicit refusals. They are import/model/check tasks; no solving or witness
recovery is attempted. `run_pilot.py` uses one fresh process per case, a 60-second external child
timeout, and Linux `RLIMIT_AS=512 MiB`, a virtual-address-space ceiling stricter than an RSS cap.
It records native self-high-water RSS and the kernel child high-water returned by GNU `time`
separately. The harness wall includes GNU `time` startup; it is not an engine stage timer.
All outcomes, including refusals or timeouts, are written after each attempt.

```sh
export CARGO_TARGET_DIR="$scratch/target"
export TMPDIR="$scratch/tmp"
export RUSTC_WRAPPER=""
mkdir -p "$TMPDIR"
cargo test --no-default-features --test r1cs
cargo build --release --no-default-features --example r1cs_import
tools/benchlock.sh r1cs-pilot timeout --signal=INT --kill-after=10s 650s taskset -c 2 \
  python3 research/r1cs-725/run_pilot.py \
  --binary "$CARGO_TARGET_DIR/release/examples/r1cs_import" \
  --reader-repo "$scratch/r1csfile" --output "$scratch/pilot"
```

The source pin in each pilot manifest is the checked-out commit; retain a source patch and its
hash too if intentionally running a dirty tree. The retained pilot is an outcome/resource
observation, with no baseline wall-clock ratio, throughput claim or production break claim.
The exact named baseline is the original sparse R1CS row evaluator; the independent oracle is
the pinned external reader plus Circom's witness calculator. See the
[decision and outcome table](../../docs/research/bounded-r1cs.md).
