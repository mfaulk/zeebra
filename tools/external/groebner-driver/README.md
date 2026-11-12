# Pinned sdiehl/groebner driver

This independent workspace calls upstream `groebner_basis_f4(generators, true)` at
`c3e1d630fba9b2155a4c389d9022f13e0ba09218` (MIT, Stephen Diehl, 2025). No upstream source is
copied into Zeebra or linked into its runtime dependency graph. `Cargo.lock` pins transitive
packages; `rust-toolchain.toml` pins Rust 1.99.1. The default `parallel` feature is enabled;
`mimalloc`, `parameters` and `ffi` are disabled, using the system allocator.

Build from the repository root:

```sh
tools/external/provision-groebner-rs.sh
. tools/external/env.sh
```

Set `ZEEBRA_GROEBNER_RS_TARGET` to a private build-cache directory to override the default
`/buildcache/cargo-target/zeebra-groebner-rs`. The provisioner uses fat LTO, one codegen unit and
`x86-64-v3`, and installs a symlink under `$ZEEBRA_EXT_PREFIX/bin` (default
`$HOME/.local/opt/zeebra-ext/bin`). It does not build other comparands.

Driver contract 2 accepts a JSON file path, `--version`, or `--startup`. Input fields are ordered
`variables`, unsigned `modulus`, `order` (`grevlex`, `grlex`, `lex`), `workers` (1–1024), and
polynomial strings in `generators`. Output is JSON containing the parsed ring, generators rendered
from engine polynomials, the full canonicalized basis and leading monomials, actual pool workers,
upstream revision, allocator/features, compile-time ISA and a build identity hashing the driver,
manifest, lockfile, toolchain file and effective compiler/profile settings, plus `rustc -Vv`.

`parse_ns` includes ring/polynomial parsing, generator echo construction and pool initialization.
Input file reading and JSON decoding precede that timer and remain in child wall time. `solve_ns`
covers the upstream reduced-basis call. `serialization_ns` covers basis rendering and one trial
JSON encoding; final encoding, the kernel snapshot read and stdout transfer remain in child wall time. The loader-only
`--startup` command constructs no ring or pool. The prime-field F4 may use randomized row
combinations even with one worker. Every answer admitted by the Zeebra adapter must match an
independently computed full monic reduced basis, coefficient for coefficient; agreement of leading
monomials alone is insufficient. Verification time is recorded separately from child solve time.

Run unit tests with a private target directory:

```sh
CARGO_TARGET_DIR=/buildcache/cargo-target/groebner-driver-tests \
  cargo test --locked --manifest-path tools/external/groebner-driver/Cargo.toml
```

`.github/workflows/groebner-driver.yml` runs this workspace's locked tests, Clippy and formatting
checks on driver changes; root CI checks the adapter without downloading the upstream runtime.

On Linux, contract 2 also reports `kernel_peak_rss_bytes`, read from the child’s own `/proc/self/status`
after computation and serialization preparation. This prevents a fast solver from supplying only a
pre-main supervisor RSS sample. The adapter takes the maximum of this snapshot and any supervisor
observations, records the distinct `ChildSelfHighWater` basis and rejects an answer whose observed
high-water mark exceeds its requested cap. Final stdout/exit allocations follow the snapshot.
The loader-only startup command supplies the same kernel snapshot without constructing a ring.
