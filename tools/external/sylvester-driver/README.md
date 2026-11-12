# Pinned sylvester F4 driver

This isolated MIT workspace links sylvester 0.4.0 at
`ea34ddf3c9b9a275265576cd881c39c0c473e9f9` (MIT OR Apache-2.0). No upstream engine or verifier
source is copied into Zeebra, and the root runtime dependency graph is unchanged. The locked
transitive dependencies and Rust 1.99.1 toolchain are committed separately.

```sh
tools/external/provision-sylvester.sh
. tools/external/env.sh
```

Override `ZEEBRA_SYLVESTER_TARGET` to select a private build-cache directory (default
`/buildcache/cargo-target/zeebra-sylvester`). The script builds release/fat LTO/one codegen unit,
`x86-64-v3`, system allocator, then installs a symlink under `$ZEEBRA_EXT_PREFIX/bin`.
`--version` records revision, source/lock/toolchain hashes, effective compiler/profile flags and
binary build identity. `--startup` runs only the loader/identity path.

Contract 1 accepts a JSON path with ordered `variables`, `modulus`, `generators`, `order`
(`grevlex` only), `workers`, `mode` (`raw` or `certified`), `wall_ns` and optional `rss_bytes`.
The actual ring variables, modulus and parsed generators are rendered from upstream values.
Every computation explicitly requests `Backend::F4`; there is no classic or rational fallback.
F4 supports primes below 2^31. Raw mode reports the actual pool size; a smaller pool is not a
matched-worker result. Certified mode records a trace and is serial, so workers other than one
are refused before computing.

Raw mode returns the full monic reduced basis and its actual engine time. Certified mode calls
`groebner_basis_certified`: engine, trace/certificate writer and independent v2 verifier all run
inside that call. This API does not expose those three costs separately; the driver reports their
combined call cost rather than inventing a split. The driver then **replays verification** under
an explicit verifier deadline and matches the accepted modulus, variable count, original ordered
coefficient/exponent arrays (including zeroes and duplicates), and basis against the request.
Certificate bytes encode coordinate positions rather than variable names; the request's ordered
names are bound through its parsed ring and used to render the accepted coordinates.

The output contains the hexadecimal `sylv-gb-cert-v2` bytes, byte count, independent input/basis
binding result, actual workers and timings. `parse_ns` is ring/input construction; `engine_ns`
is the raw engine report or the integrated certified call; `binding_verify_ns` is the additional
independent replay/input check. `solve_ns` covers the operation through result rendering,
certificate encoding and binding. Final JSON encoding/stdout remain in process wall. Linux RSS
is read after a trial complete JSON encoding so fast children do not report only pre-main samples.
Internal estimated memory budgets and verifier caps are not RSS ceilings; the external supervisor
and parent process-group watchdog remain required.

Exhausted engine/writer/verifier budgets produce stops, separately from invalid certificates and
input/output mismatch. A stopped output has no accepted basis. The root adapter additionally
requires full reduced-basis agreement with the installed Singular reference, whose probed version
is retained in verification metadata. Certified records have a distinct objective/resource key,
so they cannot compare with Zeebra's raw output or different certification trust boundary.

```sh
CARGO_TARGET_DIR=/buildcache/cargo-target/sylvester-driver-tests \
  cargo test --locked --manifest-path tools/external/sylvester-driver/Cargo.toml
```

The workspace tests include both counterexamples from upstream `KNOWN_ISSUES.md`, checked again
against Singular by the adapter's live controls, plus nonradical, zero/unit and positive-dimensional
cases. They reject changed certificate input/modulus, tampered bytes, unsupported fields/orders
and serial-certification worker mismatches. `.github/workflows/sylvester-driver.yml` runs the
locked tests, Clippy and formatting without adding upstream builds to normal root-crate jobs.
