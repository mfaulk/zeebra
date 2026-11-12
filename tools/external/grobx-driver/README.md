# Pinned grobx subprocess driver

This isolated **GPL-3.0-only** workspace links grobx and its independent checker at
`1854835dbc25f24dc9a9ba017024d5030e99da1c`. It contains original integration code and
copies no engine/checker implementation into Zeebra's MIT library. The root crate has no new
runtime dependency. The upstream license is available in the pinned Git checkout; distributing
the executable requires satisfying its GPL terms and those of its dependencies.

```sh
tools/external/provision-grobx.sh
. tools/external/env.sh
```

The provisioner pins Rust 1.99.1 and Cargo.lock, uses release/fat LTO/one codegen unit and
`x86-64-v3`, and installs a symlink under `$ZEEBRA_EXT_PREFIX/bin`. Override the target with
`ZEEBRA_GROBX_TARGET` (default `/buildcache/cargo-target/zeebra-grobx`). Build and temporary output
stay off the system drive. The driver uses upstream's allocator: mimalloc for small blocks and
the system allocator for large blocks. Build metadata hashes source, manifest, lock, toolchain,
compiler and effective settings; `--version` emits it, while `--startup` measures loader cost.

Contract 1 accepts one JSON file: `variables` (ordered names), `modulus` (u64 prime), `order`
(`grevlex` or `lex`), `generators` (expanded polynomial strings), `workers` (exactly 1), `mode`
(`raw` or `certified`), `wall_ns` (internal deadline) and optional `rss_bytes`. The pinned revision
computes serially even when given a larger thread allowance; the adapter refuses multiworker
cohorts. Seed is fixed at zero and the complete engine report retains signatures, handovers,
field kernel, orders and phases. No cheap/probabilistic certification objective is exposed.

Before solving, each original generator is parsed separately by the engine and independent
checker, preserving positions, duplicates and zeroes. Both return monic nonzero generator echoes;
the adapter checks each against the original up to a nonzero field scalar, using exact modular
cross-products and explicit variable tokens. This normalization is diagnostic only: computation
receives the original generator list and ordered header unchanged. The original request, exact
text and text SHA-256 are retained. The engine's report independently supplies its parsed
variable count and characteristic.

`parse_ns` includes those parser checks. `solve_ns` surrounds the whole upstream call: raw mode
computes a reduced basis, certified mode additionally tracks cofactors, writes them and performs
exact independent checking. JSON decoding, final output and parser work remain in process wall.
A certified result requires `certified=true`, no stop, a complete basis and completed report;
`null`, rejection and resource exhaustion are not answers. Raw and certified IDs/limits differ,
so the board cannot silently compare certified cost with raw computation. Certificate/report text
is retained in the per-attempt artifact. The Linux child self high-water snapshot complements
supervisor RSS sampling; the internal memory/deadline checks do not replace the external watchdog.

```sh
CARGO_TARGET_DIR=/buildcache/cargo-target/grobx-driver-tests \
  cargo test --locked --manifest-path tools/external/grobx-driver/Cargo.toml
```

`.github/workflows/grobx-driver.yml` checks locked driver tests, Clippy and formatting separately;
normal root builds never fetch upstream. Root adapter unit tests need no external executable;
the ignored live test requires this pinned driver and Singular.

Large retained cofactor literals are stored losslessly in gzip sidecars by the cohort tool.
`python3 tools/external/proof_artifacts.py COHORT.json.gz INDEX` restores the original response,
checking its content hash; the cohort's prefix and suffix preserve the exact original JSON bytes.

For the separately identified #713 passive-counter build, see
[`research/README.md`](research/README.md). It preserves the stock provisioner and adapter contract;
its opt-in diagnostics are research artifacts, not a replacement competitive-board engine.
