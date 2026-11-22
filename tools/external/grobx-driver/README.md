# Pinned grobx subprocess driver

This isolated **GPL-3.0-only** workspace links grobx and its independent checker at
`8005a2a1670a7264617a6f49eeb2618d7fa21701` (grobx 0.155.1). It contains original integration code and
copies no engine/checker implementation into Zeebra's MIT library. The root crate has no new
runtime dependency. The upstream license is available in the pinned Git checkout; distributing
the executable requires satisfying its GPL terms and those of its dependencies.

The pin moved from 0.73.3 (`1854835d`) to 0.155.1 in #987. Committed cohorts measured at 0.73.3
still replay: `wide-corpus.py` keeps both in `PUBLISHED_REVISIONS`, which replays accept, while a
live run accepts only the current `REVISIONS` entry.

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
(`raw` or `certified`), `wall_ns` (internal deadline), optional `rss_bytes` and optional
`digest_only` (boolean, default false). The pinned revision
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

**Digest-only replies (#1020).** With `digest_only: true` the reply's `basis` and `cofactors` are
`null`; it carries `basis_m33`, the `m33-basis-v1` digest of the basis text (the one
`tools/external/basis_digest.py` computes, and `research/m33-baseline/admission.py::grobx_digest`
reads in place of the text), its cost `basis_m33_ns`, and the texts' lengths `basis_bytes` and
`cofactors_bytes`. Certification is unchanged: the checker still rules inside `solve_ns`, and
`certified`, `flaw`, `stopped` and `report` are reported as before. The digest is computed after
`solve_ns` stops, so it is in process wall but not in-process solve time. grobx's API returns the
basis only as text, so its own render stays inside `solve_ns`; what leaves process wall is the JSON
encoding and printing of the texts — Eco-12's certified pair gzips to 1.70 GB, past `tools/bench-job`'s
1 GiB default output budget. A full reply is unchanged and carries no `basis_m33`.

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

The optional [passive-counter research workspace](research/README.md) builds a
separately identified copy for trajectory studies. It leaves this pinned driver
and normal provisioner unchanged, supports same-binary counters-on/off controls,
and reports explicitly bounded matrix storage snapshots. Its GPL source/recipe
hashes remain separate from Zeebra's MIT library; it is not installed over the
ordinary comparand.
