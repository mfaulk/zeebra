# Giac subprocess acceptance (#740)

The registered Giac 2.0.0 adapter exposes modular reduced grevlex bases, with
explicit worker counts, generator round trips, full-output parsing and bounded
independent Singular verification. No external source is linked into Zeebra.

`PLAN.md` records the plan before the cohort. `manifest.json` fingerprints source,
binaries, loaded libraries, runtime packages, flags, CPU topology and load.
`cohort.json.gz` retains every attempt, complete basis and raw independent answer.
`table.md` is generated from it. No engine-internal timer or matched-ISA claim is
invented for the upstream Debian binary. Timing columns are Giac child process
wall/RSS; exact-verification elapsed and parent guard cost are separate artifacts.

Validate without installing an algebra engine or running measurements:

```sh
python3 -m unittest discover -s research/giac -p 'test_*.py'
python3 research/giac/summary.py > /buildcache/giac-table.md
diff -u research/giac/table.md /buildcache/giac-table.md
```

The existing `agent-scripts` CI job runs those checks. Rust adapter tests run in
the existing default external-runner suite; argument/cohort tests run in the
existing `competitive_sweep` example test target. The live Giac test is explicitly
ignored in ordinary CI because it requires both installed engines. Run it with:

```sh
cargo test --lib grobner::external::giac::tests::live_giac_bases_agree -- --ignored
```

Source at measurement: `fa0790de`, based on `55fef8d9`.
`source.patch` reconstructs the compiled Rust delta from that reachable main
baseline even after a squash merge. It changes only the five named Rust files.
For a new measurement, create a fresh worktree at `55fef8d9`, copy this directory
without `cohort.json.gz`, `manifest.json` or `table.md`, and apply the source
patch. Build outside the benchmark lock with Rust 1.99.1, release/fat LTO/one
codegen unit and x86-64-v3; use a private target and TMPDIR on `/buildcache`.
The runner refuses to overwrite a cohort or scratch directory.

Install the pinned Giac package and dependencies following the
[provisioning record](../../docs/research/external-comparands.md#giac-200-modular-subprocess).
For the local extracted layout used here:

```sh
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-740-reproduce
export TMPDIR="$CARGO_TARGET_DIR/tmp"
export RUSTC_WRAPPER=''
unset RUSTFLAGS
mkdir -p "$TMPDIR"
export ZEEBRA_GIAC=/buildcache/cargo-target/zeebra-740/giac/usr/bin/icas
export ZEEBRA_GIAC_LIBRARY_PATH=/buildcache/cargo-target/zeebra-740/giac/usr/lib:/buildcache/cargo-target/zeebra-740/giac/usr/lib/x86_64-linux-gnu
export ZEEBRA_SINGULAR=/usr/lib64/Singular/Singular
export SINGULAR_DATA_DIR=/usr/share
export ZEEBRA_MACHINE=zeebra-5995wx
git apply research/giac/source.patch
cargo build --release --locked --example groebner_comparison
python3 -m unittest discover -s research/giac -p 'test_*.py'
tools/benchlock.sh issue-740-giac-reproduce \
  timeout --signal=INT --kill-after=10s 3000s python3 research/giac/run.py \
  --binary "$CARGO_TARGET_DIR/release/examples/groebner_comparison" \
  --scratch "$TMPDIR/capture" --runtime-packages research/giac/runtime-packages.json
python3 research/giac/summary.py > research/giac/table.md
```

`runtime-packages.json` records the extracted Debian dependency package versions,
filenames and SHA-256s. Replace the installation paths and package manifest with the pinned
installation being reproduced; do not assume the local Fedora paths on another
machine. Inspect `lscpu` before reusing CPU2 / CPU2–5. The runner records actual
affinity and changes `ZEEBRA_AFFINITY` with each worker cohort. Child limits are
60 seconds / 2 GiB RSS for both engines, with the existing 185-second / 2 GiB
parent watchdog. The process pair runs sequentially; verification cannot be
reported as a successful Giac answer after a timeout or refusal.

The initial metadata preflight failed before any solver invocation because
Fedora's `/usr/bin/Singular` is an `exec` wrapper rather than an ELF executable.
`preflight-failure.txt` and `benchlock.log` retain that failure. The successful
capture explicitly fingerprints the native executable and its libraries.

The normalizer tests were written red before implementation. They check input
identity, exact coefficients, missing independent evidence, and task/order
binding. The checker also revalidates the independent generator echoes and
complete bases on every retained verified row. Limit stops/refusals contribute
no timing medians. Cross-engine ratios against historical cohorts, and general
worker scaling claims from startup-heavy controls, are outside this acceptance
study; #739 owns the broader scaling experiment.
