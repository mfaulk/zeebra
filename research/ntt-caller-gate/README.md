# NTT caller gate (#732)

The [research decision](../../docs/research/multicore-ntt.md) separates current
NTT callers from hypothetical transform arithmetic. `PLAN.md` predates the
measurements; `manifest.json` binds input/source/binary identities;
`records.json` names every attempt and hashes its retained stdout/stderr/time
files. `table.md` is generated from those records. This is serial profiling,
with no parallel implementation or measured worker crossover.

Validate the retained cohort without building Rust or running benchmarks:

```sh
python3 -m unittest discover -s research/ntt-caller-gate -p 'test_*.py'
python3 research/ntt-caller-gate/summary.py > /buildcache/ntt-caller-table.md
diff -u research/ntt-caller-gate/table.md /buildcache/ntt-caller-table.md
bash tools/check-measurement-provenance.sh docs/research/multicore-ntt.md
```

The existing `agent-scripts` CI job runs the analysis tests and regenerates the
table. It does not run measurements on shared CI hardware. The profile analysis
was tested red before implementation: missing module, then passing tests; the complete-call parser likewise failed before its implementation.
No core arithmetic, scheduling behavior or public API changed, so no new Rust
behavior tests or changes to production file-level comments are needed.

To reproduce, use a **fresh worktree at the manifest's source revision**, copy
this research directory into it (without `raw/`, `manifest.json`, `records.json`
or `table.md`), and run from its root. The script refuses to replace `raw/`.
Preserve the old dataset rather than overwriting it. Match the recorded Rust
compiler/lockfile/configuration, inspect CPU topology before reusing CPU2, and
build/test outside the benchmark lock:

```sh
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-732-reproduce
export TMPDIR="$CARGO_TARGET_DIR/tmp"
export RUSTC_WRAPPER=''
mkdir -p "$TMPDIR"
# No environment RUSTFLAGS: use the pinned .cargo/config.toml ISA flags.
unset RUSTFLAGS
git apply --check research/ntt-caller-gate/probe.patch
git apply research/ntt-caller-gate/probe.patch
cargo build --release --locked --example graeffe_root
python3 -m unittest discover -s research/ntt-caller-gate -p 'test_*.py'
tools/benchlock.sh issue-732-serial-caller \
  timeout --signal=INT --kill-after=10s 360s taskset -c 2 \
  python3 research/ntt-caller-gate/run.py \
  --binary "$CARGO_TARGET_DIR/release/examples/graeffe_root" \
  --scratch "$TMPDIR/identities"
git apply -R research/ntt-caller-gate/probe.patch
python3 research/ntt-caller-gate/summary.py > research/ntt-caller-gate/table.md
```

The patch changes **only the example**, before its call timer (optional identity
serialization) and after verification (exact existing timer/counter/answer
reporting). Identity runs are separate from the timing cohort. Timing runs do
not serialize input. Every root is checked by the existing `f.eval` assertion;
all complete returned roots are retained in `GATE` lines. Canonical input SHA-256
encoding is decimal coefficients in ascending power order, each followed by LF;
the modulus and seed are bound separately in the manifest. Large input text is
regenerated, hashed and deleted, not committed. No arbitrary external instance
or full cryptanalytic solve is implied by this planted-root workload.

Each child has a 60-second external timeout and hard 2 GiB address-space limit.
The address-space guard also limits resident allocation; it is not RSS
measurement. GNU time reports full-process wall/user/system/RSS separately.
Failed attempts are retained and stop the campaign; analysis refuses them.
Forward stage wall includes non-NTT work and is only an optimistic Amdahl input.
Sub-millisecond GNU time values round to hundredths; exact caller timers use
nanoseconds. No adoption claim can be based on rounded process times.

`benchlock.log` is the campaign's excerpt from the shared lock log. Topology,
load and actual single-core affinity are captured **inside** the lock in the
manifest. Release uses fat LTO, one codegen unit, x86-64-v3. The reporting patch
and original example are independently fingerprinted; production sources stay
at the pinned revision. Historical #591 timing figures retain their original
pins in the linked research note and are not rerun or relabeled as current.
