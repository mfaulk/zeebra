# MQ10 trajectory and coefficient-work attribution

Issue [#713](https://github.com/mfaulk/zeebra/issues/713); findings and counter
semantics are in [the report](../../docs/research/grobx-trajectory.md). No solver
optimization is selected here. Grobx instrumentation stays in its separate GPL
workspace; ordinary Zeebra builds never fetch or link it.

Decode the original retained evidence without computing a basis:

```sh
python3 tools/external/grobx-trajectory.py \
  research/competitive/results/grobx-683.json.gz \
  --output /buildcache/grobx-retained-trajectories.json
python3 tools/test/grobx-trajectory-test.py
python3 tools/test/grobx-work-study-test.py
```

Build and test **before** acquiring the machine-wide benchmark lock, with a private
build cache and temporary directory. `research-work` is off by default. Its scoped
`zeebra::linalg::work::measure` observer records one serial computation and resets
on return/panic; `mq10_profile --work` enables it. `--stages` enables existing stage
clocks and is used consistently in every Zeebra campaign arm.

```sh
export RUSTC_WRAPPER=''
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-713-stock
export TMPDIR="$CARGO_TARGET_DIR/tmp"
mkdir -p "$TMPDIR"
cargo build --release --example mq10_profile

export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-713-work-native
export TMPDIR="$CARGO_TARGET_DIR/tmp"
mkdir -p "$TMPDIR"
cargo test --features research-work --lib linalg::work
cargo test --features research-work --example mq10_profile
cargo build --release --features research-work --example mq10_profile
```

Provision the ordinary pinned driver using
`tools/external/provision-grobx.sh`. Separately build the research driver using
[its GPL-only provisioner](../../tools/external/grobx-driver/research/README.md).
Do not overwrite the stock binary. Keep its generated source manifest, patch and
recipe hashes with the cohort. Source/lock/compiler/settings/binary identities
are evidence, not inferred from executable names.

Commit the instrument before measuring. The runner refuses dirty sources, changed
ordered-input echoes, altered mathematical text, absent counters, changed paths,
unverified bases, missing RSS and budget violations. It reuses the existing
full-basis checker and process-tree RSS guard from `mq10-profile.py`. The reference
basis is the complete retained independently Singular-verified result, not just a
hash of leading terms. Verification runs after process timing. No profiling
records are appended to the competitive board.

```sh
ZEEBRA_MACHINE=trpro-5995wx ZEEBRA_AFFINITY=2 \
  tools/benchlock.sh grobx-713 taskset -c 2 \
  python3 tools/external/grobx-work-study.py \
    --zeebra-stock /buildcache/cargo-target/zeebra-713-stock/release/examples/mq10_profile \
    --zeebra-work /buildcache/cargo-target/zeebra-713-work-native/release/examples/mq10_profile \
    --grobx-stock /buildcache/cargo-target/zeebra-683-driver/release/grobx-driver \
    --grobx-work /buildcache/cargo-target/zeebra-713-grobx-final/build/release/grobx-driver \
    --scratch /buildcache/cargo-target/zeebra-713-study/native \
    --output /buildcache/cargo-target/zeebra-713-study/grobx-trajectory-native.json.gz \
    --repeats 5 --max-load 4
```

Substitute actual binary paths, machine identity and an available CPU. The runner
requires the declared comma-separated affinity to equal its inherited affinity.
Each field gets six arms, five fresh processes each: stock, observed build with
counters disabled, and observed build with counters enabled for each engine.
Engine/arm order reverses every repetition. Child budgets are 60 seconds/2 GiB;
the direct-child guard is tighter than the original comparison's 185-second outer
watchdog (there is no profiler or nested verification child in the timed group).
Ambient load above the declared gate refuses the next attempt and preserves the
partial cohort. Other failures/stops are retained and make the campaign fail;
no silent retries or deletion of noisy attempts.

Peak sparse entries, allocated slots and process RSS have different meanings.
Do not sum independently attained capacity maxima as a simultaneous peak or infer
physical memory traffic from logical scans/products. Native stage timings are
separate from process wall, and historical grobx/Zeebra cohorts never become a new
paired ratio. Larger-family adoption experiments belong to follow-up issues.

After the campaign, pack repeated full-basis literals without changing any response
bytes, then regenerate tables and verify every retained answer again:

```sh
python3 tools/external/study_artifacts.py \
  /buildcache/cargo-target/zeebra-713-study/grobx-trajectory-native.json.gz \
  research/competitive/results/grobx-trajectory-native.json.gz
python3 research/grobx-trajectory/summarize.py
python3 tools/external/proof_artifacts.py \
  research/competitive/results/grobx-trajectory-native.json.gz 5 \
  > /buildcache/grobx-713-response.json
```

The existing SHA-256 proof storage now accepts an explicit `basis` payload key,
including JSON arrays. Normal certificate packing defaults are unchanged. The
study loader restores both exact stdout and parsed response, checks payload hashes,
and preserves all failure/metadata fields. Four repeated basis literals are stored
once; packing is outside timing. `summary.json`, `summary.csv`, and
`summary-rounds.csv` are reproducible from the cohort. The committed
`builds.json` records each frozen Zeebra source/config fingerprint and binary hash;
the grobx research binary embeds hashes of every patched source and recipe.

The measured instruments precede the observer-only refusal cleanup in
`b37ea6d3`: it marks incomplete batches and permits a caught resource refusal to
be followed by another measured call. No native attempt refused; the retained
binaries and measured source stamps remain unchanged, and no post-cleanup timing
is claimed.

Frozen-source recovery uses `evidence/provenance.json`: check out its `base_commit`
and apply the SHA-256-checked `evidence/instrument.patch.gz` (decompress it before `git apply`). This reconstructs the
measured instrument tree even if intermediate branch commits disappear after a
squash. The stock library is the base source; the observed Rust/config tree is the
counter source identified in `builds.json`. This recovery stamp was collected
from git after the campaign and does not modify the original native record.
