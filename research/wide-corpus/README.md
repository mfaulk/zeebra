# Hard wide-field corpus (#738)

**Measured at:** `4ea1463a` and `fa7cc30d`; native binary source `4ea1463a`.

This opt-in catalog freezes `wide64` (`18446744073709551263`), `goldilocks`
(`18446744069414584321`) and `bn254` (BN254 scalar r, decimal in the catalog).
Every entry in [cases.json](cases.json) retains the full generators, ordered variables,
transformation, canonical bytes and SHA-256 digest. The `wide-corpus-v1` identity uses a decimal
prime and grevlex; it is separate from the historical competitive `Instance::canonical` format.
[BOARD.md](BOARD.md) is regenerated from [campaign.json.gz](campaign.json.gz).

| Family | Both 64-bit fields | BN254 capability only |
|---|---|---|
| Katsura | `katsura-{4,9,11,14}` (4 is the startup control) | `katsura-9` |
| Cyclic | `cyclic-{7,11}` | `cyclic-7` |
| Dense random MQ | `mq-random-{10,11,12,14,16}` | `mq-random-10` |
| Eco | `eco-{12,14,18}` | `eco-12` |
| Noonburg | `noon-{7,8,11}` | `noon-7` |


## Measured findings

The retained campaign has **141 unique attempts: 74 completions and 67 limit stops**.
All 70 completed 64-bit answers on the 19 identities with multiple completing engines agree
coefficient for coefficient after normalization. Grobx alone completes `mq-random-12` at
`2^64 - 353`; that answer has no independent live oracle. BN254 has three native completions
(Katsura-9, Cyclic-7, Noon-7) and two 65-second runner stops (MQ-10, Eco-12), with no external oracle.

Each of the five families at each 64-bit field has at least one Zeebra/native-comparand wall ratio
above **both** engines' 2× startup-floor gate. All 24 eligible native ratios in this single-sample
campaign exceed one: the easy planted-MQ advantage does not carry over to these observations.
The table shows Zeebra/comparand wall; values above one mean Zeebra took longer.

| Rung | Z/rs, 2^64−353 | Z/grobx, 2^64−353 | Z/rs, Goldilocks | Z/grobx, Goldilocks |
|---|---:|---:|---:|---:|
| katsura-11 | 11.062x | 42.550x | 11.621x | 45.198x |
| cyclic-7 | 2.573x | 4.322x | 3.201x | 4.838x |
| mq-random-10 | 7.295x | 22.433x | 7.761x | 26.059x |
| eco-12 | 11.663x | 21.366x | 12.296x | 22.341x |
| noon-7 | 3.242x | 20.414x | 3.264x | 21.064x |

Dense MQ-11 clears the requested hard-rung target with margin: the fastest completing comparand
is grobx at **2.925 s** (`2^64−353`) and **3.326 s** (Goldilocks). Julia, groebner-rs and grobx
agree on both full bases; Zeebra reaches the 65-second runner watchdog. At Goldilocks MQ-12,
groebner-rs completes in 57.319 s and agrees with grobx, close to its 60-second ceiling.
Katsura-14, Cyclic-11, MQ-14/16, Eco-14/18 and Noon-11 retain all external limit-stop outcomes.
Zeebra's named internal stops include 32 million live nonzeros and 200,000 symbolic rows.

Julia's Katsura-4 process controls are 8.187 s and 8.044 s. Every rung where both Zeebra and Julia
complete remains below Julia's 2× process-startup gate; their wall ratios are withheld.
Native driver controls are about 6 ms. Engine-call times remain in the archive; they are never
substituted for Julia process wall to make a wall ratio pass.

Machine: AMD Ryzen Threadripper PRO 5995WX, host `fedora`, affinity CPU 2, one solver worker.
Zeebra uses release/fat LTO/codegen-units=1/x86-64-v3. Executable hashes, compiler, native driver
revision/build/allocator data and full limits are retained in the archive. These are single
observations, not repeated-run estimates of a general speedup or slowdown.

The controller continued from `4ea1463a` to `fa7cc30d` to accelerate archival compression outside
solver measurements. Saved attempts retain their original stamps, both controller headers retain
base-commit/patch provenance, and native binary hashes and all resource settings match exactly.
The old controller was stopped between solver processes; no active engine was interrupted for
this continuation. [Benchmark-lock records](benchmark-lock.log) retain the serialized run lifecycle,
including the separate initial adapter failure. The final controller exits normally after all 141
attempts and their full-basis checks.

Katsura names count variables, so `katsura-9` is literature Katsura-8. Cyclic-7 and Cyclic-11
are squarefree-size affine systems, without field equations or slicing. Eco and Noonburg use
`grobner::benchmark_systems`' independently defined equations; Noonburg's parameter is 11/10,
with each equation multiplied by 10. See the [public corpus definitions](../public-corpus/README.md).
Random MQ uses n equations in n variables, **all** monomials of degree ≤2, each with a nonzero
coefficient sampled from the full field using `StdRng` seed `0x73800000 + n`. No solution is
planted. This is a distinct identity from the historical term-capped `mq-random-n` ladder.
The catalog includes intermediate candidates and upper rungs intended to hit the resource boundary;
size alone is not an observed completion or a performance claim.

The native Rust comparands run their pinned drivers directly. Their standard adapters otherwise
run extra Zeebra/cofactor computations after the measured solve; on new widths, that can reject
a completed answer solely because the adapter's built-in verifier has no compiled instantiation.
The campaign binds the ring, ordered generator echoes, revision, ISA and build profile, retains
raw responses, and checks full reduced bases independently across engines. Polynomial comparison
reduces coefficients modulo the full declared prime and normalizes to monic grevlex form.
The [initial adapter failure](adapter-failure-738.json.gz) retains the Katsura-9 case that exposed
this verifier-width limitation; it is excluded from the final campaign and ratios.

The live-oracle provenance is the campaign's complete normalized bases from Groebner.jl,
groebner-rs and grobx, with versions and executable hashes. Every completed answer must agree
coefficient for coefficient with every other completed answer on that identity. BN254 is a native
Zeebra capability row with **no external oracle**: the current external contract stores its prime
in `u64`. No ratio or correctness claim based on an independent engine is made for that field.

Provision Groebner.jl, groebner-rs and grobx using the
[external-engine guide](../../docs/guide/external-engines.md) before running the campaign.
Build and test outside the benchmark lock:

```sh
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-738
export TMPDIR="$CARGO_TARGET_DIR/tmp"
export RUSTC_WRAPPER=""
mkdir -p "$TMPDIR"
. tools/external/env.sh
cargo test --example wide_corpus
python3 tools/test/wide-corpus-test.py
cargo build --release --example wide_corpus
"$CARGO_TARGET_DIR/release/examples/wide_corpus" --list
```

Measure a committed, clean instrument. One worker, one case/engine per fresh process, grevlex,
60 s / 2 GiB solver budgets. Direct native drivers have a 60 s / 2 GiB process-tree watchdog;
the Zeebra/Julia runner has a 65 s / 2 GiB tree watchdog to allow harness overhead. Watchdog kills
are recorded
with their specific cause, never as engine completions. Interrupting the controller reaps its
isolated solver process and leaves the last atomic checkpoint intact. F4 also has a cooperative live-byte budget;
the watchdog covers memory outside its matrices. The tree RSS observation sums process high waters
and can conservatively stop earlier than a live-RSS sum. Sampling can miss short-lived peaks;
retained kernel high-water snapshots also enforce the ceiling
after a completed child exits, so a missed poll cannot turn a recorded overrun into timing evidence.
The Julia adapter also enforces its 2-GiB subprocess RSS ceiling. Native drivers are supervised
directly; their process wall excludes separate verification computations.
Normal resumption requires the same controller commit. `--continue-controller` is reserved for an
explicitly audited controller update outside the timed solver sections; it still requires identical
executables, machine/CPU, affinity, compiler/build settings, workers and limit policy. Every attempt
retains its originating controller commit, and the archive keeps both complete controller headers
with base-commit/patch provenance. The native binary source stamp is retained separately. Use a fresh
output path for a new instrument; the retained publication archive is not overwritten on replay.
F4 retains its default matrix/nonzero limits as well as the wall/live-byte budgets; all options
and the precise internal limit responsible for a stop are recorded.

```sh
WIDE_CAMPAIGN_OUTPUT="$CARGO_TARGET_DIR/replay.json.gz"
ZEEBRA_MACHINE="$(hostname)" ZEEBRA_AFFINITY=2 \
  tools/benchlock.sh hard-wide-738 timeout --signal=INT --kill-after=60s 7200 \
  taskset -c 2 python3 tools/external/wide-corpus.py \
  --binary "$CARGO_TARGET_DIR/release/examples/wide_corpus" \
  --scratch "$CARGO_TARGET_DIR/campaign" \
  --output "$WIDE_CAMPAIGN_OUTPUT"
python3 tools/external/wide-corpus.py --pack "$WIDE_CAMPAIGN_OUTPUT" --output "$WIDE_CAMPAIGN_OUTPUT"
# Regenerate the published board from its retained evidence:
python3 tools/external/wide-corpus.py --summarize research/wide-corpus/campaign.json.gz
```

Use `--fields wide64,goldilocks` or `--rows katsura-4,mq-random-12` for bounded subsets.
Retain Katsura-4 for each engine/field if publishing ratios. The board requires both operands ≥2×
that engine's measured startup control. Native wall is the complete runner process (including
input/output); external wall is the adapter's supervised engine process, excluding version probes.
Wrapper wall and F4-call timings are separately retained. A single observation does not establish
a stable speedup. Rows with one completion have no independent live oracle, and stops do not
become ratios. A guardian stop also overrides any successful response arriving at its deadline.
At least one external completion is needed for a verified Zeebra comparison.

Intentional regeneration after changing a definition:
`python3 tools/external/wide-corpus.py --binary "$CARGO_TARGET_DIR/release/examples/wide_corpus" --freeze`.
Checkpoint writes use fast compression outside solver wall measurements; final payload chunks
use full compression. Complete basis responses can exceed GitHub's single-file limit. `--pack` replaces the main gzip
with a manifest and writes content-addressed payload chunks under `campaign-payloads/`, each at
most 16 MiB before compression. `load()` in the campaign tool checks every chunk's SHA-256 and
length, reconstructs the original attempts, and verifies a lossless round trip. Native report copies
share the raw response's basis and are restored from it; the raw JSON values are preserved exactly. Scaling-study flat basis copies and parsed native
JSON are likewise restored from the exact stdout response. Existing `proof_artifacts.py` stores
repeated native basis literals once by content hash across attempts; its SHA-256 is checked on replay.
The summary command
accepts both unpacked campaigns and this manifest. Raw native responses and full bases remain
available; no coefficients are discarded. Commit the manifest and its payload directory together.

Review the full catalog diff and remeasure; never update pins to accommodate stale evidence.
CI runs the generator and gate tests plus offline catalog integrity checks; external solvers and
long resource-boundary runs are opt-in and are not required on GitHub Actions. Published source
packages omit research data, so the fixture replay is skipped only when those files are absent
outside a Git checkout.
