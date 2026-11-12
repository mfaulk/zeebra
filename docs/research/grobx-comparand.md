# The pinned grobx comparand (#683)

**Measured at:** `da827a92`, 2026-11-11. The production Rust source is unchanged from
`db17bb51`; the intervening commit adds the absent-executable test only. Later commits package
proof artifacts losslessly and add the follow-up described below; they do not relabel this run.
**Source:** grobx `1854835dbc25f24dc9a9ba017024d5030e99da1c` (0.73.3, GPL-3.0-only), exclusively
in a standalone subprocess workspace. No engine/checker source enters the MIT root library.

## Identity, build and exact evidence

The [driver contract](../../tools/external/grobx-driver/README.md) pins source, transitive lock,
Rust 1.99.1, release/fat LTO/one codegen unit, `x86-64-v3` and upstream's small-block mimalloc /
large-block system allocator. The retained driver build identity is
`9267861f330b88263c44c1b25bca45e052a991df9e9868e3321401f785e883f8`.
Source/lock/compiler/settings hashes are in its version response, not inferred from a path.

The engine and separate checker parse each original generator, including zero and duplicate
positions. Their monic echoes must agree and must match the requested polynomial up to a nonzero
field scalar. Exact modular cross-products avoid division and retain 64-bit residues. The engine
receives the original, unnormalized input text. Requested variable order and field are retained,
and the engine report independently supplies the parsed count/characteristic and actual trajectory.

Every admitted small-field answer matches the full monic reduced basis from **Singular build
44105**, recorded in verification metadata. Matching leading monomials alone is insufficient.
Wide raw results require a second exact cofactor-certified run and full-basis equality; the checker
uses independent arithmetic and verifies both inclusions, Buchberger's criterion and reducedness.
The live adapter test covers both wide controls successfully outside the timed single-core cohort.
That is correctness evidence, not a wide-field timing result.

The revision computes on one thread despite accepting a thread allowance. Multiworker requests
are refused. Seed is zero. `grobx` is raw reduced-basis computation; `grobx-certified` includes
cofactor tracking, text generation and exact checking. The latter adds
`objective=exact-certified-basis` to the resource key. No raw/certified ratio, or comparison with
Zeebra's different certification trust boundary, is admitted by the board.

## Initial bounded cohort

[Retained cohort](../../research/competitive/results/grobx-683.json.gz): 92 attempts, three
repetitions per cell with alternating engine order. Public Katsura-4, Cyclic-5, MQ6 and MQ10 at
32003 and 2147483647, plus both existing two-variable wide controls. Inputs reuse the published
corpus digests; each attempt retains the full basis, exact driver response and startup observation.

Machine: Threadripper PRO 5995WX, `ZEEBRA_MACHINE=trpro-5995wx`, `ZEEBRA_AFFINITY=2`, one
worker, actual launcher affinity checked, under `tools/benchlock.sh`. Builds/tests finished first.
Every measured subprocess has a 60 s wall / 2 GiB RSS cap. The complete harness process group,
including subsequent verification, has a 185 s / 2 GiB parent watchdog. A new process per engine
and digest makes self high-water RSS attributable. No challenge or private instance is used.

| arm | answered | harness failures | deliberate resource stops |
|---|---:|---:|---:|
| current Zeebra defaults | 30 | 0 | 0 |
| grobx raw | 21, all verified | 9 | 2 |
| grobx exact-certified | 22, all verified | 8 | 0 |

All 17 failures say **cannot enforce RSS cap without a process RSS reading**. They are failures
of the harness's ability to observe/enforce the declared cap, not wrong answers from the engine.
They remain in history. In particular, all raw wide attempts in this cohort are inconclusive;
no wide timing ratio is claimed. Tiny controls also remain subject to the startup-floor gate.
The resource controls requested zero RSS and zero wall budgets and were correctly retained as
stopped, with no timing answer. Current Zeebra means the shipped reduced-batch/ByOrder F4 settings,
not the historical division/echelon baseline.

## The substantial raw task, separately from proof cost

The following are **medians of three complete reduced-basis attempts per arm**, paired within the
initial cohort. The grobx wall includes loader, parsing, calculation and output; independent
Singular verification runs afterwards and is separately timed. Both full bases agree. MQ10 clears
the startup floor on both operands; these ratios do not divide a process wall by an engine stage.

| MQ10 characteristic | Zeebra basis wall | grobx raw child wall | Zeebra / grobx | Zeebra peak RSS | grobx raw peak RSS |
|---|---:|---:|---:|---:|---:|
| 32003 | 4 193.588 ms | 345.727 ms | 12.13x | 137.61 MiB | 16.18 MiB |
| 2147483647 | 4 502.757 ms | 162.977 ms | 27.63x | 138.71 MiB | 16.46 MiB |

RSS is the median of attributable per-process kernel high-water marks. The child supplies its
own post-computation/post-encoding snapshot, combined with supervisor samples. Fast-child missing
samples still cause the conservative failures above. CPU tick quantization remains visible; a
zero tick count is not free calculation. Three repetitions and two fields establish these cells,
not universal performance or a new cryptanalytic frontier. Grobx signatures/handover and allocator
are its own defaults, disclosed in the report; this experiment does not attribute the gap to one
mechanism or authorize GPL implementation copying.

Proof is a stronger objective, with its own retained costs:

| MQ10 characteristic | certified child wall | certified peak RSS | uncompressed cofactor text |
|---|---:|---:|---:|
| 32003 | 14 898.399 ms | 152.86 MiB | 49 883 046 bytes |
| 2147483647 | 15 049.225 ms | 164.42 MiB | 63 047 779 bytes |

These are not raw-basis comparand times. `certified-total` includes upstream cofactor tracking,
writing and exact checking; `independent-verification` additionally records the subsequent full
Singular cross-check. Certification changes the engine trajectory: cofactor tracking disables
handover. The raw `solve` stage alone enters the engine-internal ratio selector. The complete
engine report is retained rather than substituting guessed Zeebra stage names for it.

## Proof storage and reproduction

The compressed cohort contains every row and attempt. Repeated proof JSON literals are stored
once by SHA-256 in [`grobx-683-proofs`](../../research/competitive/results/grobx-683-proofs).
Each response retains its exact prefix and suffix. The reconstruction helper checks the payload
hash and restores the original child JSON byte for byte; packing changes no measurement or
certificate. The helper tests escaped text, repeated payloads, compressed cohorts and tampering.

```sh
python3 tools/external/proof_artifacts.py research/competitive/results/grobx-683.json.gz 11 \
  > /buildcache/cargo-target/grobx-certified-response.json
```

Provision the pinned driver and build `grobx_comparison` in release before acquiring the lock.
The [adapter guide](../guide/external-engines.md#grobx) gives the full commands. Use one engine
and one digest per process, set `ZEEBRA_MACHINE`/`ZEEBRA_AFFINITY`, pin the launcher, and retain
refusals. `tools/external/grobx-cohort.py` produces the three-repetition campaign and optionally
appends history. `cargo run --release --example competitive -- --write` regenerates the board
without measuring. Normal library builds never fetch grobx.

The initial failed tiny cells motivate an additional affinity/control observation, not deleting
those failures or interpreting a missing RSS sample as a small engine memory footprint. The
remaining performance question is a current-default stage profile explaining the raw MQ gap;
the old interreduction share cannot answer it after the algorithm changed.

## Small-control follow-up

**Measured at:** `ee4905fa`, same pinned driver and production Rust, using
`ZEEBRA_MACHINE=trpro-5995wx`, `ZEEBRA_AFFINITY=0-3`, **one worker**. Four allowed CPUs are an
affinity set, not a four-worker computation. The [29-attempt follow-up](../../research/competitive/results/grobx-683-small.json.gz)
uses `--small-controls-only`: Katsura-4 at 32003 and both wide controls, three alternating repeats,
plus two deliberate stops, with the same child/parent caps.

All nine Zeebra attempts completed; all nine raw and nine certified grobx attempts passed exact
verification, including the independent two-inclusion cofactor checker at both wide primes. The
two resource controls stopped. This supplies retained wide-field correctness evidence without
removing the original single-core harness failures. The changed affinity is kept in a distinct
cohort and does not explain the original observation by itself. No timing or memory ratio pools
the cohorts, and these tiny cells do not clear the process startup floor.
