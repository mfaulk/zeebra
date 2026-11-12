# Public polynomial corpus: selection and verification

**Measured at:** `7cca5d7a4e723df51cf27a0e7b5eff14d059800f` (clean tracked tree).
The [inventory and definitions](../../research/public-corpus/README.md) document the pinned
upstream survey, original mathematical references, variable order, coefficient transformations,
and exclusions. This study adds six opt-in `Instance` values from three independently generated
families without changing the historical competitive ladder.

## Verification and measurement boundary

The [frozen campaign](../../research/public-corpus/results/public-679.json.gz) retains **54/54
successful attempts**: three fresh processes per case per engine for Zeebra, Singular build 44105,
and grobx. Every complete answer agrees coefficient-for-coefficient with the normalized reduced
basis supplied by Singular; fixture hashes bind the entire input ring and ordered generators.
The three smoke references also replay offline in ordinary Rust unit tests. Larger references are
committed, but their automated Zeebra replay is explicitly ignored unless requested.

Machine: Ryzen Threadripper PRO 5995WX, affinity CPUs 0–3, one solver worker, GF(32003), grevlex.
Build: rustc 1.99.1, release, fat LTO, one codegen unit, x86-64-v3, system allocator. Each attempt
has a 60-second/2-GiB solver limit and a 185-second/2-GiB complete-process-tree watchdog.
No attempt failed, refused the input, or crossed a limit. Canonical inputs, full answers,
engine versions, binary SHA-256, options, and statistics are inside the artifact. See the corpus
README for exact reproduction commands. Builds and tests ran outside the benchmark lock.

The table uses median native **F4 call** time, excluding parsing and reference comparison. RSS is
the maximum of the three native process high-water snapshots immediately after F4, before reference
verification. Whole-process-tree observations are separately retained and can undersample very
short processes. Singular/grobx adapters include different setup/output boundaries: their timings
are retained for audit, not interpreted as cross-engine speedups.

## Extra regimes

| Case | Variables | Batches | F4 ms | RSS MiB | Max rows / columns | Built / live peak entries | Row ops | Candidate rank sum | Worst fill ratio |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| eco-4 | 4 | 4 | 0.090 | 3.47 | 15 / 16 | 63 / 63 | 71 | 17 | 1.28 |
| noon-3 | 3 | 5 | 0.148 | 3.53 | 25 / 42 | 150 / 151 | 120 | 24 | 1.45 |
| reimer-3 | 3 | 8 | 0.206 | 3.53 | 23 / 30 | 217 / 224 | 312 | 33 | 1.28 |
| eco-8 | 8 | 15 | 11.516 | 4.89 | 515 / 514 | 13786 / 18948 | 57580 | 405 | 1.99 |
| noon-6 | 6 | 11 | 49.213 | 15.10 | 3817 / 4432 | 50448 / 393268 | 118502 | 751 | 7.80 |
| reimer-5 | 5 | 18 | 19.678 | 4.94 | 359 / 478 | 21191 / 32026 | 47548 | 282 | 2.48 |

Rows and columns are **independent maxima**, not necessarily a single matrix's dimensions.
Built and live entry peaks are also independent maxima. The last column is the largest
within-batch live/as-built ratio, from the paired `worst_fill_in_*` counters; it is not the ratio of
the previous column. Candidate rank sums count useful pair-row contributions across batches,
not the rank of a single matrix or the ideal's quotient dimension.

- **Eco:** coupled cubic equations plus an affine constraint. Eco-8 reaches roughly square,
  moderately sparse matrices; its exact quotient dimension is 64.
- **Noonburg:** symmetric cubic coupling, with parameter 11/10 explicitly cleared by an invertible
  factor 10. Noon-6 reaches much wider matrices and the strongest fill amplification of these
  additions, with quotient dimension 717.
- **Reimer:** increasing-degree alternating power sums. Reimer-5 reaches degree six at input and
  exercises more batches with a smaller quotient dimension, 144.

These differ from the existing Cyclic/Katsura/random-MQ mix. The larger three are useful short
performance controls, not replacements for MQ10's multi-second elimination workload. The smoke
cases are correctness checks; their sub-millisecond times are too close to startup and timer
floors for performance conclusions.

## CI budget and exclusions

The declared local execution budget for the complete new smoke/identity/reference test group is
**5 seconds**, excluding compilation. Five serialized, fresh-process debug test runs on the same
CPU set took **29.17–30.69 ms** total each, including the Rust test harness and `/usr/bin/time`;
maximum reported RSS was **47.15 MiB**. The [raw budget observations](../../research/public-corpus/results/smoke-budget.json)
record all five runs and the executable hash. These are local measurements, not a guarantee about
shared CI runners. CI executes the library smoke tests, the example reference-check test, and
transactional regeneration tests. No external solver is required for those new checks.

The inventory also reviews Chandra, Henrion, biology, chemistry, and classic candidates. Residue-like
exports with unestablished original definitions and model files with unresolved derivation or data
terms remain excluded. A repository-wide MIT license alone does not settle third-party data rights.
No excluded candidate bytes are committed. Physical-model provenance is not asserted for Reimer;
its independently defined benchmark equations and exact finite-field oracle are the retained identity.
No new competitive-history rows or cross-library speedup claims are introduced.
