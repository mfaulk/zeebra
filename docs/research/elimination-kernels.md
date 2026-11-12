# Elimination kernels: skip the untouched sparse prefix

**Measured at:** `cc6916fc` (baseline) and `dd36652e` (final prefix-only kernel).
Earlier prototypes: `220a99f1` and `cc993a00`. Build metadata inside each artifact records full
commits, rustc identity and executable SHA-256 values. Focused repeats use runner `62c252d3` with
the same frozen baseline/final binaries. Campaign date: 2026-11-12 (UTC).

## Decision and scope

Keep the generic prefix-only merge. During sparse back-substitution, a pivot cannot change target
entries to the left of its leading column. The previous kernel nevertheless merged and copied the
entire target. The new kernel finds that boundary, merges only the tail into reusable scratch,
truncates to the untouched prefix and copies the tail back. Each row retains its own buffer and
scratch stays caller-owned, preserving #554's capacity safeguard. Field arithmetic, pivot order,
F4 strategies and live-entry limits retain their exact observable results.

This implements the focused sparse-row/back-substitution arm of #269. The
[current-default profile](mq10-current-profile.md) selected this hotspot. The new
[verified public families](public-polynomial-corpus.md) supply additional controls: their negative
results on earlier prototypes helped reject unnecessary second-bound searches and splicing.
Broader #269 work on controlled density curves and coefficient-specific kernels remains open.

## Protocol and retained evidence

Ryzen Threadripper PRO 5995WX; rustc 1.99.1; release, fat LTO, one codegen unit, x86-64-v3,
system allocator; one solver worker. Main cohorts have affinity CPUs 0–3. Baseline and candidate
alternate order between repetitions, with a fresh process for each attempt. Builds, tests and
analysis ran outside the measurement processes; builds/tests never overlapped the benchmark lock.
Each complete process tree has a 185-second/2-GiB watchdog. Public/classical solves and matrix
captures additionally have a 60-second solver limit; MQ10 uses its existing default-strategy
instrument with the outer watchdog. Stage clocks are enabled on both full-solve arms.

The final [solve](../../research/row-merge/results/native-solves.json.gz),
[matrix](../../research/row-merge/results/native-matrices.json.gz),
[diagnostic](../../research/row-merge/results/native-work.json.gz), and
[hardware-counter](../../research/row-merge/results/native-counters.json.gz) cohorts retain
**290/290 successful attempts**: 120 full solves, 150 matrix replays, eight diagnostic replays,
and 12 separately profiled solves. Four focused cohorts add **120/120** successful attempts.
No resource stop, process failure, input drift, full-basis mismatch or RREF mismatch occurred.

Every full basis is checked coefficient-for-coefficient against either the public corpus's frozen
Singular 44105 answers or the previously independently verified grobx records. The corrective
`grobx-683-small` record supplies small-prime Katsura-4, whose earlier grobx attempt failed.
Every matrix's pinned input fingerprint, complete RREF hash and rank agree across arms and
backends. Full-solve batch/row-operation/matrix-size/live-entry counters also agree across arms.
No competitive-history row was edited or appended.

See the [experiment README](../../research/row-merge/README.md) for build/snapshot commands,
resource boundaries and phase selection. `b3641ded` contains the snapshot runner and has identical
Rust sources, Cargo manifest and examples to the recorded `cc6916fc` baseline; use it to rebuild
that baseline with snapshot tooling. Final Rust sources are unchanged after `dd36652e`.

## Full-pipeline result

Median native F4 call time in milliseconds, five runs per arm. Parsing, basis rendering and
reference checking are outside the F4 timer. RSS is the maximum process high-water snapshot from
those five runs. Public/classical snapshots precede reference checking; MQ10's existing instrument
snapshots after basis rendering. Process-tree observations are retained separately, not substituted
for these self snapshots. These are consistent boundaries within each comparison.

| Case | F4 ms, baseline → final | Peak RSS MiB, baseline → final |
|---|---:|---:|
| public-eco-4 | 0.089 → 0.091 | 3.52 → 3.46 |
| public-noon-3 | 0.158 → 0.154 | 3.66 → 3.62 |
| public-reimer-3 | 0.198 → 0.223 | 3.64 → 3.68 |
| public-eco-8 | 11.691 → 11.302 | 4.82 → 4.77 |
| public-noon-6 | 49.262 → 48.499 | 16.04 → 15.03 |
| public-reimer-5 | 18.215 → 16.863 | 5.00 → 5.25 |
| mq10/32003 | 4372.139 → 2940.117 | 134.54 → 134.33 |
| cyclic-5/32003 | 0.829 → 0.821 | 4.17 → 4.23 |
| katsura-4/32003 | 0.155 → 0.148 | 4.04 → 4.04 |
| mq10/2147483647 | 4658.384 → 3092.643 | 135.60 → 135.55 |
| cyclic-5/2147483647 | 0.853 → 0.904 | 4.16 → 4.19 |
| katsura-4/2147483647 | 0.161 → 0.151 | 4.02 → 3.95 |

MQ10 improves **32.8%** at GF(32003) and **33.6%** at GF(2147483647), or about 1.49×/1.51×.
Every one of the five paired MQ10 runs improves. Baseline/candidate ranges are 4.356–4.375 s /
2.936–2.966 s at the small prime and 4.628–4.709 s / 3.088–3.101 s at the larger prime.
The 9,943,484 / 9,943,743 row operations are unchanged. Peak RSS stays approximately 135 MiB.
All three larger public-family controls improve by their main-cohort medians. Sub-millisecond
smoke/classical controls remain correctness checks; their small absolute changes and cold-process
variability do not establish performance wins or losses from ratios alone.

## Backend crossover points

Three natural shapes each for Mersenne31 and the 64-bit prime, plus two BN254 shapes; three runs
per cell. The label's `preset baseline` describes **source F4 matrix-generation options**, distinct
from the old-kernel arm. Density is initial stored entries divided by rows×columns. All columns
compare the specified **forward** backend followed by the same production sparse back-substitution.
Total elimination medians include both stages, excluding capture. RSS covers the whole capture and
replay process; its table entry is the maximum over all three backends/repetitions for that arm.

| Captured case / field | Rows×cols | Density % | Rank | Sparse ms B→C | Dense ms B→C | Adaptive ms B→C | Peak RSS MiB B→C |
|---|---:|---:|---:|---:|---:|---:|---:|
| katsura-7 grevlex m31 | 361×369 | 7.92 | 306 | 3.439 → 3.633 | 2.976 → 2.863 | 1.710 → 1.682 | 5.02 → 4.87 |
| cyclic-6 grevlex m31 | 159×175 | 23.46 | 112 | 1.180 → 0.912 | 0.772 → 0.649 | 0.642 → 0.647 | 4.46 → 4.48 |
| katsura-6 lex m31 (preset baseline) | 1954×945 | 3.51 | 914 | 20.925 → 21.353 | 28.325 → 27.971 | 9.647 → 10.435 | 13.05 → 12.07 |
| katsura-7 grevlex p64 | 361×369 | 7.92 | 306 | 3.884 → 3.401 | 4.859 → 4.749 | 1.783 → 1.733 | 5.21 → 5.20 |
| cyclic-6 grevlex p64 | 159×175 | 23.46 | 112 | 0.984 → 0.942 | 1.036 → 0.993 | 0.685 → 0.628 | 4.70 → 4.75 |
| katsura-6 lex p64 (preset baseline) | 1954×945 | 3.51 | 914 | 21.982 → 21.725 | 63.567 → 63.204 | 9.764 → 9.349 | 21.08 → 21.08 |
| katsura-6 grevlex bn254 | 144×152 | 11.24 | 121 | 2.050 → 1.998 | 3.653 → 3.672 | 1.949 → 1.697 | 4.61 → 4.69 |
| cyclic-5 grevlex bn254 (preset baseline) | 635×379 | 3.48 | 365 | 14.775 → 14.484 | 36.568 → 35.773 | 10.348 → 10.217 | 11.09 → 11.05 |

Adaptive has the lowest point estimate at each sampled input; no backend selection changes are
justified here. Dense-versus-Sparse order changes with field and shape. These natural matrix
points are not a controlled density sweep and do not locate a universal crossover threshold.
Three-repeat small timings are noisy: some individual medians regress, including M31 Sparse K7
and Adaptive lex K6. The focused repeats below test those points rather than deleting them.

Sparse tuples occupy 16 bytes for both Mersenne31 and the 64-bit prime, and 40 bytes for BN254.
Halving the coefficient width therefore does not halve this sparse representation's tuple traffic.
Dense coefficient buffers do differ: for K7, 532,836 bytes at M31 versus 1,065,672 bytes at the
64-bit prime; Adaptive's corresponding single dense row is 1,476 versus 2,952 bytes. Explicit
coefficient-buffer size is distinct from sparse payload, allocation capacity and process RSS.
This is not an isolated estimate of the benefit from per-bitwidth arithmetic specialization.

For the large pinned MQ10 batch, fingerprint `f9a86d072bdc760f`, input 12,554×12,020 with
783,737 entries, final rank 11,665, Adaptive only:

| Arm | Forward ms | Back-substitution ms | Total ms | Process peak RSS MiB |
|---|---:|---:|---:|---:|
| baseline | 822.293 | 1825.987 | 2648.080 | 140.20 |
| candidate | 804.628 | 834.554 | 1642.752 | 140.68 |

Back-substitution falls about 54%; the full captured elimination falls about 38%. This is a
single batch, not a full-solve speedup. Stage medians need not add to the median total. The complete
F4 measurements above are the adoption evidence; matrix-only improvements would not suffice.

## Work anatomy and traffic model

Diagnostic replay exactly reproduces production RREF and target visits. Target roles classify
inherited reducer **pivot columns**, not original row provenance after backend row reordering.
The following counts are cumulative **entry visits**, not resident unique matrix entries:

| MQ10 back-substitution target role | Row updates | Own entry visits | Untouched prefix visits | Untouched suffix visits |
|---|---:|---:|---:|---:|
| Inherited reducer-pivot targets | 237,532 | 81,749,680 | 14,127,669 | 33,326 |
| New-pivot targets | 606,210 | 1,055,336,540 | 859,379,820 | 169,704 |

Of 1,137,086,220 target entry visits, 873,507,489 (76.8%) are untouched prefixes.
Prefixes account for 99.98% of all untouched visits; suffixes are only 203,030.
The final kernel skips prefixes and still copies suffixes as part of the tail. Its counts are
`own_terms - prefix_terms` and `output_terms - prefix_terms`; the diagnostic's two-sided
`overlap_terms`/`output_window_terms` fields describe the discarded prototype's potential span.

A deliberately **logical tuple-traffic model**, ignoring cache reuse, allocation/reallocation,
metadata, control flow and write allocation, counts target/pivot reads, scratch writes, then scratch
reads and target writes. For a full-row merge this is `(own + pivot + 3*output)*entry_bytes`.
For the final tail merge it is `(own-prefix + pivot + 3*(output-prefix))*entry_bytes`.
On this batch the model changes **76.97 GB → 21.07 GB**. Arithmetic stays
508,566,282 algorithmic field operations (one multiplication and subtraction per pivot term), giving
0.00661 → 0.02414 field operations per modeled byte. These are not hardware FLOPs,
measured memory transfers, or DRAM bandwidth. Cache residency can satisfy repeated logical visits.

## Hardware observations

Three separately profiled full solves per arm/prime, with the same complete-basis checks and
resource guard. `perf stat` 7.3.3-200.fc44 counts user-mode events for the whole solver child,
including parsing/rendering/output. All requested events ran for at least 99% of their enabled
time; unavailable, zero or materially multiplexed counts are rejected by the runner. These times
are not pooled with the unprofiled F4 medians.

| Case | Cycles, billions B→C | Instructions, billions B→C | cache-references, billions B→C | cache-misses, millions B→C |
|---|---:|---:|---:|---:|
| mq10/32003 | 19.018 → 12.542 | 75.785 → 47.632 | 2.577 → 1.069 | 348.097 → 266.706 |
| mq10/2147483647 | 20.225 → 13.270 | 80.518 → 52.356 | 2.671 → 1.172 | 364.529 → 284.869 |

Cycles fall about 34%; instructions fall about 37%/35%. Both generic cache-event counts also
fall. This supports removal of repeated loop/copy work. No uncore memory-controller counters were
collected, so physical DRAM bandwidth and whether elimination is DRAM-bandwidth-bound remain
unresolved. The logical model is not offered as a substitute for that measurement.

## Focused repeat and rejected prototypes

The main small-matrix sample uses only three repetitions. Four separate 15-pair follow-ups pin
**CPU 3 only**, to reduce migration variability. They use the same frozen binaries and full
verification. Their times are not pooled with the CPUs 0–3 cohort. The middle column shows the two timing medians;
the final column is the independently calculated median of the 15 paired C/B ratios (lower is
faster). Absolute times vary with the binding and surrounding machine state.

| Focused control | ms baseline → final | Median paired C/B |
|---|---:|---:|
| katsura-7/grevlex/m31/default/sparse | 4.082 → 3.871 | 0.952 |
| katsura-6/lex/m31/baseline/adaptive | 10.220 → 9.787 | 0.967 |
| public-eco-8 | 13.558 → 13.116 | 0.970 |
| public-noon-6 | 55.165 → 54.414 | 0.990 |

Raw follow-ups: [M31 Sparse](../../research/row-merge/results/focused-m31-sparse.json.gz),
[M31 lex Adaptive](../../research/row-merge/results/focused-m31-lex-adaptive.json.gz),
[Eco-8](../../research/row-merge/results/focused-public-eco-8.json.gz), and
[Noon-6](../../research/row-merge/results/focused-public-noon-6.json.gz).
The two anomalous small matrix points improve in these repeats, as do Eco and Noon. This supports
the final choice without claiming that every small-matrix timing point improves on every binding.

The [first prototype](../../research/row-merge/results/first-solves.json.gz) searched both ends of
the overlap and spliced the replacement. It improved MQ10 but regressed public controls and
small-field Sparse elimination. A [full-span fast-path refinement](../../research/row-merge/results/window-refined-solves.json.gz)
still regressed Noon-6 about 10% and several Sparse matrix points; its complete matrix, work and
counter cohorts are retained beside it. Neither discarded prototype is the shipped decision.
The final single-bound, truncate-and-copy merge removes that machinery while retaining almost
all of the available untouched-entry saving.

The baseline instrument sanity check deliberately runs the **same binary** under both arm labels;
its duplicate timings are not independent candidate evidence. Nothing from the rejected or sanity
cohorts is pooled into the final medians.

## Validation and broader #269 questions

Red-Green tests first exposed full-target scratch reservation, then checked prefix retention,
maximum-column/disjoint/empty supports, dense-reference arithmetic over prime and extension
fields, and existing #554 capacity safeguards. All 2,821 active tests pass, including required
msolve coverage. All-target/all-feature and no-default-feature Clippy pass. Focused rust-analyzer
inference reports zero unknown expression types in the modified subtraction methods. CI runs
the example replay test and the Python acceptance tests, including coefficient/input/RREF drift,
stale executable hashes, missing hardware events and empty focused selections. README commands,
source headers and published-fixture paths were reviewed.

[#149](https://github.com/mfaulk/zeebra/issues/149) is already closed with the negative AVX2
shipping decision in [#541](https://github.com/mfaulk/zeebra/pull/541), recorded in the
[SIMD milestone](../MILESTONE-SIMD-PARALLELISM.md). This generic merge does not change that decision.
Controlled density sweeps, a separate delayed-reduction/per-bitwidth experiment, and physical
bandwidth measurement remain broader #269 follow-ups. The current result establishes one safe,
measured improvement to the identified production hotspot across complete independently checked
solves; it does not claim those other research questions are settled.
