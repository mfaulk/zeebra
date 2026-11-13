# Elimination kernels: sparse prefixes and bounded specialization

**Measured at:** `cc6916fc` (baseline) and `dd36652e` (final prefix-only kernel).
Earlier prototypes: `220a99f1` and `cc993a00`. Build metadata inside each artifact records full
commits, rustc identity and executable SHA-256 values. Focused repeats use runner `62c252d3` with
the same frozen baseline/final binaries. Campaign date: 2026-11-12 (UTC).
Candidate-only feasibility below uses `0ed4fe33` with controller `c148058b`, measured 2026-11-13 UTC.

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
The subsequent H13 remainder below supplies nested density curves and a bounded scalar
coefficient-specific prototype, with its own decision and remaining limits.

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
fields, and existing #554 capacity safeguards. At the prefix campaign pin, all 2,821 active tests
passed, including required
msolve coverage. All-target/all-feature and no-default-feature Clippy pass. Focused rust-analyzer
inference reports zero unknown expression types in the modified subtraction methods. CI runs
the example replay test and the Python acceptance tests, including coefficient/input/RREF drift,
stale executable hashes, missing hardware events and empty focused selections. README commands,
source headers and published-fixture paths were reviewed.

[#149](https://github.com/mfaulk/zeebra/issues/149) is already closed with the negative AVX2
shipping decision in [#541](https://github.com/mfaulk/zeebra/pull/541), recorded in the
[SIMD milestone](../MILESTONE-SIMD-PARALLELISM.md). This generic merge does not change that decision.
Those density, specialization and bandwidth questions were outside the prefix-only campaign;
the H13 remainder below now measures nested density points, one delayed pilot and read-side fills.
Physical controller bandwidth remains unavailable. The current result establishes one safe,
measured improvement to the identified production hotspot across complete independently checked
solves; it does not claim those other research questions are settled.


## H13 remainder: density curves and the scalar delayed-reduction gate

**Measured at:** `6578c0ab93f1ac59e56da62dcbefa51385be38d6`, baseline versus the isolated
`delayed.patch` overlay SHA-256 `e057dd71136cfb39de009bbb215eac1fb833686b435e64a7fc966d8f93a5bc0e`.
The successful region-counter instrument includes the acknowledgement-only fix at `ab74fdca`;
its unchanged pilot library comes from `6578c0ab`. Every cohort retains source/compiler/binary
identities. Measurements: 2026-11-12 UTC, same 5995WX, rustc 1.99.1, fat LTO, one codegen unit,
x86-64-v3, system allocator, **CPU 3 only**, one solver worker. Do not pool these with the earlier
CPUs 0–3 prefix campaign. Parent Cargo config also selects mold; actual counter rebuild flags
are retained in its build metadata.

**Decision: retain production Adaptive and the prefix merge; do not ship this delayed pilot.**
Delayed reduction wins its arithmetic test and MQ10/32003, but regresses Noon-6 and does not give
a broad full-solve or capacity win. This closes the bounded scalar feasibility arm negatively,
not by pretending its arithmetic win is a full-pipeline win. No production API, backend selection,
field representation, intrinsic path, dependency or default budget changes in this study.

### Scope, correctness and retained attempts

The [runner and reproduction instructions](../../research/elimination-kernels/README.md) retain
**714 successful attempts**: seven arithmetic comparisons, 540 density replays, 30 paired pilot
matrix replays, 120 full solves, three acknowledged region-counter runs, six conversion diagnostics
and eight work diagnostics. All complete bases, matrix RREFs, ranks and structural work counters
agree at their matched inputs. The 120 bases use the same independent references as the earlier
prefix campaign; public Eco, Noonburg and Reimer plus MQ, Cyclic and Katsura cover six families.
Entry allowances and exact mid-operation stop counts are unchanged.

Three additional [counter attempts](../../research/elimination-kernels/results/region-rejected.json.gz)
were rejected after a NUL-framed perf acknowledgement triggered an instrument panic. Their positive
raw counters do **not** make them accepted measurements. The failure exposed a test gap; a new
Red-Green regression covers buffered `ack\n\0ack\n` responses. Fixed runs use separate artifacts.
The [lock log](../../research/elimination-kernels/results/benchlock.log) preserves the first campaign's
nonzero exit and subsequent successful counter, diagnostic and work windows. No builds or tests
ran during these measurement windows.

All attempts run in fresh processes under the existing 185-second/2-GiB process-tree watchdog;
source captures and classical/public solves also have 60-second solver limits. The 540 density
replays rotate backend order between repetitions; paired pilot/full solves alternate arm order.
Every table reports native medians of five repetitions unless stated otherwise. Peak RSS is the
maximum self high-water snapshot in those repetitions, **including capture for matrix rows**.
Explicit buffers, live entries and RSS are separate quantities. No resource refusal was removed.

Raw data, complete paired summaries and all 36 density points are retained as
[compressed cohorts](../../research/elimination-kernels/results),
[summary.json](../../research/elimination-kernels/summary.json) and
[curves.csv](../../research/elimination-kernels/curves.csv). Regenerate the latter two with
`python3 research/elimination-kernels/summarize.py`; it also rechecks complete bases, structural
counters, curve identities and cell coverage before writing tables.

### Three fields, three shapes: the controlled density curves

K7 is Katsura-7 grevlex batch 4, C6 is Cyclic-6 grevlex batch 7, and K6lex is Katsura-6 lex
**baseline-preset** batch 21. M31/p64 captures must match H6's pinned fingerprints. BN254 uses the
same three family/order/batch selectors; these additional source fingerprints are retained and
checked across repeats. All use the current structured reducer-first split on replay.

Each source gets nested deterministic masks retaining 1/8, 2/8, 4/8 or 8/8 of tail entries, with
leading entries always preserved. Eight eighths is the original capture. The other points are
**synthetic derivatives of real captured supports**, not native F4 batches or equivalent ideals.
The reducer block stays valid. Rank, fill-in and initial density can change across masks; the
CSV reports them. The comparison at one mask holds the complete input constant across backends.

Entries in each cell below run from 1/8 to 8/8. Ratios use median **forward** time to isolate backend
work; the common production back-substitution follows and verifies exact canonical RREFs. Values
below one are faster than Sparse. Full elimination times and peak RSS are in the CSV.

| Field/shape | Initial density %, 1/8 → 8/8 | Dense/Sparse forward | Adaptive/Sparse forward |
|---|---|---|---|
| m31/k7 | 1.23 / 2.18 / 4.15 / 7.92 | 1.36 / 0.93 / 0.76 / 0.74 | 0.40 / 0.35 / 0.32 / 0.31 |
| m31/c6 | 3.44 / 6.41 / 12.12 / 23.46 | 0.79 / 0.89 / 0.54 / 0.58 | 0.56 / 0.53 / 0.48 / 0.55 |
| m31/k6lex | 0.53 / 0.96 / 1.81 / 3.51 | 2.21 / 1.54 / 1.17 / 1.45 | 0.36 / 0.31 / 0.28 / 0.41 |
| p64/k7 | 1.23 / 2.18 / 4.15 / 7.92 | 2.81 / 2.20 / 1.63 / 1.58 | 0.49 / 0.37 / 0.29 / 0.32 |
| p64/c6 | 3.44 / 6.41 / 12.12 / 23.46 | 1.53 / 1.29 / 1.12 / 1.33 | 0.58 / 0.52 / 0.48 / 0.52 |
| p64/k6lex | 0.53 / 0.96 / 1.81 / 3.51 | 4.75 / 3.60 / 2.80 / 3.48 | 0.37 / 0.30 / 0.27 / 0.38 |
| bn254/k7 | 1.23 / 2.18 / 4.15 / 7.92 | 3.87 / 3.46 / 3.06 / 3.03 | 0.84 / 0.78 / 0.72 / 0.70 |
| bn254/c6 | 3.44 / 6.41 / 12.12 / 23.46 | 1.74 / 1.60 / 1.36 / 1.43 | 0.89 / 0.84 / 0.75 / 0.82 |
| bn254/k6lex | 0.53 / 0.96 / 1.81 / 3.51 | 9.45 / 7.69 / 5.84 / 5.39 | 0.71 / 0.68 / 0.67 / 0.74 |

M31 K7's point estimate crosses Sparse between 1.23% and 2.18% density; the latter is close to
parity, so this is a bracket, not a tuned threshold. M31 C6 favors Dense throughout the sampled
range, while M31 K6lex does not. All p64/BN254 Dense points lose to Sparse. Adaptive wins every
sampled forward point. **There is no field-independent density threshold to install.** Wider
coefficients make touching empty dense cells more expensive, but these measurements do not
isolate storage width from field arithmetic. They also do not reach arbitrary dense matrices.

The opt-in large corpus now contains a 24.8-million-entry capture (#640 is closed). This campaign
still deliberately stays in the smaller three-shape and MQ10 regimes; it makes no large-matrix
blocking, cache-scaling or GPU claim. A full dense copy of that larger shape would not fit the
pilot's process ceiling.

### What delayed reduction actually buys, with representation controlled

The existing field-width study established 32-bit versus 64-bit arithmetic differences, and #149
already settled the eight-lane AVX2 shipping question. The remaining bounded question from #269's
later evidence is scalar delayed reduction at **GF(32003)**. That selects the one prototype here;
it is not a general bitwidth backend replacement.

The prototype uses split u16 pivot coefficients and u64 nonnegative working sums. Its canonical
control uses **identical storage and traversal** but reduces after each update. All three arms
include exact modular-zero support bookkeeping and assert identical final coefficients. Seven
fresh processes, 4,194,304 updates each, 4,096 columns, fixed factor:

| Arithmetic arm | Median ns/update |
|---|---:|
| Generic GF(32003) DenseAccumulator | 1.575 |
| Split pilot, canonical after every update | 1.611 |
| Split pilot, delayed reduction | 1.138 |

The delayed schedule saves about 28% against generic and 29% against its same-storage canonical
control. The latter is the evidence for delayed arithmetic; a comparison of different coefficient
representations alone would confound it. These working sets fit cache and are not a bandwidth test.
No new handwritten SIMD arm is justified by these results.

After a fold every cell is at most `p-1`; one update adds at most `(p-1)^2`. Therefore the exact
safe update count is `floor((u64::MAX-(p-1))/(p-1)^2)`:

| Prime | Updates before a mandatory full-row fold |
|---|---:|
| 32003 | 18,012,146,920 |
| 2^31−1 | 4 |
| 2^64−59 | 0 |

This is why the prototype stops at the small prime. The last row needs a wider accumulator;
the middle cannot inherit the small-prime schedule. Fold-boundary tests use u128 arithmetic,
force short fold intervals and exercise maximal factors, cancellation, reactivated columns,
word boundaries and scratch reuse. Known 128/256-bit, binary and extension types explicitly use
the generic fallback. The overlay is never part of the committed library API.

### Conversion-inclusive matrix and full-solve gate

Captured GF(32003) elimination, including pivot conversion/cache building and row conversion,
followed by unchanged sparse back-substitution:

| Shape | Elimination ms B → C | Median paired C/B | Peak RSS MiB B → C |
|---|---:|---:|---:|
| k7 | 1.536 → 1.432 | 0.896 | 4.53 → 4.45 |
| c6 | 0.600 → 0.554 | 0.921 | 3.92 → 4.08 |
| k6lex | 9.554 → 7.868 | 0.821 | 7.47 → 7.40 |

Separate one-pair diagnostics report the selected replay's conversion **plus normalization** and
additional pivot-cache capacities; earlier capture-batch diagnostic lines are not summed into the
replay. These instrumented timings are not pooled with the native medians:

| Shape | Conversion/normalization µs | Additional cache capacity bytes | Pilot cell payload bytes |
|---|---:|---:|---:|
| k7 | 168.705 | 106,688 | 2,952 |
| c6 | 48.770 | 57,682 | 1,400 |
| k6lex | 579.835 | 359,432 | 7,560 |

The cache duplicates coefficients/columns still owned by the sparse matrix. Its bytes are outside
the existing F4 entry-byte accounting, although the process guard covers them. The u64 working
buffer also doubles the generic small-prime cell width. These are reasons not to present this
feasibility build as a production memory-capacity improvement. RSS alone can hide an allocation
whose lifetime does not coincide with the process high-water peak.

The full F4 call, same shipping strategies on both arms, with parsing/reference comparison outside
the timer. All public-family controls here are GF(32003). The middle column below reports the
median of **paired** C/B ratios and its observed range; it need not equal the ratio of medians.
Sub-millisecond controls remain correctness/sanity checks with substantial cold-process noise.

| Full solve | F4 ms B → C | Paired C/B median (range) | Peak RSS MiB B → C |
|---|---:|---:|---:|
| public-eco-4 | 0.091 → 0.092 | 1.013 (0.952–1.212) | 3.46 → 3.49 |
| public-noon-3 | 0.153 → 0.165 | 1.089 (0.956–2.282) | 3.60 → 3.66 |
| public-reimer-3 | 0.197 → 0.205 | 1.062 (0.954–1.137) | 3.60 → 3.69 |
| public-eco-8 | 11.639 → 11.635 | 0.994 (0.979–1.016) | 4.79 → 5.00 |
| public-noon-6 | 49.870 → 53.288 | 1.068 (1.040–1.085) | 15.00 → 14.87 |
| public-reimer-5 | 17.843 → 17.185 | 0.971 (0.950–1.111) | 5.16 → 5.26 |
| mq10/32003 | 3041.540 → 2768.770 | 0.912 (0.903–0.913) | 134.95 → 134.29 |
| cyclic-5/32003 | 0.969 → 0.993 | 1.007 (0.930–1.066) | 4.22 → 4.16 |
| katsura-4/32003 | 0.143 → 0.154 | 1.041 (1.033–1.192) | 4.07 → 4.02 |
| mq10/2147483647 | 3208.772 → 3322.047 | 1.034 (1.028–1.055) | 135.37 → 135.50 |
| cyclic-5/2147483647 | 0.992 → 0.987 | 0.995 (0.811–1.125) | 4.18 → 4.15 |
| katsura-4/2147483647 | 0.144 → 0.142 | 1.025 (0.412–2.302) | 4.02 → 4.12 |

MQ10/32003 improves consistently by about 9%, while **every Noon-6 pair regresses** (4–8.5%).
Eco-8 is effectively unchanged and Reimer-5's range crosses parity. The 31-bit MQ10 fallback
also regresses 2.8–5.5% in this build despite using the generic algorithm; code-generation/layout
and machine effects are not separated here. No claim attributes that control's change to delayed
field arithmetic. This candidate fails the no-material-regression gate and does not justify broad
production dispatch or extending the prototype to other widths. The earlier prefix-only merge
remains the stronger, already shipped result.

### Logical intensity and acknowledged hardware region

The fresh work replay reproduces the earlier pinned MQ10 back-substitution anatomy exactly:
**508,566,282 algorithmic field operations / 21,067,458,864 modeled tuple bytes =
0.0241399 field operations per logical byte**. This is multiplication plus subtraction per pivot
term, with the prefix-only copy model defined above. It is not hardware arithmetic intensity in
FLOPs/DRAM-byte; one field operation expands into several integer instructions.

Perf 7.3.3 user-mode counters are enabled by an acknowledged FIFO immediately before forward
elimination and disabled after back-substitution. Capture, input/RREF hashing, basis work and
output are excluded. The three corrected runs have complete inputs/RREFs, no resource stops,
positive cycle/instruction counts and at least 99% event running time. They use the acknowledgement
fix at `ab74fdca`, linked to the unchanged pilot library from `6578c0ab`; its 31-bit field takes the
generic fallback. The direct-rustc rebuild flags and library SHA are in the cohort metadata (`TARGET` denotes
the private build directory).
This distinct counter build is not pooled into baseline/candidate native medians.

| Region observation | Median, three runs |
|---|---:|
| Complete elimination | 1776.516 ms |
| User cycles | 7.312 billion |
| User instructions | 28.427 billion |
| Local DRAM-or-IO data-cache fills | 1,908,555 |
| Remote DRAM-or-IO data-cache fills | 0 |
| Read-side fill estimate, 64-byte lines / elapsed | 0.0688 GB/s |

The line size is verified from this host's cache sysfs. The events count demand/prefetch data fills
from the documented source, not all physical bus traffic. They exclude writebacks, coherence
traffic and other cores. Low read-side traffic is consistent with the hot work being cached,
arithmetic or control work; it does not prove which of those limits execution or rule out a cache
bandwidth bottleneck. The logical intensity above describes **back-substitution only**, while the
hardware region includes both forward and backward elimination; do not divide those quantities
together to invent a physical roofline point.

**Physical memory-controller bandwidth remains unmeasured.** The
[capability record](../../research/elimination-kernels/results/environment.json) retains both failed
AMD Data Fabric probes: the default user-only form is unsupported, and the kernel-inclusive form
is denied with `perf_event_paranoid=2`. No system policy was changed. This is an outstanding strict
#269 acceptance item, not evidence that total DRAM bandwidth is 0.069 GB/s or that all elimination
regimes are ALU-bound.

### Existing decisions and what this result does not reopen

- **#149 stays closed:** #541's negative AVX2 shipping decision applies. An isolated contiguous
  eight-lane win does not replace Adaptive's indexed scatter; no new intrinsic path is shipped.
- **#168 is already fixed:** current back-substitution builds `PivotColumnRows` and visits rows
  holding each pivot column. F4 now calls that pass through its reduced-batch strategy; the old
  issue's statement that F4 never calls it no longer describes this pin. #712's untouched-prefix
  improvement targets the remaining merge work, not the retired all-rows probe loop.
- **#169 is already fixed:** `Matrix::Mul` has a 2×8 register tile. The measured F4 paths here use
  sparse rows/DenseRows/DenseAccumulator, not dense matrix multiplication, so that ticket supplies
  no additional kernel speedup for these F4 shapes.
- **Faugère–Lachartre is a shared block-elimination principle, not a free replacement.** The
  shipping reducer-first triangular block already supplies known pivots for lower-row elimination.
  `InterreducedBlock` explicitly makes the reducer block an identity first and was rejected for
  fill-in. GBLA/Sagebrush's schedules/storage are not identical to the shipped streaming scatter;
  revisiting them requires a measured distinction, not renaming `structured.rs`. The source study's
  old universal 7–22% stage ceiling also must not be carried to MQ10's newer profile.

Bitmap scans, source-row coefficient reuse and multi-row bands remain distinct hypotheses from
#269's later source-study comments. They were not folded into this arithmetic pilot. This report
settles the bounded density/one-prototype experiments; it leaves physical controller bandwidth
and extrapolation to the large capture explicit. Tests cover the prototype and protocol bugs,
CI runs those offline tests and the isolated overlay, and README/reproduction commands point to
the retained source pins. No corpus-only result is used as production adoption evidence.

Local verification for this remainder: nine example tests, seven Python acceptance/integrity tests,
188 linear-algebra tests, and the overlay's explicit field-selection test pass. Clippy passes for
all targets with all features and without default features. Formatting, measurement provenance,
artifact hashes, derived-summary regeneration and package inclusion of the example/support source
were checked. The independent full-basis corpus controls above supply the prototype's end-to-end
validation; this PR changes no production library code.

## Candidate-only backward feasibility (#269)

**Measured at:** Rust source `0ed4fe33`, controller `c148058b`; 2026-11-13 UTC.
The [retained study](../../research/selective-backward/README.md) contains 120 quiet native
attempts and 40 separate work/overhead attempts. Every complete basis matches the retained
independent Singular-verified reference coefficient-for-coefficient. Pair counts, batch degrees,
input matrix shapes and basis-growth counts agree across arms; observed matrix fingerprints and
forward work counts agree across diagnostic arms. No production default changes.

### Invariant and bounded choice

Candidate extraction in `src/grobner/f4/reduction.rs` keeps precisely the pivot rows whose
leading monomials were absent from the input leading set. Symbolic preprocessing records exactly
the original row leads (its closure test asserts this). Forward elimination fixes the distinct
unit pivots. Backward operations cannot change a leading column, so candidate selection can occur
before backward reduction.

The research entry `linalg::selective::reduce`, behind `research-work`, processes selected targets
by increasing leading column. It loads one target into a dense row and scans later columns left
to right. A nonzero pivot column is cleared with its original echelon pivot, which has no entries
to the left of that column. Newly introduced pivot entries therefore lie strictly later and are
cleared before gathering. Earlier selected targets are never sources for a later target, so
later pivots remain the original echelon rows. The result for each selected pivot is its unique
full-RREF row; unselected rows retain their echelon tails. These elementary row operations preserve
the whole row space. F4 extracts exactly the same polynomials, including their tails, and hence
has the same subsequent basis, pairs and final interreduction. Public whole-matrix RREF is unchanged.
Leading-divisibility filtering and the `reduce_batch_rows` option are not weakened or disabled.

This selects transient substitution instead of precomputing reduced inherited tails. A dependency
closure can contain every later pivot, and memoizing its reduced tails can require rank times
free-column count entries in the worst case. Lazy substitution may revisit those dependencies for
each requested target; this experiment pays that arithmetic explicitly. For `t` selected targets,
its product bound is the sum of the later echelon supports for each target, at most
`t * sum(pivot_nnz)`. One dense row plus a column-to-pivot index costs `columns*(sizeof(F)+sizeof(usize))`
bytes; no recursive stack or cache of reduced inherited rows is retained. Only selected sparse
outputs are replaced. A single target can still become dense: the existing entry allowance charges
both its retained original and live dense copy, refusing before accepting an oversized row.
The scratch/index byte ceiling is separately 64 MiB. This is stricter than the ordinary entry
budget and can refuse earlier; it never increases a declared F4 allowance.

### Native result

5995WX, rustc 1.99.1, release/fat LTO/one codegen unit, x86-64-v3, mold, system allocator, one
worker on CPU 3. Five interleaved fresh processes per arm, 60-second/2-GiB child caps and the
existing 185-second outer watchdog. Builds/tests finished before measurement. Compiler processes
were checked before and after every accepted child; none were observed. Native load observations
range from 1.55 to 2.15. A prior 160-attempt cohort overlapped another worktree's compilation;
its complete answers and counts are retained under `exploratory/`, but its times are excluded.
No exploratory and quiet times are pooled.

Median complete F4 call milliseconds. The native CSV and summary retain ranges, process wall/CPU,
all F4 stages, and sampled tree RSS separately. Self RSS covers the child through basis rendering,
as in the existing instrument. Parsing/rendering are outside the F4 timer. RSS entries below are
the maximum self high water across five attempts, in MiB.

| Family / prime | Stock | Observed full RREF | Dense all targets | Dense selected | Stock → selected RSS |
|---|---:|---:|---:|---:|---:|
| MQ10 / 32003 | 3278.917 | 3144.293 | 14167.295 | 1321.362 | 134.64 → 35.32 |
| MQ10 / 2147483647 | 3321.061 | 3387.923 | 15580.292 | 1476.386 | 136.74 → 35.84 |
| Cyclic-5 / 32003 | 0.980 | 1.129 | 0.755 | 0.596 | 4.16 → 4.79 |
| Cyclic-5 / 2147483647 | 0.995 | 1.033 | 0.691 | 0.620 | 4.18 → 4.55 |
| Katsura-6 / 32003 | 1.636 | 1.738 | 1.571 | 1.048 | 4.68 → 5.81 |
| Katsura-6 / 2147483647 | 1.664 | 1.722 | 1.488 | 1.213 | 4.41 → 4.87 |

Selected reduction clears the predeclared 10% MQ10 improvement gate at both primes, stays within
1.25x RSS on every control and has no control median regression. MQ10 improves 59.7%/55.5%
against the feature-absent stock build. The observer/feature-present full arm itself differs from
stock by approximately -4.1%/+2.0%; that perturbation is retained rather than attributed to selection.
Sub-two-millisecond controls establish agreement and no observed regression, not a broad precision
speedup claim. No independent field-width performance claim is made from these two primes.

Final interreduction remains approximately 13 ms in selected native runs, as in stock. The
improvement therefore does not recreate #477's deferred tail-reduction debt. Other stages remain
charged: selected construction is about 17.5 ms versus stock's 13.4–13.8 ms; this cost is included
in the complete call, not hidden behind the backward timer.

### Work and materialization

Across all ten MQ10 batches, the all-target arm loads 50,912 nonzero rows; only **250** rows are
candidates. These are distinct target visits within the respective row-major passes, not the
column-major full pass's repeated row applications. The all-target arm isolates selection within
the new traversal, but comparing it with production also changes pivot traversal and source-row
forms; its difference is not a pure copy-cost measurement.

| Prime / arm | Backward applications | Coefficient products | Sparse copyback entries | Dense gathered entries |
|---|---:|---:|---:|---:|
| 32003 / full | 2,058,159 | 579,721,912 | 610,222,599 | 0 |
| 32003 / dense all | 117,422,954 | 7,079,509,066 | 0 | 15,572,375 |
| 32003 / selected | 471,831 | 23,566,622 | 0 | 71,088 |
| 2147483647 / full | 2,058,195 | 579,751,105 | 610,252,491 | 0 |
| 2147483647 / dense all | 117,426,323 | 7,079,798,757 | 0 | 15,572,924 |
| 2147483647 / selected | 471,840 | 23,567,093 | 0 | 71,089 |

All five diagnostic repeats reproduce these counts. Selected reduction performs 629,935 logical
scan-column visits and 630,185 gather-column visits. Its maximum scratch/index footprint is
144,240/192,320 bytes by field. Peak charged entries are 1,069,717/1,069,741; peak sparse capacities,
including the output before replacement, are 1,066,897/1,066,920 entries. Dense scratch is separate
from sparse capacity. The vector-allocation model is 20 scratch/index allocations plus 250 output
allocations; this is not an allocator or DRAM event count. Original row buffers never receive a
shared scratch buffer's high-water capacity.

Observation overhead is material: diagnostic selected medians are 1.64/1.91 s versus native
1.32/1.48 s. Full-off diagnostic controls are 3.17/3.40 s versus full-on 3.52/3.91 s. Counts and
native clocks therefore stay in separate cohorts. Logical products, copies and scans are not
physical bandwidth measurements; the earlier controller-bandwidth limitation remains.

The scalar row-major all-target replacement is **rejected**: avoiding sparse copies while expanding
arithmetic to 7.08 billion products is a full-pipeline loss. Candidate-only transient reduction
passes the isolated feasibility gate. Marked scans are **deferred** as a separate factor: this
prototype removes work without adding mark maintenance, and its scan counts do not establish a
scan-time bottleneck. Generic correctness covers characteristic two, binary extension, 64-bit
and BN254 fields; wide-field performance and independently witnessed wider full solves remain
outside this shipping decision. #149's negative AVX2 shipping verdict remains unchanged.

### Forward/backward crossing and larger probe

**Measured at:** combined executable Rust source `ff15a0af`, controller `1bf48baa`.
The [combined summary](../../research/selective-backward/combined-summary.json) retains
140 native attempts, 12 separately timed work diagnostics and four MQ14 probes. All 152 completed
native/diagnostic answers match the full independent references and preserve the F4 pair/degree/
shape trajectory. There are no excluded attempts or compiler-gate refusals in these cohorts.
After waiting 1,737 seconds for the shared lock, this campaign ran on the same machine, toolchain,
ISA/profile and allocator as above. Serial/one-worker children pin CPU 3; four-worker children pin
CPUs 0–3. Native load observations are 2.06–2.93. Its times are not pooled with the earlier binary.

Median complete F4 call milliseconds, five fresh processes per cell. `one` is the same concurrent
forward algorithm at one worker, not a relabelled serial control. The last column is maximum
self RSS, serial selected → four-worker selected, MiB.

| Prime | Serial full | Serial selected | One full | One selected | Four full | Four selected | Selected RSS |
|---|---:|---:|---:|---:|---:|---:|---:|
| 32003 | 3200.824 | 1300.425 | 3169.729 | 1274.008 | 2332.214 | 494.656 | 34.49 → 40.43 |
| 2147483647 | 3309.431 | 1383.567 | 3264.976 | 1367.392 | 2438.262 | 513.758 | 34.84 → 40.97 |

Within this cohort the combined route is 6.47x/6.44x faster than serial full, 2.63x/2.69x faster
than serial selected, and 2.58x/2.66x faster than one-worker selected. Selected RSS rises about
17%/18% with four workers, remaining below the existing 1.5x feasibility ceiling. The matched
serial-full ranges are 3073–3219/3142–3421 ms; four-selected ranges are 471–501/473–530 ms.
The sign is not an overlapping-noise result. Final interreduction remains approximately 13 ms.

The stage split makes the interaction explicit. At the small prime, median batch-forward/backward
sums change from **1156/1896 ms** (serial full), to **1126/40 ms** (serial selected), to **301/44 ms**
(four selected). At the larger prime they are **1197/1967**, **1203/45**, and **315/49 ms**.
Removing backward work exposes a forward stage that the existing concurrent prototype can shorten.
The full task still charges symbolic preprocessing, construction, extraction, final interreduction
and observer/runtime overhead. Medians of stage sums need not add to the complete-call median.

The small controls reject an unconditional parallel policy:

| Control / prime | Serial selected ms | Four selected ms |
|---|---:|---:|
| Cyclic-5 / 32003 | 0.704 | 2.110 |
| Cyclic-5 / 2147483647 | 0.724 | 2.240 |
| Katsura-6 / 32003 | 0.965 | 1.656 |
| Katsura-6 / 2147483647 | 0.961 | 1.753 |

The concurrent forward route grows to 0.8–1.5 ms on these controls, versus 0.1–0.3 ms serial.
This campaign does not isolate thread startup from its other forward overhead. It fails the
no-5%-control-regression shipping gate despite the MQ10 result. A size gate or runtime policy belongs to the existing
#592/#728 work; this study does not silently select one or introduce a production thread pool.

Single work-on observations preserve the complete pre-forward matrix digests across concurrent
arms. Serial forward work remains 585,166,982/585,195,178 products under both backward policies.
Four-worker selected observations report 584,134,280/584,319,879 forward products, including
8,415,756/7,231,959 products attributed to failed-publication retries. One-worker concurrent
products equal serial and retry products are zero. Publication order changes the echelon pivots;
backward selected products are 23,561,084/23,530,121 at four workers versus
23,566,622/23,567,093 serial. These are measured trajectory differences, not a pure cost-per-product
comparison. Worker-local passive counts equal the direct worker products; row aggregation covers
every non-inherited input row. Each diagnostic has one sample and its time is not a native median.

Four-worker forward workspace is bounded at 865,440/1,057,760 bytes in these diagnostics.
Peak reserved entries are 1,571,889/1,573,215: these are the concurrent algorithm's conservative
reservation upper bounds, including retained input/pending reservations, not measured mathematical
nonzero peaks. They are distinct from sparse capacities, dense scratch and process RSS.

All four MQ14 probes end with `TooManyNonzeros` at the **unchanged 32,000,000-entry allowance**:

| Prime | Full offending count | Selected offending count | Full/selected sampled tree RSS MiB |
|---|---:|---:|---:|
| 32003 | 32,000,887 | 32,000,270 | 767.16 / 725.28 |
| 2147483647 | 32,001,899 | 32,000,112 | 769.41 / 738.43 |

No probe completed, no basis was promoted and no stopped duration is used as a speedup.
Both routes hit the same declared entry ceiling before the 60-second/2-GiB outer caps. Lower
observed RSS on an incomplete computation is not a frontier-capacity win. The requested public
MQ14 digests, derived from the invoked case and frozen corpus source, are
`4e440cfac84262260736a2368f43c7a96181986ca5bc108517299520d56f8795` and
`029def705543e29b9f0648d3fa21a87be32358b79c3e64bb6dd222fa432c439d`, respectively.
Raw commands, typed refusal messages and complete outputs for every completed control remain in
the archives. A future larger successful solve needs its own independent reference.

**Disposition:** adopt candidate-only transient reduction as a justified production follow-up;
reject the all-target dense replacement and an unconditional four-worker default; defer marked
scans, wider-field performance and any frontier-capacity claim. This PR retains experimental
entry points behind `research-work`, with ordinary F4/RREF defaults unchanged. Production
integration is tracked in [#749](https://github.com/mfaulk/zeebra/issues/749) and must reconcile
mathematical versus reserved-entry statistics, stricter temporary-copy
budget charging, backend/order coverage and fallback behavior before enabling a default.

Red-Green tests first failed on selected-subset behavior and refusal/reuse, then covered five
field types, random rank deficiency, duplicate/nonmonic pivots, empty/partial selections and
mid-operation entry stops. Complete small F4 solves and one/four-worker composition agree.
All 2,808 active library tests at the initial pin passed; the final seven focused kernel tests
and four profiling-example tests pass. Offline CI rechecks basis coefficients, complete plans,
trajectory/input digests, timer/RSS validity, worker counter consistency and all artifact hashes.
Commands, source pins, README examples, workflow references and source comments were reviewed.
The unresolved performance claims above are deliberately not presented as completed evidence.
