# Grobx and Zeebra trajectory attribution (#713)

**Measured at:** `b108c2be` — frozen campaign runner; stock Zeebra Rust source `ff65d2b4`, observed Rust source `6d951ea4`. The counter contract below was committed before the native campaign. Binary/source/config fingerprints are retained in `research/grobx-trajectory/builds.json`; `evidence/provenance.json` and its SHA-256-checked base patch reconstruct the frozen source even after squash/branch deletion.

This study compares complete reduced grevlex bases on the two public `mq-random-10`
instances, not a solver redesign. Baseline production code is main after #717
(`ff65d2b4`), including the #712 prefix optimization. Grobx is pinned to
`1854835dbc25f24dc9a9ba017024d5030e99da1c` (0.73.3); its current default branch was
identical when this work began. The isolated GPL instrumentation is confined to
`tools/external/grobx-driver/research/` and a separate build workspace. No upstream
implementation is introduced into the MIT library.

## Counter contract and scope

The report decoder first reads the existing `grobx-683.json.gz` evidence. It retains
all signature rounds, the discarded run and original-input restart, the plain
rounds, both input echelon phases, and final basis interreduction. Grobx's public
`Stats` describes only the last run and excludes final interreduction. The full
report is the observation interface: enabling a trace listener or cofactors would
change randomization and handover and is forbidden as an instrumentation method.

| Quantity | Meaning and comparability |
|---|---|
| Pair decisions | Engine-native generated/considered/rejected/queued/processed counts, preserving criterion names. Signature reductants are not ordinary S-pairs. |
| Round degree | Plain sugar degree versus signature degree; the same integer is not proof of the same trajectory. |
| Matrix dimensions/entries/density | Initial encoded rows and columns, not peak fill or allocated capacity. |
| Rank/new pivots | Keep inherited pivots and newly discovered rows distinct. Zero combinations/tests are not individual zero rows. |
| Pivot applications | One target update by a pivot, including band lanes separately. Counts are never assumed to have equal cost. |
| Coefficient products | Entries actually multiplied in the update kernel. Include zero multiplier lanes if executed; distinguish pivot leading entries included/skipped. |
| Entry charges | Existing grobx budget `subtracted`/`added`: full row length per target/lane. A diagnostic work proxy, not exact products. |
| Sparse target work | Entries scanned/merged/rewritten by the actual post-prefix kernel. Preserved prefixes are reported separately; they are not coefficient arithmetic. |
| Dense work | Loaded entries, cells scanned/cleared/gathered and pivot scatter updates. Count actual loops, not hypothetical dense spans. |
| Live payload | Simultaneous entries by original/source-reference and newly materialized row roles, plus scratch. Mathematical live entries and duplicate physical input copies are distinguished. |
| Capacity | Allocated slots by buffer type, including scratch/dense/auxiliary arrays. Entry sizes and sharing determine logical bytes; allocator residency/RSS cannot be inferred exactly. |
| Process wall/RSS | Fresh-process spawn to reap and process high-water RSS, including full output encoding; independent answer checking is afterwards. Stage durations remain separate. |

Counters are scoped to one serial computation, opt-in, and separated into
forward reduction, back-substitution, final interreduction and per-batch metadata.
They must not reorder rows, change pivot selection, add tracing, change field
representations, or alter mathematical budgets. Known-rank hand-computable tests
establish product and row-application counts before MQ runs. Feature-absent,
feature-present/counters-off and counters-on arms distinguish compilation/layout
cost from observation overhead. Same-path checks compare dimensions, degrees,
pairs, ranks, zeros and entry charges, not clocks.

This is a bounded matrix ledger, not a replacement for #268's whole-process memory
accounting. Basis objects, monomial intern tables, queues, output strings and
allocator retention must remain explicitly unaccounted where not observed.
Logical bytes and unique pivot-entry reads are not measured physical DRAM traffic.

## Reproduction

Use the existing [external comparison protocol](external-comparison-protocol.md),
[driver contract](../../tools/external/grobx-driver/README.md), and
[study commands](../../research/grobx-trajectory/README.md). The runner reuses
`mq10-profile.py`'s full-answer checker and descendant RSS observation, the corpus
reference artifacts, and `benchlock.sh`; it does not append profiling rows to the
competitive board. Every failure/refusal remains in the retained cohort.

Exact initial identities:

- GF(32003): `16422dafcdb6487ea541f976f7754112b811c85af2b3537ed10fe4ef9c8f3d7f`.
- GF(2147483647): `72d0ad315fc25409792625465578d18329597d3ee183e75f257774d9215803b2`.

All completed answers must match the full retained independently Singular-verified
247-polynomial bases. Reusing those exact reference polynomials is independent
answer verification, not rerunning Singular within timed solver work. Tiny
hand-matrix tests supplement this check; rank or leading monomials alone never
suffice. Five interleaved fresh-process repetitions per arm, one worker, same
machine/affinity/ISA, 60 seconds and 2 GiB per child, frozen sources and binary
hashes, and explicit load gates are required. This attribution study does not
adopt a technique; larger MQ/Katsura/Cyclic validation gates any later adoption.

## Native evidence and observation overhead

[The retained cohort](../../research/competitive/results/grobx-trajectory-native.json.gz)
contains **60 complete, verified attempts**, five per arm per field, with exact
input echoes and full reduced-basis equality. No failures, refusals, missing RSS or
structural path differences occurred. Every fixed-input work report is identical
across its five repetitions. The [summary](../../research/grobx-trajectory/summary.json)
and [per-round CSV](../../research/grobx-trajectory/summary-rounds.csv) are regenerated
with full-answer checks and counter reconciliation in CI.

Machine: Threadripper PRO 5995WX, `trpro-5995wx`, CPU affinity `2`, one worker,
Rust 1.99.1, release/fat LTO/one codegen unit, matched x86-64-v3. The benchmark
[lock evidence](../../research/grobx-trajectory/evidence/benchlock.log) has START
18:50:51 and END 18:58:58 on 2026-11-12, `status=0 end=exited`; detached launch
accounts for `launcher=gone`. Load gates observed 0.80–1.79, below the declared 4.
The eight-minute window includes response checking and repeated evidence
compression, which are outside each solver's process timing. No builds/tests ran
inside it. All solver children stayed below 60 seconds/2 GiB. Direct children
need no nested profiler/checker watchdog; the 60-second guard is tighter than the
historical 185-second outer harness guard.

Each table row reports **process wall and process high-water RSS together**.
Verification happens afterwards. Zeebra includes public input generation/parsing,
F4 and full-basis JSON serialization; grobx includes loader, ordered-input parser
checks, raw reduced-basis solve/report and full output encoding. Stage clocks are
enabled consistently for Zeebra, and grobx already emits report timers. These are
fresh profiling/driver boundaries, not relabelled competitive-board rows or a
before/after experiment against November 11. No historical rows were pooled.

| Field | Arm | Wall median [min,max], ms | RSS median [min,max], MiB |
|---|---|---:|---:|
| 32003 | Zeebra stock | 3045.48 [3035.91,3081.99] | 135.60 [135.57,135.73] |
| 32003 | Zeebra observed/off | 3025.64 [3018.19,3041.94] | 134.18 [134.08,134.29] |
| 32003 | Zeebra observed/on | 3038.63 [3033.25,3074.69] | 135.73 [135.66,135.82] |
| 32003 | grobx stock | 342.24 [339.87,344.10] | 16.25 [16.13,16.38] |
| 32003 | grobx observed/off | 389.82 [383.65,407.55] | 16.26 [16.12,16.50] |
| 32003 | grobx observed/on | 402.68 [400.15,438.28] | 16.37 [16.35,16.43] |
| 2147483647 | Zeebra stock | 3204.68 [3193.01,3261.91] | 136.33 [136.18,136.36] |
| 2147483647 | Zeebra observed/off | 3326.91 [3305.48,3369.97] | 136.10 [136.03,136.15] |
| 2147483647 | Zeebra observed/on | 3331.64 [3315.62,3555.42] | 136.53 [136.48,136.59] |
| 2147483647 | grobx stock | 161.05 [159.60,164.88] | 16.32 [16.27,16.45] |
| 2147483647 | grobx observed/off | 173.90 [173.34,176.60] | 16.50 [16.37,16.51] |
| 2147483647 | grobx observed/on | 181.69 [178.21,185.06] | 16.39 [16.25,16.51] |

Instrumentation is not free. Grobx observed/off versus stock has median wall
quotients 1.139/1.080, and on/off 1.033/1.045. Zeebra off/stock is 0.993/1.038;
on/off 1.004/1.001. Some ranges overlap and the last Zeebra large-field on run is
slow; all samples are retained. The negative small-field difference is not an
optimization. **Use stock times for baseline costs and observed/on only for
validated structural/work attribution.** These controls do not assign the
compiler/layout/no-op/collection overhead to individual instructions.

Stock Zeebra elimination is 95.23%/95.56% of its F4 call (within-run median shares),
with stage medians 2872.19/3034.27ms. Final interreduction is 12.14/12.35ms. Thus
post-prefix elimination remains the priority; the historical 97% and cycle samples
are not substituted for this new measurement.

## Actual trajectories, pairs and row roles

Both engines return the same 247-element reduced basis, but take different paths.
Zeebra runs ten batches at degrees `2,3,4,5,6,6,6,7,7,8`, processes 1777 pairs,
uses 49225 inherited free pivots across batches and has 1867 dependent candidate
rows. Its snapshot reports 31893 GM rejections. Grobx starts with Schreyer-ordered
signature F4, degrees `2,3,4,4,5,6,7,8,9`, then at round 9 finds all three new
leading monomials divisible and restarts plain F4 from the original ten/95-term
generators. It executes ten more rounds at the same degree sequence as Zeebra.
Input echelon is executed twice; final interreduction belongs to the plain run.

| Count or active path | GF(32003) | GF(2147483647) |
|---|---:|---:|
| grobx signature pair candidates considered | 77028 | 77028 |
| signature equal / high / low decisions | 87 / 3025 / 30941 | 87 / 3025 / 30941 |
| syzygy / Koszul / queued decisions | 34187 / 518 / 8270 | 34187 / 518 / 8270 |
| signature reductions / zero reductions | 659 / 250 | 662 / 244 |
| plain reductions / zero reductions | 1775 / 1529 | 306 / 60 |
| plain mode | individual rows | random block combinations |
| band-eligible matrices actually reported | none | plain round 5 only |
| maximum Zeebra rows / columns | 12554 / 12020 | 12554 / 12020 |
| maximum grobx rows / columns | 15882 / 16217 | 15882 / 16217 |

These pair categories have upstream-specific meanings; they are not ordinary
Zeebra pair operations. Rank/new pivots, zero rows versus zero tests and given
rows are preserved per matrix in the CSV and full trajectories. Zeebra's normal
pair queue exposes global counts; per-batch generated/rejected reasons and grobx's
plain GM reason breakdown are unavailable and explicitly not inferred. Grobx's
**largest dimensions are larger**, not smaller, despite much less coefficient work.
Row/column maxima are independent unless a single CSV row identifies both.
Dimensions alone would give the wrong explanation.

Stock grobx's signature-prefix median internal times are 85.75/101.25ms and plain
run times 251.40/53.38ms. These are engine-internal phases, **not** process walls or
new cross-engine ratios. The abandoned work is included in every aggregate below.
The report decoder checks all 19 rounds, both `ran` summaries, restart input shape,
final basis size and terminal completion; the caller binds the full mathematical
input and answer. A structural-comparison regression ensures string-valued
`reduce=rows/combinations/tests` survives removal of numeric `reduce` timers.

## Comparable coefficient work, not equal row operations

The following counters are invariant across all five observed repetitions. Grobx
matrix rows include the signature prefix, plain restart **and final matrix
interreduction**. Zeebra batch counters exclude its separately listed final pass.

| Counter | Zeebra32003 | grobx32003 | Zeebra2147483647 | grobx2147483647 |
|---|---:|---:|---:|---:|
| forward target/pivot applications | 7885325 | 7691016 | 7885548 | 2267307 |
| backward target/pivot applications | 2058159 | 2103 | 2058195 | 3939 |
| forward pivot-update coefficient products | 585166982 | 370268317 | 585195178 | 115679011 |
| backward pivot-update coefficient products | 579721912 | 647264 | 579751105 | 1151936 |
| random-combination coefficient products | 0 | 101798 | 0 | 5496832 |
| additional Zeebra final-pass products | 93441 | included above | 93441 | included above |
| forward dense cells scanned/read-reset | 19463077 | 12903215 | 19463310 | 4085983 |
| sparse backsub target terms consumed | 597657296 | different dense strategy | 597686688 | different dense strategy |
| sparse backsub merged output entries | 610222599 | no repeated sparse merge | 610252491 | no repeated sparse merge |
| sparse backsub copyback entries | 610222599 | no repeated sparse merge | 610252491 | no repeated sparse merge |

Grobx target/pivot applications are lane-weighted, derived from full-row
subtraction charges minus nonzero tail products; a four-target kernel call can
represent several applications. Public `Stats.reduced` counts rows/combinations
instead and cannot substitute for this metric. Zeebra's final pass adds 281
applications, already excluded from its batch rows in the table.

The dense-scan row compares different loops: Zeebra tightens `[lead,tail)` and
counts its successful/zero probes, whereas grobx counts `take` calls, with separate
workspace clears not folded into that counter. It is descriptive, not an equality
of instruction costs. Grobx scalar direct-field multiply calls are another
187525/227980 within matrices, outside sparse MAC kernels; outside-matrix setup/input-echelon work
adds 714 direct multiply calls and 296 sparse-kernel products. Modular inversions,
normalization, construction and non-field operations must not be silently priced
as one MAC each. The exact counter definitions and omissions are in the GPL
[observer README](../../tools/external/grobx-driver/research/README.md).

Zeebra performs 1164888894/1164946283 batch pivot products, plus 93441 in each final
pass. Grobx executes 371017379/122327779 matrix MAC products **including
combinations and the abandoned prefix**. Grobx skips an implicit leading pivot
entry that Zeebra really multiplies. Subtracting Zeebra's 9943765/9944024 total
pivot applications normalizes that leading-entry convention; its remaining
1155038570/1155095700 products still exceed grobx's matrix MAC counts by
**3.11×/9.44×**. This deliberately charges grobx's combination construction while
excluding Zeebra's normalization products, so it cannot be explained away by
omitting grobx's randomized setup.

Budget-charge reconciliation independently checks grobx's matrix records:
378608700/119102193 charged subtractions equal all report-round charges plus the
93201 final-interreduction charges; both initial echelon phases add 470 outside
those matrices. Each nonzero target's implicit leading entry is the difference
between its charge and kernel-tail products. Band source reuse counts unique
source traversals separately from lane products. At the larger prime, matrix
kernel source traversals 114307669 versus 122327779 lane products show about 6.6%
logical source-entry reuse across the observed matrix kernels. That is not a measured
SIMD speedup or DRAM saving; no signature matrix used bands here.

Zeebra's backsub is 20.7% of batch row applications but 49.8% of batch coefficient
products. An average forward application touches about 74 coefficients; an average
backward one about 282. Of 2058159/2058195 backward applications,
1089354/1089357 target inherited reducer rows and 968805/968838 target other rows;
these are repeated visits, not distinct targets or measured time shares. #712
already avoids about 1.115 billion prefix-entry visits in this accounting. The
remaining affected-tail work is real and is not the prefix optimization again.

## Matrix working-set bounds

| Measurement | GF(32003) | GF(2147483647) |
|---|---:|---:|
| Zeebra maximum initial entries | 783727 | 783737 |
| Zeebra mathematical live-entry peak | 3932926 | 3933045 |
| Zeebra sparse live-entry peak including old target/scratch duplicates | 3933280 | 3933399 |
| Zeebra sparse capacity high-water, slots | 6857596 | 6861263 |
| Zeebra entry bytes | 16 | 16 |
| Zeebra largest dense buffer | 48080 bytes | 96160 bytes |
| Zeebra auxiliary incidence/pivot capacity maximum | 7198576 bytes | 7198728 bytes |
| grobx maximum observed stored sparse entries | 741444 | 741456 |
| grobx maximum accounted capacity snapshot | 33895400 bytes | 33895408 bytes |

Zeebra's mathematical payload is about 60 MiB; allocated sparse slots alone are
about 104.6 MiB. Dense and auxiliary figures are independent maxima, so **do not
sum them as an observed simultaneous total**. They help bound RSS, not reconcile
every allocator byte.

Grobx's roles differ: original columns are four-byte IDs whose coefficients are
borrowed from basis polynomials; made rows have separate four-byte columns and
four-byte coefficients. Its largest stored snapshot is mostly 740023/740035
original column references, not filled-in coefficient-bearing reduced rows.
The snapshots include owned row/work buffers at sampled boundaries, but exclude
shared basis coefficients, monomial tables, headers/pivot maps, some external
result collections and input-echelon merges. They are **row-boundary lower bounds on accounted allocated-capacity and
stored-entry high waters**, not bounds on resident memory or complete live
mathematical coefficients.

The 32 MiB original-column reservation explains why the observed capacity can exceed
process RSS: reserved virtual capacity is not committed resident pages. Packing
Zeebra's unchanged 3.93M live tuples to eight bytes still leaves about 30 MiB of
payload, above grobx's entire stock process peak. Representation-only halving
therefore cannot close the RSS gap while preserving that live count. Fewer
materialized rows/fill and source-coefficient borrowing are concrete additional
mechanisms. #268 retains the whole-process allocation ledger; this bounded census
does not claim to explain every byte of the 8.3× stock RSS difference.

## Attribution decisions and downstream gates

| Question | Verdict | Next action |
|---|---|---|
| Is the gap equal matrix work executed faster? | **Reject** for observed MAC work: normalized products differ 3.11×/9.44× even including discarded grobx work. | Optimization choices must consider work reduction, not only field kernels. |
| Is a smaller maximum matrix the explanation? | **Reject**: grobx reaches larger row/column maxima. | Use phase/role/product and fill counts. |
| Is field width alone the field-inversion cause? | **Reject**: both grobx cases are Gf31/u32; plain randomization branches differ. | #714 same-prime isolated combinations/tests ablations and exact-validation cost. |
| Is full-row backsub materialization a useful target? | **Adopt for bounded feasibility**, not production. | #269 prove what F4 extraction needs, then compare candidate/new-row-only and row-major scratch against current prefix-tail merges; price roles by coefficients, not row counts. |
| Can packing alone recover grobx memory? | **Reject** at unchanged live count; **adopt** combined role/lifetime/layout investigation. | #268 compare checked compact columns, coefficient borrowing and necessary live rows under fixed budgets. |
| Is SIMD the main established explanation? | **Defer/unsupported**: bands activate in one plain matrix and aggregate matrix-kernel source reuse is limited. | #715 scalar single-target versus scalar multi-target versus SIMD with fixed arithmetic/skipping. |
| Is a signature redesign justified? | **Defer**: default discards its signature run on both inputs. | #716 signatures-off/handover controls; #223 remains historical evidence, not an automatic implementation decision. |
| What remains of kernel/arithmetic cost? | **Unresolved**: work ratios alone do not assign wall-time shares, and merge/scan/normalization costs differ. | #270 same-prime representation and delayed-arithmetic controls; #273 consumes only justified policies. |

These are research priorities, not forecast gains or a product-of-speedups model.
No solver algorithm, arithmetic, pivot order, field representation or default was
optimized. Correctness remains exact for Zeebra; accepting these externally
verified raw grobx results does not establish soundness of arbitrary Monte Carlo
zero skipping. Larger public MQ/Katsura/Cyclic experiments gate adoption and were
not needed to price these fixed-input baseline trajectories.

## Validation and remaining limits

Red–Green tests preceded the report parser, scoped work counters, process/input
checks and content-addressed artifact extension. Known-rank tests verify scalar,
band-lane products, live/capacity snapshots, unchanged full F4 output, and
scope restoration after panic/refusal. Report tests exercise all six original raw
MQ reports plus malformed completion/restart/counter cases. CI also reconstructs
all 60 new responses, verifies full answers, compares structural paths, reconciles
work totals and regenerates the committed tables.

Five final work tests, 192 linalg tests and 2771 active library tests were exercised;
the library suite's single Singular-launch failure was rerun successfully after
loading `tools/external/env.sh` (the initial shell lacked the executable on PATH).
The frozen counter source predates observer-only refusal cleanup in `b37ea6d3`;
no measured solve refused, and no post-cleanup timing is claimed. Build/source
fingerprints and all raw response bytes remain available.

Remaining uncertainties are causal feature attribution, a complete grobx live
allocation peak, all original coefficient-array sharing and allocator residency,
per-criterion plain-F4 pair rejection, exact source-level repeated target loads,
physical cache/bandwidth behavior, and generality outside these two public MQ10
inputs. The external paper/probability analysis belongs to #714/#716. None of
these omissions changes the demonstrated fact that the observed matrix work is
substantially different.
