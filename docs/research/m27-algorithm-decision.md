# M27-D: defer an additional solver prototype

**Issue:** #457. **Decision:** no additional algorithmic prototype is justified by the retained
evidence. Reopen on the measurements in §5.
**Reviewed at:** `800b75df3a9b10fc9dfd83e1d03d67496ac5d4b4`, 2026-11-11.
**Measured at:** not measured here — figures below come from the cited M27 baseline and subsequent
records. Historical timings are neither re-measurements of this revision nor speedup denominators
for it. No new literature claims or cross-hardware timing comparisons enter this decision.

The issue permits a refusal. This is that outcome, following its narrowing after #668: the decision
concerns public polynomial-system solvers. Challenge imports and campaigns moved out of this
repository. The distinction between overdetermined and underdetermined MQ still matters; the old
challenge registry is not an executable benchmark here.

## 1. The measured target, and the part already implemented

The named target is **`mq-random-10`, GF(2147483647), grevlex**, digest
`72d0ad315fc25409792625465578d18329597d3ee183e75f257774d9215803b2`.
M27-0 measured its bottleneck at `1985504`: **79.5% final interreduction**, 14.9% elimination,
3.6% construction and 1.4% symbolic preprocessing. Three runs had identical work counts. This
is a measured M27 bottleneck, not an inference from an external engine. See
[`m27-baseline.md` §2](m27-baseline.md#2-the-stage-split-re-taken-at-1985504-and-304-did-not-move-this-row).

Making that historical interreduction free gives an **arithmetic upper bound** of
`1 / (1 - 0.795) = 4.88x` on that basis computation. It is not a bound on today's solver.
M27-A already acted on it: at `3d0e3759`, three repetitions of each arm measured:

| basis configuration | mean wall | mean per-process peak RSS |
|---|---:|---:|
| division, echelon batch rows | 27 536.2 ms | 162.1 MiB |
| matrix, reduced batch rows (ByOrder's graded route) | 4 695.7 ms | 418.8 MiB |

These are **measured basis costs**, from the same cohort on `workstation`, affinity `0-7`, one
worker, release with the repository ISA floor, under `benchlock`, one row per process. Their
**5.86x basis improvement** exceeds the historical stage-only ceiling because reducing batch rows
also changes earlier work. It is not a solver speedup. The study retains the increased RSS and
limited family coverage; see [`interreduction-cost.md` §3h](interreduction-cost.md#3h-575-the-2x2-over-both-flags-and-both-defaults-move).
The retained rows are in [`history.json`](../../research/competitive/results/history.json), cohort
`3d0e3759`, with both flags in `library_version`. That field names the measured arm `matrix`,
which is the route ByOrder selects for grevlex. RSS here is the arithmetic mean of the three
per-process peaks, converted from retained bytes to MiB; the study labels those values MB.

At the reviewed revision, `src/grobner/f4/options.rs:631` selects reduced batch rows and ByOrder.
The later counted experiment finds **zero division-loop steps** on this default path, over 247
returned elements (`interreduction-cost.md:1503`, §3i.0). Reusing the 79.5% share to fund another
interreduction rewrite would spend a bottleneck already removed. Today's remaining cost needs a
fresh profile.

The primary metric remains [#77's methodology](mq-comparison-methodology.md#1-the-primary-metric-time-and-peak-bytes-to-a-verified-solution):
**total wall and attributable process peak RSS to a point verified against the original system**.
The basis tables diagnose a stage; they exclude conversion and point recovery. A kernel vector,
basis, affordable matrix or higher completed degree does not satisfy that metric.

## 2. Read the bounds before selecting a candidate

Each row gives the strongest retained evidence and its applicability limit. None supplies a
measured full-solver gain on the named target under the reviewed defaults.

| candidate | measured or counted opportunity | cost and unresolved risk | disposition |
|---|---|---|---|
| Variable ordering | Historical two-system study: last-round-first was 1.67x and 1.61x faster in the basis experiment; reported peak matrix memory fell 2.1x and 1.3x. No measured gain on this target. | Checked permutation/apply/recover already exist. A generic selector needs useful orders without cipher-round metadata, charged selection work and correct point recovery. | Consider first for measurement; defer a default or portfolio. |
| HDF4 limiting | Historical pilot: 30.8 ms versus a fixed cap's 33.1 ms, within noise; slack zero reduced peak entries 74% versus uncapped. Entries are not process RSS. | Limiting modes already ship. Slack changes the time/memory trade; semiregular predictions have large measured errors on structured inputs. No current target-sized advantage over a fixed cap is established. | Keep selectable; defer a scheduler or automatic slack rule. |
| XL with block Wiedemann | Exact dense-quadratic model at n=20, m=40, degree 5: 53 130 columns, 16 364 040 nonzeros, 249.7 MiB of sparse entries. Operating degree is predicted. | Construction, block recurrence, kernel recovery and verified point extraction need a complete budget. Storage does not bound iterations, rank behaviour or recovery. | Defer a solver; construction counts alone cannot pass. |
| Adaptive solving policy | Counted quotient dimension is compared against dense conversion budgets. No validated time/memory objective rule across the requested five families and three routes exists. | Extend existing planning code. Need paired whole-route measurements, fallback cost and nonseparating/small-characteristic controls. | Defer objective-driven selection under #273. |

Evidence: [`structure-experiments.md` §2](structure-experiments.md#2-variable-order),
[`hilbert-driven.md` §§2, 6](hilbert-driven.md#2-fukuoka-type-iii-n10-the-instance-where-capping-pays),
[`xl-block-wiedemann.md` §§2–6](xl-block-wiedemann.md#2-what-is-priced-and-why-no-solver-is-needed),
and the pinned source map in §4. The variable-order report's memory column does not establish an
attributable process-RSS ratio.

The XL/F4 comparison also needs qualification. #453 measured a degree-5 refusal at **40 003 287
entries**, with a 40-million entry allowance, at `96bf1969` (base `b7847824`, no Rust delta).
That is a **lower bound on eventual demand**, not a peak. Its **1 495.5 MB RSS** includes basis
storage that subsequent changes removed. It identifies the original matrix-size barrier but cannot
size a new solver or predict today's memory. `f4-resource-scaling.md:732` (§11) retains the
measurement and `:815` explains #557's later exact construction-demand diagnostic. Neither prices
the complete XL iteration/recovery route. Affordable XL storage therefore does not pass the gate.

Two subsequent changes retire premises in the issue's original candidate list:

- **Berlekamp–Massey is implemented**, in `src/grobner/fglm/wiedemann.rs:182`. The XL note's
  missing-prerequisite statement is historical. Scalar conversion is not block Wiedemann for XL;
  it removes one piece of cost without supplying that solver.
- **Certified scalar Wiedemann conversion ships**, with adaptive size/density screening and
  classical fallback. Its public-family experiment measured conversion ratios of 4.28x at quotient
  dimension 625 and 23.75x at 3 125. These include operator construction and exclude basis computation
  and point recovery. They establish neither a solve ratio nor a universal crossover.
  [`certified-wiedemann.md`](certified-wiedemann.md) records the implementation patch, retained
  samples, independent certificate, RSS measurements and fallback limits.

The planner still preflights **classical dense blocks** before calling conversion
(`src/grobner/planning/policy.rs:374`). Adaptive conversion's smaller workspace is not by itself
proof that the planned route reaches it. A #273 study must exercise the public planned entry point,
including this integration boundary, as well as direct converter calls.

## 3. Shape and field determine applicability

In the overdetermined encryption shape `m = 2n`, many quadratic equations can constrain a small
quotient and motivate XL's fixed linearized operator. Equation count alone proves neither rank nor
necessary degree; the semiregular operating degree remains a prediction until checked.

In the underdetermined signature shape `n ≈ 1.5m`, a zero-dimensional solver cannot simply be handed
the original generic system. Specialization creates a different, often square system; a slice can
be inconsistent. Charge failed slices and recover/verify points in the original coordinates.
A slice's failure is not evidence that the original system has no point. The n=20, m=40 XL storage
model therefore cannot justify a signature-system solver.

Field size independently changes enumeration cost (`q^k` guesses) and arithmetic/storage. A GF(2)
bit-packing hypothesis is not a GF(31) or wide-prime result. This decision needs no current external
record-holder claim or cross-hardware timing ratio.

Existing negative decisions stand: signatures have a historical 33–60% rank-redundant pair-row
opportunity, not an end-to-end speedup; immediate lower-degree mutant priority already exists and
measured only 0–2 degree regressions per run; aggressive Hilbert deferral measured a 214x slowdown
on one structured case. See `signature-based.md:391`, `mutants.md:113` and `hilbert-driven.md:122`.
Block Wiedemann remains unsuitable as a replacement for F4 echelonization: F4 needs the transformed
row space, whereas XL's fixed operator serves a different output (`xl-block-wiedemann.md:12`).
None is reopened by the new conversion implementation.

## 4. Source map pinned to the reviewed revision

All source and documentation path:line citations refer to
[`800b75df3a9b10fc9dfd83e1d03d67496ac5d4b4`](https://github.com/mfaulk/zeebra/tree/800b75df3a9b10fc9dfd83e1d03d67496ac5d4b4),
not moving `main`. Measurement-era commits are stated separately.

| path:line at that revision | what it establishes |
|---|---|
| [`src/grobner/f4/options.rs:631`](https://github.com/mfaulk/zeebra/blob/800b75df3a9b10fc9dfd83e1d03d67496ac5d4b4/src/grobner/f4/options.rs#L631) | Recommended F4 strategies. |
| [`src/grobner/transform/reorder.rs:81`](https://github.com/mfaulk/zeebra/blob/800b75df3a9b10fc9dfd83e1d03d67496ac5d4b4/src/grobner/transform/reorder.rs#L81) | Bijection validation; apply and inverse point mapping are public. |
| [`src/grobner/planning/analysis.rs:128`](https://github.com/mfaulk/zeebra/blob/800b75df3a9b10fc9dfd83e1d03d67496ac5d4b4/src/grobner/planning/analysis.rs#L128) | Cheap features; no dimension or cost-model guarantee. |
| [`src/grobner/planning/policy.rs:374`](https://github.com/mfaulk/zeebra/blob/800b75df3a9b10fc9dfd83e1d03d67496ac5d4b4/src/grobner/planning/policy.rs#L374) | Dense preflight before conversion; shared attempt budgets in the same module. |
| [`src/grobner/fglm/options.rs:320`](https://github.com/mfaulk/zeebra/blob/800b75df3a9b10fc9dfd83e1d03d67496ac5d4b4/src/grobner/fglm/options.rs#L320) | Adaptive conversion in recommended options. |
| [`src/grobner/fglm/wiedemann.rs:48`](https://github.com/mfaulk/zeebra/blob/800b75df3a9b10fc9dfd83e1d03d67496ac5d4b4/src/grobner/fglm/wiedemann.rs#L48) | Size/density/workspace screen, three projections and fallback; recurrence at :182. |
| [`src/grobner/external/corpus.rs:445`](https://github.com/mfaulk/zeebra/blob/800b75df3a9b10fc9dfd83e1d03d67496ac5d4b4/src/grobner/external/corpus.rs#L445) | Public random-MQ controls independent of the moved importer. |

## 5. What would change the decision

The first hypothesis to test is **a cheap input-derived variable permutation improves total verified
solve time or process RSS on current public systems after charging permutation and recovery**.
This has the lowest implementation cost among the surviving hypotheses because checked
transformations exist. It is a proposed measurement, not a selected solver prototype or promised gain.

A useful reopening record would compare identity, reversal and one explicitly defined structural
ordering on public Katsura, Cyclic and random-MQ systems. Include known-point controls, and report
positive-dimensional and budget-refused cases as such. Before timing, test permutation round trips,
recover every point, and substitute it into every original equation. Compare reduced bases only
after returning to the same coordinates and monomial order; bases under different orders need not
be equal.

Use paired alternating-order current-default runs, fixed seeds, one worker and one row per process
for attributable RSS, under `benchlock`. Report all basis/conversion/recovery/verification costs and
dispersion. Proposed pilot caps are **60 s and 2 GiB per process**, externally enforced; they are
experiment limits, not measured costs. Retain refusals. A repeatable total time or RSS improvement
beyond the project's 20% readability band, with no material control regression, would justify a
separately scoped public prototype. The older two-instance round-aware basis-stage win does not
meet that condition.

For the other candidates, reopening requires respectively: a current Hilbert-limited versus fixed
cap result demonstrating the requested objective; a bounded XL construction/apply/recurrence/point-
recovery cost on an identified public system; or #273's measured whole-route table including adaptive
conversion and the planned-entry boundary. Existing #317 and #268 representation experiments retain
their own gates.

**Uncertainty:** today's full-solver stage split, generic ordering benefit, XL iteration/recovery
cost and a multi-family policy crossover are unmeasured here. No fitted or extrapolated gain fills
those gaps. The completed outcome of #457 is to defer an additional prototype until a testable
condition above is met.
