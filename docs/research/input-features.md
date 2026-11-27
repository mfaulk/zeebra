# Structural input features: incidence, the linear part, supports and leading monomials (#1009)

**Measured at:** `6d46e583` (tag `measured/1009-feature-costs`), on the #1006 public pilot panel.
Dev mode, CCDs 1–2 reserved, CPUs 8–23. Data: [`research/1009-feature-costs/`](../../research/1009-feature-costs/README.md).

**Status:** definitions (§1–§7), the measured extraction-cost table (§8), the coverage summary of
the pilot panel (§9) and the stop-condition verdicts (§10). Four of the seven extractors fail the
declared bound on the panel's smallest inputs and move to #1010 (§10).

`src/grobner/planning/structure.rs` adds features that `SystemShape` (`planning/analysis.rs`) and
`DispatchFeatures` (`sigf4/dispatch.rs`) lack: equation–variable incidence and the affine-linear
subsystem. `src/grobner/planning/support.rs` adds the monomial supports (§5) and the initial
leading monomials under a requested order (§6). Nothing calls either module yet, and the dispatcher
is unchanged.

## 1. Two kinds of statement

| kind | features | may be used for |
|---|---|---|
| **exact** | `LinearSubsystem::consistent == false`; `IncidenceStructure::components` | eligibility and decomposition decisions |
| **presentation statistic** | everything else | prediction only, recorded as such |

- **Inconsistent linear part.** If the augmented matrix of the degree ≤ 1 generators has larger rank
  than the coefficient matrix, some linear combination of generators is a nonzero constant, and the
  ideal is the unit ideal. `test_inconsistent_linear_part_is_the_unit_ideal` checks this against F4.
- **Disjoint components.** If the generators split into blocks over disjoint variable sets, leading
  monomials from different blocks are coprime under any order. By Buchberger's product criterion,
  every cross-block S-pair reduces to zero, so the union of the blocks' reduced bases is the reduced
  basis of the whole. `test_disjoint_blocks_solve_separately` checks this. Two cases need explicit
  handling:
  - A nonzero constant generator makes the ideal the unit ideal whatever the components are. It is
    reported apart, in `constant_generators`.
  - Unused variables are free and belong to no block. They are listed in `unused_variables`.

  `grobner::f4_decomposed` (#1036) uses this to solve the blocks separately.
  [`component-decomposition.md`](component-decomposition.md) has what that saves and what it does
  not.

A small separator or a low elimination width, short of exact disconnection, is only a performance
hypothesis.

## 2. Definitions

The incidence graph is bipartite: generators on one side, variables on the other, with an edge when
the variable occurs with a positive exponent in some term of the generator. The **primal graph** has
the variables as vertices and joins two variables that share a generator.

This is **not** monomial co-occurrence. `SystemShape::interaction_pairs` joins two variables only when
they appear in one *monomial*. `x² + y² − 1` has `interaction_pairs = 0` but one incidence component,
`{x, y}` (`test_incidence_is_not_monomial_co_occurrence`). Both are kept because they measure
different things.

| feature | definition | cost bound |
|---|---|---|
| `components` | connected components of the incidence graph over nonconstant generators; each lists its variables and generator indices | `O(T·N)` exponent reads for `T` terms, plus near-linear union-find |
| `unused_variables` | variables in no generator | included above |
| `constant_generators` | nonzero constant generators | included above |
| `arity_histogram` | `(distinct variables, generators)` over nonconstant generators | included above |
| `elimination_width` | the largest degree at elimination, eliminating in greedy min-degree order on the primal graph with ties broken by index; an **upper bound** on treewidth | at most `width_work` units (default `2^20`); `None` if the cap is reached |
| `LinearSubsystem::rank` | rank over `F` of the coefficient matrix of the generators of degree ≤ 1 | `O(m·N·min(m, N))` field operations for `m` such generators |
| `LinearSubsystem::consistent` | the augmented matrix has the same rank | included above |
| `ScalarSubstitution` | a generator `a·x_j + h` with `a ∈ F \ {0}` and `x_j` absent from `h` | one pass per generator to detect, one pass over the system per substitution found |
| `fill_bound` | `Σ` over the other generators containing `x_j`, over their terms, of `C(r + e − 1, e)`, where `e` is the term's exponent of `x_j` and `r` is the number of terms in `h` | included above |

Notes:

- **Rank depends on the field.** `x + y` and `x − y` have rank 2 in odd characteristic and rank 1 in
  characteristic two (`test_linear_rank_depends_on_the_field`). Rank is computed over the actual
  coefficient field, never over the integers.
- **A polynomial coefficient is not a scalar.** `y·x + 1` does not solve for `x`. Neither does
  `x + x²`, because `x` occurs in a second term.
- **`fill_bound` is an upper bound before merging.** Substituting `x_j = −h/a` turns `x_j^e` into at
  most the number of degree-`e` monomials in `r` symbols. Merging and cancellation only lower the
  count. The bound grows quickly with `e`, so it is loose for high powers.
- **Width is greedy.** Min-degree elimination finds the treewidth exactly on the paths, cycles and
  cliques in the tests, but in general it is only an upper bound.

## 3. Invariance

| feature | variable permutation | generator reorder | generator scaling | invertible generator mixing | ideal invariant? |
|---|---|---|---|---|---|
| component count and sizes | invariant | invariant | invariant | **not invariant**: mixing blocks merges them | no |
| component membership | relabelled | indices relabelled | invariant | not invariant | no |
| `unused_variables` count | invariant | invariant | invariant | not invariant: cancellation can drop a variable | no¹ |
| `arity_histogram` | invariant | invariant | invariant | not invariant | no |
| `elimination_width` | not guaranteed, because ties break by index | invariant | invariant | not invariant | no |
| linear `rank` | invariant | invariant | invariant | not invariant: mixing can cancel a nonlinear part and add a linear generator | no |
| `consistent == false` | invariant | invariant | invariant | stays sound: it still implies the unit ideal | the conclusion is |
| scalar substitutions | relabelled | indices relabelled | invariant | not invariant | no |

¹ A variable absent from every generator is absent from every element of the ideal, so it is free.
The converse does not hold: a variable can appear in the generators and still not be constrained.

These are presentation features. They are legitimate predictors as long as they are recorded as
presentation features. Systems built from independent blocks, such as the planted family in
`strategy-selection.md` §2, keep their components only while the presentation keeps the blocks
apart.

## 4. Left to other issues

- Whether the dispatcher reads any of this through an allocation-free fast path. That is #1013's
  decision; §8 gives it the costs.
- Coverage of #1007's controlled families, which are not available (§9).

Scope items 2, 5 and 6 are §5 and §6. The costs, coverage and stop condition are §8–§10.

## 5. Supports: `support_profile`

| feature | definition | cost bound |
|---|---|---|
| `terms_histogram` | `(terms, generators)` over nonzero generators | one pass over the terms |
| `degree_spread_histogram` | `(max − min term degree, generators)`; spread 0 is a homogeneous generator | included above |
| `homogeneous_generators` | generators with spread 0; all of them is `hilbert::is_homogeneous` | included above |
| `top_degree_terms`, `homogeneous_capacity` | terms of each generator's top degree, and `Σ C(N + d − 1, d)` over generator degrees `d` | included above |
| `top_degree_density()` | `top_degree_terms / homogeneous_capacity` | — |
| `affine_density()` | `terms / Σ C(N + d, d)`, equal to `SystemShape::monomial_density` | — |
| `distinct_monomials`, `shared_monomials`, `max_monomial_multiplicity` | monomials across the system; those in two or more generators; the most generators any one is in | one hash per term |
| `overlapping_pairs` | unordered generator pairs sharing a **nonconstant** monomial | at most `overlap_work` pair insertions (default `2^20`); `None` if the cap is reached |
| `max_exponent`, `exponent_mass` | per variable, the largest exponent in any term and the sum over all terms | included in the first pass |
| `monomial_generators`, `binomial_generators` | nonconstant one-term generators; two-term generators | included in the first pass |
| `duplicate_generators` | nonzero generators that are a nonzero scalar multiple of an earlier one | expected `O(T)`: bucket by term count and lex-leading monomial, compare monic forms within a bucket |

Notes:

- **Two densities, because the capacity differs.** A homogeneous degree-`d` generator can only use
  the `C(N + d − 1, d)` monomials of degree exactly `d`. Measuring it against the `C(N + d, d)` of
  degree at most `d` understates it. `affine_density` is kept because it is the existing
  `SystemShape` figure, and the test checks that the two agree.
- **The constant is left out of overlap.** Nearly every affine generator has a constant term, and
  sharing it multiplies nothing. `shared_monomials` and `max_monomial_multiplicity` do count it.
- **Duplicates are exact about the presentation.** Dropping a scalar multiple of another generator
  leaves the ideal unchanged. The comparison is over the coefficient field: `x + y` and `x − y`
  are duplicates in characteristic two and not otherwise
  (`test_duplicates_are_normalized_and_field_exact`).

## 6. Initial leading monomials: `leading_profile`

Every figure here depends on the requested monomial order, which the profile records.

| feature | definition | cost bound |
|---|---|---|
| `leading_degree_histogram` | `(deg LM, generators)` | `O(T)` order comparisons |
| `divisible_leading` | generators whose LM is divisible by another's; of equal LMs, all but the first | `O(m² N)` exponent reads for `m` nonzero generators |
| `total_pairs`, `sampled_pairs` | `m (m − 1) / 2`, and the pairs examined | — |
| `coprime_pairs` | sampled pairs with coprime LMs | `O(m + pair_sample · N)` (default sample `2^14`) |
| `lcm_degree_histogram`, `gcd_degree_histogram` | `deg lcm` and `deg gcd` of the sampled pairs' LMs | included above |

Notes:

- **The sample is deterministic and spread out.** Up to the cap every pair is examined. Past it,
  the pair at linear index `⌊s · total / cap⌋` is taken for `s = 0 … cap − 1`, exactly `cap` pairs,
  so the late rows are reached rather than only the first generator's pairs
  (`test_pair_sampling_is_capped_and_spread`).
- **A coprime pair is exact for that pair.** Buchberger's product criterion reduces its
  S-polynomial to zero. The fraction is still only a predictor: it says nothing about the pairs that
  later generators form.
- **`divisible_leading > 0` means the input is not interreduced.** A generator whose leading
  monomial another divides is top-reducible before any pair is formed. A nonzero constant has
  leading monomial 1 and makes every other generator count.
- The divisibility count is quadratic in `m` and has no cap. On the pilot panel (`m ≤ 34`) the
  whole profile costs at most 16.8 µs and passes §10, so no cap is added yet.

## 7. Invariance of §5 and §6

| feature | variable permutation | generator reorder | generator scaling | invertible generator mixing | ideal invariant? |
|---|---|---|---|---|---|
| term, spread and homogeneity counts | invariant | invariant | invariant | not invariant | no² |
| densities | invariant | invariant | invariant | not invariant | no |
| distinct and shared monomials, overlap | invariant | invariant | invariant | not invariant | no |
| `max_exponent`, `exponent_mass` | permuted with the variables | invariant | invariant | not invariant | no |
| monomial, binomial, duplicate counts | invariant | invariant | invariant | not invariant | no |
| leading-monomial figures | **not invariant**: the order ranks variables by index | invariant³ | invariant | not invariant | no |

² Homogeneity of every generator is a property of the presentation. An ideal is homogeneous if *some*
generating set is, and mixing homogeneous generators of different degrees gives a non-homogeneous
generating set of the same homogeneous ideal.

³ Reordering changes which of two equal leading monomials counts as "first", but not how many count.
The pair sample is taken over pair positions, so past the cap a reorder can change which pairs are
sampled, but not `total_pairs` or `sampled_pairs`.

`test_support_profile_invariance_under_reorder_and_scaling` checks reordering and scaling together.

## 8. Measured extraction cost

**Panel.** The 78 `corpus-instance-v1` records of `research/m34-public-corpus/catalog.json`: 39
SymbolicData problems, each at 2³¹−1 and 2⁶⁴−59, grevlex, task T-GB (#1006, PR #1094).

**Method.** `examples/feature_costs.rs` runs one record per fresh process and measures two things:

- **Extractor cost.** Each extractor's median per-call time over 7 batches. Each batch repeats the
  call until it takes at least 2 ms.
- **Solve time.** The `entry` (`f4_signature_reported`) and `f4` (`f4_reported`) arms run
  alternately on `F4Options::default()` with a 60 s wall, up to 5 calls or 10 s per arm. The
  **cheapest arm** is the faster of their two medians.

Taking the faster of the two lowers the denominator, so the ratio is conservative. Both arms are
shipping entry points: `entry` is the dispatch every caller reaches, and `f4` is the engine it
falls back to.

Scope item 7 (field, order, task, worker cap) is read from the request in constant time and is
not timed. `DispatchFeatures` is computed inside `entry` and is already in its wall.

**Placement.** Dev mode: CCDs 1–2 reserved, CPUs 8–23, nothing compiled during the runs, builds
allowed on the other CCDs. Absolute times were taken beside builds. Each ratio pairs two figures
from one process.

**Rules, declared on #1009 before the run.**

- **Small inputs** are the records whose cheapest arm completes within 1 s: 72 of 78.
- **Threshold.** A feature passes if its worst ratio over the small inputs is at most 1%. The
  seven together are held to 2%.

| feature | scope item | median cost | max cost | median ratio, small | worst ratio, small (repeat) | worst record | small inputs over | failing solves at most |
|---|---|---:|---:|---:|---:|---|---:|---:|
| `analyze` (`SystemShape`) | 1, 2 (existing) | 2.9 µs | 67.5 µs | 0.160% | 2.501% (2.937%) | `sd-fourcircles@p31` | 8 / 72 | 130.7 µs |
| `is_homogeneous` | 2 | 15 ns | 301 ns | 0.001% | 0.067% (0.076%) | `sd-raksanyi@p31` | 0 / 72 | — |
| `incidence` | 3 | 1.3 µs | 15.9 µs | 0.069% | 1.536% (1.664%) | `sd-raksanyi@p31` | 2 / 72 | 61.7 µs |
| `linear_subsystem` | 4 | 112 ns | 10.1 µs | 0.009% | 0.991% (0.985%) | `sd-raksanyi@p64` | 0 / 72 | — |
| `scalar_substitutions` | 4 | 495 ns | 39.0 µs | 0.033% | 1.114% (1.094%) | `sd-raksanyi@p31` | 2 / 72 | 61.7 µs |
| `support_profile` | 1, 2, 6 | 6.0 µs | 84.1 µs | 0.327% | 6.545% (7.261%) | `sd-fourcircles@p31` | 20 / 72 | 372.6 µs |
| `leading_profile` (grevlex) | 5 | 594 ns | 16.8 µs | 0.041% | 0.480% (0.481%) | `sd-czapor-86a@p31` | 0 / 72 | — |
| all seven | | 11.6 µs | 213.3 µs | 0.616% | 10.530% (10.433%) | `sd-raksanyi@p64` | 19 / 72 | 372.6 µs |

The parenthesized worst ratios come from the repeat session, which ran straight after. Both
sessions give the same verdicts. "Failing solves at most" is the slowest cheapest-arm solve on which
the feature exceeds its threshold. Per-record figures are in
`research/1009-feature-costs/tables.md`.

Readings:

- **Every failure is on a solve under 0.4 ms.** On the 42 small records that take 1 ms to 1 s, no
  extractor exceeds 1%, and the set exceeds 2% nowhere. The largest set ratio there is 1.56%, on
  `sd-robot-jcf26` (n = 34, 10 ms). The 30 sub-millisecond records solve in 38–583 µs. On them, a
  few microseconds of extraction is several percent of the solve.
- **The cost scales with the input, as the bounds in §2 and §5 say.** The maxima are on
  `sd-signaltheory-f966` (796 terms), which no arm solves. Neither work cap (`width_work`,
  `overlap_work`) is reached on any record, so the panel does not measure what a cap costs.
- **The cold first call is 3–67× the warm median** (median over records, per extractor). Most of
  that is first-touch in a fresh process: `analyze` runs first and absorbs most of it. The verdicts
  use warm medians on both sides, because the solve's median likewise discounts its cold first call. A
  dispatcher that extracts once per process pays the cold figure. `tables.md` reports the worst
  cold ratio for each extractor.
- **Aside for #1011/#1012.** On the 32 records where `entry` routes to the signature engine, `entry`
  takes a median 1.62× the wall of `f4`. That ranges from 0.36× on `sd-singular-schwarz-9` to 4.8×
  on `sd-trinks-1`. These are 5-call dev-mode medians, not a qualification result.

## 9. Coverage of the pilot panel

**What the panel is.** It is #1006's public first slice only. #1007's controlled families are not
available: their claim went stale with no PR. The two fields give identical feature values on
every one of the 39 problems, because no record has a field-dependent rank or duplicate. The
panel is therefore **39 points in feature space, from 21 families**, not 78.

| region | records (of 78) |
|---|---:|
| variables `n` | 2–34; only `sd-robot-jcf26` above 16 |
| generators `m` | 3–34 |
| max degree | 2–12 |
| terms | 12–796 |
| `m > n` / `m = n` / `m < n` | 12 / 44 / 22 |
| every generator homogeneous | 2 (`sd-raksanyi`) |
| degree 2, no linear generator | 16 |
| affine-linear rank > 0 | 32 |
| a scalar substitution | 36 |
| a univariate generator | 12 |
| binomials > half the generators | 6 (`sd-robot-jcf26`, `sd-signaltheory-f633`, `-f966`) |
| a monomial generator | 2 (`sd-robot-rr`) |
| a duplicate generator | 4 (`sd-signaltheory-f855`, `-f966`) |
| a leading monomial divisible by another | 50 |
| greedy elimination width | 1–24; ≥ 10 on 10 records |
| top-degree density | 3.3·10⁻⁵ (`sd-ellipsoid-4`) to 1 (`sd-czapor-86a`) |
| cheapest solve | 38 µs – 7.8 s; 30 under 1 ms; 4 records refused by a budget (`sd-signaltheory-f966`, `sd-ellipsoid-m2`) |

**Gaps.** These are regions the panel never reaches:

- **The exact features are never exercised.** No record has more than one incidence component, an
  unused variable, a constant generator or an inconsistent linear part. The exact
  eligibility/decomposition facts of §1 are untested on public data. #1036 has no positive case
  here.
- **No caps.** Neither the width cap nor the overlap cap is reached, and no record has more than
  `2^14` initial pairs. The pair sample is always exhaustive.
- **One order, one task, two large primes.** The data never varies `leading_profile` by order, item
  7 by task, or the field-dependent features (rank, duplicates) by characteristic.
- **Thin at the extremes.** Homogeneous inputs are one problem. Wide inputs (`n > 16`) are one
  problem. Every initial pair coprime occurs nowhere.
- **Controlled scaling is absent.** That was #1007's role. Only signal theory, gametwo and Schwarz
  are parameter ladders. Robot kinematics and Runge–Kutta change size across distinct models.

A selector trained on this panel (#1013) sees too few distinct points to separate the features
that vary together, such as `n`, terms and width along the signal-theory ladder.

## 10. Stop-condition verdicts

The stop condition: "a feature whose extraction cannot be bounded below a declared fraction of the
cheapest arm's solve time on small inputs moves to #1010 or is dropped, with the measurement
recorded." The fraction is 1% per feature and 2% for the set, judged at the worst small input
(§8).

| feature | verdict | action |
|---|---|---|
| `is_homogeneous` | pass (0.07%) | stays inexpensive |
| `linear_subsystem` | pass, at the margin (0.99%) | stays inexpensive. It is within 0.01 points of the bound on `sd-raksanyi`, so any growth fails it |
| `leading_profile` | pass (0.48%) | stays inexpensive |
| `analyze` (`SystemShape`) | **fail** (2.5%) on `sd-czapor-86a`, `sd-ellipsoid-2`, `sd-fourcircles`, `sd-raksanyi` | moves to #1010 |
| `incidence` | **fail** (1.5%) on `sd-raksanyi` | moves to #1010 |
| `scalar_substitutions` | **fail** (1.1%) on `sd-raksanyi` | moves to #1010 |
| `support_profile` | **fail** (6.5%) on 12 problems, every one solved under 0.4 ms | moves to #1010 |
| all seven | **fail** (10.5%) | — |

**Why "moves to #1010", not "dropped".** That is the conservative reading. The four extractors
are kept in the crate and stay correct. They are simply not certified as inexpensive, so a policy
that reads them is charged their measured cost (plan §9.1, VBS⁺). None of them is dropped, for
three reasons:

- Each fails only on inputs that solve in under 0.4 ms.
- Each is under 1% on every small input that takes 1 ms or longer.
- `analyze` is the planner's existing first pass.

**For an owner decision (recorded on #1009).** The bound fails on 0.4 ms solves, and a selector has
almost nothing to gain there. A size gate before extraction would restore the bound: for example,
no extraction below a term count, with the default arm used instead. Whether to adopt such a
gate, or to restate the bound per millisecond of solve, is #1013's design question. This document
does not decide it.
