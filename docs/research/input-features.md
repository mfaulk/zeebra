# Structural input features: incidence, the linear part, supports and leading monomials (#1009)

**Status:** definitions and implementation only. No timing or memory figure appears here. The
measured cost table and the coverage summary #1009 asks for need the pilot panel from #1006/#1007,
and both are still open.

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

## 4. Still open in #1009

- Measured extraction cost, absolute and as a fraction of the cheapest arm's solve time, on the
  #1006/#1007 pilot panel. This needs that panel and a measurement host.
- A feature-space coverage summary of the pilot panel, and the stop-condition check against the
  measured costs.
- Whether the dispatcher reads any of this through an allocation-free fast path. That is #1013's
  decision, made after the costs are measured.

Scope items 2, 5 and 6, listed here as open before, are §5 and §6.

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
- The divisibility count is quadratic in `m` and has no cap. If the pilot panel shows it is too
  expensive on wide inputs, it gets a work cap like `overlapping_pairs`.

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
