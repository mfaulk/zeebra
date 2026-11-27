# Exact decomposition into disjoint variable components (#1036, Stage 1)

**Measured at:** `e5aad5a8` — `cargo run --release --example decompose_evidence`, the
repository's release profile, on the owner's M4 Pro laptop (macOS, ARM64). One unpinned run per row,
no repetition, no comparand: **development figures, not a deciding measurement** (tracker #1169).

**Status:** Stage 1 (laptop implementation) is done: an opt-in wrapper, its correctness argument,
tests, and the symbolic-state evidence below. The evidence is the **expected reject signal** the
issue's stop conditions name. Generic F4 already does no cross-component elimination work on these
inputs. Stage 2 (the deciding ≥ 1.5× measurement against best Zeebra and grobx) still needs its own
workstation allocation, and on this evidence it is unlikely to pass.

## 1. What was built

`zeebra::grobner::f4_decomposed(generators, order, options, cancel)`, in `src/grobner/decompose.rs`.
It reads `planning::structure::incidence` (#1009), and with two or more components it runs the
caller's F4 route on each component's generators separately and returns the union of the bases,
sorted as F4 sorts its output. With one component it is the caller's route, run once on the whole
input. Nothing calls it by default.

Each component runs in the full `N`-variable ring with only its own generators. So the **induced
order** needs no construction: every polynomial a component forms lies in `K[X_i]`, and the
requested order restricted to those monomials is a monomial order on `K[X_i]`. Lex, block and
weighted orders need no translation, and no smaller ring type has to be instantiated per component.
The module documentation gives the full argument: coprime leading monomials across components,
freeness of `K[X]` over `K[X_i]`, reducedness of the union, the unit exception, and degenerate
generators.

**One budget.** `max_wall_time` is a deadline from entry. `max_batches` and `max_basis_elements` are
charged with every component's work, including work a fallback discards. `max_live_bytes` for a
later component is reduced by the term payload of earlier components' retained bases. A
resource refusal falls back to the undecomposed computation on what is left. Time stops,
cancellation, invalid options and certification failures return as they are. The wrapper also
checks the deadline itself before each component and before the fallback, because F4 always
reduces one batch before reading its clock. Cancellation is an `AtomicBool`, checked per batch on
conventional F4 and between components under `GradedEngine::Adaptive`, whose dispatch takes no
observer.

## 2. Tests

`src/grobner/decompose/tests.rs`, 16 tests, 0.11 s in a debug build:

- the decomposed basis equals the undecomposed F4 basis and the crate's Buchberger basis, under
  grevlex, lex and a grevlex/lex block order, on interleaved blocks over GF(31) and GF(2³¹−1),
  including three unequal blocks and positive-dimensional components;
- coupling with no mixed monomial (`x² + y² − 1`) and a coupled-blocks control do not split;
- a unit component, a nonzero constant generator, zero generators, unused variables, the empty
  input;
- a single component is the plain route, with the same statistics;
- the shared batch, basis-element and byte budgets (the retained first component's output pushes
  the second over a budget that admits it alone, and the fallback then runs on the full byte
  allowance); cancellation without fallback; a spent deadline not refunded; the adaptive engine.

Inputs come from `benchmark_systems::dense_blocks`, a new seeded generator of dense quadratic
blocks whose variables interleave in the variable order. None of the sizes is a `zb/coupled-blocks`
rung, and none is in #1162's M35 panel.

## 3. Symbolic state, decomposed vs undecomposed

GF(2³¹−1), default `F4Options`, seed `0x1036`. `rows`, `cols` and `live` are the largest matrix's
rows, columns and peak live nonzeros. For the split arm they are the maximum over components. `ops`
is row operations summed over every batch and component, and `ms` is the whole call's wall time.

| input | order | rows whole → split | cols whole → split | live whole → split | ops whole → split | ms whole → split |
|---|---|---|---|---|---|---|
| 3+4 | lex | 44 → 29 | 68 → 47 | 574 → 501 | 564 → 564 | 1.4 → 0.7 |
| 2×5 | grevlex | 180 → 90 | 213 → 107 | 4 634 → 2 328 | 5 952 → 5 952 | 1.8 → 1.0 |
| 3×4 | grevlex | 126 → 42 | 148 → 50 | 1 907 → 643 | 1 797 → 1 797 | 0.8 → 0.7 |
| 4×3 | grevlex | 68 → 17 | 85 → 22 | 621 → 159 | 364 → 364 | 0.3 → 0.3 |
| 3+6 | grevlex | 203 → 203 | 232 → 227 | 9 125 → 9 125 | 15 305 → 15 305 | 2.8 → 2.3 |
| 5+6 | grevlex | 293 → 203 | 333 → 227 | 11 431 → 9 125 | 18 190 → 18 190 | 3.3 → 3.1 |
| 2×7 | grevlex | 882 → 441 | 981 → 491 | 92 429 → 42 036 | 130 858 → 129 900 | 20.1 → 13.9 |
| 3×6 | grevlex | 609 → 203 | 679 → 227 | 36 470 → 9 125 | 46 280 → 45 642 | 8.7 → 6.9 |
| 2×8 | grevlex | 1 918 → 959 | 2 087 → 1 044 | 317 093 → 158 699 | 673 135 → 678 093 | 47.3 → 51.0 |

Every row's bases were checked equal. Detection (`incidence`) cost 4–20 µs.

## 4. Reading

- **The undecomposed matrices are block sums, not products.** With k equal blocks, rows, columns
  and peak live entries shrink by almost exactly k. That is the signature of a matrix that is the
  concatenation of the components' matrices at the same degree. The issue's premise was that
  generic F4 "pays for the full product of the components' monomial spaces". Under these inputs it
  does not: a pair from component i generates only multiples in `K[X_i]`, and symbolic
  preprocessing only pulls in reducers whose leading monomials divide those, which are again in
  `K[X_i]`. Cross-component S-pairs are discarded by the product criterion before any matrix is
  built.
- **Elimination work is unchanged** (ops ratio 0.99–1.01), because a block-diagonal matrix
  eliminates as its blocks do. The small differences on 2×7, 3×6 and 2×8 come from batches of
  different composition reaching slightly different intermediate rows, not from saved work.
- **What decomposition does buy is peak memory per batch** (k× on equal blocks) and freedom of
  schedule: a component with a lower degree of regularity no longer shares batches with the rest.
  Neither shows up in wall time here. The 0.9–2.0× wall ratios are single unpinned runs of one to
  fifty milliseconds and do not separate from noise. Where ops are equal, the honest prediction
  for a pinned run is ≈ 1×, plus whatever per-batch overhead (sorting, hashing a larger column
  set) scales superlinearly in matrix width.

**Stop-condition verdict.** "If symbolic-state evidence shows generic F4 already removes nearly
all cross-component work on fresh inputs, record that as the expected reject signal before
Stage 2." It does, and this note records it. The remaining open question for Stage 2 is narrow:
does matrix *width* cost superlinearly anywhere (symbolic preprocessing's monomial sets, the
parallel paths, the signature engine, the 16-worker arm)? A Stage 2 run should be designed to
answer that, not to repeat the row-operation count above.
