# Bilinear and multigraded Gröbner feasibility (#1034)

**Status:** in progress, no decision. The instruments are here: the exact structure verifier, the
seeded bilinear generator and the bidegree census. So are the development matrix counts (§5). On
balanced affine instances they meet the pre-declared count criteria, but narrowly on one of them
and on one shape only. The comparator arms and the deciding freeze are still open (§6).

**Measured at:** `73a14be0`, tag `measured/1034-bilinear-census` (matrix counts only; no timing or memory figure appears here).

Parent: #1028 (candidate C). Generator family: #1007. Shared verifier: #1010.

## 1. Contract

The task is the complete reduced Gröbner basis of the **original ideal**, in the requested order
(grevlex unless stated), over a prime field. Any multigraded computation is internal, and a
conversion back to the requested basis is charged to it.

Eligibility is decided **exactly**, never by a learned or heuristic signal. Every generator is
checked against a declared block split. For affine inputs, the inhomogeneous part is counted
rather than ignored.

## 2. The verifier: `planning::multigrading`

`src/grobner/planning/multigrading.rs`.

- A `BlockSplit` assigns every variable to one block. Blocks are numbered from zero, and none may
  be empty. `BlockSplit::two_blocks(N, k)` is the bilinear split `x = x_0 … x_{k−1}`, `y = the
  rest`, the same split `BigradedHilbertSeries` uses.
- The **multidegree** of a monomial is its exponent sum over each block.
- `multigrading(system, split)` reports, for each nonzero generator, its bound, whether it is
  homogeneous, how many distinct multidegrees it has, and its top and lower term counts. The
  bound is the componentwise maximum of its terms' multidegrees.

It makes two exact statements:

| statement | method | meaning |
|---|---|---|
| multihomogeneous of `d` | `all_homogeneous_of(d)` | every term of every generator has multidegree exactly `d` |
| within `d` | `within(d)`, `violations(d)` | every term is `≤ d` componentwise, so each generator is the dehomogenization of a multihomogeneous form of multidegree `d` (one homogenizing variable per block) |

An affine bilinear system `xᵀA_i y + b_iᵀx + c_iᵀy + d_i` is exactly one that is within `[1, 1]`.
Its linear and constant terms are counted in `lower_terms`. A bound need not be attained by any
term: `x + y` is within `[1, 1]` with no top term. Under total degree, `x·y` and `x²` cannot be
told apart; the split separates them (#207).

The verifier does **not** check genericity, dimension or regularity. Every complexity statement
in §4 needs those as well.

Cost: one pass over the terms, `O(terms · N)`, with no allocation beyond one vector per term.

## 3. The generator: `benchmark_systems::bilinear`

`src/grobner/benchmark_systems/bilinear.rs`. This is #1007's bilinear/multihomogeneous family.
Each instance is fixed by a `BilinearSpec`:

| parameter | meaning |
|---|---|
| `x_variables` | `k`, the size of the `x` block; `y` holds the other `N − k`. Both blocks are nonempty. Balanced is `k = N/2`; the unbalanced ratios 1:2 and 1:3 come from `k = N/3` and `k = N/4`. |
| `equations` | `m`. A zero-dimensional affine system needs `m ≥ N` generically. |
| `affine` | adds `b_iᵀx + c_iᵀy + d_i`, with every coefficient nonzero. Without it, every generator is bihomogeneous of `(1, 1)`. |
| `support_per_mille` | the share of the `k(N − k)` products `x_a y_b` that each generator keeps, drawn independently per generator. A generator whose draw keeps none keeps one random product. |
| `perturbation` | distinct same-block products `x_a x_b` or `y_a y_b` added to each generator. This builds the nearby perturbed control. |
| `planted` | chooses each `d_i` so the system vanishes at a seeded point. Affine only. |
| `seed` | one `StdRng` (rand 0.8). Equal specs give equal systems. |

The draw order is part of the family's definition, and changing it changes every instance. It is:
the planted point first, then for each generator the support mask, the `A_i` coefficients, `b_i`,
`c_i`, the perturbation monomials and their coefficients, and `d_i`.

What is **known** by construction:
- An unperturbed affine instance is within `[1, 1]`.
- An unperturbed homogeneous instance is bihomogeneous of `(1, 1)`.
- Every drawn coefficient is nonzero, so the support is exactly the drawn one.
- A planted instance vanishes at its point.
- A perturbed instance violates `[1, 1]` in every generator, and the tests check this through the
  verifier.

What is **not known**: dimension, radicality, and the number of solutions. Faugère, Safey El Din
and Spaenlehauer's bounds hold for generic systems. A sparse support or a perturbation may fall
outside their hypotheses, and no instance is checked against them here.

The family is not yet registered in a corpus manifest. That follows #1005 (§6).

## 4. Assumptions table (draft)

The source is Faugère, Safey El Din and Spaenlehauer, *Gröbner bases of bihomogeneous ideals
generated by polynomials of bidegree (1,1)* (arXiv:1001.4004; J. Symbolic Comput. 2011).

| claimed effect | needs | verified by this code? |
|---|---|---|
| affine bilinear, `d_reg ≤ min(n_x + 1, n_y + 1)` under grevlex | zero-dimensional, generic coefficients, `m = n_x + n_y` | bilinearity yes; genericity and dimension no |
| Jacobian-minor syzygies extend the F5 criterion | bihomogeneous `(1, 1)`; their Conj. 4.1 for the full description | bihomogeneity yes; the conjecture no |
| per-bidegree Macaulay matrices | multihomogeneous input | yes, exactly |
| bounds for unbalanced blocks or other bidegrees | stated hypotheses only; no general transfer | n/a |

## 5. Matrix counts (development, measured at `73a14be0`)

### 5.1 Instrument

`src/grobner/bilinear_census.rs`. A `BidegreeCensus` is an F4 `BatchObserver`. It takes every
matrix conventional F4 builds, before elimination, and groups the matrix's rows by their bidegree
bound: the componentwise maximum over the row's terms. Each group is one block, with that group's
rows and the distinct monomials they touch.

- **Bihomogeneous input.** Every built row is bihomogeneous, so the matrix is exactly
  block-diagonal. The blocks partition its rows, columns and nonzeros, and a test checks this.
- **Affine input.** A row `t·g` bihomogenizes to bidegree `bound(t·g)`. The same affine monomial
  then becomes a different column in each block that holds it, so the blocks' columns add up to
  more than the matrix's ("column duplication" below). The census counts the rows F4 actually
  built. It does **not** claim that a bihomogenized computation builds the same rows: the affine
  computation exchanges information across degrees, and a homogenized one would not.

The run is `examples/bilinear_census.rs`, and its artifacts are in
[`research/1034-bilinear-census/`](../../research/1034-bilinear-census/). It covers the cohort, the
pre-declared criteria and the instance statuses below. Every figure is a count; none is a time.

- **S** = the largest built matrix ÷ the largest regrouped block, both as rows × columns.
- **D** = the perturbed control's largest matrix ÷ the bilinear instance's largest matrix. The
  control adds two same-block products to each generator.
- **Share** = ln D ÷ (ln D + ln S): the part of the total gain over the nearby non-bilinear control
  that total-degree F4 already has, through its lower solving degree.

### 5.2 Results

Each row covers 3 fields × 3 supports × 2 seeds. Brackets give `[min, max]`.

| kind | k × n_y | completed | F4 degree | control degree | S | D | share | column duplication |
|---|---|---:|---|---|---:|---:|---:|---:|
| affine | 2 × 6 | 18/18 | 4 | 7–9 | 3.25 [2.51, 3.61] | 134 [22, 1140] | 0.817 [0.708, 0.856] | 2.54 |
| affine | 3 × 6 | 18/18 | 5 | 8–9 | 7.80 [7.75, 10.96] | 474 [121, 2342] | 0.750 [0.674, 0.791] | 3.16 |
| affine | **5 × 5** | 18/18 | 7 | 9–11 | **13.64** [8.70, 18.83] | 522 [37, 1929] | **0.702** [0.626, 0.749] | 4.36 |
| affine | 3 × 9 | 18/18 | 5 | refused | 5.29 [5.29, 6.03] | — | — | 3.05 |
| affine | 4 × 8 | 18/18 | 6 | refused | 7.85 [7.83, 9.48] | — | — | 3.45 |
| affine | **6 × 6** | 18/18 | 8 | refused | **14.96** [14.96, 30.86] | — | — | 4.61 |
| affine | 7 × 7, 8 × 8 | 0/18 each | refused | — | — | — | — | — |
| homogeneous | 2 × 6 | 18/18 | 5–8 | 8–14 | 3.66 [2.80, 3.66] | 350 [50, 4371] | 0.823 [0.751, 0.866] | 1.00 |
| homogeneous | 3 × 6 | 18/18 | 8–9 | 8–15 | 7.13 [6.12, 9.82] | 526 [57, 2853] | 0.762 [0.657, 0.792] | 1.00 |
| homogeneous | 5 × 5 | 18/18 | 8–10 | 9–14 | 10.54 [3.35, 11.02] | 146 [20, 1082] | 0.680 [0.617, 0.774] | 1.00 |
| homogeneous | 3 × 9 | 18/18 | 11–12 | refused | 5.23 [2.18, 12.22] | — | — | 1.00 |
| homogeneous | 4 × 8 | 18/18 | 11 | refused | 5.37 [1.00, 8.94] | — | — | 1.00 |
| homogeneous | 6 × 6 | 18/18 | 11–12 | refused | 10.42 [6.51, 12.63] | — | — | 1.00 |
| homogeneous | 7 × 7 | 0/18 | censored (1), skipped (17) | — | — | — | — | — |
| homogeneous | 8 × 8 | 0/18 | refused | — | — | — | — | — |

"Refused" means F4's shipping live-entry budget (32 M entries) refused the run. A re-run at
256 M entries spent more than 30 minutes inside one batch of the first 6 × 6 instance, where the
wall cap cannot interrupt, and it was stopped. `research/1034-bilinear-census/tables.md` has
every column. That includes the signature engine's matrix extents: on the balanced affine shapes,
its largest rows × largest columns is still 6.8× (5 × 5) and 7.9× (6 × 6) the largest regrouped
block. That product is an upper bound on its largest matrix, because the two maxima may come from
different batches.

### 5.3 Against the pre-declared criteria

The criteria were posted on #1034 before any count was read. The rule is: go toward the deciding
freeze if the median S over completed balanced affine instances is ≥ 2 and their median share is
< 0.75. It is disproved if S < 1.5 or the share is ≥ 0.75.

- **Median S = 14.96** over 36 instances (5 × 5 and 6 × 6). The criterion holds by a wide margin.
- **Median share = 0.702** over 18 instances, all 5 × 5, because every 6 × 6 control was refused.
  The criterion holds, but narrowly: the largest share is 0.749.

So the counts **support** the hypothesis under the stated rule. They do not settle it.

- **One shape decides the share.** The share falls with size: affine 0.817 → 0.750 → 0.702 from
  2 × 6 to 3 × 6 to 5 × 5. That trend favours the hypothesis but is not evidence for 6 × 6 and up,
  which were not measured here.
- **The degree drop is large.** The bilinear instances already run F4 at degree 7 (5 × 5), against
  9–11 for their controls, so their F4 matrices are 37–1,929× smaller than the controls'. Total-degree
  F4 therefore already takes most of what bilinearity offers. The regrouping adds another 9–19×
  on top, in rows × columns.
- **Affine regrouping duplicates columns** 4.4–4.6× on the balanced shapes. S already includes
  that, because each block counts its own columns. But a real bihomogenized computation builds
  rows of its own (§5.1), and only a prototype can say whether S survives that.
- **F4's degree is a column degree**: the largest total degree of any matrix column. It is one
  above the `min(n_x + 1, n_y + 1)` bound of §4 on 5 × 5 (7 against 6) and on 6 × 6 (8 against 7).
  The two measure different things, so this is no contradiction of the bound.

## 6. Remaining work

1. **The excluded shapes on the bench host.** That means balanced affine 7 × 7 and 8 × 8, plus
   the 6 × 6 controls, with F4's live-entry budget raised (`ZB_ENTRIES`, `ZB_SHAPES` in the
   example), so the share is measured on more than one shape.
2. **Comparator arms.** Pinned grobx, and Zeebra's conventional and signature F4 at 1 and 16
   workers, under the shared measurement rules on #1034.
3. **The deciding freeze** at a tagged revision, after #975.
4. **Corpus registration.** Register the family under #1005's manifest, with lineage fields.
5. **The decision**, go or defer/reject, recorded here. Go means filing the bounded prototype issue
   #1034 specifies.

