# Bilinear and multigraded Gröbner feasibility (#1034)

**Status:** decision recorded: **go** under the pre-declared count criteria (§6), and the bounded
prototype filed as #1224. The instruments are here: the exact structure verifier, the seeded
bilinear generator and the bidegree census. So are the matrix counts (§5), now at three balanced
affine sizes. This is a feasibility result, not a solver result; the comparator arms are still
open, on the bench host (§7).

**Measured at:** `73a14be0` (tag `measured/1034-bilinear-census`) and `efa2478d` (tag `measured/1034-bilinear-census-2`); matrix counts only, no timing or memory figure appears here.

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

## 5. Matrix counts (development, measured at `73a14be0` and `efa2478d`)

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

### 5.2 Two runs

The counts come from two runs on the same macOS laptop. They do not depend on the machine, the
worker count or the build profile; the run limits decide only which instances complete.

1. **`73a14be0`** (PR #1112): the whole cohort in one process, at F4's shipping budgets (32 M live
   entries) and a 60 s wall cap.
2. **`efa2478d`** (this note's second revision): every instance and shape that run did not
   complete, one process per instance and arm (`split_run.py`). The run limits were fixed before
   any of these counts was read: F4's live-entry budget raised to 400 M (`ZB_ENTRIES`, a 6.4 GB
   payload), a 12 GB RSS ceiling and an 1,800 s wall cap per process, both enforced by the
   watchdog, and 6 workers. The binary was the `ci-release` profile with thin LTO.

A run of the first kind that completed was not repeated. The second run reproduces it where the
two overlap: two 5 × 5 affine instances rerun at `efa2478d` give identical F4 counts.

Statuses:
- **refused (F4)**: F4's own live-entry budget refused the run (32 M in run 1, 400 M in run 2).
- **refused (RSS)**: the watchdog stopped the run at the 12 GB RSS ceiling.
- **censored**: past the wall cap. No run of the second kind reached it.
- **skipped**: not attempted, because an earlier instance of the same shape, kind and arm was
  censored or refused at the RSS ceiling. This is the pre-declared rule, applied per arm, and
  extended from the wall cap to the RSS ceiling because both stop a run that has already spent
  its budget. It is applied in the pre-declared order: GF(31) first, then by support and seed.

None of the refused, censored or skipped instances counts toward any figure below.

### 5.3 Results

Each row covers 3 fields × 3 supports × 2 seeds. Brackets give `[min, max]`. "Controls" says how
many of the completed instances have a completed control; the share is taken over those only.

| kind | k × n_y | completed | F4 degree | control degree | S | D | share | column duplication | controls |
|---|---|---:|---|---|---:|---:|---:|---:|---|
| affine | 2 × 6 | 18/18 | 4 | 7–9 | 3.25 [2.51, 3.61] | 134 [22, 1140] | 0.817 [0.708, 0.856] | 2.54 | 18 |
| affine | 3 × 6 | 18/18 | 5 | 8–9 | 7.80 [7.75, 10.96] | 474 [121, 2342] | 0.750 [0.674, 0.791] | 3.16 | 18 |
| affine | **5 × 5** | 18/18 | 7 | 9–11 | **13.64** [8.70, 18.83] | 522 [37, 1929] | **0.702** [0.626, 0.749] | 4.36 | 18 |
| affine | 3 × 9 | 18/18 | 5 | 10–11 | 5.29 [5.29, 6.03] | 5228 [2968, 20637] | 0.832 [0.828, 0.856] | 3.05 | 5; 1 refused (RSS), 12 skipped |
| affine | 4 × 8 | 18/18 | 6 | — | 7.85 [7.83, 9.48] | — | — | 3.45 | 0; 1 refused (RSS), 17 skipped |
| affine | **6 × 6** | 18/18 | 8 | 11–12 | **14.96** [14.96, 30.86] | 3261 [775, 7274] | **0.749** [0.677, 0.767] | 4.61 | 18 |
| affine | **7 × 7** | 18/18 | 8–9 | — | **21.87** [21.67, 29.45] | — | — | 4.51 | 0; 1 refused (RSS), 17 skipped |
| affine | 8 × 8 | 0/18: 16 refused (F4), 1 refused (RSS), 1 skipped | — | — | — | — | — | — | — |
| homogeneous | 2 × 6 | 18/18 | 5–8 | 8–14 | 3.66 [2.80, 3.66] | 350 [50, 4371] | 0.823 [0.751, 0.866] | 1.00 | 18 |
| homogeneous | 3 × 6 | 18/18 | 8–9 | 8–15 | 7.13 [6.12, 9.82] | 526 [57, 2853] | 0.762 [0.657, 0.792] | 1.00 | 18 |
| homogeneous | 5 × 5 | 18/18 | 8–10 | 9–14 | 10.54 [3.35, 11.02] | 146 [20, 1082] | 0.680 [0.617, 0.774] | 1.00 | 18 |
| homogeneous | 3 × 9 | 18/18 | 11–12 | 12–20 | 5.23 [2.18, 12.22] | 256431 [46893, 4130830] | 0.883 [0.866, 0.902] | 1.00 | 10; 5 refused (F4), 1 refused (RSS), 2 skipped |
| homogeneous | 4 × 8 | 18/18 | 11 | 12–21 | 5.37 [1.00, 8.94] | 22602 [1390, 499266] | 0.858 [0.805, 1.000] | 1.00 | 13; 5 refused (F4) |
| homogeneous | 6 × 6 | 18/18 | 11–12 | 11–18 | 10.42 [6.51, 12.63] | 2171 [297, 80175] | 0.764 [0.708, 0.827] | 1.00 | 16; 2 refused (F4) |
| homogeneous | 7 × 7 | 18/18 | 13 | — | 2.89 [1.02, 3.98] | — | — | 1.00 | 0; 1 refused (F4), 1 refused (RSS), 16 skipped |
| homogeneous | 8 × 8 | 0/18: 1 refused (RSS), 17 skipped | — | — | — | — | — | — | — |

`research/1034-bilinear-census/tables.md` has every column, including the signature engine's
matrix extents. Those are context, not a criterion, and were not rerun: the signature arm was
run only at `73a14be0`, so no shape completed in the second run has one. They have also moved
since: one 5 × 5 instance rerun at `efa2478d` has different extents (3,161 × 3,311 against
4,429 × 4,291), while its F4 counts are identical.

The one 7 × 7 affine control attempted (GF(31), full support, seed 1) reached a degree-9 matrix
of 459,962 × 464,802 before the RSS ceiling. Its largest matrix is at least that, so its D is at
least 29.6 and its share at least 0.52. That bound decides nothing, because it sits below 0.75
either way, and the instance is refused under the rules above.

### 5.4 Against the pre-declared criteria

The criteria were posted on #1034 before any count was read. The rule is: go toward the deciding
freeze if the median S over completed balanced affine instances is ≥ 2 and their median share is
< 0.75. It is disproved if S < 1.5 or the share is ≥ 0.75. It is inconclusive between the two,
or if fewer than two balanced affine shapes complete.

- **Median S = 15.23** over 54 instances (5 × 5, 6 × 6 and 7 × 7). The criterion holds by a wide
  margin, and S grows with size: 13.64, 14.96, 21.87.
- **Median share = 0.716** over 36 instances (5 × 5 and 6 × 6), the ones with a completed
  control. The criterion holds.
- Three balanced affine shapes complete, so the result is not inconclusive. The 8 × 8 shape was
  refused at both budgets.

**The counts support the hypothesis under the pre-declared rule.** M35's count gate (plan §9.6)
adds "evidence at more than one balanced size". S has it at three sizes and the share at two.

What the rule does not see, and the prototype has to:

- **The share rises with balanced size.** Its per-shape median is 0.702 at 5 × 5 and 0.749 at
  6 × 6, where 8 of 18 instances are at or above 0.75. The pooled median is under the threshold
  because the 5 × 5 instances are. The share at 7 × 7 is unknown: its controls are out of reach
  here. The first version of this note read a falling share from 2 × 6 to 3 × 6 to 5 × 5; those
  shapes mix block ratios, and the balanced shapes alone show it rising.
- **Unbalanced shapes are worse.** On affine 3 × 9 the share is 0.83 over the 5 controls that
  completed, and the degree drop already explains most of the gain there. Unbalanced rows are
  reported and do not change the decision.
- **Homogeneous 7 × 7 has a small S**, 2.89 [1.02, 3.98], against 10.42 at 6 × 6. Its F4 runs at
  degree 13, and its largest bidegree block is a third or more of its largest matrix. Homogeneous rows do not
  change the decision, but a prototype on (1, 1) input should not assume S grows with size.
- **The degree drop is large.** On 6 × 6 the controls' F4 matrices are 775–7,274× the bilinear
  instances'. Total-degree F4 already takes most of what bilinearity offers; the regrouping adds
  15–31× on top, in rows × columns.
- **Affine regrouping duplicates columns** 4.4–4.6× on the balanced shapes. S already includes
  that, because each block counts its own columns. But a real bihomogenized computation builds
  rows of its own (§5.1), and only a prototype can say whether S survives that.
- **F4's degree is a column degree**: the largest total degree of any matrix column. It is one
  above the `min(n_x + 1, n_y + 1)` bound of §4 on 5 × 5 (7 against 6) and on 6 × 6 (8 against
  7), and at or one above it on 7 × 7 (8–9 against 8). The two measure different things, so this
  is no contradiction of the bound.

## 6. Decision

**Go**, under the criteria pre-declared on #1034: median S = 15.23 ≥ 2 and median share = 0.716
< 0.75 over completed balanced affine instances, at three shapes for S and two for the share.

As #1034's decision criteria require, this files the bounded prototype issue, #1224. It
specifies a multidegree-separated matrix construction for verified bilinear inputs, the exact
verifier with fallback to the shipping engine, the output path to the requested basis, and a
≥ 1.3× complete-task gate on the held-out block ratio. M35's ≥ 1.5× competitive gate (§9.6) is
recorded there separately.

This is a feasibility result, not a solver result. Under M35 §7.6 the prototype starts only with
time reallocated from a stopped package. Until a prototype passes its gate, WP F stands at
*feasibility delivered, solver advantage unproven* (M35 §9.6).

## 7. Remaining work

1. **Comparator arms, on the bench host.** Pinned grobx, and Zeebra's conventional and signature
   F4 at 1 and 16 workers, under the shared measurement rules on #1034 (M35's 1 h allocation).
2. **Corpus registration.** Register the family under #1005's manifest, with lineage fields.
3. **The prototype**, #1224, when M35 reallocates time to it.
4. **Out of reach here, if anyone needs them:** the 7 × 7 and 4 × 8 affine controls and the
   8 × 8 shapes, which need more than 12 GB, and the signature extents at `efa2478d`. None of
   them can change the decision above. A 7 × 7 share would only inform the prototype's
   expectations.
