# Sparse (toric) Gröbner bases: feasibility on Zeebra's inputs (#1035)

**Measured at:** branch `research/1035-sparse-toric` from `main` `04d949ff`. Apple M-series
laptop, release build. Every figure is a matrix count, so none depends on the machine.
**Status:** complete, 2026-11-25. **Decision: disproved** under the rule predeclared on #1035
([comment](https://github.com/mfaulk/zeebra/issues/1035#issuecomment-7171870608)).

Data, scripts and the full tables: [`research/1035-sparse-toric/`](../../research/1035-sparse-toric/README.md).

## 1. The method and its contract

Faugère, Spaenlehauer and Svartz, *Sparse Gröbner bases: the unmixed case* (ISSAC 2014,
arXiv:1402.7205), compute in the polytopal algebra `k[P]`. Here `P` is a lattice polytope that
holds every generator's support. The degree-`d` Macaulay matrix has `HP_P(d)` columns, the Ehrhart
polynomial of `P`, rather than the `C(n + d, n)` of total degree. For a regular sequence of `n`
generators of sparse degrees `d_j`, the witness degree is at most
`reg(k[P]) + 1 + Σ(d_j − 1)`, where `reg(k[P]) = n + 1 − ℓ` and `ℓ` is the smallest dilation of
`P` with an interior lattice point (their Lemma 5). For overdetermined systems, the paper
conjectures semi-regularity in `k[P]` (Conj. 1), and the witness degree is the first non-positive
coefficient of `HS_P(t)·(1 − t)^m`.

What a sparse computation returns, and what it costs to turn that into Zeebra's contract (the
reduced Gröbner basis of the original ideal, in the requested order):

| contract point | sparse method | here |
|---|---|---|
| output | a sparse GB of the ideal in `k[P]`, not an ordinary GB | needs conversion |
| conversion | sparse-FGLM, `O(r·δ³)` for a simplicial, Cohen–Macaulay semigroup with `r` generators, quotient dimension `δ` | `δ` = 5–15 on every eligible public problem, so this is negligible against either matrix |
| solutions with a zero coordinate | lost in general: `k[P]`'s chart is the torus | not lost on a product of scaled simplices. Its semigroup is all of `ℕⁿ`, so the chart is affine space. Every polytope below is such a product |
| complexity statements | need regularity (square) or Conj. 1 (overdetermined), and a normal semigroup | Table 3 (fewnomials, not normal) is excluded, as the paper excludes it from its analysis |

So for every comparison below, conversion and coordinate-zero handling add nothing that changes a
ratio. The decision rests on the matrix sizes alone.

## 2. Instruments

- [`research/1035-sparse-toric/counts.py`](../../research/1035-sparse-toric/counts.py) counts the
  sparse side. It takes `HP_P` for a product of scaled simplices, `∏ C(n_j + d·b_j, n_j)`, then the
  witness degree. The rows are the **rank** at that degree, which is what an F5-pruned matrix
  holds. That is the smallest sparse matrix the theory allows, so every ratio below is the most
  favourable one to the sparse method. The full Macaulay row count is in the data beside it.
- [`examples/sparse_toric_counts.rs`](../../examples/sparse_toric_counts.rs) generates the paper's
  shapes: `m` generators on the full support of `dx·Δ_{nx} × Δ_{ny}`, with a planted solution at
  GF(65521). It runs conventional F4 (grevlex, shipping options) and reports
  `max_matrix_rows × max_matrix_columns`, F4's largest matrix. `--perturb k` adds `k` products
  `y_a·y_b` per generator, which takes the support out of `P`: these are the controls.
- `examples/sig_f4_study.rs --catalog` runs the same F4 on the #1006 panel records. This PR adds its
  instantiations at 16, 18, 21, 22 and 24 variables.

**Size** is rows × columns throughout. **Advantage** is F4's largest ÷ the sparse matrix: above 1,
the sparse matrix is the smaller one.

## 3. Reproduction on the paper's shapes (development)

The rows of Tables 1–2, plus the smaller rows commented out of the paper's source, at seeds 1–2.
There are 41 shapes. Every shape whose variable count the example instantiates was run: 33 shapes,
132 solves. `tables.md` has every row. In summary:

- **Advantage on the 27 completed shapes: median 1.53, range [0.38, 8.12].** None reaches 10×, and
  7 are below 1×, where F4's largest matrix is already the smaller one. These are mostly the
  smallest bidegree-(2,1) shapes, with `n_y ≤ 9`.
- **The advantage grows with `n_y`** on the families the paper wins most on: bidegree (2,1) with
  `n_x = 2` goes 1.73 → 6.72 → 8.12 for `n_y` = 15, 17, 19; bilinear `(2, 29, 40)` is 7.72. The
  larger rows of Table 1 (`n_y` = 39–59) were not run. The example has no instantiation for 41 or
  more variables. They may cross 10×. That is the regime the paper reports its largest gains in.
- **F4 refuses six shapes** (`TooManyNonzeros`, the 32 M shipping budget), all with `n_x ≥ 10`.
  The sparse matrix there has 14,280–448,448 columns at full rank.
- **The paper's speedups are times against FGb-F5, not matrix sizes against F4.** The 22–19,584×
  of Tables 1–2 do not translate into matrix ratios at this scale.

**Controls.** One added `y_a·y_b` per generator moves the support into `dx·Δ_{nx} × 2·Δ_{ny}`. The
sparse witness matrix then grows to 5,880 – 1.9·10²⁸ columns. Where both F4 runs of a seed complete,
F4's largest matrix changes by 0.70–22×, and on 18 of the 33 shapes at least one control seed is
refused. The sparse advantage is
not robust to support: a single term outside `P` removes it. An eligibility check would have to be
exact, as #1034's `planning::multigrading` verifier is for bidegrees.

## 4. The public panel (the deciding comparison)

**Survey.** Every base problem of the #1006 panel (62 at `p31`) was screened. For each one,
`counts.py survey` searches the 2-block splits for the product `a_X·Δ × a_Y·Δ` holding all
generators (`a_B` = the largest block degree of any term). It then compares `HP_P(3)` with
`C(n + 3D, n)`, where `D` is the largest generator degree. The search is exhaustive for `n ≤ 20` and
a local search above. **7 of the 62 are eligible** (ratio ≤ 0.1): six phosphorylation records and
`sd-ellipsoid-4`. All are development records. The next best, `gen-phosphorylation-4` at 0.103 and
`sd-hairer-2` at 0.116, miss the threshold.

| problem | P | normalized volume | affine solutions | sparse d_wit | sparse rank × columns | F4 largest | advantage |
|---|---|---:|---:|---:|---|---|---:|
| `gen-phosphorylation-5` | `Δ₁₆ × Δ₂` | 153 | 11 | 3 | 9,537 × 9,690 | 466 × 582 | 0.0029 |
| `gen-phosphorylation-6` | `Δ₂ × Δ₁₉` | 210 | 13 | 3 | 15,190 × 15,400 | 737 × 944 | 0.003 |
| `gen-phosphorylation-7` | `Δ₂ × Δ₂₂` | 276 | 15 | 3 | 22,724 × 23,000 | 1,095 × 1,432 | 0.003 |
| `gen-phosphorylation-2-nonzero` | `5Δ₅ × Δ₅` | 7.9·10⁵ | 5 | 6 | 1.5·10⁸ × 1.5·10⁸ | 55 × 62 | 1.5·10⁻¹³ |
| `gen-phosphorylation-4-nonzero` | `7Δ₇ × Δ₉` | 9.4·10⁹ | 9 | 8 | 1.3·10¹³ × 1.3·10¹³ | 270 × 327 | 4.9·10⁻²² |
| `gen-phosphorylation-6-nonzero` | `9Δ₉ × Δ₁₃` | 1.9·10¹⁴ | 13 | 10 | 2.0·10¹⁸ × 2.0·10¹⁸ | 1,019 × 1,032 | 2.7·10⁻³¹ |
| `sd-ellipsoid-4` | `Δ₄ × 12Δ₆` | — | — | — | not counted: 4 generators in 10 variables, so not zero-dimensional | — | — |

**The sparse matrix is 300× or more larger on every eligible problem.** That is the predeclared
"disproved" outcome: the advantage is under 3× on every eligible public problem.

**This does not rest on the regularity assumption.** The phosphorylation systems are far from
generic in `P`: 11–15 affine solutions against a normalized volume of 153–276. So they need not be
regular in `k[P]`, and Lemma 5's degree need not be their witness degree. But no degree rescues
the comparison. At sparse degree 2, `P`'s columns already number 918, 1,260 and 1,656, more than
F4's largest matrix has (582, 944, 1,432). Degree 1 is the generators themselves. F4 finishes every
one of these in under 7 ms at one worker. The `-nonzero` variants add one high-degree generator,
and with it one block's scale. That puts `P` out of reach.

## 5. Decision

**Disproved** for Zeebra's public inputs, under the rule posted before any count was read. No
prototype issue is filed.

What the evidence does and does not say:

- **On public inputs, eligibility is rare and does not pay.** Unmixed products of simplices fit 7 of
  62 panel problems under a generous screen. On every one, the total-degree F4 Zeebra ships already
  builds matrices hundreds of times smaller than the sparse theory's witness matrix.
- **On the paper's own random families, the matrix advantage is real but small at this scale:**
  ≤ 8.1×, rising with the unbalanced block's size. The largest Table 1 rows (≥ 41 variables), where
  the trend points past 10×, are not run here. A future proposal would have to start from a public
  application family of that shape, and none is in the panel.
- **The advantage is fragile to support.** One extra term per generator destroys it, so any use
  would need an exact eligibility check and a tested fallback.

## 6. What this does not change

- No library code changes. The example and the `sig_f4_study` instantiations are research
  instruments.
- #1034's bilinear census is a different construction: it regroups F4's own matrices by bidegree.
  It is untouched, and its open arms are still open.
