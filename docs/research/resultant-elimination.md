# Elimination that is not a Gröbner basis: a resultant on the registered CICO slices

Reference for M23-E (#141), which consumes #82 and #85.

```sh
cargo run --release --example resultant_cico
cargo test --lib grobner::research::resultant
```

The spike the plan asks for, on the instances that make the comparison mean something: these are the
**registered** `t = 16` reductions M23-B measured, sliced at the same precommitted seed, so the
resultant's cost sits beside an F4 figure for exactly the same problem.

## 1. The structure, and why F4 is not told about it

Fix twelve of the fourteen free inputs and two unknowns remain. Every S-box output is then a
*polynomial in those two*: the permutation is a straight-line program, so there is nothing to solve
for, only to evaluate. The whole 46-equation system collapses to **two polynomials in two
variables**, and the CICO condition is their common root.

The S-box-per-variable formulation exists to stop the degree compounding — `y − L^3 = 0` is degree 3
whatever the round count — and pays 32 extra variables for it. At `t = 16` those variables are what
make the matrices unaffordable: M23-B measured fourteen of eighteen rows dying on live entries at
degree 4–5. Evaluating them away trades the variables back for degree `3^rounds`, and the question
is where that trade stops paying.

## 2. Measured

One resultant eliminates the second unknown; its roots are candidates for the first; each candidate
is extended and then checked **by running the permutation**. Nothing here decides that a candidate
is a solution — a resultant root is a necessary condition, not a sufficient one.

| row | rounds | bivariate degree | terms | build | resultant degree | Bézout | eliminate | roots | verify | **total** | F4 on the same slice |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `t16 R_F=2 R_P=0` | 2 | 9 | 55 | 2.8 ms | **81** | 81 | 30.8 ms | 18.1 ms | 0.5 ms | **52.2 ms** | **30 142 ms** |
| `t16 R_F=2 R_P=2` | 4 | 81 | 3 403 | 431 ms | — | 6 561 | see §4 | — | — | — | stopped at the entry cap |

**578x on the row both routes can do**, and the resultant returns *all three* base-field witnesses
where F4's search returns the first one it finds. Both were checked through the permutation.

The bivariate degree is exactly `3^rounds` on every row — the straight-line bound, with no
cancellation — and the resultant's degree on the 2-round row is exactly the Bézout bound `9 × 9`.
So nothing about Poseidon's structure reduces the degree here; what the resultant exploits is the
*variable count*, not a degree collapse. That is worth stating plainly because the plan asked
whether a structural degree reduction appears, and the answer is **no**.

## 3. Why this is not a general answer

The resultant route costs about `16 · 3^{5·rounds}` field operations before any polynomial
arithmetic: `2d²` interpolation samples of an order-`2d` Sylvester determinant, with `d = 3^rounds`.
That is 1.0 × 10⁶ at two rounds, 2.3 × 10⁸ at three, 5.6 × 10¹⁰ at four, and 10¹⁸ at six — and the
*evaluation* itself has to cube a polynomial with `d²/2` terms, which is 266 000 terms at six
rounds.

So the reach of **this implementation** is two rounds, and §4 is the four-round attempt. The example
predicts rather than attempts anything past `10^10` predicted operations, printing the arithmetic
that rules each row out. F4's reach on the same slices was also two rounds — so what the spike
establishes is not a frontier extension but a **cost difference of 578x at the frontier both
routes share**, plus an arithmetic ceiling for the alternative that F4 does not have in writing.

Two constants are visibly loose and would be the first things to fix in an implementation
milestone, not in a spike:

- **The sample count.** The degree bound `n·deg_x(f) + m·deg_x(g)` is `2d²`, and the observed degree
  is `d²` — exactly 2x loose on the row that finished. An early-terminating interpolation would
  halve the work and need no bound at all.
- **The determinant.** This takes an order-`2d` determinant per sample through the generic dense
  path. A Sylvester matrix is structured, and a subresultant or Euclidean algorithm is
  asymptotically better; the module docs record why the spike did not use one — the specialization
  trap it would have to handle is exactly what the determinant construction avoids.
- **The interpolation**, which §4.1 measures at `O(n³)` and which turns out to dominate both of the
  above. Ranked there rather than here, because it took attempting a row that does not finish to
  see it.

## 4. The four-round row, attempted

`--all` attempts what the guard declines. On `t16 R_F=2 R_P=2` — four rounds, so degree 81 — the
symbolic evaluation takes **431 ms** and produces two polynomials of 3 403 terms each, exactly the
straight-line degree. The resultant then needs 13 123 samples of an order-162 Sylvester determinant,
and **it had not finished after two hours** when this was written. §4.1 is why.

### 4.1 Where the time actually goes, measured

The first draft of this section blamed the determinants. That was wrong, and the measurement is
easy: `lagrange_interpolate` is **cubic** in the number of points.

| points | time | factor for 2x the points |
|---:|---:|---:|
| 250 | 28.6 ms | — |
| 500 | 219.4 ms | 7.7x |
| 1 000 | 1 632 ms | 7.4x |
| 2 000 | 12 880 ms | 7.9x |

`7.4x`–`7.9x` per doubling is `2³`: the implementation builds each of the `n` Lagrange basis
polynomials by multiplying `n − 1` linear factors into a growing polynomial and then dividing, which
is `O(n²)` apiece and `O(n³)` in total. Extrapolating 12.9 s at 2 000 points to the 13 123 the
four-round row needs gives **about an hour for the interpolation alone** — against roughly
`3 × 10^10` field multiplications, or a few minutes, for all 13 123 determinants together.

So the ranked list of what to fix is not what §3 guessed:

1. **The interpolation.** `O(n³)` where Newton's divided differences are `O(n²)` and a product-tree
   or NTT evaluation is `O(n log² n)`. KoalaBear has the two-adic roots of unity for the NTT route —
   #147 landed them — and 13 123 points pad to 16 384.
   **Fixed, in part: #162 stage 1 made `lagrange_interpolate` `O(n²)`, and the 13 123-point
   interpolation above now takes 1.37 s measured rather than the extrapolated hour. The table in
   this section is the pre-#162 measurement and is kept as such; see
   [`fast-univariate.md`](fast-univariate.md) §4.3.2 for the same point counts after.**
2. **The sample count**, 2x loose: the degree bound is `2d²` and the observed degree is `d²`.
3. **The determinant**, which is a few minutes of the hour and therefore last.

That reordering is the useful output of attempting a row that does not finish. `bivariate_resultant`
is a reference implementation and the module says so; what the spike establishes is which of its
three costs is worth an implementation milestone, and it is not the one that looked obvious.

Together those are a factor of several before any algorithmic change, which is why the conclusion is
"scope an implementation" rather than "the resultant route stops at two rounds". What can be said
without an implementation milestone is: **two rounds in 52 ms, four rounds not in two hours, and
six rounds never** — `3.3 × 10¹⁵` field operations for the resultant alone, before cubing a polynomial
with 265 720 terms.

## 5. What this decided

| question | answer |
|---|---|
| Does structure-aware elimination beat general F4 here? | **Yes, by 578x** on the one row both can do, and it returns every witness rather than the first. |
| Is the univariate polynomial manageable? | Yes at two rounds — degree 81, 17 ms to find its roots over KoalaBear. |
| Does Poseidon's structure reduce the degree below Bézout? | **No.** The bivariate degree is exactly `3^rounds` and the resultant's is exactly `d²`. |
| Does it scale? | No. The cost is `16 · 3^{5·rounds}`: two rounds in 52 ms, four rounds not in two hours with this implementation, six rounds `3.3 × 10^15` operations. |
| Which cost should an implementation attack first? | **The interpolation**, measured at `O(n³)` — not the determinant, which is a few minutes of the hour. §4.1. |
| Did it extend the frontier? | **No** — both routes reach two rounds. What it changed is the cost there, by 578x. |
| Should a resultant implementation be scoped? | Yes, and narrowly: early-terminating interpolation plus a structured determinant, aimed at the slice shape, not at a general solver. |

The deeper consequence is about the **formulation**, not the algorithm. Three orders of magnitude
separate two ways of writing the same CICO slice, and the expensive one is the one the whole
cryptanalysis literature uses by default because it bounds the degree. When the free-variable count
is small, bounding the degree is the wrong trade — and the scoreboard is what made that visible,
because both routes are measured against the same registered problem.
