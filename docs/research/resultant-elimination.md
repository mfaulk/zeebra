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
  asymptotically better; §5 of the module docs records why the spike did not use one — the
  specialization trap it would have to handle is exactly what the determinant construction avoids.

## 4. The four-round row, attempted

`--all` attempts what the guard declines. On `t16 R_F=2 R_P=2` — four rounds, so degree 81 — the
symbolic evaluation takes **431 ms** and produces two polynomials of 3 403 terms each, exactly the
straight-line degree. The resultant then needs 13 123 samples of an order-162 Sylvester determinant,
and **it had not finished after 90 minutes** when this was written.

That is the measurement, and it is the one the default guard is set by: the row is reachable in
principle — nothing about it is impossible, the polynomials exist and are small — and it is not
reachable with a Sylvester determinant per interpolation point taken through a generic dense
`Matrix`. The two constants in §3 are where the hour goes:

- 13 123 samples where 6 562 would do, because the degree bound is `2d²` and the degree is `d²`.
- An order-162 dense determinant per sample, where the Sylvester structure is not used at all.

Each sample costs about `162³/3` multiplications plus 162 modular inversions, so 13 123 of them is
roughly `3 × 10^10` field multiplications through a generic `Matrix` — which is where the ninety
minutes go, and it is arithmetic rather than a surprise.

Together those are a factor of several before any algorithmic change, which is why the conclusion is
"scope an implementation" rather than "the resultant route stops at two rounds". What can be said
without an implementation milestone is: **two rounds in 52 ms, four rounds not in ninety minutes,
and six rounds never** — `3.3 × 10¹⁵` field operations for the resultant alone, before cubing a polynomial
with 265 720 terms.

## 5. What this decided

| question | answer |
|---|---|
| Does structure-aware elimination beat general F4 here? | **Yes, by 578x** on the one row both can do, and it returns every witness rather than the first. |
| Is the univariate polynomial manageable? | Yes at two rounds — degree 81, 17 ms to find its roots over KoalaBear. |
| Does Poseidon's structure reduce the degree below Bézout? | **No.** The bivariate degree is exactly `3^rounds` and the resultant's is exactly `d²`. |
| Does it scale? | No. The cost is `16 · 3^{5·rounds}`: two rounds in 52 ms, four rounds not in ninety minutes with this implementation, six rounds `3.3 × 10^15` operations. |
| Did it extend the frontier? | **No** — both routes reach two rounds. What it changed is the cost there, by 578x. |
| Should a resultant implementation be scoped? | Yes, and narrowly: early-terminating interpolation plus a structured determinant, aimed at the slice shape, not at a general solver. |

The deeper consequence is about the **formulation**, not the algorithm. Three orders of magnitude
separate two ways of writing the same CICO slice, and the expensive one is the one the whole
cryptanalysis literature uses by default because it bounds the degree. When the free-variable count
is small, bounding the degree is the wrong trade — and the scoreboard is what made that visible,
because both routes are measured against the same registered problem.
