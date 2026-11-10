# Controlled cryptanalytic experiments: dimension, variable order, affine elimination

Reference for M22-E (#74, #79, #81). Every figure comes from the `cryptanalysis_ladder` example
(moved out in #668), run under `F4Options::recommended()` with `profile_degrees`, `max_matrix_columns = 60_000`,
`max_live_bytes = 400 MB` (slack: the effective live cap is the `min` of the two budgets, so `max_live_nonzeros` bound first at 20 000 000 entries — **320 MB** over these fields' 16-byte entry; #322, #469), grevlex throughout. Solving uses `SolvePolicy::AutoWithFallback`, which
is what M21-D's measurements selected — a bare `SolveOptions::default()` is `DirectLexF4`, and that
route crosses both the row and the column budget on every Poseidon system here.

**No full-round claim is made anywhere.** The 2026 initiative's CICO instance is
`t = 16, R_F = 6, R_P = 8` — 104 S-box variables plus fourteen free inputs — and the largest row
below has nine variables.

Every recovered Poseidon witness is verified by **running the permutation**, not by evaluating the
polynomial system, so no bug in the generator or in any transformation here can make a verification
pass. Every recovered Fukuoka witness is evaluated against the published coefficient vectors.

## 1. The ladder: `N − E = t − 2k`

*§1 (the planted Poseidon CICO ladder and its dimension confound) was moved out with the cryptanalysis research in #668; it is preserved at commit 9532a9a2.*

## 2. Variable order

Three layouts of the same system, as verified bijective permutations. The constructor rejects
anything that is not a bijection of `0..N`; every witness is mapped back with the inverse and
re-verified through the permutation. A relabelling is a ring isomorphism, so the quotient dimension
cannot move — the basis, the matrices and the cost can.

| instance | layout | cols | peak MB | ms | basis |
|---|---|---:|---:|---:|---:|
| `t=2 R_F=2 R_P=2` | generated | 925 | 1.7 | 130.7 | 70 |
| | **last-round-first** | **897** | **0.8** | **78.1** | 56 |
| | free-inputs-last | 1 079 | 1.5 | 101.8 | 57 |
| `t=2 R_F=4 R_P=0` | generated | **1 341** | 3.8 | 351.9 | 102 |
| | **last-round-first** | 1 554 | **2.9** | **218.7** | 85 |
| | free-inputs-last | 1 430 | 4.3 | 366.2 | 90 |

**`last-round-first` is 1.67x and 1.61x faster, with 2.1x and 1.3x less peak memory.** It is the
only layout that wins on both instances, and it wins on peak memory even where it loses on columns —
`t=2 R_F=4` goes from 1 341 to 1 554 columns while peak live bytes fall from 3.8 to 2.9 MB, so the
matrices are wider and sparser.

The construction is one sentence: keep the free inputs first, then take the round blocks in reverse
order with each block's internal order unchanged. Under grevlex the later variables are the ones
eliminated first, so reversing the rounds puts the S-box variables the output constraint touches
*directly* at the front and the first round's at the back — the computation works inwards from the
constrained end rather than forwards from the free one.

It is also the layout with the **smallest intermediate basis** on both instances (56 against 70, 85
against 102, before interreduction), which is the mechanism: fewer appended elements means fewer
critical pairs.

Two instances at one state width is not a curve. What the experiment establishes is that variable
order is worth **a factor comparable to the largest single-strategy effect M16 measured** — the
dense accumulator's 1.9x on elimination — and notably more than *critical-pair* order, which M22-A
measured at no runtime effect at all. The two are not competing for the same resource: pair order
decides which rows share a matrix, variable order decides what the monomial order is.

## 3. Affine elimination

A CICO instance's `k` output constraints are affine and nothing else in the system is — the S-box
equations are `v − s^alpha`. So `k` variables are determined, and `t=2 R_F=4` has nine variables
where eight would do.

| system | vars | eqs | cols | peak MB | ms | dimension |
|---|---:|---:|---:|---:|---:|---|
| as generated | 9 | 9 | 1 341 | 3.8 | 355 | zero |
| substituted only | 9 | 8 | **870** | **2.9** | 265 | **positive** |
| projected to 8 variables | **8** | 8 | 870 | 2.9 | 258 | zero |

**The matrix shrinks from the substitution and not from the projection** — 1 341 columns to 870, and
3.8 MB to 2.9 MB, with the projected row identical to the substituted one. That is as it must be: a
column is a monomial that *appears*, and after substitution the eliminated variable appears in no
generator, so it has no column either way.

What the projection changes is the **dimension**. After substitution the eliminated variable appears
in no generator, so it is unconstrained and the ideal is positive-dimensional — F4 completes and the
zero-dimensional solvers then correctly refuse the result. That is the same trap
`Specialization::apply` documents, and it is why `AffineElimination::project` exists and why its
target dimension is checked to be exactly the number of survivors rather than merely large enough.

So the honest summary is: **substitution is worth about 1.34x on this instance, and projection is
what makes the result solvable.** The two are not alternatives.

The sweep is deliberately bounded — Gaussian elimination on the affine part of a generating set, not
a general preprocessor and not nonlinear elimination. An affine relation appearing only after some
nonlinear cancellation is not found and nothing looks for one. A generator substituting to a nonzero
constant is kept, so an inconsistent system still reports `{1}`; that is asserted in a test, because
dropping it would turn an unsatisfiable system into a satisfiable one.

## 4. Fukuoka MQ

*§4 (the Fukuoka MQ challenge instances) was moved out with the cryptanalysis research in #668; it is preserved at commit 9532a9a2.*

## 5. What this decided

*§5 (the M22-E decision table, which answers §1's and §4's challenge questions) was moved out with the cryptanalysis research in #668; it is preserved at commit 9532a9a2.*

## 6. Reproducing

```sh
cargo test --lib grobner::transform::reorder
cargo test --lib grobner::transform::affine
```

The `cryptanalysis_ladder` example that produced the tables was moved out in #668.

The tests assert what the tables assume: only a bijection is accepted as a variable order; `forward`
and `recover` are mutually inverse; a relabelled planted system's solution maps back to the original
plant; relabelling changes the basis but not the quotient dimension; an affine elimination preserves
the ideal (checked by adding the recorded relations back and comparing reduced bases); every recorded
expression mentions surviving variables only; an inconsistent system stays inconsistent; and a
projected planted system lifts back to exactly the plant.
