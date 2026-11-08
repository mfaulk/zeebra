# Controlled cryptanalytic experiments: dimension, variable order, affine elimination

Reference for M22-E (#74, #79, #81). Every figure comes from

```sh
tools/fetch-mq-challenge.sh
cargo run --release --example cryptanalysis_ladder
```

under `F4Options::recommended()` with `profile_degrees`, `max_matrix_columns = 60_000`,
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

| instance | vars | eqs | planted | deg | cols | MB | ms | dimension |
|---|---:|---:|---|---:|---:|---:|---:|---|
| `t=2 R_F=2 R_P=0` | 5 | 5 | yes | 4 | 71 | 0.0 | 0.6 | zero |
| `t=2 R_F=2 R_P=2` | 7 | 7 | yes | 6 | 925 | 1.7 | 143 | zero |
| `t=2 R_F=4 R_P=0` | 9 | 9 | yes | 5 | 1 341 | 3.8 | 356 | zero |
| `t=3 R_F=2 R_P=1`, as generated | 9 | **8** | yes | **11** | **42 229** | **155.3** | 18 167 | column budget crossed |
| `t=3 R_F=2 R_P=1`, input 0 pinned at the plant | 9 | 9 | yes | 5 | 393 | 0.2 | **13.5** | zero |
| `t=3 R_F=2 R_P=1`, input 0 pinned off-plant | 9 | 9 | no | 5 | 393 | 0.2 | 14.0 | zero |

At `k = 1` the `t = 2` rows are square and the `t = 3` row has one variable more than equation, so
**the two nine-variable instances M21 compared are not the same kind of system** and that comparison
is confounded. The fifth row removes the confound: it is the same `t = 3` system with one free input
pinned, which matches the equation count without touching the round structure.

Pinned, it is **the easiest of the three nine-variable systems** — 13.5 ms at degree 5 and 0.2 MB,
against the square `t = 2` instance's 356 ms and 3.8 MB — where unpinned it crossed the column
budget at degree 11 and 155 MB. So M21's nine-variable frontier is a fact about the
**underdetermined direction**, not about state width: one free coordinate takes the computation from
degree 5 to degree 11 and from 0.2 MB to 155 MB.

Three cautions, each of which the program enforces rather than merely states:

- The dimension is read from `classify_ideal` of the **computed basis**, not inferred from the
  variable and equation counts. Fixing one variable does not by itself prove zero-dimensionality.
- The fifth row is pinned to a *planted* value, so a solution is known to exist on that slice. The
  sixth is the same transformation at a different value and is a genuine search. A dead slice there
  would be a correct fact about the slice and would say nothing about the instance.
- Both are planted instances. **Comparing either against an arbitrary-target CICO challenge would be
  comparing different distributions** — M21 already measured that an arbitrary target at
  `t=2, R_F=2` has no base-field solution at all.

The last two rows have identical matrix shapes (393 columns, 0.2 MB, a 46-element basis), so the
Gröbner structure of the slice does not depend on the value pinned. That is what makes the planted
and off-plant rows comparable as *computations* even though they answer different questions.

Both were solved and both witnesses verified through the permutation. The off-plant slice returned
**a different preimage** — not the plant, since the plant is not on that slice — which is the
outcome that distinguishes a live search from a lucky one: the slice at an arbitrary value still had
a solution, and it was found and checked without the answer being known in advance.

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

| instance | vars | eqs | deg | cols | MB | ms | dimension |
|---|---:|---:|---:|---:|---:|---:|---|
| type III `n=10` seed 0 | 10 | 20 | 4 | 859 | 2.7 | 113 | zero |
| type VI `n=10` seed 0, as published | 10 | **7** | 9 | **38 456** | **84.7** | 2 705 | column budget crossed |
| type VI `n=10`, 3 variables fixed at the published answer | 10 | 10 | 9 | 4 315 | 4.0 | 461 | zero |
| type VI `n=10`, 3 variables fixed at seed 1 | 10 | 10 | 9 | 4 319 | 4.0 | 463 | zero |

Type III `n=10` recovered **the published answer** — the solver was not told it — and both type VI
slices produced witnesses that satisfy the *original* published coefficient vectors, so the
specialization is inverted rather than assumed. The seeded slice being alive is a fact about that
slice; M21 measured that others are dead.

Type III is the overdetermined encryption family and is the main MQ target. Type VI is the signature
family — `n ≈ 1.5m`, so underdetermined and positive-dimensional as published, and it crosses the
column budget at degree 8 while still selecting pairs at degree 9.

**A specialized type VI instance is a different problem**, and the distinction matters for M22
specifically: it is not an overdetermined semiregular system, so nothing in #74's justification for
HDF4 transfers to it. The two specialized rows differ only in the values fixed, and the matrix
shapes are within 0.1% of each other — so again the Gröbner structure of a slice does not depend on
the slice, which is what makes the planted and seeded rows comparable as computations.

The specialization does **not** lower the degree here: all three type VI rows reach degree 9. What it
lowers is the width at each degree, 38 456 columns to 4 315. That is the opposite of the Poseidon
`t = 3` case in §1, where pinning took the degree from 11 to 5 — so "specialize to make it feasible"
has at least two distinct mechanisms, and which one applies is a property of the system.

## 5. What this decided

| question | answer |
|---|---|
| Is M21's nine-variable Poseidon frontier about state width? | **No.** It is about dimension; pinned, the `t = 3` system is the easiest of the three. |
| Does variable order matter? | **Yes, substantially** — 1.6x to 1.7x and up to 2.1x less peak memory from `last-round-first`, on identical mathematical systems. |
| Does affine elimination matter? | Substitution is worth ~1.34x; projection is what restores zero-dimensionality and makes the result solvable. |
| Do the Fukuoka type VI specializations behave like the Poseidon ones? | **No.** Poseidon pinning lowers the *degree*; type VI specialization lowers the *width* at a fixed degree. |
| Any full-round claim? | None. Nine variables against 118. |

For M22-I, the consequence is that **variable order has to be held fixed across the ablation**, and
at the generated layout — otherwise a 1.7x ordering effect would be attributed to whichever F4
strategy happened to be varied alongside it.

## 6. Reproducing

```sh
cargo run --release --example cryptanalysis_ladder
cargo test --lib grobner::research::reorder
cargo test --lib grobner::research::linear
```

The tests assert what the tables assume: only a bijection is accepted as a variable order; `forward`
and `recover` are mutually inverse; a relabelled planted system's solution maps back to the original
plant; relabelling changes the basis but not the quotient dimension; an affine elimination preserves
the ideal (checked by adding the recorded relations back and comparing reduced bases); every recorded
expression mentions surviving variables only; an inconsistent system stays inconsistent; and a
projected planted system lifts back to exactly the plant.
