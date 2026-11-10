# The semiregular Hilbert model against the measurement

Reference for M22-B (#74, #81). Every figure comes from

```sh
cargo run --release --example hilbert_study
```

under `F4Options::recommended()` with `profile_degrees`, grevlex throughout, degrees compared over
`0..=12`. The Fukuoka rows also needed `tools/fetch-mq-challenge.sh`, which was moved out in #668.

**M22-B is diagnostic.** Nothing in this workstream discards work, and nothing correctness-critical
consults a prediction. The question is whether the prediction is accurate enough, and early enough,
to be worth acting on — and the answer decides whether M22-C is built.

## 1. Three quantities, kept apart

| | what it is | status |
|---|---|---|
| **`H obs`** | the exact Hilbert function of the leading-term ideal of a *computed* Gröbner basis | exact; for a homogeneous ideal it is the graded dimension of `R/I` |
| **`H pred`** | the positive truncation of `Π(1 − z^{d_i}) / (1 − z)^n` | a theorem for a regular sequence, a conjecture for a generic overdetermined one, **nothing** for a structured one |
| **`gens`, `F4 new`** | minimal generators of the leading-term ideal at degree `d`; new basis elements F4 extracted at selection degree `d` | the first is a property of the ideal, the second of a run |

`gens` and `F4 new` are deliberately not the same column. A batch at degree `d` can produce a
relation of degree below `d` — M22-0 measured a third to a half of all new elements arriving that
way — so the gap between them is not prediction error.

The exact side is computed in closed form rather than by enumeration. Counting the degree-8
monomials outside a leading-term ideal in twenty variables is 2.7 million divisibility sweeps and
the same count at degree 12 is 141 million; the recursion on
`0 → R/(L:p) → R/L → R/(L+<p>) → 0` is a few thousand nodes on every instance here.

**Two separate budgets bound it**, because there are two resources and neither is small by
construction:

- `DEFAULT_NODE_BUDGET` bounds the recursion's breadth. The recursion is exponential in the worst
  case.
- `DEFAULT_COEFFICIENT_BUDGET` bounds any single series' length. A numerator is one plus the summed
  degrees of the generators, and a monomial's exponents are `u32` — so `<x^100000000>` is
  representable and its honest numerator is 1.6 GB of `i128`. Nothing in F4's matrix budgets covers
  this preprocessing, and in a Hilbert-driven run it happens *before* the first matrix is built.

A crossing of either is an error, not a termination: in `HilbertSelection` it makes the prediction
unavailable, which is counted in `predictions_unavailable` and leaves the computation ordinary. The
widest numerator in this corpus is a few hundred coefficients, which is asserted — a limit that
refuses the pathological case but not the real ones is only half a guard.

## 2. Where the model is exact

| system | homogeneous | `d_reg` | F4's top selection degree | agreement |
|---|---|---:|---:|---:|
| 10 random quadratics in 5 variables | yes | 3 | 4 | **100%** |
| 12 random quadratics in 6 variables | yes | 3 | 4 | **100%** |
| 14 random quadratics in 7 variables | yes | 3 | 4 | **100%** |
| 6 random quadratics in 6 variables (square) | yes | 7 | 8 | **100%** |
| three squares in three variables | yes | 4 | — (nothing to do) | **100%** |
| Fukuoka III `n=10` seed 0, top forms | yes | 4 | 5 | **100%** |
| Fukuoka III `n=15` seed 0, top forms | yes | 4 | 5 | **100%** |
| katsura-5 | **no** | 5 | 6 | **100%** |

Zero error at every degree compared, on every one. That includes the two genuine Fukuoka challenge
instances' top forms and — unexpectedly — katsura-5, which is inhomogeneous and has a linear
generator: with degrees `(1, 2, 2, 2, 2)` the model is `(1 + z)^4 = 1, 4, 6, 4, 1`, and the measured
leading-term ideal gives exactly that.

So on random and genuine overdetermined MQ systems the semiregularity assumption **holds**, which is
the regime #74 cites it for. That is a real positive result, and it is worth noting that it was not
a foregone conclusion at these sizes: `n = 5` over a field is not asymptotic.

### The pattern in the last two columns

On every exact row, **F4's highest selection degree is exactly `d_reg + 1`**. The degree-`d_reg`
rows have `H = 0`, so no residue class is left and no new basis element can arise — and F4 goes one
further still. What it does there is not nothing:

| system | work at `d_reg + 1` | new elements there |
|---|---:|---:|
| 10 random quadratics in 5 variables | 14 rank | 0 |
| 12 random quadratics in 6 variables | 43 rank | 0 |
| 14 random quadratics in 7 variables | 82 rank | 0 |
| Fukuoka III `n=10`, top forms | 107 rank | 0 |
| Fukuoka III `n=15`, top forms | **2 807 rank** | 0 |

**That is the HDF4 opportunity, measured exactly.** On the `n=15` top-form system the final pass
performs 2 807 rows' worth of independent elimination and yields not one basis element, and the
model says so in advance.

## 3. Where the model fails, and in which direction

| system | agreement | first disagreement | error sign |
|---|---:|---|---|
| `x^2, x*y, x*z` — a common factor | 23% | degree 3: predicted 1, observed 4 | **negative** |
| four squares spanning two variables | 23% | degree 2: predicted 6, observed 7 | negative |
| a quadratic repeated up to scalars | 23% | degree 2: predicted 6, observed 7 | negative |
| Poseidon `t=2 R_F=2 R_P=0`, top forms | 23% | degree 3: predicted 16, observed 17 | negative |
| Poseidon `t=2 R_F=2 R_P=2`, top forms | 23% | degree 3: predicted 50, observed 51 | negative |
| Fukuoka III `n=10`, **inhomogeneous** | 77% | degree 1: predicted 10, observed 0 | **positive** |
| Poseidon `t=2 R_F=4`, **inhomogeneous** | 15% | degree 2: predicted 36, observed 31 | **positive** |

The sign is what decides whether a wrong prediction is merely wasteful or unsound.

**Negative error** — predicted `H` below observed — means the model thinks *fewer* residue classes
remain than do, hence that the ideal contains *more* than it does, hence `dim I pred > dim I obs`. A
selection cap of `N_d + slack` built on it is **too large**: more pairs are selected than needed.
Wasteful, never incomplete. Every structured *homogeneous* counterexample fails this way, including
both Poseidon top-form systems.

**Positive error** — predicted `H` above observed — is the dangerous direction: the model
underestimates the ideal, so the cap is **too small** and pairs that were needed are skipped. And
this is the direction the *inhomogeneous* systems fail in — which is to say, the systems the
challenge and the bounty actually pose.

### The sharpest case

Fukuoka III `n=10` seed 0, as published:

| d | dim R_d | H pred | H obs | dim I pred | dim I obs | gens | F4 new |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 10 | 10 | **0** | 0 | **10** | 10 | 0 |
| 2 | 55 | 35 | 0 | 20 | 55 | 0 | 18 |
| 3 | 220 | 20 | 0 | 200 | 220 | 0 | 65 |
| 4 | 715 | 0 | 0 | 715 | 715 | 0 | 85 |

The instance has a unique solution, so `D = dim R/I = 1` and the grevlex basis is essentially
linear: the leading-term ideal is `<x_1, …, x_10>` and the ideal's own Hilbert function is
`1, 0, 0, …`. The model is a statement about the top forms and has no claim on this row at all,
which is why it is shown.

What it does get right is the **solving degree**: `d_reg = 4` for the top-form system, and F4's
highest selection degree on the published instance is 4. The classical use of the model — predict
how high the computation has to go — is correct here.

What it gets wrong is everything downstream of that. **At degree 4 — the degree the model says has
nothing left — F4 finds 85 of its 168 basis elements.** A selection rule that truncated at `d_reg`
on the strength of the prediction would return an incomplete basis on the genuine challenge
instance, and would look like a 3x speedup while doing it.

That is the correctness boundary of the plan's §2.4, in one table, on real data.

## 4. The question the plan asks

> §7.5: does the Hilbert model reliably identify degrees at which additional critical-pair
> reductions will contribute no new basis elements?

**On homogeneous overdetermined quadratic systems, yes, exactly** — `d_reg` is precisely the first
such degree and the model computes it from `n` and `m` alone, before any computation. §2's last
table measures what is spent past it.

**On the inhomogeneous systems the milestone cares about, no.** The model's `d_reg` coincides with
F4's last *useful* degree rather than its first useless one, so there is no degree to skip; and
acting on `H pred = 0` at `d_reg` would discard the degree that produces half the basis.

There is a second, narrower prediction that survives the inhomogeneous case, because it does not
rest on `H pred` being the ideal's Hilbert function. At degree `d` the number of **new** leading
monomials available is

```text
N_d = (predicted dim I_d) − dim (current leading-term ideal)_d
```

where the second term is computed **exactly** from the basis in hand, by the same recursion as
`H obs`. On Fukuoka III `n=10` top forms that gives 20, 65, 20 at degrees 2, 3, 4 — and the measured
`gens` column is 20, 65, 20. So the per-degree count of new generators *is* predictable where the
model holds, and that is the quantity Sakata–Takagi's `SelectPairLimited` caps on.

## 5. What this decided for M22-C

**Proceed, with three constraints the measurement imposes.**

1. **Cap pairs within a degree; do not truncate degrees.** `d_reg` is tight on the inhomogeneous
   instances, and §3 shows what truncating at it costs. Within-degree limiting on `N_d + slack` is
   the only form of the idea the data supports.
2. **The reference is a capped run, not the uncapped baseline.** M22-A measured a plain cap of 64
   pairs per batch at 3.6x on Fukuoka III `n=10` and 2.2x at `n=15`, with 24%–64% less peak memory,
   and with no prediction and no certification. The predicted `N_3` on that instance is **65**. A
   fixed cap of 64 is therefore within one pair of the Hilbert-derived cap at the degree that
   matters, so **the plain cap already captures most of what the prediction would buy** — and M22-C
   has to show what the prediction adds over a number picked without one.
3. **Completeness cannot rest on the prediction.** §3's positive-error rows are the systems the
   milestone is about. The design has to be complete by construction — deferred pairs promoted, not
   discarded — with certification reported as a cost rather than relied on as a safety net.

## 6. Reproducing

```sh
cargo run --release --example hilbert_study
cargo test --lib grobner::hilbert
```

The tests check the closed-form recursion against **direct enumeration** on nine small monomial
ideals over all degrees up to eight, reproduce the regular-sequence formula exactly, and check the
summed Hilbert function against the standard monomials `QuotientBasis` enumerates independently —
two computations of `dim_F R/I` that were not written with each other in mind.
