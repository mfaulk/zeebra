# Solving polynomial systems

Zero-dimensional solving end to end: the lex route, FGLM conversion, resultants, solution
verification, and how the solver chooses a route.

`grobner::solve` finds every point of F^N at which a system of multivariate polynomials
vanishes, over a finite field F:

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::{fields::Zp13, grobner::solve, MultivariatePolynomial};

let vars = ["x", "y"];
let system = vec![
    MultivariatePolynomial::<2, Zp13>::parse("x + y", vars).unwrap(),
    MultivariatePolynomial::<2, Zp13>::parse("x*y - 1", vars).unwrap(),
];

let mut rng = StdRng::seed_from_u64(0);
for point in solve(&system, &mut rng) {
    println!("x = {}, y = {}", point[0], point[1]);
}
```

It computes a lexicographic Grobner basis, which is triangular, then assigns variables from the
last backwards. At each step the basis polynomials that have become univariate in the current
variable are solved with `roots`, so only their common roots are tried. An inconsistent system is
detected from its basis being `{1}` and yields no points. The order of the returned points is
unspecified.

A system with finitely many solutions therefore needs no enumeration, and works over fields far
too large to list — the tests cover GF(2^31 - 1) and the largest 64-bit prime.

A system that leaves a variable unconstrained is the exception. Its solution set grows with the
field, so covering a free variable means enumerating, and `solve` refuses above an order of 2^20.
That is a limit on the size of the answer rather than on the method.


## Solving zero-dimensional systems

`grobner::solve_one` finds one solution and stops; `grobner::solve_zero_dimensional` finds every
distinct one. Both refuse a system that is not zero-dimensional rather than enumerating the field,
and both report every failure as a `Result`:

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::fields::Zp2147483647;
use zeebra::grobner::{solve_one, SolveError};
use zeebra::{MultivariatePolynomial, Zero};

type F = Zp2147483647;
let mut rng = StdRng::seed_from_u64(1);

// Two equations, two unknowns, finitely many solutions.
let system: Vec<MultivariatePolynomial<2, F>> = ["x^2 - 4", "y - x"]
    .iter()
    .map(|s| MultivariatePolynomial::parse(s, ["x", "y"]).unwrap())
    .collect();
let point = solve_one(&system, &mut rng).unwrap().expect("a solution exists");
assert!(system.iter().all(|p| p.eval(&point).is_zero()));

// A curve has infinitely many solutions, so it is refused rather than enumerated.
let curve: Vec<MultivariatePolynomial<2, F>> =
    vec![MultivariatePolynomial::parse("x*y - 1", ["x", "y"]).unwrap()];
assert_eq!(solve_one(&curve, &mut rng), Err(SolveError::PositiveDimensional));
```

`Ok(None)` means the system is zero-dimensional and has **no solution over the base field** — which
is an answer, not a failure. `x^2 + 1` over GF(3) has quotient dimension two and no point in GF(3).
Only `Err` means the computation could not be completed, and `SolveOptions` bounds it: search
branches, returned solutions, and the F4 and FGLM limits underneath. An exceeded budget is an error
rather than a truncated list.

### Which answer, and what it cost

`Ok(None)` collapses two different answers: the equations may contradict each other, or they may
simply have no base-field solution while the variety is nonempty over an extension.
`solve_one_with_outcome` separates them and returns the diagnostics alongside:

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::{fields::Zp2147483647, grobner::{solve_one_with_outcome, SolveOptions, SolveOutcome},
             MultivariatePolynomial};

type F = Zp2147483647;
let parse = |s| MultivariatePolynomial::<2, F>::parse(s, ["x", "y"]).unwrap();
let options = SolveOptions::default();

// 1 is in the ideal: the equations contradict each other.
let contradiction = vec![parse("x - 1"), parse("x - 2")];
let (outcome, _) =
    solve_one_with_outcome(&contradiction, &mut StdRng::seed_from_u64(1), &options).unwrap();
assert_eq!(outcome, SolveOutcome::Inconsistent);

// 2^31 - 1 is 3 mod 4, so -1 is not a square: zero-dimensional, and no point in the field.
let no_point = vec![parse("x^2 + 1"), parse("y")];
let (outcome, statistics) =
    solve_one_with_outcome(&no_point, &mut StdRng::seed_from_u64(1), &options).unwrap();
assert_eq!(outcome, SolveOutcome::NoBaseFieldPoint);

// And what the route cost, which `solve_one` discards.
assert!(statistics.f4.is_some());
```

Every `SolveOutcome` variant is an answer; a crossed budget is still an `Err` and can never appear
as one. `SolveStatistics` carries the Gröbner stage's `F4Statistics` and, on the converting route,
the `FglmStatistics`, with `estimated_peak_bytes` the larger of the two stage estimates. That
figure is an estimate of the *representation* — on katsura-7 under lex it is 320 MB against a
measured 1,303 MB of process RSS, so use `util::peak_resident_bytes` when the question is about the
process.

### Structural analysis, which decides nothing

`grobner::analyze` reads a system's shape off its terms without computing anything:

```rust
use zeebra::{fields::Zp2147483647, grobner::analyze, MultivariatePolynomial};

type F = Zp2147483647;
let system: Vec<MultivariatePolynomial<3, F>> = ["x*y - 1", "x^2 - z"]
    .iter()
    .map(|s| MultivariatePolynomial::parse(s, ["x", "y", "z"]).unwrap())
    .collect();

let shape = analyze(&system);
assert_eq!(shape.quadratic_generators, 2);
assert_eq!(shape.occurrences, vec![2, 1, 1]);      // per variable, generators it appears in
assert!(!shape.constant_contradiction);
// Least-constrained variable first. A ranking, not a recommendation.
assert_eq!(shape.specialization_candidates(), vec![1, 2, 0]);
```

`constant_contradiction` is the only sound conclusion in `SystemShape` — a nonzero constant
generator puts 1 in the ideal by itself. **Nothing else there bounds the quotient dimension or the
solving degree.** In particular `generators == variables` proves nothing: cyclic-4 is four
equations in four variables and positive-dimensional, katsura-4 is four in four and
zero-dimensional, and the two agree on every column `analyze` reports.

### Letting the solver choose

`solve_one_planned` picks a route on stated grounds and, if permitted, tries the other one — with
a decision log beside the answer. It is opt-in: the explicit entry points above are untouched.

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::{fields::Zp2147483647, grobner::{benchmark_systems::katsura, solve_one_planned,
             PlannedSolveOptions, SolveOutcome, SolvePolicy}};

let options = PlannedSolveOptions::with_policy(SolvePolicy::AutoWithFallback);
let (outcome, plan) = solve_one_planned(
    &katsura::<7, Zp2147483647>(),
    &mut StdRng::seed_from_u64(1),
    &options,
);

assert!(matches!(outcome, Ok(SolveOutcome::Point(_))));
assert_eq!(plan.attempts.len(), 1);              // the opening route worked
println!("{}", plan);                            // every decision, with its reason and its cost
```

**The conservative opening is grevlex-then-FGLM**, which contradicts `DirectLexF4` being the
`#[default]` strategy described as "the conservative choice". The argument is not that conversion
usually wins — it loses on the whole planted family — but that **its refusals are cheap by
construction**: FGLM's binding budget is the span's `D² + D(D+1)` cells, computed from `D` and
checked before anything is allocated, while F4's is discovered during elimination and so costs the
whole elimination up to the crossing. Measured: katsura-7's direct attempt burns 28.3 s and 1.3 GB
before refusing; planted-12's conversion refuses after 36 ms. The conservative question is not
which route usually wins but **which route's failure is affordable**.

The one decision made on a measured quantity is the conversion's feasibility: after a source basis
exists, `D` is *counted* and the span requirement is a function of `D` alone, so
`SolveError::ConversionInfeasible` means the conversion was never started — distinct from
`Fglm(SpanStorageExceeded)`, which means it ran and crossed the limit.

`PlanBudget` is shared across attempts, and holds only quantities that are *spent* —
`max_elapsed` and `max_total_batches`. A peak is not consumed by an attempt, so the entry and byte
budgets stay per-attempt in `SolveOptions`. `SolvePlan` keeps the same split: `total_batches()`
sums, `peak_estimated_bytes()` maxes. `max_elapsed` is checked *between* attempts, since F4 has no
cooperative time check, so it bounds whether a second route starts rather than how long the first
runs.

An `Err` from the planner means **inconclusive**, never "no solution".
`cargo run --release --example solve_auto` compares all four policies against an offline
best-of-two the planner was not allowed to see.

### Underdetermined systems, and what a slice establishes

The zero-dimensional solvers refuse a positive-dimensional system, which is the right answer — but
many systems that arise in practice are underdetermined, so `grobner::transform` fixes some
variables and solves the slice:

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::{fields::Zp2147483647, grobner::{transform::{solve_slice, Specialization},
             PlannedSolveOptions}, FiniteField, MultivariatePolynomial};

type F = Zp2147483647;
// A curve: one equation, two unknowns, so positive-dimensional.
let curve: Vec<MultivariatePolynomial<2, F>> =
    vec![MultivariatePolynomial::parse("x*y - 6", ["x", "y"]).unwrap()];

let slice = Specialization::new(&[(0, F::new(2))]).unwrap();
let (outcome, _plan) = solve_slice(
    &curve, &slice, &PlannedSolveOptions::default(), &mut StdRng::seed_from_u64(1),
);
assert_eq!(outcome.unwrap().witness(), Some([F::new(2), F::new(3)]));
```

The slice ideal is `I + <x_i - a_i>`, **not** the substituted generators alone. Because `const N`
is not replaced, a fixed variable does not leave the ring — substitution only removes it from every
monomial, and a variable in no generator is *unconstrained*. `x*y - 6` at `x = 2` substitutes to
`2y - 6`, whose zero set in `F[x, y]` is the line `{(x, 3)}`. So `Specialization::apply` appends
the pinning equations, which generate the same ideal and make the fixed coordinates part of the
answer.

`SliceOutcome` has three variants where a solver has `Option`, and only one of them says anything
about the system you started with:

| outcome | about |
|---|---|
| `Witness(p)` | the **original** system — verified against every original generator |
| `EmptySlice` | this slice: zero-dimensional, no base-field point |
| `SliceInconsistent` | this slice: `1` is in `I_a` |

**A run of dead slices proves nothing.** A section of a nonempty variety can be empty over `F_q`,
and only exhausting all `q^|S|` slices would settle it.
`SliceOutcome::is_evidence_about_the_original_system` returns true for exactly one variant so that
a caller has to pass through it rather than reason about the variants.
`cargo run --release --example specialize_slices` runs ten slices at each of two sizes on one
system — seven witnesses at three fixed, ten dead at six fixed — which closes the argument with
evidence on both sides rather than asserting it. Each slice comes from its own seed, and
`Specialization::seeded` builds the RNG from it, so `seed()` is a promise that the slice
reconstructs; `Specialization::new` takes chosen values and records no seed.

### Transforming a system before solving it

`grobner::transform` also holds the two transformations that change a system's shape without
changing its solutions. Both carry the solution back explicitly, because a transformed answer that
is mapped back the wrong way satisfies nothing — and on a system whose answer is not known in
advance that is indistinguishable from a solver that found nothing.

#### Relabelling the variables, and getting the answer back

Which variable is `x_0` changes the Gröbner basis, the matrices and the cost, while changing nothing
about the problem — so variable order is a free parameter of any solving experiment.
`transform::VariableOrder` makes exploring it safe:

```rust
use zeebra::{fields::Zp2147483647, grobner::{benchmark_systems::planted,
             transform::{satisfies, VariableOrder}}, FiniteField};

let point = [Zp2147483647::new(7), Zp2147483647::new(11), Zp2147483647::new(13)];
let system = planted::<3, Zp2147483647>(&point);

// sources[new] = old, checked to be a bijection of 0..N.
let order = VariableOrder::<3>::new("reversed", &[2, 1, 0]).unwrap();
let relabelled = order.apply(&system);

// The plant, moved into the new coordinates, solves the relabelled system — and comes back.
let moved = order.forward(&point);
assert!(satisfies(&relabelled, &moved));
assert_eq!(order.recover(&moved), point);
```

The constructor is the only way in and it rejects anything that is not a bijection, because a
non-bijective "permutation" silently identifies two variables and changes the problem. `recover` is
the only way back, and using `forward` in its place produces a point that satisfies nothing.
`VariableOrder::prefixed` moves a chosen set of variables to the front, and `reversed` and
`identity` cover the two orders every experiment starts from.

#### Eliminating the variables an affine generator determines

Systems often carry a few affine constraints among many nonlinear ones — a linear output condition,
a fixed sum. `transform::eliminate_affine` solves each affine generator for its highest-indexed
variable and substitutes, recording an affine expression in the **surviving** variables for each
one eliminated.

**Substituting is not enough, and the reason is worth stating.** F4 already reduces by an affine
basis element; what it cannot do is make the variable stop existing, so it keeps a column in every
Macaulay matrix and a place in the monomial order. Worse, after substitution the variable appears in
no generator — so it is *unconstrained*, and the ideal becomes positive-dimensional. That is the
same trap `Specialization::apply` documents. `AffineElimination::project` removes the variables from
the ring at a smaller compile-time dimension, and `lift` puts a solution back; the dimension is
checked to be exactly the number of survivors, since a spare position is another unconstrained
variable.

The sweep is deliberately bounded: it is Gaussian elimination on the affine part of a generating
set, not a general preprocessor and not nonlinear elimination. An affine relation that appears only
after some nonlinear cancellation is not found, and nothing looks for one. A generator that
substitutes to a nonzero constant is **kept**, so an inconsistent system still reports `{1}`.

### Elimination that is not a Gröbner basis

`grobner::resultant::bivariate_resultant` computes `Res_y(f, g)` for two bivariate polynomials, as
the determinant of their Sylvester matrix recovered by interpolating scalar determinants;
`bivariate_resultant_ntt` computes the same resultant with the samples taken on a power-of-two
subgroup, so the recovery is an inverse NTT rather than a cubic solve. The
determinant construction needs no case analysis: evaluating a matrix and taking its determinant
commutes with evaluation *always*, where specializing `f` at a point that kills its leading
coefficient in `y` drops its degree, and the specialized resultant is then not the specialization of
the resultant.

```rust
use zeebra::{fields::Zp2147483647, grobner::resultant::bivariate_resultant,
             FiniteField, MultivariatePolynomial, Polynomial, Zero};

type F = Zp2147483647;
let f = MultivariatePolynomial::<2, F>::parse("y - x", ["x", "y"]).unwrap();
let g = MultivariatePolynomial::<2, F>::parse("y^2 - 4", ["x", "y"]).unwrap();

// Eliminate y (variable 1): the resultant vanishes exactly at the x of a common root, x = ±2.
let resultant = bivariate_resultant(&f, &g, 1).unwrap();
assert!(resultant.eval(&F::new(2)).is_zero());
assert!(resultant.eval(&-F::new(2)).is_zero());
assert!(!resultant.eval(&F::new(3)).is_zero());
```

A root of the resultant is a **candidate**, not a solution: `Res_y(f, g)(a) = 0` is necessary for a
common root with `x = a` and not sufficient, since the specialized pair may share a root only in an
extension, or both leading coefficients may vanish. Every candidate must be checked against the
system it came from.

**Which per-sample kernel evaluates that scalar is a choice**, `ResultantOptions::kernel`:

- `DeterminantKernel::Dense` — dense LU on the `(m + n)`-square matrix, `O(n³)`. The **default**, so
  a figure taken before the alternative existed reproduces unchanged.
- `DeterminantKernel::Euclidean` — `resultant_from_coefficients`, driving `f mod g` down the
  polynomial remainder sequence in `O(n²)`.

Both return the same scalar, including at the specialization points, where the fixed Sylvester order
and the fallen true degrees differ by a correcting power of a leading coefficient — the case analysis
the dense route avoids, closed in `O(1)` per sample by `resultant_at_formal_degrees` and asserted
against an explicitly built determinant over all 15 625 degree-drop combinations. Measured
same-binary on one pinned core, the Euclidean kernel is **137× faster at order 162 and 2 094× at
order 1 458**, with fitted exponents of **2.94** and **1.85** — the ratio grows with the order
because the kernels differ by a power of it. See `docs/research/structured-sylvester.md` §5.6.

`bivariate_resultant_ntt` moves where the samples are taken: the *same* Sylvester determinants on a
power-of-two multiplicative subgroup, recovered with one `interpolate`, with `interpolation_route`
falling back to `bivariate_resultant_reference` on a field whose two-adicity admits no domain —
Mersenne-31's is 1. **Single-threaded it is measured slower than the reference, by 1.23x–1.40x**:
the sample count goes as `2d²` and each sample is an order-`2d` determinant, so determinant work
grows as `d^5` against a quadratic interpolation's `d^4`, and padding 13 123 samples up to 16 384
costs 10.4 s of determinants to remove 1.5 s of interpolation.

**That sign flips under concurrency, and retaining both routes is why it could be seen.**
`ResultantOptions::concurrency` spreads the independent determinants over worker threads and
defaults to 1, so every figure above reproduces unchanged. The samples are written into their own
index rather than collected as they finish, so the recovered polynomial does not depend on the
worker count — asserted byte-identical at 1, 8 and 32. Measured on a 32-core pinned set under the
benchmark lock, the determinant stage of an order-162 resultant runs at **92–95% parallel
efficiency out to 32 of this box's 128 cores**. The subgroup route then *wins* by 1.7–1.8x, because
its extra determinants parallelize and the reference route's Lagrange solve does not.

`bivariate_resultant_predicted` takes a caller's **predicted** degree — structured inputs often have
a resultant far below the Bézout bound — and samples one point more than that rather than the
Bézout-sized `2d²`. A prediction is not a bound, so the route validates rather than trusts it: the
recovered polynomial is checked against a direct Sylvester determinant at points the interpolation
never sampled; the check is part of the route rather than a flag —
`ResultantOptions::with_off_domain_checks(0)` panics rather than disabling it — and on disagreement
the proven `2d²` path produces the answer, with `DegreeSource::PredictionFalsified` recording that
the prediction did not hold. It remains a **probabilistic consistency check and not a proof of a
polynomial identity** — `k` agreements bound the failure probability by `(bound/p)^k`.

The cost of the determinant kernel is **measured rather than assumed**.
`cargo run --release --example determinant_sweep` times it at orders 18, 162, 486, 1 458 and 4 374
on random bivariate pairs and fits a power law with per-point residuals, and the answer is
piecewise: above the L2 footprint the exponent is **2.9953 ± 0.0285** with a worst residual of 3.7%
— cubic to within the measurement, including at order 4 374 whose 153 MB matrix exceeds a CCX's L3,
so there is no cache cliff to model — and below it 2.79, which is fixed per-determinant overhead the
small orders cannot amortize. `fit_power_law` and `time_sylvester_determinants` are the public
instruments. See [`docs/research/resultant-elimination.md`](../research/resultant-elimination.md)
§6.9.
