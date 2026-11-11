# Gröbner bases

Buchberger's algorithm, monomial orders including a weighted family, reduction against a basis you
supply, zero-dimensional classification, and FGLM order conversion.

`grobner::buchberger` computes a reduced Gröbner basis under a chosen monomial order. The three
standard orders and a weighted family are available, and `MonomialOrder` is exported from the crate
root:

```rust
use zeebra::{fields::Zp13, grobner::buchberger, MonomialOrder, MultivariatePolynomial};

let vars = ["x", "y", "z"];
let system = vec![
    MultivariatePolynomial::<3, Zp13>::parse("x*z - y^2", vars).unwrap(),
    MultivariatePolynomial::<3, Zp13>::parse("x^3 - z^2", vars).unwrap(),
];

let basis = buchberger(&system, MonomialOrder::GradedReverseLexicographic);
```

The returned basis is reduced and in a deterministic order, so it is reproducible across runs.
Which order you pick matters: graded reverse lexicographic is usually cheapest, while lexicographic
is what makes a system easy to solve by back-substitution and can be dramatically more expensive.

## Weighted monomial orders

`MonomialOrder::Weighted` grades by a weighted degree `Σ wᵢeᵢ` instead of the total degree, with a
tie-break you choose. The weights must be strictly positive — that is what makes the order a
well-order, so reduction terminates — and a weight vector that is empty or holds a zero is refused
at construction rather than producing a quietly wrong basis:

```rust
use zeebra::{Monomial, MonomialOrder, WeightedOrderError, WeightedTieBreak};
use std::cmp::Ordering;

// The FreeLunch order for Griffin at r = 5: weights (1, 7, 49), ties to the larger exponent at
// the highest differing index.
let order = MonomialOrder::weighted(&[1, 7, 49], WeightedTieBreak::LastVariableFirst).unwrap();

// x_2 outranks x_0^48 despite 48 times the total degree, which no unweighted order does.
let x2 = Monomial::<3>::new(&[0, 0, 1]);
let x0_48 = Monomial::<3>::new(&[48, 0, 0]);
assert_eq!(order.cmp(&x2, &x0_48), Ordering::Greater);
assert_eq!(
    MonomialOrder::GradedReverseLexicographic.cmp(&x2, &x0_48),
    Ordering::Less
);

// A zero weight is not a usable grading.
assert_eq!(
    MonomialOrder::weighted(&[1, 0], WeightedTieBreak::Lexicographic),
    Err(WeightedOrderError::NonPositiveWeight { index: 1 })
);
```

`WeightedTieBreak::Lexicographic` with every weight 1 reproduces `GradedLexicographic` exactly, and
`WeightedTieBreak::ReverseLexicographic` reproduces `GradedReverseLexicographic`; both agreements
are asserted against the existing implementations. `LastVariableFirst` is Definition 2 of the
Algebraic FreeLunch paper and is **not** the grevlex tie-break — it favours the larger exponent at
the highest differing index where grevlex favours the smaller, so the two disagree on every tie.

A weight vector known at compile time can skip the interning `MonomialOrder::weighted` does, and an
invalid one then fails to compile:

```rust
use zeebra::{MonomialOrder, WeightedOrder, WeightedTieBreak};

static GRIFFIN_R5: WeightedOrder = WeightedOrder::new(&[1, 7, 49], WeightedTieBreak::LastVariableFirst);
let order = MonomialOrder::Weighted(&GRIFFIN_R5);
assert_eq!(order.arity(), Some(3));
```

The weight vector's arity must equal the number of variables. A mismatch panics rather than
comparing a prefix, because a truncated weight vector is a consistent order on a *different* ring;
`normal_form_modulo` below reports it as an error instead, so a caller that assembled the order and
the system separately learns which is wrong.

Weighted orders are refused by every external comparand adapter. No third-party engine here has a
weighted spelling whose coefficient and ordering conventions have been verified the way the
unweighted ones have, and substituting degrevlex would compare a correct basis against a different
question.

## Reducing against a basis you already have

`MultivariatePolynomial::normal_form_modulo` reduces by a basis the caller supplies rather than one
Zeebra computed. `normal_form` has always accepted an arbitrary divisor set; what this adds is the
contract that makes the answer canonical, plus the preconditions that can be checked cheaply:

```rust
use zeebra::fields::Zp13;
use zeebra::grobner::leading_monomials_are_pairwise_coprime;
use zeebra::{MonomialOrder, MultivariatePolynomial, WeightedTieBreak};

let vars = ["x0", "x1", "x2"];
let parse = |s: &str| MultivariatePolynomial::<3, Zp13>::parse(s, vars).unwrap();
let order = MonomialOrder::weighted(&[1, 2, 4], WeightedTieBreak::LastVariableFirst).unwrap();
let basis = [parse("x1^3 - x0^6"), parse("x2^3 - x0^12"), parse("x0^12 - x1*x2")];

// Pure powers of distinct variables: pairwise coprime leading monomials, so Buchberger's first
// criterion certifies this is already a Gröbner basis with no reduction performed.
assert!(leading_monomials_are_pairwise_coprime(&basis, order));

let reduced = parse("x0^15").normal_form_modulo(&basis, order).unwrap();
// Canonical, so independent of the order the basis is given in.
let mut rotated = basis.to_vec();
rotated.rotate_left(1);
assert_eq!(parse("x0^15").normal_form_modulo(&rotated, order).unwrap(), reduced);
```

If the supplied basis really is a Gröbner basis under the order, the result is *the* normal form:
independent of the basis permutation, zero exactly on members of the ideal, and linear in the
dividend. `grobner::leading_monomials_are_pairwise_coprime` is a sufficient certificate that costs
no reduction — Buchberger's first criterion disposes of every S-pair when the leading monomials
share no variable — and it is how the FreeLunch route establishes a Gröbner basis without running
one. `false` means *not certified by this criterion*, never *not a Gröbner basis*.

`buchberger_with_statistics` returns the same basis alongside counters describing the computation,
which is useful for understanding cost on a hard system. `buchberger_with_criteria` additionally
takes a `PairCriteria`, so the classical engine can be run under the same pair-elimination
criteria as F4 — and compared against `PairCriteria::NONE`, which reduces every pair. `grobner::benchmark_systems` provides the
standard `cyclic` and `katsura` families plus `planted`, which builds a zero-dimensional system
around a solution you choose. `grobner::reference` holds a deliberately naive textbook
implementation kept as a correctness oracle — use `buchberger` or `f4` for real work.

## Krull dimension

Call `grobner::krull_dimension(&basis, order)` with a Gröbner basis and the order used to compute it.
It returns `Some(0)` for a zero-dimensional ideal, `None` for the unit ideal, and the number of
variables for the zero ideal. `QuotientBasis::dimension` gives the vector-space dimension of a
finite quotient. The Krull dimension search works from the supports of the leading monomials and
can take exponential time in the number of variables.

## Zero-dimensional ideals

A Gröbner basis says whether the quotient `R/I` is finite-dimensional, and if it is, what its
monomial basis is. `grobner::classify_ideal` separates the unit ideal, a proper zero-dimensional
ideal, and a positive-dimensional one; `grobner::QuotientBasis` enumerates the standard monomials —
those divisible by no leading monomial — whose count is the quotient dimension `D`:

```rust
use zeebra::fields::Zp2147483647;
use zeebra::grobner::{classify_ideal, f4, IdealClass, QuotientBasis};
use zeebra::{MonomialOrder, MultivariatePolynomial};

type F = Zp2147483647;
let order = MonomialOrder::GradedReverseLexicographic;

// <x^2, y^2>: one point over the algebraic closure, but a quotient of dimension four.
let system: Vec<MultivariatePolynomial<2, F>> = ["x^2", "y^2"]
    .iter()
    .map(|s| MultivariatePolynomial::parse(s, ["x", "y"]).unwrap())
    .collect();
let basis = f4(&system, order).unwrap();

assert_eq!(classify_ideal(&basis, order), IdealClass::ZeroDimensional);
let quotient = QuotientBasis::new(&basis, order, 1 << 20).unwrap();
assert_eq!(quotient.dimension(), 4);      // 1, x, y, xy
```

`D` is the dimension of `R/I` as a vector space, **not** the Krull dimension: it counts the zeros
over the algebraic closure with multiplicity, so it is an upper bound on the number of distinct
points rather than a count of them. `<x^2, y^2>` above has one distinct zero and `D = 4`. A
positive-dimensional ideal is rejected with `FglmError::PositiveDimensional` before any
enumeration, since the enumeration would not terminate, and the `max_dimension` argument bounds it
otherwise.

`grobner::QuotientAlgebra` adds the arithmetic: coordinate vectors over those monomials, and the
`N` linear operators that multiply by a variable.

```rust
use zeebra::fields::Zp2147483647;
use zeebra::grobner::{f4, FglmOptions, QuotientAlgebra};
use zeebra::{MonomialOrder, MultivariatePolynomial, Zero};

type F = Zp2147483647;
let order = MonomialOrder::GradedReverseLexicographic;

let system: Vec<MultivariatePolynomial<2, F>> = ["x^2", "y^2"]
    .iter()
    .map(|s| MultivariatePolynomial::parse(s, ["x", "y"]).unwrap())
    .collect();
let basis = f4(&system, order).unwrap();
let algebra = QuotientAlgebra::new(&basis, order, &FglmOptions::default()).unwrap();

// Multiplication by x is nilpotent here: x is nonzero in R/I but x^2 is not.
let x = algebra.multiply_by_variable(0, &algebra.one());
let x_squared = algebra.multiply_by_variable(0, &x);
assert!(x.iter().any(|c| !c.is_zero()));
assert!(x_squared.iter().all(|c| c.is_zero()));
```

That nilpotence is the point of keeping multiplicities: `<x^2, y^2>` has a single geometric zero,
and an operator with no eigenbasis. `cargo run --release --example fglm_operators` reports how much
storage the operators need — 0.34% of a dense matrix on planted-8, but 57% on the katsura family,
where the sparse representation does not pay for itself.

## Monomial-order conversion (FGLM)

`grobner::fglm_to_lex` converts a zero-dimensional Gröbner basis under any order into the
lexicographic basis, by linear algebra over `R/I` rather than by another Gröbner computation. The
point is that grevlex is usually much cheaper to compute than lex:

```rust
use zeebra::fields::Zp2147483647;
use zeebra::grobner::{f4, fglm_to_lex};
use zeebra::{MonomialOrder, MultivariatePolynomial};

type F = Zp2147483647;
let system: Vec<MultivariatePolynomial<2, F>> = ["x^2 - y", "y^3 - 1"]
    .iter()
    .map(|s| MultivariatePolynomial::parse(s, ["x", "y"]).unwrap())
    .collect();

let grevlex = f4(&system, MonomialOrder::GradedReverseLexicographic).unwrap();
let lex = fglm_to_lex(&grevlex, MonomialOrder::GradedReverseLexicographic).unwrap();

// A reduced Gröbner basis is unique for an ideal and an order, so this is an equality of values.
assert_eq!(lex, f4(&system, MonomialOrder::Lexicographic).unwrap());
```

The conversion is checked against **29 lexicographic bases computed by Singular**, committed as
literals and regenerable with `Singular -q tools/reference_bases.sing`. Singular's `std` is
Buchberger/slimgb lineage, so those references are independent of Zeebra's F4 in algorithm and not
only in implementation. No external system is needed to run the tests. A further **240 recorded
cases** check every intermediate result rather than only the final basis — see "Differential
testing against Singular" below.

**`fglm_to_lex` trusts its input to be a Gröbner basis under the stated order, and returns a wrong
basis rather than an error if it is not.** Use `fglm_to_lex_checked` for input of unknown
provenance; it verifies Buchberger's criterion first, which costs 0.6x to 27x what computing the
basis cost, and that is why it is not the default. `grobner::is_grobner_basis` is the check on its
own.

### Building the multiplication operators

Column `j` of the operator `T_i` is the normal form of `x_i b_j`, and almost all of a conversion is
computing those: **95% of katsura-7's**, measured. But the products `x_i b_j` that leave the
standard monomials are not distinct — `x*y` is reached from both `x * y` and `y * x` — and between a
fifth and a third of them repeat a monomial some other column already reduced.
`FglmOptions::operator_construction` chooses whether to notice:

```rust
use zeebra::grobner::fglm::{FglmOptions, OperatorConstruction};

// One normal form per nonstandard column: M17's strategy, kept as the reference.
let per_column = FglmOptions::baseline();

// One normal form per *distinct* border monomial, reused by every column that reaches it.
let deduplicated = FglmOptions::default()
    .with_operator_construction(OperatorConstruction::DeduplicatedBorder);
```

A third strategy shares more than the reductions:

```rust
use zeebra::grobner::fglm::{FglmOptions, OperatorConstruction};

// Border monomials reduced in batches against a shared symbolic closure, with the arithmetic over
// integer column indices rather than through a polynomial's hash map. The default since M18-5.
let batched = FglmOptions::default();
assert_eq!(batched.operator_construction, OperatorConstruction::BatchedBorder);
```

All three build **identical operators**, which the tests assert by comparing whole
`QuotientAlgebra` values rather than the lex bases they lead to. Measured on the whole conversion:

| system | `D` | per-column | deduplicated | batched |
|---|---:|---:|---:|---:|
| katsura-6 | 32 | 3.56 ms | 2.70 ms | **0.52 ms** |
| katsura-7 | 64 | 42.92 ms | 31.58 ms | **2.69 ms** |
| cyclic-6 | 156 | 29.77 ms | 19.60 ms | **2.82 ms** |
| planted-8 | 256 | 3.40 ms | 3.28 ms | 2.86 ms |
| planted-10 | 1,024 | 42.71 ms | 40.47 ms | 36.33 ms |

**Katsura-7's operator construction goes from 34.4 ms to 1.69 ms** under Criterion, a 20x change in
the stage that was 96% of the conversion — and nothing in the corpus is slower.

The batch *size* is what makes that last clause true. A bigger batch shares more closure and wins on
katsura and cyclic; on the planted family a reduction is one step, so the closure is nearly all the
work and a bigger batch is pure overhead — one unbounded batch is 1.3x **slower** than the scalar
path on planted-10. `BorderBatch::recommended()` uses 64 targets, which is within 13% of the best
size on both families and faster than scalar on every system.

`BatchOverflow` decides what happens when a batch's closure crosses a limit, and neither option
drops a target: `Fail` returns `FglmError::BorderBatchExceeded` naming the limit, and `Scalar`
reduces that batch one target at a time and counts that it did.

**`BatchedBorder` at a batch of 64 is the default**, chosen from the integration ablation in
`docs/MILESTONE-FGLM-SCALABILITY.md` §9 rather than from katsura-7 alone: it is the one strategy
that is at least as fast as M17's on every system in the corpus. `FglmOptions::baseline()` names
the M17 configuration, so a measurement still has something fixed to be quoted against.

### Storing the multiplication operators

A column that leaves the staircase is not necessarily sparse. Measured, a reduced column holds **79%
of `D` on katsura-7 and 0.14% on planted-10** — and a sparse entry carries an index as well as a
coefficient, so it costs twice a dense cell and only saves below half fill.
`FglmOptions::operator_storage` chooses, **per column**:

```rust
use zeebra::grobner::fglm::{FglmOptions, OperatorStorage};

// `(index, coefficient)` pairs for every reduced column: M17's representation, the reference.
let sparse = FglmOptions::baseline();

// Whichever of the two allocates fewer bytes, decided column by column. The default since M18-5.
let adaptive = FglmOptions::default();
assert_eq!(adaptive.operator_storage, OperatorStorage::Adaptive);
```

On katsura-7 the operators go from 264.5 kB to **163.6 kB**, and `Adaptive` beats *both* extremes
there — 163.6 against sparse's 264.5 and an all-dense 172.0 — which only a per-column choice can do.
On the planted family it declines every column and is sparse exactly. All-dense is kept as a
strategy to show that it is ruinous rather than to be used: planted-10 would need 51 MB where it
needs 380 kB.

`max_operator_bytes` is a second budget beside `max_operator_entries`, not a redefinition of it:
entries are mathematical nonzeros and bytes are allocations, and the two diverge once a column is
held densely.


### Certified scalar Wiedemann

`FglmOptions::conversion_strategy` selects `Classical`, `Adaptive` (recommended default), or `Wiedemann` (force an
attempt). Adaptive selection tries quotients of dimension at least 128 when the last variable's
operator scans at most one quarter of the cells of a dense matrix. Three reproducibly seeded
projections bound the work before classical fallback. This heuristic does not assert shape position.

```rust
use zeebra::{fields::Zp13, grobner::{f4, fglm::{
    fglm_to_lex_with_options, ConversionStrategy, FglmOptions,
}}, MonomialOrder, MultivariatePolynomial};
let order = MonomialOrder::GradedReverseLexicographic;
let source: Vec<MultivariatePolynomial<2, Zp13>> = ["x-y^2", "y^7-1"].iter()
    .map(|p| MultivariatePolynomial::parse(p, ["x", "y"]).unwrap()).collect();
let source = f4(&source, order).unwrap();
let options = FglmOptions { conversion_strategy: ConversionStrategy::Wiedemann,
    ..FglmOptions::recommended() };
let (lex, stats) = fglm_to_lex_with_options(&source, order, &options).unwrap();
assert_eq!(lex.len(), 2);
assert!(stats.wiedemann_attempts > 0);
```

A full-degree scalar recurrence supplies candidates, including multiplicities for nonradical
ideals. Every relation is evaluated independently in the quotient algebra before the fast route
returns it. Membership and the shape leading monomials prove that the result is the reduced lex
basis. Lower-degree recurrences, failed certification or insufficient workspace select the
classical walk; `conversion_route`, `wiedemann_attempts`, and `wiedemann_fallback` report the choice.
A projection failure does not prove that the variable is nonseparating.

Both routes enforce `max_span_entries` and `max_span_bytes` before allocating their dependence
workspace. Wiedemann checks a conservative linear allowance, recorded as
`memory.krylov_workspace_cells` and `memory.krylov_workspace_bytes`; classical fallback checks the
original quadratic blocks after the fast workspace is released. Operator budgets and the quotient
dimension cap apply to both. These are representation budgets, not process-RSS ceilings; output
polynomial maps and allocator overhead are excluded.

`cargo run --release --example wiedemann_conversion -- --variables 4 --degree 5` compares alternating
classical and adaptive runs on a deterministic shape-position family. It asserts equal bases and
reports operator construction separately. `--route adaptive` runs only that policy in a fresh
process for attributable peak RSS. `--input FILE` reads a **precomputed grevlex basis**: variable
names on line one, characteristic `65537` on line two, then comma-separated polynomials. The input
precondition is the same as `fglm_to_lex_with_options`; the file path is not a claim of validation.

With the `external-runners` feature, `--msolve PATH` additionally checks exact eliminant equality
against msolve on those same generators. Zeebra computes the full certified lex basis before
projecting its eliminant; msolve's process wall includes its own basis pass. The example reports
raw durations and does not claim a startup-floor-qualified speedup. Set `ZEEBRA_MACHINE` and
`ZEEBRA_AFFINITY`, build first, then use `tools/benchlock.sh` and `taskset` for measurements.

The measurement example exposes explicit overrides through `--max-dimension`, `--span-cells`,
`--span-bytes`, `--operator-entries`, `--operator-bytes`, `--border-entries`, `--border-columns`,
and `--border-rows`. These change only that invocation; keep an external wall/RSS backstop when
raising them. A border-construction refusal precedes conversion and needs its own budget decision.
