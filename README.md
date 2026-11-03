
![Zeebra](./zeebra.jpg "Zeebra is ZEro knowledge algeBRA")

# Zeebra is ZEro-knowledge algEBRA
[![CI](https://github.com/mfaulk/zeebra/actions/workflows/rust.yml/badge.svg)](https://github.com/mfaulk/zeebra/actions/workflows/rust.yml)

Zeebra implements a subset of computational algebra and number theory for zero-knowledge cryptography.

## Why You Should Use Zeebra
As the saying goes, you can either make software so simple that it obviously has no bugs, or so complicated that it has no obvious bugs. Zeebra emphasizes clear documentation,  published references for algorithmic implementations, interoperability with Sage, and property-based testing for exhaustive test coverage.

### Status
- [x] Big Integers
- [x] Integer Factoring
- [x] Finite Field Arithmetic for Large Finite Fields
- [x] Univariate and Multivariate Polynomials over Finite Fields
- [x] Linear Algebra over Finite Fields
- [x] Number-Theoretic Transform (FFT over Finite Fields)
- [x] Grobner Bases
- [x] Polynomial System Solving via Grobner Basis Algorithms
- [x] Sparse Linear Algebra over Finite Fields
- [x] F4 Grobner Bases
- [x] Gebauer-Moller and chain criteria, structured elimination, adaptive linear algebra

## Building and Testing
Zeebra builds on stable Rust; no nightly toolchain or feature gates are required.

```sh
cargo build
cargo test
```

Development checks, matching what CI enforces:

```sh
cargo fmt --all --check
cargo clippy --all-targets --all-features -- -D warnings
cargo test --doc
```

The Rust examples in this file are **compiled and run** by `cargo test --doc`, through a
`cfg(doctest)` item in `src/lib.rs`, so they cannot drift from the API they document. Blocks that
are illustrative rather than executable are fenced `text`.

CI resolves its toolchain to `stable`, which moves. A clippy run that is clean on an older stable
is therefore **not** evidence that CI is clean — new lints arrive with new releases, and one did
during this project's history. `rustup update stable` before trusting a clean run, or name the
version explicitly:

```sh
rustup run stable cargo clippy --all-targets --all-features -- -D warnings
```

Some tests compare the optimized Gröbner engine against the naive reference implementation, or
factor large integers, on inputs slow enough to take minutes. They are `#[ignore]`d so the default
suite stays fast, and need release mode to finish in reasonable time:

```sh
cargo test --release -- --ignored test_optimized_agrees_with_reference_on_slow_systems
cargo test --release -- --ignored test_f4_on_larger_systems
cargo test --release -- --ignored test_factorization
```

Four other `#[ignore]`d tests are unimplemented placeholders for statistical distribution checks
and a rare division branch, and they panic if run. A bare `cargo test -- --ignored` therefore
reports those four as failures; the commands above select the tests that are meant to pass.

CI runs the suite twice: once in debug, and once in release in a separate job that also runs the
two Gröbner engine-agreement tests above. Both configurations are checked because a release build
takes different paths — `debug-assertions` and `overflow-checks` are off, so every
`debug_assert`-guarded invariant goes unchecked and integer arithmetic wraps instead of panicking.
Release is also the configuration every benchmark uses, so

```sh
cargo test --release
```

is worth running locally before claiming a measurement.

### Benchmarks

Criterion benchmarks cover field arithmetic, sparse polynomial operations, dense and sparse linear
algebra, and Gröbner basis computation:

```sh
cargo bench                              # everything
cargo bench --bench grobner              # one suite
cargo bench --bench sparse_linear_algebra
cargo bench --bench f4_stages
```

`sparse_linear_algebra` has two groups, and the difference between them matters. `sparse_linalg`
times sparse row echelon beside dense *reduced* row echelon, which performs a back-substitution
pass the sparse side never does; it is indicative of nothing about storage and is kept only for
continuity. `matched_echelon` runs the identical algorithm under each `linalg::echelon` backend on
identical matrices, and times densification and sparsification in their own benchmark, so the
comparison measures representation rather than algorithm or conversion.

`f4_stages` times F4's stages separately — symbolic preprocessing, matrix construction,
elimination under each backend, representation conversion, and a whole batch — replaying the
batches a real computation produced rather than synthetic ones. `grobner` says whether something
got faster; `f4_stages` says whether a change removed cost or moved it from one stage to another.

Wall-clock time alone does not say *why* a Gröbner computation got faster. For the algorithmic
counters — pairs considered, pairs eliminated by Buchberger's first criterion, reductions, zero
reductions, basis size:

```sh
cargo run --release --example grobner_statistics   # Buchberger
cargo run --release --example f4_statistics        # F4, beside Buchberger
cargo run --release --example f4_profile           # F4, cost attributed per stage
cargo run --release --example f4_profile -- list   # the configurations available
cargo run --release --example f4_blocks            # F4, row arrangements of the Macaulay matrix
cargo run --release --example f4_selection         # reducer selection and the reducer cache
cargo run --release --example elimination_density  # how dense an F4 matrix really is
cargo run --release --example pair_criteria        # what each pair criterion discards, F4
cargo run --release --example pair_criteria -- buchberger
cargo run --release --example f4_ablation          # every configuration, one table
cargo run --release --example f4_milestone         # both engines, at matched and default criteria
cargo run --release --example fglm_baseline        # which systems are zero-dimensional, and what
                                                   # a lex basis costs against a grevlex one
cargo run --release --example fglm_baseline -- cyclic-6   # one system per process
timeout 900 cargo run --release --example buchberger_reach -- katsura-6 lex all
```

`f4_statistics` prints matrix dimensions, how many reductions each matrix absorbed, how much of
each matrix was reduction scaffolding, and how much elimination filled it in. It asserts that the
two engines agree wherever both can run. It pins itself to `F4Options::baseline()`, because its
columns are the ones `docs/MILESTONE-F4.md` §7.1 records and comparing against them needs that
configuration.

`f4_profile` prints where the time went: symbolic preprocessing, construction, elimination,
candidate extraction, and the final interreduction, with the remainder shown as `other` so an
unattributed cost cannot hide. It takes the name of a configuration — `baseline` by default,
`recommended` for what `F4Options::default()` is — so the effect of one optimization can be read
off against another's. The timing comes from
`F4Options::measure_stages`, which reads a clock four times per batch and is off by default.

`f4_blocks` replays the batches a computation really built and eliminates each one four ways —
rows as preprocessing produced them, reducer rows first, reducer rows taken as established pivots,
and the same with the reducer block interreduced — reporting row operations, peak live nonzeros,
final nonzeros, and time on the identical matrices. Holding the matrix fixed is the point: a
change of row arrangement changes which candidates come out, hence every later batch, so the
whole-computation effect and the per-elimination effect are different measurements.

`elimination_density` reports the density a representation policy would have to read: the
distribution of row densities as built and at each row's own peak during its reduction, the density
of the densest 64x64 blocks, and the three backends' elimination times with representation
conversion in its own column. A global density of a fraction of a percent says nothing about
either. `-- list` names the instances; the largest are excluded by default, because a dense
representation of katsura-7 grevlex is 374 MB for a matrix holding 112k entries.

`f4_selection` compares the two reducer-selection policies and the three cache modes against one
common baseline, on one line each: the closure size, the largest matrix, the peak live entries, the
row operations, the share of reducer multiples that had been needed before, and the stage times.
`f4_profile`'s configurations bundle several options together, so neither effect can be attributed
from it alone.

`f4_ablation` runs twelve configurations over the corpus and asserts every one returns the
baseline's basis, which is what establishes that the optimizations compose rather than conflict.
`f4_milestone` is the headline comparison: both engines on identical inputs in one process, with
the bases asserted equal wherever both can run. It reports **two** ratios, because the pair
criteria are shared machinery and the two functions' defaults do not match — see "Choosing a
strategy" below. `buchberger_reach` runs the classical engine on one hard instance per invocation
so an external timeout can bound it, which is how a dash in that table is shown to mean "does not
finish" rather than "was not tried".

`fglm_baseline` classifies each benchmark system as unit, zero-dimensional, or
positive-dimensional from the leading monomials of its grevlex basis, reports the dimension `D` of
`R/I` as a vector space, and times a lex basis against a grevlex one under both engines. It is the
baseline for the order-conversion work; **cyclic-4 is positive-dimensional**, so FGLM does not
apply to it, and that is measured rather than assumed.

Recorded baselines, before/after measurements, and the reasoning behind each optimization are in
[`docs/MILESTONE-ALGEBRA-FOUNDATION.md`](docs/MILESTONE-ALGEBRA-FOUNDATION.md),
[`docs/MILESTONE-F4.md`](docs/MILESTONE-F4.md),
[`docs/MILESTONE-F4-OPTIMIZATION.md`](docs/MILESTONE-F4-OPTIMIZATION.md), and
[`docs/MILESTONE-FGLM-SOLVING.md`](docs/MILESTONE-FGLM-SOLVING.md).

## Gröbner Bases

`grobner::buchberger` computes a reduced Gröbner basis under a chosen monomial order. All three
standard orders are available, and `MonomialOrder` is exported from the crate root:

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

`buchberger_with_statistics` returns the same basis alongside counters describing the computation,
which is useful for understanding cost on a hard system. `buchberger_with_criteria` additionally
takes a `PairCriteria`, so the classical engine can be run under the same pair-elimination
criteria as F4 — and compared against `PairCriteria::NONE`, which reduces every pair. `grobner::benchmark_systems` provides the
standard `cyclic` and `katsura` families plus `planted`, which builds a zero-dimensional system
around a solution you choose. `grobner::reference` holds a deliberately naive textbook
implementation kept as a correctness oracle — use `buchberger` or `f4` for real work.

### Zero-dimensional ideals

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
points rather than a count of them. A positive-dimensional ideal is rejected with
`FglmError::PositiveDimensional` before any enumeration, since the enumeration would not
terminate, and the `max_dimension` argument bounds it otherwise.

### F4

`grobner::f4` computes the same basis by Faugère's F4 algorithm, which replaces individual
S-polynomial reductions with batched symbolic preprocessing and sparse finite-field linear algebra:

```rust
use zeebra::{fields::Zp13, grobner::f4, MonomialOrder, MultivariatePolynomial};

let vars = ["x", "y", "z"];
let system = vec![
    MultivariatePolynomial::<3, Zp13>::parse("x*z - y^2", vars).unwrap(),
    MultivariatePolynomial::<3, Zp13>::parse("x^3 - z^2", vars).unwrap(),
];

let basis = f4(&system, MonomialOrder::GradedReverseLexicographic).unwrap();
```

A reduced Gröbner basis is unique for a given ideal and order, so `f4` and `buchberger` return
exactly the same thing, with the same handling of zero, duplicate, and redundant generators. They
differ only in how they get there, and therefore in cost.

**Which to use.** `buchberger` is the better choice on small systems, where building a matrix costs
more than the reductions it replaces. F4 pays off where Buchberger wastes the most work: on
katsura-5 under lex, Buchberger reduces 1790 S-polynomials and 1725 of them come out zero, while
F4 covers the same ground in 29 matrices. See
[`docs/MILESTONE-F4.md`](docs/MILESTONE-F4.md) for measurements, including the cases where F4
loses.

`f4` returns a `Result`: an F4 matrix can grow far beyond what its inputs suggest, and elimination
can make it denser still, so both are budgeted. Exceeding a budget is an `F4Error` naming the limit
— never a basis that looks complete and is not. `f4_with_options` takes an `F4Options` and returns
`F4Statistics` alongside the basis:

```rust
use zeebra::{fields::Zp13, grobner::{f4_with_options, F4Options}, MonomialOrder, MultivariatePolynomial};

let vars = ["x", "y", "z"];
let system = vec![MultivariatePolynomial::<3, Zp13>::parse("x*z - y^2", vars).unwrap()];
let options = F4Options { max_pairs_per_batch: Some(16), ..F4Options::default() };

let (basis, statistics) =
    f4_with_options(&system, MonomialOrder::GradedReverseLexicographic, &options).unwrap();
println!("{} batches, largest matrix {} x {}",
    statistics.batches, statistics.max_matrix_rows, statistics.max_matrix_columns);
```

`max_pairs_per_batch: Some(1)` reduces one S-polynomial per matrix, which is useful for isolating
the effect of batching; the answer does not change, only the number and shape of the matrices.

#### Choosing a strategy

`F4Options` also selects *how* the computation is performed. A reduced Gröbner basis is unique for
a given ideal and order, so **no strategy changes the answer** — only the cost. Each is a separate
field rather than one "fast" switch, so that the contribution of each can be measured on its own:

| Field | Choices | What it changes |
|---|---|---|
| `elimination` | `Backend::{Sparse, Dense, Adaptive}` | the representation elimination works in: sparse rows throughout, dense rows throughout, or sparse rows reduced through a dense accumulator |
| `reduction` | `ReductionStrategy::{Unstructured, Structured}` | whether reducer rows are established as pivots before the pair rows are reduced against them |
| `reducer_selection` | `ReducerSelection::{FirstApplicable, LargestLeadingMonomial}` | which basis element symbolic preprocessing picks to reduce a monomial. `FirstApplicable` is the default and the faster of the two: picking the largest divisor minimizes the multiplier but maximizes how much of the reducer's tail stays reducible, which grows the matrix |
| `criteria` | `PairCriteria { product, chain, gebauer_moller }` | which criteria may discard a critical pair before a matrix is built |
| `reducer_cache` | `CacheMode::{Off, Count, Store}` | whether reducer multiples are remembered between batches. `Count` measures repetition without serving anything; `Store` currently behaves as `Count`, because building a multiple's terms is an integer addition per variable per term and serving them from a map costs more than that even at a 95% hit rate |
| `measure_stages` | `bool` | whether `F4Statistics::stages` is populated |

`ReductionStrategy::Structured` exploits the fact that symbolic preprocessing gives every reducer
multiple a distinct leading monomial, none of them a critical pair's lcm: putting those rows first,
descending by leading monomial, makes the upper-left block unit upper triangular without any work,
so elimination takes those pivots as given and never reduces the block against anything. It
performs *more* row operations than the one-pass path and far less fill-in — on katsura-7 under
grevlex, 8% of the baseline's peak live entries — which is a net win on the dense grevlex and lex
instances and a small loss under grlex. The per-order numbers are in
[`docs/MILESTONE-F4-OPTIMIZATION.md`](docs/MILESTONE-F4-OPTIMIZATION.md) §7.1.

There are two named configurations, and both are public on purpose:

- **`F4Options::recommended()`**, which is what `default()` is — structured elimination, all pair
  criteria, the dense accumulator. It is the fastest of twelve configurations on ten of eleven
  instances measured; on the eleventh the criteria have already made elimination 9% of the total,
  so the accumulator's gain there is smaller than run-to-run variation.
- **`F4Options::baseline()`**, every strategy off. This is the configuration the measurements are
  taken against, and it is kept reachable so they can be reproduced; a default that absorbed its
  own reference would make the comparison impossible to repeat.

Note that two of the improvements are *not* selectable, because they are not trade-offs: a cheaper
monomial hash in symbolic preprocessing and the rewritten final interreduction apply to
`baseline()` too.

`PairCriteria::NONE` reduces every pair, which is the reference the criteria are checked against: a
criterion is sound exactly when enabling it does not change the basis.

With `default()`, **F4 is faster than `buchberger()` on every system and order measured** — 1.2x
to 236x — and katsura-6 under grevlex, F4's worst case at 0.47x one milestone ago, is 3.8x.

That comparison is between the two functions' defaults, and the two defaults are not
algorithmically matched: the pair criteria are **shared machinery**, and `F4Options::recommended()`
enables `PairCriteria::ALL` while `buchberger()` uses `PRODUCT_ONLY`. Give the classical engine the
same criteria via `buchberger_with_criteria` and it speeds up 2.2x to 13.1x on its own; F4 then
wins on fourteen of sixteen instances by 1.12x to 45x, and loses on two instances under 100
microseconds where there is nothing to amortise. That matched figure is the one that isolates F4's
*matrix algorithm* from the critical-pair selection either engine can use.

The criteria also change what is *reachable*: katsura-7 is within `buchberger`'s range with them
and was not without. The one instance that remains categorically F4's is **katsura-6 under lex** —
the classical engine does not finish it in 900 seconds with every criterion enabled, and F4
returns the same basis in 16 ms.

`cargo run --release --example f4_milestone` reports both columns; §8.3 of
[`docs/MILESTONE-F4-OPTIMIZATION.md`](docs/MILESTONE-F4-OPTIMIZATION.md) has the analysis.

Every backend returns the identical matrix and the identical `EliminationStatistics`, so the choice
is purely a cost one. `Backend::Adaptive` is the fastest on every instance measured — 1.2x to 2.0x
over `Sparse` on the elimination stage — and `Backend::Dense` is slower than `Sparse` everywhere,
which is the honest answer to whether a dense representation pays on F4-shaped matrices. It is kept
because it is the control the other two are compared against. See §7.4 of
[`docs/MILESTONE-F4-OPTIMIZATION.md`](docs/MILESTONE-F4-OPTIMIZATION.md).

The three criteria are Buchberger's first criterion (`product`, relatively prime leading
monomials), Buchberger's chain criterion (`chain`, applied when a batch is selected), and
Gebauer–Möller pair-set minimization (`gebauer_moller`, applied as pairs are inserted). All three
are available to both engines, and `examples/pair_criteria.rs` reports what each discards.
Gebauer–Möller is the strongest of the three in F4 — on katsura-6 under lex it takes the pairs
reduced from 4611 to 231 and the largest matrix from 1954 rows to 92 — and it subsumes what the
chain criterion finds at selection time, so enabling both discards nothing more than enabling
Gebauer–Möller alone. In the classical engine neither dominates: on katsura-5 under lex the chain
criterion reduces fewer pairs than Gebauer–Möller does.

`grobner::solve` still uses `buchberger`. The sparse linear algebra F4 is built on is reusable on
its own, as `linalg::sparse`, with the dense representations as `linalg::dense`;
`linalg::echelon` is the backend-selecting interface over both.

`grobner::trace_batches` runs a computation and returns every batch it reduced, each as the basis
at the time plus the pairs selected. That is what lets a stage be benchmarked or counted on real
input instead of on a synthetic approximation of it; `benches/f4_stages.rs` is built on it.

Field elements reject non-canonical representatives on deserialization. Every value this crate
serializes round-trips unchanged, but bytes encoding an integer outside `[0, P)` are an error
rather than being silently reduced, since they indicate corruption or a mismatched modulus.

## Solving Polynomial Systems
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

## Factoring Univariate Polynomials
`factorize` returns the monic irreducible factors of a univariate polynomial over a finite field,
with multiplicities, and `is_irreducible` tests a single polynomial:

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::{factorize, fields::Zp7, is_irreducible, FiniteField, UnivariatePolynomial};

// x^3 + 6x^2 + 11x + 6 = (x + 1)(x + 2)(x + 3) over GF(7)
let f = UnivariatePolynomial::<Zp7>::new(&[
    Zp7::new(6), Zp7::new(11), Zp7::new(6), Zp7::new(1),
]);

let mut rng = StdRng::seed_from_u64(0);
for (factor, multiplicity) in factorize(&f, &mut rng) {
    assert!(is_irreducible(&factor));
    println!("({})^{}", factor, multiplicity);
}
```

The distinct irreducible factors of each degree are collected with `gcd(f, x^(q^d) - x)`, then
each group of equal-degree factors is separated by Cantor–Zassenhaus splitting. Because
`x^(q^d) - x` is squarefree, that gcd gives the distinct factors whatever the multiplicities in
`f` are — so no squarefree decomposition is needed, and `x^p` in characteristic `p`, whose
derivative vanishes, needs no special handling. Multiplicities are recovered afterwards by
division.

Splitting is randomized, so this takes an rng and the order of the returned factors is
unspecified.

## Why You *Shouldn’t* Use Zeebra
I wrote Zeebra as an educational exercise. It is not yet complete or mature. It is not necessarily correct. For something more production-ready, please consider:

- **[arkworks-rs/algebra](https://github.com/arkworks-rs/algebra/tree/master)** - Algebraic structures and operations for zkSNARKs
- **[dimforge/nalgebra](https://github.com/dimforge/nalgebra)** - Linear Algebra library for the Rust programming language
- **[tspiteri/rug](https://gitlab.com/tspiteri/rug)** - Arbitrary-precision numbers
- **[axect/peroxide](https://github.com/Axect/Peroxide)** - Linear algebra library for machine learning
