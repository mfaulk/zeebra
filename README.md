
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
```

A few tests compare the optimized Gröbner engine against the naive reference implementation on
systems where the reference takes minutes. They are `#[ignore]`d so the default suite stays fast,
and need release mode to finish in reasonable time:

```sh
cargo test --release -- --ignored
```

### Benchmarks

Criterion benchmarks cover field arithmetic, sparse polynomial operations, dense linear algebra,
and Gröbner basis computation:

```sh
cargo bench                              # everything
cargo bench --bench grobner              # one suite
```

Wall-clock time alone does not say *why* a Gröbner computation got faster. For the algorithmic
counters — pairs considered, pairs eliminated by Buchberger's first criterion, reductions, zero
reductions, basis size:

```sh
cargo run --release --example grobner_statistics
```

Recorded baselines, before/after measurements, and the reasoning behind each optimization are in
[`docs/MILESTONE-ALGEBRA-FOUNDATION.md`](docs/MILESTONE-ALGEBRA-FOUNDATION.md).

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
which is useful for understanding cost on a hard system. `grobner::benchmark_systems` provides the
standard `cyclic` and `katsura` families, and `grobner::reference` holds a deliberately naive
textbook implementation kept as a correctness oracle — use `buchberger` for real work.

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
