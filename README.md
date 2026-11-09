![Zeebra](./zeebra.jpg "Zeebra is ZEro knowledge algeBRA")

# Zeebra is ZEro-knowledge algEBRA
[![CI](https://github.com/mfaulk/zeebra/actions/workflows/rust.yml/badge.svg)](https://github.com/mfaulk/zeebra/actions/workflows/rust.yml)

**Zeebra is a computational algebra library, in Rust, for developing and analyzing advanced
cryptography.** It provides the algebraic primitives that zero-knowledge proof systems are built
from — fast arithmetic over cryptographically large finite fields, polynomials, linear algebra — and
a Gröbner basis engine for the nonlinear systems whose hardness those primitives rely on for
security.

## What it is

Zero-knowledge proofs, and the hash functions designed to be cheap to prove, are built almost
entirely out of arithmetic in a large finite field: a number system of 31 to 256 bits in which
addition and multiplication wrap around a prime. Zeebra implements that layer and the mathematics
directly above it — field arithmetic, univariate and multivariate polynomials, dense and sparse
linear algebra, and the number-theoretic transform, which is the FFT over a finite field. It is a
library rather than a shell: plain Rust, generic over a `FiniteField` trait, stable toolchain, no C
dependencies and no linked algebra system.

The other half is a solver. A ZK-friendly primitive is an algebraic object — a low-degree round
function iterated a few times — and its security claim is that the system of polynomial equations
describing it cannot be solved in feasible time. Deciding whether that is true, for a given design
at a given number of rounds, is a computation: build the polynomial system, compute a Gröbner
basis, and read the solutions off it. Zeebra implements that pipeline end to end. Buchberger's
algorithm and Faugère's F4 compute bases under lexicographic, graded, graded-reverse and weighted
orders; FGLM converts a cheap basis into the lexicographic one that solves by back-substitution;
resultants offer a second, independent elimination route; and univariate root finding and
factorization finish the job. The solver returns *verified field points*, not a basis the caller
still has to interpret, and every stage carries an explicit resource budget whose breach is a typed
error naming the limit — a cost model is only as useful as its refusal to return a partial answer
as though it were a complete one.

For someone who already uses computational algebra: coefficient domains run to 256-bit prime fields
in Montgomery and CIOS form (BN254 and BLS12-381 scalar fields, Proth primes, Mersenne-31, 64-bit
primes), binary fields using carry-less multiplication, and general extension fields, with field
equations `x^q - x` available so a quotient dimension counts base-field points. F4 ships
Gebauer–Möller and the chain criterion, symbolic preprocessing over interned monomial handles,
sparse Macaulay matrices with selectable elimination backends, Hilbert-function degree bounds, and
per-stage timing and memory instrumentation. The zero-dimensional pipeline is differentially tested
against Singular, and timed against Singular, msolve, Groebner.jl and Sagebrush on a shared corpus
whose ideals are checked for equivalence before any timing is published.

## Quickstart

Zeebra builds on stable Rust. No nightly toolchain, no feature gates, no system libraries.

```sh
cargo build
cargo test
```

Solving a system over a finite field — every point of `F^N` where the polynomials vanish:

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

A Gröbner basis directly, by F4:

```rust
use zeebra::{fields::Zp13, grobner::f4, MonomialOrder, MultivariatePolynomial};

let vars = ["x", "y", "z"];
let system = vec![
    MultivariatePolynomial::<3, Zp13>::parse("x*z - y^2", vars).unwrap(),
    MultivariatePolynomial::<3, Zp13>::parse("x^3 - z^2", vars).unwrap(),
];

let basis = f4(&system, MonomialOrder::GradedReverseLexicographic).unwrap();
```

Every Rust example in this file and in [`docs/guide/`](docs/guide) is compiled and run by
`cargo test --doc`, so none of them can drift from the API.

Criterion benchmarks cover field arithmetic, polynomial arithmetic, dense and sparse linear algebra,
and Gröbner basis computation:

```sh
cargo bench                      # everything
cargo bench --bench grobner      # one suite
cargo bench --bench f4_stages    # F4, stage by stage
```

Wall-clock time does not say *why* a Gröbner computation cost what it did, so the algorithmic
counters are reported by examples rather than benchmarks:

```sh
cargo run --release --example f4_statistics   # pairs, reductions, zero reductions, basis size
cargo run --release --example f4_profile      # cost attributed per stage
cargo run --release --example solve_one       # a system in, verified solutions out
```

[`docs/guide/benchmarking.md`](docs/guide/benchmarking.md) is the full list — around seventy
instrumented examples — along with the measurement rules this repository follows: a benchmark lock
so two runs cannot share a machine, a memory ceiling guard, and a lint that refuses a published
figure carrying no commit.

## What is in the box

| Area | Guide |
|---|---|
| Finite fields: 31- to 256-bit primes, binary fields, extension fields | [`finite-fields.md`](docs/guide/finite-fields.md) |
| Polynomials: multivariate arithmetic, GCD, squarefree decomposition, factorization | [`polynomials.md`](docs/guide/polynomials.md) |
| Linear algebra: dense and sparse matrices, echelon backends | [`linear-algebra.md`](docs/guide/linear-algebra.md) |
| NTT and fast univariate arithmetic, root finding | [`ntt.md`](docs/guide/ntt.md) |
| Gröbner bases: Buchberger, monomial orders, FGLM conversion | [`grobner-bases.md`](docs/guide/grobner-bases.md) |
| F4, its resource budgets, and Hilbert functions | [`f4.md`](docs/guide/f4.md) |
| Solving zero-dimensional systems, and route selection | [`solving-systems.md`](docs/guide/solving-systems.md) |
| Integers, perfect powers, Lenstra's elliptic curve method | [`number-theory.md`](docs/guide/number-theory.md) |
| Reed–Solomon codes over an FFT domain | [`reed-solomon.md`](docs/guide/reed-solomon.md) |

## How Zeebra relates to existing systems

Gröbner basis computation already has excellent implementations. **Singular**, **Macaulay2** and
**Magma** are computer algebra systems: you drive them from their own language, interactively or by
script. **msolve** is a C library and command-line tool specializing in solving. **Groebner.jl** is
a Julia package. In Rust, **arkworks** covers field and curve arithmetic for proof systems but not
polynomial system solving. Zeebra occupies the gap between those two groups, and differs in four
ways that matter:

- **It is a library you link, under a permissive licence.** Singular, msolve and Groebner.jl are
  GPL; Magma is commercial. Zeebra is MIT, which is what lets a solver live inside a proof-system
  codebase rather than beside it as a subprocess.
- **The coefficient fields are the cryptographic ones.** Singular and msolve cap a prime
  characteristic below 2^31 — a limit visible in this repository's own comparison runs, where both
  decline the 64-bit and 254-bit instances. Zeebra runs F4, FGLM and zero-dimensional solving over
  BN254 and BLS12-381 scalar fields, and over binary and extension fields, with no change of
  representation.
- **It is Rust, with resource behaviour as part of the contract.** One toolchain, no FFI boundary,
  and budgets on matrix entries, bytes and degree that produce a typed error instead of exhausting
  the machine.
- **Correctness is checked against other systems, not asserted.** The zero-dimensional pipeline is
  differentially tested against Singular, and a cross-library corpus of standard families — Katsura,
  Cyclic, random MQ — is checked for ideal equivalence before any comparison is run.

On speed, the honest statement is a measured one rather than a claim. Zeebra, Singular 4.4.1,
msolve 0.11.0, Groebner.jl 0.10.11 and Sagebrush are timed on the same corpus on the same machine,
one process per row, each engine's answer agreed term-for-term first, and every ratio against an
engine's own startup floor is refused rather than quoted. **As of the current board, Zeebra loses
most of the comparisons it is admitted to** — it is the slowest of the five on random MQ at 10
variables, the corpus family closest in shape to a cryptographic system. Those losses are the
subject of ongoing work, and they are published in full, including the rows where an engine produced
nothing: [`research/competitive/COMPETITIVE.md`](research/competitive/COMPETITIVE.md), under the
protocol in
[`docs/research/external-comparison-protocol.md`](docs/research/external-comparison-protocol.md).

## Status and maturity

Zeebra began as an educational exercise and is version 0.1.0. The API is not stable, it has not been
audited, and it should not be assumed correct — what it has instead is published references for each
algorithm, property-based and differential testing, and a habit of measuring rather than claiming.
[`docs/guide/status.md`](docs/guide/status.md) is the running record of what is implemented.

For production use today, consider:

- **[arkworks-rs/algebra](https://github.com/arkworks-rs/algebra)** — algebraic structures and
  operations for zkSNARKs
- **[dimforge/nalgebra](https://github.com/dimforge/nalgebra)** — linear algebra for Rust
- **[tspiteri/rug](https://gitlab.com/tspiteri/rug)** — arbitrary-precision numbers
- **[msolve](https://github.com/algebraic-solving/msolve)**,
  **[Singular](https://github.com/Singular/Singular)** — mature polynomial system solving

## Contributing and documentation

- [`docs/guide/development.md`](docs/guide/development.md) — building, the full test matrix, what CI
  enforces, and the build configuration
- [`docs/guide/benchmarking.md`](docs/guide/benchmarking.md) — benchmark suites, instrumented
  examples, and the rules for publishing a measurement
- [`docs/guide/external-engines.md`](docs/guide/external-engines.md) — differential testing against
  Singular, and the contract for driving external engines
- [`docs/`](docs) — milestone records and [`docs/research/`](docs/research) notes, where the design
  decisions and their measurements are argued out
- [CLAUDE.md](CLAUDE.md) — repository conventions, including how concurrent coding agents claim work

Licensed under the [MIT licence](LICENSE-MIT).
