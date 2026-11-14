![Zeebra](./zeebra.jpg "Zeebra is ZEro knowledge algeBRA")

# High-Performance Computational Algebra for Cryptographic Security Research
[![CI](https://github.com/mfaulk/zeebra/actions/workflows/rust.yml/badge.svg)](https://github.com/mfaulk/zeebra/actions/workflows/rust.yml)

**Zeebra is a computational algebra library, in Rust, for developing and analyzing advanced
cryptography.**

It provides the algebraic primitives that zero-knowledge proof systems are built from — fast
arithmetic over cryptographically large finite fields, polynomials, linear algebra, the
number-theoretic transform — and a Gröbner basis engine for the nonlinear systems whose hardness
those constructions depend on for security.

Zeebra is a library rather than a shell: plain Rust, generic over a `FiniteField` trait, stable
toolchain, no C dependencies and no linked algebra system.

## What it is

Zero-knowledge proofs, and the hash functions designed for them, are built almost entirely out of
arithmetic in finite fields of 31 to 256 bits. Zeebra implements those fields — prime fields up to
BN254 and BLS12-381, binary fields and extension fields — and the mathematics built on them.

Zeebra is also a solver. The security claim of a ZK-friendly primitive is that the polynomial system
describing it cannot be solved in feasible time. Checking that claim is a computation: build the
system, compute a Gröbner basis, and read off the solutions. Zeebra does this end to end with
Buchberger, Faugère's F4, FGLM, resultants and univariate root finding, and returns *verified*
field points. Every stage runs under an explicit resource budget, so a computation at the edge of
feasibility fails with a typed error rather than exhausting the machine.

## Why this matters for security

Hash functions and ciphers designed for zero-knowledge proofs, such as Poseidon-style
constructions, choose their round counts from estimates of how expensive an algebraic attack would
be. Those estimates are usually extrapolated from complexity formulas rather than measured. Zeebra
makes them measurable: model the primitive as a polynomial system, run the attack under an explicit
compute and memory budget, and check every recovered solution against the original equations.
The result is evidence, a measured cost or a verified break, rather than an asymptotic argument.

## Quickstart

Zeebra builds on stable Rust 1.91 or newer.

```sh
cargo build
cargo test
cargo run --release --example quickstart
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
`cargo test --doc`.

## What is in the box

| Area | Guide |
|---|---|
| Finite fields: 31- to 256-bit primes, binary fields, extension fields | [`finite-fields.md`](docs/guide/finite-fields.md) |
| Polynomials: multivariate arithmetic, GCD, squarefree decomposition, factorization, modular composition | [`polynomials.md`](docs/guide/polynomials.md) |
| Linear algebra: dense and sparse matrices, echelon backends | [`linear-algebra.md`](docs/guide/linear-algebra.md) |
| NTT and fast univariate arithmetic, root finding | [`ntt.md`](docs/guide/ntt.md) |
| Gröbner bases: Buchberger, monomial orders, FGLM conversion | [`grobner-bases.md`](docs/guide/grobner-bases.md) |
| F4, its resource budgets, and Hilbert functions | [`f4.md`](docs/guide/f4.md) |
| Solving zero-dimensional systems, and route selection | [`solving-systems.md`](docs/guide/solving-systems.md) |
| Integers, perfect powers, Lenstra's elliptic curve method | [`number-theory.md`](docs/guide/number-theory.md) |
| Reed–Solomon codes over an FFT domain | [`reed-solomon.md`](docs/guide/reed-solomon.md) |
| R1CS import and assignment checks | [`r1cs.md`](docs/guide/r1cs.md) |

### Cargo features

| Feature | Default | What it adds |
|---|---|---|
| `external-runners` | on | Drives msolve, Groebner.jl, Sagebrush, Giac and Singular as subprocesses. Adds no dependency. |
| `proptest` | off | `Arbitrary` implementations for the public types, for property-testing downstream code. |
| `research-work` | off | Research counters and opt-in experiments. Shipping defaults are unaffected. |
| `research-multirow` | off | Research-only four-row band elimination ([#715](docs/research/multirow-reuse.md)), selected per thread; single-row stays the default even when enabled. |

## How Zeebra relates to existing systems

Gröbner basis computation already has excellent implementations: **Singular**, **Macaulay2** and
**Magma** are computer algebra systems, **msolve** is a C library and tool, and **Groebner.jl** is a
Julia package. In Rust, **arkworks** covers field and curve arithmetic but not system solving.
Zeebra fills the gap between them:

- **A library you link, under a permissive licence.** Singular, msolve and Groebner.jl are GPL;
  Magma is commercial. Zeebra is MIT.
- **The coefficient fields are the cryptographic ones.** Singular and msolve cap prime
  characteristic below 2^31. Zeebra runs F4, FGLM and solving over 64-bit primes, BN254 and
  BLS12-381 scalar fields, and binary and extension fields.
- **Resource behaviour is part of the contract.** Budgets on matrix entries, bytes and degree
  produce a typed error instead of exhausting the machine.
- **Correctness is checked, not asserted.** The solving pipeline is differentially tested against
  Singular, and a shared corpus of standard families is checked for ideal equivalence before any
  comparison is timed. Cross-engine results are on the
  [competitive board](research/competitive/COMPETITIVE.md).

## Assurance

- **Memory-safe Rust.** `unsafe` is confined to two sites: a row iterator over contiguous matrix
  storage (`src/linalg/matrix/iterating.rs`) and the carry-less multiply intrinsic for binary
  fields (`src/fields/binary_field.rs`).
- **Small supply chain.** No C dependencies, no FFI and no linked algebra system; external engines
  are driven only as supervised subprocesses.
- **Bounded handling of untrusted input.** R1CS import enforces explicit `ImportLimits` on size,
  wires and constraints, and checks assignments independently.
- **Results are verified.** Solutions are checked against the input system, the solving pipeline is
  differentially tested against Singular, and every documentation example runs in CI.
- **Measurements carry provenance.** A CI lint rejects any published timing or memory figure that
  does not name the commit it came from.

## How it is built

Zeebra is developed by several AI coding agents working concurrently, coordinated through the
GitHub issue tracker rather than a central scheduler. An agent claims an issue with a structured,
leased marker; concurrent claims resolve deterministically to the earliest one; a lost race is
conceded without touching the winner's state; and an expired lease makes the work reclaimable.
Every read distinguishes *empty* from *failed*, so an unauthenticated or rate-limited API call
can never look like an empty work queue. The protocol is in [`CLAUDE.md`](CLAUDE.md) and is
implemented and unit-tested in [`scripts/agent/zb-claim.sh`](scripts/agent/zb-claim.sh).

## Documentation

- [`docs/guide/`](docs/guide) — user guides for each area above
- [`docs/guide/status.md`](docs/guide/status.md) — what is implemented
- [`docs/guide/development.md`](docs/guide/development.md) — building, testing and CI
- [`docs/guide/benchmarking.md`](docs/guide/benchmarking.md) — benchmarks, instrumented examples,
  and the rules for publishing a measurement
- [`docs/guide/external-engines.md`](docs/guide/external-engines.md) — comparisons with Singular,
  msolve, Groebner.jl and other engines
- [`docs/research/`](docs/research) and [`research/`](research) — design studies, measurements and
  their reproduction instructions
- [`docs/`](docs) — milestone plans and integration reports
- [`CHANGELOG.md`](CHANGELOG.md) — release notes, including breaking changes
- [`CLAUDE.md`](CLAUDE.md) — repository conventions, including how coding agents claim work

Licensed under the [MIT licence](LICENSE-MIT).
