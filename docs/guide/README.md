# Zeebra guides

User guides to Zeebra's public API, one per area. Each guide explains what a module does, what it
costs, and where its limits are, with examples. Every Rust example in these files is compiled and
run by `cargo test --doc`, so the code shown matches the current API.

New to Zeebra? Start with [finite fields](finite-fields.md), then
[solving polynomial systems](solving-systems.md). Together they cover what the root
[README](../../README.md) quickstart does, in more depth.

## Arithmetic

| Guide | Covers |
|---|---|
| [Finite fields](finite-fields.md) | Prime fields from 31 to 255 bits, binary and extension fields, and what their arithmetic costs |
| [Polynomials](polynomials.md) | Multivariate arithmetic, GCD and squarefree decomposition, composition, univariate factorization, permutation polynomials |
| [Number-theoretic transform](ntt.md) | The NTT and the univariate operations built on it: multiplication, division, evaluation, interpolation, root finding |
| [Linear algebra](linear-algebra.md) | Dense and sparse matrices over a finite field, and the echelon backends F4 selects between |
| [Integers and factoring](number-theory.md) | Integer roots, perfect powers, Lenstra's elliptic curve method |
| [Error-correcting codes](reed-solomon.md) | Reed–Solomon encoding, erasure recovery, and a decoder that verifies its own correction |

## Gröbner bases and solving

| Guide | Covers |
|---|---|
| [Gröbner bases](grobner-bases.md) | Buchberger's algorithm, monomial orders, reduction against a given basis, zero-dimensional classification, FGLM order conversion |
| [F4 and Hilbert functions](f4.md) | Faugère's F4, its resource budgets, the opt-in signature F4, and the Hilbert functions that predict its cost |
| [Solving polynomial systems](solving-systems.md) | Zero-dimensional solving end to end: routes, resultants, solution verification, and how the solver chooses |
| [F4 matrix files](f4-matrix-files.md) | Capturing an F4 matrix once and replaying its elimination offline |

## Cryptographic inputs

| Guide | Covers |
|---|---|
| [Checked R1CS import](r1cs.md) | Importing R1CS constraint systems under explicit limits, checking assignments, and expanding constraints into polynomials |

## Working on Zeebra

| Guide | Covers |
|---|---|
| [Building, testing and CI](development.md) | Toolchain, test suites, what CI enforces, and what to run before opening a PR |
| [Benchmarking and measurement](benchmarking.md) | Benchmark suites, instrumented examples, and the rules for publishing a measurement |
| [External engines](external-engines.md) | Differential testing against Singular, and driving msolve, Groebner.jl and other engines as comparands |
| [Status](status.md) | A running record of what Zeebra implements |
