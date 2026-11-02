# Milestone: Algebra Foundation and Performance

Status: in progress. Baseline commit `f56e5de`, 491 tests passing.

This milestone solidifies the correctness of Zeebra's computational algebra core, establishes
reproducible benchmarks, removes measured bottlenecks, and replaces the naive Buchberger strategy
with an incremental one. It deliberately stops short of F4, which the closing section specifies
as the next milestone.

Future workloads guide the priorities here — polynomial systems in tens of variables, sparse
low-degree input with heavy intermediate growth, prime fields from 31 to 255 bits, and
zero-dimensional systems where one solution matters more than the whole variety — but nothing in
this milestone is specific to any application.

## 1. Current capabilities

| Area | Capability | Algorithm |
|---|---|---|
| Integers | arbitrary-precision arithmetic | schoolbook multiply, Knuth algorithm D division |
| Integers | factorization, primality | trial division then Pollard's rho; Miller–Rabin |
| Fields | GF(p) at 64 and 128 bits | direct mod-p arithmetic |
| Fields | GF(2^m), GF(p^n) | carry-less / schoolbook multiply with polynomial reduction |
| Fields | inverse, primitive element, root of unity | Fermat's little theorem; randomized search (HAC 4.80) |
| Univariate | gcd, division, interpolation | Euclid; long division; Lagrange |
| Univariate | root finding, factorization, irreducibility | `gcd(f, x^(q^d) - x)` + Cantor–Zassenhaus; Rabin |
| Multivariate | sparse arithmetic, division | `HashMap<Monomial<N>, F>`; standard multivariate division |
| Linear algebra | LU, row reduction, rank, inverse, determinant | Crout; Gaussian and Gauss–Jordan elimination |
| FFT | forward and inverse over a finite field | recursive radix-2 Cooley–Tukey |
| Gröbner | reduced basis, system solving | Buchberger; lex basis plus triangular back-substitution |

### Known limitations carried into this milestone

- **Nothing is asymptotically fast.** Multiplication is schoolbook; Buchberger has no pair
  elimination; inversion uses Fermat rather than extended Euclid.
- **`N` is a const generic.** The number of variables is fixed at compile time, so variable counts
  cannot vary at runtime. This blocks benchmark families parameterized by n without macro
  instantiation, and is a genuine constraint on F4 (section 9.1).
- **`FiniteField::order() -> u128`** caps field order at 128 bits, so 254–255-bit fields are
  unreachable (section 9.3).
- **`ExtensionFieldElement` and `BinaryFieldElement` are crate-private** with no external users.
- Six tests remain `#[ignore]`d, each for a stated reason, none a placeholder.

## 2. Confirmed correctness defects

All six were reproduced before any fix. Each gets a regression test.

### C1 — `MonomialOrder::cmp` dispatches grevlex to grlex

```rust
MonomialOrder::GradedReverseLexicographic => grlex(a, b),   // should be grevlex
```

`grevlex` is implemented and correct but never called by `cmp`. Since `cmp` is the only path used
by `leading_term`, `leading_monomial`, `Hash`, and `Display`, **grevlex has silently behaved as
grlex throughout the public API** — including in every Gröbner basis computed with it.

Compounding this, `MonomialOrder::max` *does* dispatch to `grevlex`, so the two functions
disagree with each other. `max` has no callers outside tests, which is why nothing failed.

Severity: high. grevlex is the order of choice for Gröbner computation, and is the intended input
to FGLM conversion.

### C2 — `SparseMultiPoly::div_rem` violates its own contract

It returns as soon as the leading term is not divisible, leaving lower reducible terms in the
remainder. Division by `g` must produce `f = qg + r` where **no monomial of `r` is divisible by
`LT(g)`**.

```text
div_rem(x^2 + y, y)  returns  q = 0, r = x^2 + y     // r still contains y
correct                        q = 1, r = x^2
```

`f = qg + r` does hold, so the bug is confined to the normal-form property. `multi_div_rem`
handles the same input correctly, and Buchberger uses `multi_div_rem`, so computed bases are
unaffected. `div_rem` is public API.

### C3 — A zero generator panics Buchberger

`minimize_grobner_basis` scales each element by `leading_coefficient().inverse()`, and the zero
polynomial's leading coefficient is zero, so `inverse()` asserts. Both `buchberger(&[zero])` and
`buchberger(&[x + y, zero])` panic. A zero generator is legitimate input: it contributes nothing
to the ideal.

### C4 — The reduced basis is returned in non-deterministic order

`minimize_grobner_basis` and `reduce_grobner_basis` accumulate into `HashSet`, so iteration order
varies between runs of the same input:

```text
run 1: ["x_1^2 + x_1*x_2 + x_2^2", "x_2^3 + 12", "x_0 + x_1 + x_2"]
run 2: ["x_1^2 + x_1*x_2 + x_2^2", "x_0 + x_1 + x_2", "x_2^3 + 12"]
```

This defeats reproducibility, forces tests to compare sets rather than sequences, and would make
benchmark comparison unreliable. A reduced Gröbner basis is unique as a *set* for a given ideal
and order, so sorting by leading monomial yields a canonical sequence. The source already carries
a TODO asking for this.

### C5 — Pivot normalization recomputes a modular inverse per entry

```rust
let pivot = A[[cursor.row, cursor.column]];
for j in cursor.column..num_columns {
    A[[cursor.row, j]] /= pivot;          // each division recomputes pivot.inverse()
}
```

`Div` for a field element is `self * rhs.inverse()`, and `inverse()` is `pow(order - 2)` — a full
modular exponentiation of roughly `log2(q)` modular multiplications. Normalizing an n-column row
therefore costs about `60n` modular multiplications at 64 bits instead of `60 + n`.

The same pattern appears in `crout.rs`.

### C6 — Field addition and subtraction use 128-bit division

```rust
fn add(..) { let sum = self.value as u128 + rhs.value as u128; (sum % P as u128) as u64 }
fn sub(..) { let d = self.value as i128 - rhs.value as i128; d.wrapping_rem_euclid(P as i128) }
```

Both reduce with a 128-bit division where a single conditional branch suffices, since the inputs
are already reduced. Hardware 128/64 division is an order of magnitude slower than a compare and
subtract. `Mul` necessarily needs a wide reduction, but add and sub do not.

## 3. Performance bottlenecks from inspection

Ordered by expected impact on Gröbner workloads. Section 7 reports measurements.

| # | Bottleneck | Evidence |
|---|---|---|
| P1 | 128-bit division in every field add, sub, and mul | C6; `prime_field_64.rs` |
| P2 | Inverse by Fermat — `log2(q)` modmuls per call | `finite_field.rs` default |
| P3 | Repeated inverse in pivot normalization | C5 |
| P4 | `leading_term` is `O(terms)`, called once per reduction step | `max_by` over the whole map |
| P5 | Each reduction step allocates: `SparseMultiPoly::from(term)`, `&q * divisor`, a fresh map | `div_rem`, `multi_div_rem` |
| P6 | Buchberger rescans **all** basis pairs every outer iteration | `buchberger.rs` loop |
| P7 | No pair-elimination criteria, so every S-polynomial is reduced | `buchberger.rs` |
| P8 | Addition and subtraction build an intermediate `Vec` then rebuild the map | `sparse_..._arithmetic.rs` |

P6 and P7 dominate asymptotically; P1 through P5 dominate the constant factor inside reduction.

## 4. Planned tasks

Ordered by dependency. Each lands as its own commit.

1. **Benchmarks and baseline** (section 6). Must precede optimization so claims are measured.
2. **C1** grevlex dispatch, with order-axiom tests across all three orders.
3. **C2** `div_rem` normal form, with the contract as a property test.
4. **C3, C4** Buchberger robustness and determinism.
5. **Normal form** — a remainder-only `normal_form` avoiding quotient bookkeeping, plus in-place
   reduction that reuses buffers.
6. **Incremental Buchberger** — pair queue, normal selection strategy, product criterion,
   interreduction; reference implementation retained as a test oracle.
7. **C5, C6** — one inverse per pivot; conditional add and sub. Measured before and after.
8. Re-verify, re-benchmark, document.

## 5. Mathematical invariants and correctness criteria

Properties checked by tests rather than compared against the implementation's own output.

**Monomial orders.** For each of lex, grlex, grevlex: totality; antisymmetry; transitivity;
multiplicativity (`a < b` implies `ac < bc`); a well-ordering on monomials of bounded degree; and
`1` minimal. Agreement between `cmp` and `max`.

**Division and normal form.** `f = sum(q_i * g_i) + r`, and no monomial of `r` is divisible by any
`LT(g_i)`. Normal form agrees with the remainder from `multi_div_rem`. Reduction terminates.

**Gröbner bases.** For every system and order:
1. every input generator reduces to zero modulo the basis;
2. every S-polynomial of basis pairs reduces to zero (Buchberger's criterion);
3. the basis is monic, duplicate-free, and reduced — no monomial of any element lies in
   `<LT(G \ {p})>`;
4. the ideal is unchanged: each basis element reduces to zero modulo the original generators under
   a basis of the input ideal;
5. optimized and reference implementations agree as sets, for all three orders;
6. small systems agree with independently obtained reference results.

**Fields.** Field axioms by property test. Optimized arithmetic agrees with the previous
implementation exhaustively near zero, near `P-1`, and on random input. Inverse satisfies
`a * a^-1 = 1`.

**Linear algebra.** `PA = LU`; RREF is idempotent and in reduced row echelon form;
`A * A^-1 = I`; `rank(A) = rank(A^T)`; `det(A) = 0` exactly when `A` is singular.

External cross-validation (SageMath, Singular, Groebner.jl) is used to *generate* expected values,
which are then committed as literals. No test requires external software at runtime, and CI stays
self-contained.

## 6. Benchmark methodology

Criterion, `cargo bench`, release mode. Each benchmark reports wall-clock time; Gröbner
benchmarks additionally report algorithmic counters (pairs processed, pairs eliminated, zero
reductions, maximum degree, basis size, terms generated) through an instrumentation struct, so
improvements can be attributed rather than guessed.

Machine, toolchain, and configuration are recorded alongside results in section 7. Measurements
from different machines are not compared.

**Field arithmetic** — multiply, add, subtract, invert over GF(2^31 - 1), the largest 64-bit
prime, and a 68-bit prime in `u128`.

**Sparse polynomials** — addition, multiplication, multiplication by a monomial, and normal form
against a set of reducers, at several term counts and variable counts.

**Linear algebra** — dense Gaussian elimination and Gauss–Jordan at several sizes over a 31-bit
and a 64-bit field.

**Gröbner bases** — `cyclic-n` and `katsura-n` from the standard benchmark families, deterministic
seeded random systems, and planted-solution systems where the answer is known. Instances are
chosen to run in seconds, not minutes; the point is a reliable baseline, not a record.

Because `N` is a const generic, each instance size needs its own instantiation. A macro generates
them.

## 7. Measurements

Machine: AMD Ryzen Threadripper PRO 5995WX, 64 cores. `rustc 1.97.0`, release profile, Criterion
with a 1 s warm-up and 2 s measurement window. Figures are the median of the reported interval.
Measurements from other machines are not comparable.

### 7.1 Field arithmetic — baseline

Per operation, from a 256-operand loop. `p31` is 2^31 - 1, `p64` the largest 64-bit prime, `p68`
a 68-bit prime in the `u128` type.

| op | p31 | p64 | p68 |
|---|---|---|---|
| mul | 3.6 ns | 4.5 ns | **251 ns** |
| add | 3.8 ns | 3.6 ns | **186 ns** |
| sub | 4.5 ns | 4.5 ns | **177 ns** |
| inverse | 329 ns | 746 ns | **21.5 us** |

Two findings. **Inverse costs 90x to 165x a multiply**, consistent with Fermat's `log2(q)` modular
multiplications — which is what makes the per-entry inverse in C5 so expensive. And the 128-bit
field is roughly **50x slower than the 64-bit one even for addition**, because
`PrimeFieldElement128` routes every operation through `U256`, a software bignum, and then performs
a full `U256 % U256` long division. Addition of two already-reduced values needs only a
conditional subtract.

### 7.2 Linear algebra — baseline

Dense Gauss–Jordan elimination, n x n.

| n | p31 | p64 |
|---|---|---|
| 8 | 24.0 us | 49.6 us |
| 16 | 103 us | 206 us |
| 32 | 507 us | 937 us |
| 64 | 2.81 ms | 4.50 ms |

At n = 64 over p64 there are 64 pivots x 64 entries = 4096 divisions, each recomputing an inverse
at 746 ns — about **3.06 ms of the 4.50 ms measured, or 68% of total runtime**, spent on inverses
that one per pivot would replace.

### 7.3 Sparse polynomials — baseline

Selected figures at 6 variables:

| op | 16 terms | 64 terms | 256 terms |
|---|---|---|---|
| add | 2.5 us | 9.6 us | 37.5 us |
| mul | 20.3 us | 318 us | 6.48 ms |
| mul by term | 1.4 us | 5.4 us | 20.1 us |

Normal form, 48-term dividend at 6 variables: 300 us at 2 reducers, 581 us at 4, **2.14 ms at 8**.

A larger instance was instrumented directly to characterise the growth. Reducing a 128-term
polynomial in 6 variables modulo 16 reducers took **1.35 s** across 4464 reduction steps, peaking
at 2512 terms — **303 us per step**, where a step touching 2512 terms should cost on the order of
10 us. Two quadratic behaviours account for it:

- `multi_div_rem` recomputes `p.leading_term(order)` **inside** the divisor loop, so a step with
  16 divisors performs 16 full O(terms) scans.
- The remainder is accumulated with `r += SparseMultiPoly::from(term)`, which rebuilds the whole
  remainder map on each of 3791 insertions — about 7 million map operations, O(steps^2).

### 7.4 Gröbner bases — baseline

| system | lex | grlex | grevlex | basis size |
|---|---|---|---|---|
| cyclic-3 | 176 us | 171 us | 162 us | 3 |
| katsura-3 | **173.9 s** | 149.5 ms | 146.1 ms | 3 / 4 / 4 |
| katsura-4 | did not complete in 300 s | | | |
| cyclic-4 | did not complete in 300 s | | | |

Two observations. Lex on katsura-3 is **1160x slower** than the graded orders, the classic lex
blowup amplified by a strategy that rescans every basis pair each round. And grlex and grevlex
produce identical timings and identical basis sizes — independent confirmation of C1, since
grevlex is in fact executing grlex.

The benchmark suite therefore ships only the instances the current engine can finish. katsura-4
and cyclic-4 are the targets for the improved engine.

## 8. Acceptance criteria

- C1–C6 fixed, each with a regression test that fails without the fix.
- All three monomial orders correct through the public API, with order axioms tested.
- `div_rem` and `normal_form` satisfy their contracts as property tests.
- Buchberger uses incremental pair processing and at least the product criterion.
- Optimized and reference Buchberger agree, as sets, over the benchmark systems and all three
  orders.
- A deterministic basis ordering, tested across repeated runs.
- Reproducible benchmarks for field arithmetic, sparse polynomials, linear algebra, and Gröbner
  bases, with recorded baselines.
- Every performance claim backed by a before/after measurement.
- The full suite, `cargo fmt --check`, and `clippy -D warnings` all pass.

## 9. Design for the next milestone

### 9.1 F4

F4 replaces one-pair-at-a-time reduction with batched linear algebra: select all pairs of the
lowest degree, build a Macaulay matrix whose rows are the S-polynomials and the reducers needed to
reduce them, row-reduce once, and read new basis elements off the nonzero rows.

The infrastructure this milestone builds is what F4 needs:

- The **pair queue** already groups pairs by degree, which is exactly F4's selection step.
- **Symbolic preprocessing** needs, for a set of monomials, the reducer whose leading monomial
  divides each — the same lookup the incremental reducer uses, so a shared monomial-to-reducer
  index serves both.
- **Matrix construction** needs a stable column order over the union of monomials appearing in the
  selected polynomials. A `BTreeMap<Monomial<N>, usize>` keyed by the monomial order gives
  deterministic columns directly, which is why deterministic ordering (C4) is a prerequisite
  rather than a nicety.

Requirements not yet met:

- **Sparse matrix storage.** Macaulay matrices are large and very sparse. Compressed sparse rows
  over field elements, with row operations expressed as sparse axpy, is the minimum. The existing
  dense `Matrix<T>` is unsuitable at F4 sizes and should not be forced into the role.
- **Sparse row reduction** that pivots on sparsity as well as position, to limit fill-in.
- **Runtime variable counts.** `N` as a const generic is the sharpest obstacle. F4 wants to
  construct polynomials whose variable count comes from the input system. Options, in increasing
  order of disruption: keep `N` and generate instantiations by macro; add a parallel
  runtime-length monomial type used only inside the F4 engine; or move `SparseMultiPoly` to a
  runtime variable count and accept the breaking change. The second is likely the right
  compromise, keeping the verified public type intact while giving the engine what it needs.

### 9.2 FGLM

FGLM converts a grevlex basis of a zero-dimensional ideal into a lex basis far more cheaply than
computing the lex basis directly. It needs:

- a **zero-dimensionality test** — the quotient ring is finite-dimensional exactly when, for each
  variable, some basis element has a leading monomial that is a pure power of it;
- a **monomial basis** of the quotient ring, obtained as the monomials not divisible by any
  leading monomial of the basis;
- **multiplication matrices** for each variable, acting on that basis — built by reducing
  `x_i * m` to normal form for each basis monomial `m`, which is the normal form this milestone
  makes efficient;
- **linear algebra over the quotient ring** to find the minimal polynomial of a generic element.

This connects directly to the existing solver. `grobner::solve` currently computes a lex basis via
Buchberger, which is the expensive route; with FGLM it would compute grevlex, convert, and feed
the lex basis to the back-substitution and root finding already in place. The solver's interface
need not change.

### 9.3 Larger prime fields

`FiniteField::order() -> u128` is the binding constraint: a 254-bit field cannot report its order.
The trait also assumes `Copy` elements, which suits small fields and fights larger ones.

A viable path, least disruptive first:

1. Return the order as a `BigUInt` instead of `u128`, or add `order_bits()` for the uses that only
   need a magnitude. Most internal uses — Fermat inversion, `x^(q^d)`, trace lengths — need the
   order as an exponent, so they need a big-integer exponent interface.
2. Keep `Copy` by implementing a fixed-width 256-bit element over `Ux64<4>`, which already exists.
3. Alternatively, adapt an established library (`ark-ff`, `blstrs`) behind the `FiniteField`
   trait. This is the pragmatic choice for the 254–255-bit curve-order fields, since Montgomery
   arithmetic there is already well optimized and independently tested.

An adapter is preferable to a reimplementation: the arithmetic is easy to get subtly wrong, and
the project's correctness emphasis is better served by delegating.

### 9.4 Solving APIs

Four distinct operations are currently conflated under `solve`:

| Operation | Cost | Current support |
|---|---|---|
| compute a Gröbner basis | dominant | `buchberger` |
| decide zero-dimensionality | cheap given a basis | none |
| find **one** solution | cheaper than all | not distinguished |
| enumerate all solutions | can be exponential | `solve` |

The anticipated workloads care most about the third, which is not separately available.
A future API should distinguish them, likely as `GroebnerBasis` with methods `is_zero_dimensional`,
`dimension`, `any_solution`, and `solutions`. Finding one solution can stop at the first root at
each level rather than iterating all of them — a small change to the existing back-substitution,
but one that needs the distinction to exist in the interface first.

## 10. Explicitly deferred

Out of scope for this milestone, recorded so the boundary is clear:

- F4, F5, and signature-based criteria beyond the product criterion.
- Sparse matrix storage and sparse row reduction.
- FGLM and order conversion.
- Fields above 128 bits.
- Montgomery or Barrett multiplication, unless the benchmarks in section 7 justify it. Add and sub
  are in scope; changing the *representation* is not.
- Karatsuba or FFT-based integer multiplication.
- Runtime variable counts and any change to `SparseMultiPoly`'s public shape.
- GPU, SIMD, parallelism, and distribution.
- Any cryptanalysis-specific functionality, including hash primitives and attack tooling.
