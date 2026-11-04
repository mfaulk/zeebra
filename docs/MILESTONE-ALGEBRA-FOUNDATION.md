# Milestone: Algebra Foundation and Performance

Status: complete, in review. Baseline commit `f56e5de`, 491 tests passing; 537 at the close of the milestone.

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
  unreachable (section 9.3). *Resolved in M20-A: the order moved to `KnownOrder` as little-endian
  limbs. See `docs/MILESTONE-LARGE-PRIME-FIELDS.md`.*
- **`ExtensionFieldElement` and `BinaryFieldElement` are crate-private** with no external users.
- Seven tests remain `#[ignore]`d. Three are real but slow — two large integer factorizations and
  the comparison against the naive reference engine — and pass under
  `cargo test --release -- --ignored <name>`. The other four are `unimplemented!()` placeholders
  for statistical distribution checks and a rare division branch, and panic if run.

## 2. Confirmed correctness defects

All seven were reproduced before any fix. Each gets a regression test. C1 through C6 were found
in the opening review; C7 was found in review of this milestone's own changes.

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

### C7 — Deserialization bypasses the representation invariant

Found in review of this milestone, after C6 had been fixed. Every field type derives `Deserialize`
over its private representation, which makes deserialization the one construction path that
reaches a field element without passing a constructor, and the derived impl trusts its input.

This already broke `PartialEq` and `Hash`, which are derived over the representation, so an
unreduced value compared unequal to the element it denotes. C6 turned it into an arithmetic defect
as well, because conditional reduction assumes its operands are already reduced:

- `sub` returns an unreduced input unchanged — `9 - 0` over GF(7) gave 9.
- `add` subtracts P at most once, so it is wrong at or above 2P — `26 + 0` over GF(13) gave 13.

The remainder-based arithmetic C6 replaced happened to normalize such inputs, so this is a
regression that C6 introduced and that blocks the optimization until the invariant holds.

`BinaryFieldElement` shares the defect, and its stated bound was also wrong: `new` asserted
`coefficients < P`, but the elements of GF(2^m) are the polynomials of degree below m and P is
monic of degree m, so `[2^m, P)` was admitted while denoting no element. No arithmetic can produce
such a pattern; only `new` and deserialization could inject one.

## 3. Performance bottlenecks from inspection

Ordered by expected impact on Gröbner workloads. Section 7 reports measurements.

| # | Bottleneck | Evidence | Outcome |
|---|---|---|---|
| P1 | 128-bit division in every field add, sub, and mul | C6; `prime_field_64.rs` | Fixed for add and sub (3.9x–105x). Multiply still divides: §9.3 |
| P2 | Inverse by Fermat — `log2(q)` modmuls per call | `finite_field.rs` default | Not addressed. Call count reduced instead, in pivot normalization (P3), backward elimination, and reducer construction |
| P3 | Repeated inverse in pivot normalization | C5 | Fixed; cumulatively 4.0x–10.8x on dense elimination |
| P4 | `leading_term` is `O(terms)`, called once per reduction step | `max_by` over the whole map | Fixed in `normal_form` via precomputed sorted terms |
| P9 | A modular inverse per reduction step, to divide by the reducer's leading coefficient | Found in review; `normal_form` inner loop | Fixed; inverted once per reducer, skipped entirely when monic. 1.9x–2.5x on Gröbner |
| P5 | Each reduction step allocates: `SparseMultiPoly::from(term)`, `&q * divisor`, a fresh map | `div_rem`, `multi_div_rem` | Fixed in `normal_form` via a reused scratch buffer |
| P6 | Buchberger rescans **all** basis pairs every outer iteration | `buchberger.rs` loop | Fixed; incremental pair queue |
| P7 | No pair-elimination criteria, so every S-polynomial is reduced | `buchberger.rs` | Product criterion added, eliminating 20%–58% of pairs. Chain criterion deferred |
| P8 | Addition and subtraction build an intermediate `Vec` then rebuild the map | `sparse_..._arithmetic.rs` | **Measured, left alone.** §7.3 |

P6 and P7 dominate asymptotically; P1 through P5 dominate the constant factor inside reduction.

P8 is the one item measurement argued against. Sparse add and multiply are dominated by hashing
and map growth rather than by the intermediate `Vec`, so making field add 4x faster moved them
only 5%–10%; removing the intermediate would be a speculative rewrite of a path the data does not
implicate. It is recorded here rather than attempted.

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

Criterion, `cargo bench`, release mode. Each benchmark reports wall-clock time. Algorithmic
counters for Gröbner computation — pairs considered, pairs eliminated, reductions, zero
reductions, elements added, maximum pair degree, maximum terms — come from
`buchberger_with_statistics` and are printed by `cargo run --release --example grobner_statistics`,
so improvements can be attributed rather than guessed. They live in an example rather than in the
benchmark because they are counts, not timings, and do not need Criterion's sampling.

Machine, toolchain, and configuration are recorded alongside results in section 7. Measurements
from different machines are not compared.

**Field arithmetic** — multiply, add, subtract, invert over GF(2^31 - 1), the largest 64-bit
prime, and a 68-bit prime in `u128`. Each operation is measured twice. The accumulating form
(`acc += x op y`) is a dependency chain and so reports latency, but every sample also includes one
addition, so it measures a fused operation rather than the named one. The `isolated/` form
discards each result through `black_box`, measuring the operation alone at the cost of a barrier,
and runs independent iterations so it reports throughput. Neither subsumes the other; figures are
only ever compared within a form.

**Sparse polynomials** — addition, multiplication, multiplication by a monomial, and normal form
against a set of reducers, at several term counts and variable counts. Inputs carry exactly the
labelled number of distinct monomials: sampling monomials and letting duplicates merge made the
realised count a function of the arity, so the sizes were neither accurate nor comparable across
arities (§7.3). `normal_form` and `multi_div_rem` are both measured, on the same input in the same
run, so their comparison needs no cross-run arithmetic.

**Linear algebra** — dense Gaussian elimination and Gauss–Jordan at several sizes over a 31-bit
and a 64-bit field.

**Gröbner bases** — `cyclic-n` and `katsura-n` from the standard benchmark families, deterministic
seeded random systems, and planted-solution systems where the answer is known. Instances are
chosen to run in seconds, not minutes; the point is a reliable baseline, not a record.

System generators live in `grobner::benchmark_systems` rather than in `benches/`, so that
`cargo test` compiles and checks them. The planted family is why this matters: while it lived in
the benchmark it emitted a fully linear system despite a comment describing nonlinear equations,
and nothing could catch the discrepancy because the file was never built by the test suite.

Because `N` is a const generic, each instance size needs its own instantiation. A macro generates
them.

## 7. Measurements

Machine: AMD Ryzen Threadripper PRO 5995WX, 64 cores. `rustc 1.97.0`, release profile, Criterion
with a 1 s warm-up and 2 s measurement window. Figures are the median of the reported interval.
Measurements from other machines are not comparable.

"Before" is the state at the start of this milestone; "after" is the final state of the branch.
Run-to-run variance on this machine is about +/-10%, so a change below that is recorded as no
change rather than claimed.

### 7.1 Field arithmetic

Per operation, from a 256-operand loop. `p31` is 2^31 - 1, `p64` the largest 64-bit prime, `p68`
a 68-bit prime in the `u128` type.

The baseline was measured only with an accumulating loop (`acc += x op y`), so every sample
included one addition. "After, composite" uses that same harness and is therefore the comparable
column; "after, isolated" is a new microbenchmark that discards each result through `black_box`
and so measures the named operation alone.

| op | p31 before | p31 composite | p31 isolated | p64 before | p64 composite | p64 isolated | p68 before | p68 composite | p68 isolated |
|---|---|---|---|---|---|---|---|---|---|
| add | 3.8 ns | **1.01 ns** | 0.77 ns | 3.6 ns | **0.96 ns** | 0.85 ns | 186 ns | **2.12 ns** | 1.31 ns |
| sub | 4.5 ns | **0.96 ns** | 0.76 ns | 4.5 ns | **0.95 ns** | 0.82 ns | 177 ns | **1.77 ns** | 1.20 ns |
| mul | 3.6 ns | 2.44 ns | 2.12 ns | 4.5 ns | 2.84 ns | 2.96 ns | 251 ns | 183 ns | 174 ns |
| inverse | 329 ns | 336 ns | 342 ns | 746 ns | 843 ns | 894 ns | 21.5 us | 22.7 us | 23.8 us |

Addition and subtraction are **3.8x to 4.7x** faster on the 64-bit fields and **88x to 100x** on
the 128-bit one, by replacing a 128-bit division with a conditional subtraction (C6). The 128-bit
field is the large win because it previously routed every operation through `U256`, a software
bignum, and then performed a full `U256 % U256` long division.

Two rows must not be read as improvements:

- **`mul` is unchanged.** No multiply implementation was modified. Its apparent gain in the
  composite column is the faster accumulating addition, which is precisely why the isolated
  variant was added — and the isolated p64 figure (2.96 ns) is slightly *above* the composite one,
  because `black_box` imposes its own barrier.
- **`inverse` is unchanged.** It is Fermat's `a^(q-2)`, built entirely from multiplications, which
  were not touched. Across five runs p64 measured 789, 790, 817, 754 and 843 ns against a 746 ns
  baseline. The spread covers the difference, so this is noise — neither a regression nor a gain.

`PrimeFieldElement128::mul` remains a bottleneck at 174 ns, roughly **59x** the 64-bit multiply,
because it still reduces through `U256` long division. Montgomery or Barrett arithmetic would fix
it but changes the element representation; see section 9.3.

### 7.2 Linear algebra

Dense Gauss–Jordan elimination and matrix inversion, n x n. Two changes contribute: one modular
inverse per pivot instead of per entry (C5), and not dividing by a backward-elimination pivot that
is already one.

| | n=8 | n=16 | n=32 | n=64 |
|---|---|---|---|---|
| Gauss–Jordan p31, before | 24.0 us | 103 us | 507 us | 2.81 ms |
| Gauss–Jordan p31, after | 4.63 us | 18.4 us | 94.3 us | **703 us** |
| speedup | 5.18x | 5.60x | 5.38x | **4.00x** |
| Gauss–Jordan p64, before | 49.6 us | 206 us | 937 us | 4.50 ms |
| Gauss–Jordan p64, after | 9.43 us | 26.2 us | 111 us | **724 us** |
| speedup | 5.26x | 7.87x | 8.44x | **6.21x** |
| inverse p31, before | 49.7 us | 219 us | 1.12 ms | 6.28 ms |
| inverse p31, after | 7.34 us | 33.0 us | 196 us | **1.49 ms** |
| speedup | 6.77x | 6.63x | 5.72x | **4.23x** |
| inverse p64, before | 102 us | 429 us | 1.97 ms | 9.82 ms |
| inverse p64, after | 11.7 us | 39.6 us | 215 us | **1.51 ms** |
| speedup | 8.70x | 10.8x | 9.14x | **6.51x** |

Inversion gains more than Gauss–Jordan at the same n because it eliminates on an n x 2n augmented
matrix, giving each pivot twice the columns to amortise over.

**The 31-bit and 64-bit fields now measure almost the same** — 703 us against 724 us at n = 64,
where the baseline had the 64-bit field nearly twice as slow. Inversion was the whole of that
difference, and it is now out of the inner loops. This is the clearest evidence that the
bottleneck the milestone identified is actually gone, rather than merely reduced.

The original C5 prediction was 3x at n = 64 over p64, from 4096 inverses at 746 ns accounting for
3.06 ms of the 4.50 ms measured. The realised figure is 6.21x — larger than predicted, because
the estimate only counted the forward pass. Backward elimination was performing a further
n(n-1)/2 inverses, 2016 at n = 64, none of which the baseline analysis had noticed.

### 7.3 Sparse polynomials

**The input generator was wrong, so the baseline table here is not comparable.** Monomials were
sampled independently and duplicates merged, so the realised term count depended on the arity:
with N = 3 and exponents bounded by 4 there are only 5^3 = 125 monomials, so the "256 terms" input
actually held 116 terms and the "64" input held 52. Comparing arities at a fixed label compared
116 terms against 254 against 256. The generator now draws until the target number of *distinct*
monomials is reached, raising the exponent bound per arity where needed (N = 3 uses 6, since
7^3 = 343 > 256).

Current figures at 6 variables, where the generator was close to correct already:

| op | 16 terms | 64 terms | 256 terms |
|---|---|---|---|
| add | 2.57 us | 9.99 us | 39.7 us |
| mul | 20.3 us | 323 us | 6.94 ms |
| mul by term | 1.52 us | 5.46 us | 20.6 us |

The before/after for these operations was **5% to 10%**, measured with the old generator on
identical inputs on both sides, so that comparison remains valid even though the absolute numbers
have moved. Its conclusion is unchanged: these operations are dominated by hashing and map growth,
not by field arithmetic, which is why making add and sub four times faster barely showed, and why
P8 was measured and declined.

Reduction is where the milestone's gain is. `normal_form` and `multi_div_rem` are benchmarked on
the same dividend in the same run, 48 terms against 2, 4 and 8 reducers:

| variables | reducers | `multi_div_rem` | `normal_form` | speedup |
|---|---|---|---|---|
| 3 | 2 | 773 us | 12.8 us | 60x |
| 3 | 4 | 846 us | 14.2 us | 60x |
| 3 | 8 | 1.40 ms | 25.1 us | 56x |
| 6 | 2 | 325 us | 6.70 us | 49x |
| 6 | 4 | 620 us | 10.6 us | 58x |
| 6 | 8 | 1.16 ms | 15.1 us | **77x** |
| 10 | 2 | 368 us | 7.83 us | 47x |
| 10 | 4 | 419 us | 9.21 us | 46x |
| 10 | 8 | 657 us | 14.7 us | 45x |

The gap widens with the number of reducers, which is the signature of the defects involved:
`multi_div_rem` rescans for the leading term inside the divisor loop, so its cost is proportional
to the divisor count on every step.

It also widens with the size of the dividend, because two of the three costs are quadratic in the
number of reduction steps. Measured directly on the larger instance used to characterise the
baseline — a 128-term polynomial in 6 variables modulo 16 reducers, with both results asserted
equal in the same run:

| reducers | `multi_div_rem` | `normal_form` | speedup |
|---|---|---|---|
| 4 | 52.9 ms | 0.329 ms | 161x |
| 16 | 13.81 s | 49.9 ms | **277x** |

Four costs were removed. Two were visible by inspection — the `leading_term` rescan per divisor
(P4) and accumulating the remainder with `r += SparseMultiPoly::from(term)`, which rebuilt the
whole remainder map per insertion (P5). The third was not: `quotients[i] += ...` rebuilt each
quotient's map on every step, worth about 10x on its own. `normal_form` returns only the
remainder, so it does not pay for quotient bookkeeping that Gröbner reduction never reads. The
fourth, P9, was found in review: a modular inverse per step to divide by the reducer's leading
coefficient, now taken once per reducer and skipped entirely for monic ones.

### 7.4 Gröbner bases

| system | order | before | after | speedup |
|---|---|---|---|---|
| cyclic-3 | lex | 176 us | 18.4 us | 9.6x |
| cyclic-3 | grlex | 171 us | 18.8 us | 9.1x |
| cyclic-3 | grevlex | 162 us | 18.7 us | 8.7x |
| cyclic-4 | grevlex | did not finish in 300 s | **143 us** | newly tractable |
| katsura-3 | lex | 173.9 s | 39.4 us | **4,400,000x** |
| katsura-3 | grlex | 149.5 ms | 30.7 us | 4870x |
| katsura-3 | grevlex | 146.1 ms | 31.2 us | 4683x |
| katsura-4 | lex | did not finish in 300 s | 746 us | newly tractable |
| katsura-4 | grlex | did not finish in 300 s | 210 us | newly tractable |
| katsura-4 | grevlex | did not finish in 300 s | **126 us** | newly tractable |
| katsura-5 | grlex | not attempted | 2.19 ms | newly tractable |
| katsura-5 | grevlex | not attempted | **1.03 ms** | newly tractable |

The katsura-3 lex figure is the headline but also the least representative: that instance was
pathological for the old engine, which rescanned every basis pair each outer iteration while lex
drove the basis large. The **~4700x on the graded orders** is the more honest summary. Both were
verified to produce the same basis as the reference implementation.

These factors measure how inefficient the former implementation was. They are not evidence that
Zeebra is competitive with established high-performance Gröbner engines, and should not be read
that way.

**grevlex now beats grlex**, as theory says it should. Before the C1 fix they were identical
because grevlex was executing grlex. After: katsura-4 126 us against 210 us, katsura-5 1.03 ms
against 2.19 ms with a 13-element basis against 16.

Counters from `cargo run --release --example grobner_statistics`, which attribute the change
rather than infer it from wall-clock:

| system | order | pairs | eliminated | elim % | reduced | zero reductions | basis |
|---|---|---|---|---|---|---|---|
| cyclic-3 | grevlex | 10 | 4 | 40.0% | 6 | 4 | 3 |
| cyclic-4 | grevlex | 45 | 10 | 22.2% | 35 | 29 | 7 |
| katsura-3 | grevlex | 15 | 8 | 53.3% | 7 | 4 | 4 |
| katsura-4 | grlex | 55 | 28 | 50.9% | 27 | 20 | 8 |
| katsura-4 | grevlex | 36 | 21 | 58.3% | 15 | 10 | 7 |
| katsura-5 | lex | 2415 | 625 | 25.9% | 1790 | 1725 | 5 |
| katsura-5 | grlex | 190 | 90 | 47.4% | 100 | 85 | 16 |
| katsura-5 | grevlex | 105 | 56 | 53.3% | 49 | 39 | 13 |

Buchberger's first criterion eliminates **20% to 58%** of pairs without reducing them. The pair
counts also confirm C1 independently of timing: grevlex considers 36 pairs on katsura-4 where
grlex considers 55, and 105 against 190 on katsura-5 — distinct algorithmic behaviour, not merely
distinct timings.

**The clearest remaining waste is visible here.** Of 49 reductions on katsura-5 grevlex, 39 reduce
to zero — 80%. On katsura-5 lex it is 1725 of 1790, or 96%. Every one of those is an
S-polynomial reduced at full cost to learn nothing. This is exactly what the chain criterion
suppresses and what F4 amortises by reducing many S-polynomials in one matrix; see section 9.1.

The planted-solution family is also benchmarked, at 6 variables: lex 55.8 us, grlex 39.4 us,
grevlex 40.2 us. Its original formulation emitted only `x_i - a_i`, a fully linear system that is
already a Gröbner basis under every order — all three orders reported an identical 12.4 us, which
is the signature of measuring nothing. It now plants the solution in coupled quadratics.

## 8. Acceptance criteria

All met.

| Criterion | Status |
|---|---|
| C1–C7 fixed, each with a regression test that fails without the fix | Met. C7 was found reviewing this milestone's own C6 change |
| All three monomial orders correct through the public API, with order axioms tested | Met — totality, antisymmetry, transitivity, multiplicativity, 1 minimal, across all three orders |
| `div_rem` and `normal_form` satisfy their contracts as property tests | Met |
| Buchberger uses incremental pair processing and at least the product criterion | Met — pair queue ordered by degree, product criterion. Chain criterion deferred |
| Optimized and reference Buchberger agree over the benchmark systems and all three orders | Met — the slowest cases are `#[ignore]`d and run with `cargo test --release -- --ignored test_optimized_agrees_with_reference_on_slow_systems` |
| A deterministic basis ordering, tested across repeated runs | Met — `HashSet` removed from both basis-reduction paths |
| Reproducible benchmarks for field arithmetic, sparse polynomials, linear algebra, and Gröbner bases, with recorded baselines | Met — four benchmarks plus the statistics example |
| Every performance claim backed by a before/after measurement | Met. Unchanged figures are labelled as such in §7.1, P8 is documented as measured-and-declined in §3, and §7.3 states where the baseline is not comparable |
| The full suite, `cargo fmt --check`, and `clippy -D warnings` all pass | Met |

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

*Superseded by `docs/MILESTONE-LARGE-PRIME-FIELDS.md`, which audited this and took a different
path: rather than widening `order()`, M20-A moved it out of `FiniteField` entirely, because the
algebraic core turned out never to call it. The analysis below is what was believed at the time.*

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
