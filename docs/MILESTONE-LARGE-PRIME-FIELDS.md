# Milestone: Large Prime Fields and Cryptographic Algebra Readiness

**Status:** M20-0, M20-A, M20-B and M20-D landed. The milestone's primary demonstration passes
over both target fields: a planted zero-dimensional system goes through F4, the quotient algebra,
FGLM and `solve_one`, and the returned point is verified against the original system. Remaining:
M20-C's byte-accounted resource limits, and M20-E's benchmark corpus.
**Prerequisites:** M18 merged; M19 complete on `m19-field-arithmetic` but **not yet on `main`**
(`main` carries only the M19-0/M19-A merge). M20 branches from the merged M19.

## 1. What this milestone is actually blocked on

The objective is that the *existing* algorithms — `f4`, `buchberger`, `fglm_to_lex`,
`solve_one` — run over the BN254 and BLS12-381 scalar fields, with no wide-field fork of any
of them.

The audit's central finding changes the shape of the work:

> **The algebraic core does not use field cardinality at all.** Across
> `src/poly/multivariate/`, `src/linalg/`, `src/grobner/f4/`, `src/grobner/fglm/`,
> `src/grobner/buchberger.rs`, `src/grobner/pairs.rs` and `src/grobner/s_polynomial.rs`
> there is not one call to `F::order()` or `F::characteristic()`.

Every cardinality dependency outside `src/fields/` lives in four files:

| File | Use | Fate |
|---|---|---|
| `src/poly/univariate/roots.rs:54` | `pow_mod(&x, F::order(), f)` | must widen (M20-D) |
| `src/poly/univariate/factorize.rs:50,123,193,220,237` | `q`, `(q-1)/2`, `q.trailing_zeros()` | must widen (M20-D) |
| `src/grobner/solve.rs:105,219,421` | `F::order() <= MAX_FIELD_ORDER` before enumerating the field | stays small-field only |
| `src/grobner/differential/comparison.rs:213` | matches a Singular fixture's characteristic | stays small-field only |

`src/fft/` uses `F::root_of_unity`, which is cardinality-derived but is a test-only call site in
every instance (`fft/domain.rs:117`, `fft/evaluate.rs:96…204`, `fft/interpolate.rs:54,74`).

So M20 is not a 253-site bound migration. The blocker is narrower and sharper: **`FiniteField`
*requires* `fn order() -> u128`, so a 254-bit field cannot implement the trait at all.** Nothing
in F4 asks for the cardinality; the trait does, on F4's behalf.

### 1.1 The secondary blocker: the default `inverse`

```rust
// src/fields/finite_field.rs:183
fn inverse(&self) -> Self {
    let order = Self::order();
    self.pow(order - 2)
}
```

`inverse` is a provided method, so an adapter *can* override it — and must. Worth recording:
**no field in the crate overrides it today.** `PrimeFieldElement64`, `PrimeFieldElement128`,
`BinaryField` and `ExtensionField` all invert by exponentiation. That shows up in §4's baseline
and is an M19-shaped follow-up, not M20 work.

### 1.2 What `Ring` and `FiniteField` demand of an adapter

`Ring` (`src/rings/mod.rs`) requires `Copy + Zero + One + Eq + Display + Debug + Add + AddAssign
+ Mul + MulAssign + Arbitrary`. `FiniteField` adds `Hash + Serialize + DeserializeOwned +
Default + Div + DivAssign + Sub + SubAssign + Neg`, the four borrowed-RHS operator variants, and
`new(u64)`, `from_str`, `random`, `order`, `characteristic`.

Classified against a `Fp256<MontBackend<…>>` from `ark-ff` 0.6:

| Requirement | Satisfied by `ark-ff` `Fp` | Adapter cost |
|---|---|---|
| `Copy`, `Eq`, `Debug`, `Default`, `Hash` | yes | none |
| `Display` | yes, canonical decimal (verified: `-1` prints `21888…495616`) | none |
| `Add/Sub/Mul/Neg` + assign forms | yes | none |
| borrowed-RHS variants | partial | `impl_*_variants!` macros already in `src/util/` |
| `Zero`/`One` as **associated consts** | `ark-ff` has them as consts (`Fp::ZERO`, `Fp::ONE`) | none |
| `Serialize`/`DeserializeOwned` | `ark-serialize`, not serde | newtype impl over canonical LE bytes |
| `Arbitrary` (proptest) | no | newtype impl |
| `random<R: RngCore + CryptoRng>` | `UniformRand` over **rand 0.8** — same version zeebra uses | thin wrapper |
| `new(u64)`, `from_str` | `From<u64>`, `from_str` via `PrimeField` | thin wrapper |
| `order()`, `characteristic()` | 4 limbs, not `u128` | **the blocker** |

Only one of these is a design problem. The rest are a newtype with derives and two macro
invocations — which is why §3 proposes the smallest change that unblocks the one real conflict,
and leaves `Ring`'s `Arbitrary` bound alone (§3.4).

The right-hand columns record the `ark-ff` evaluation as it stood; §2 explains why the field was
implemented in-crate instead. The left-hand column is what matters either way — it is the list
`PrimeFieldElement256` had to satisfy, and `Display`, serde, `Arbitrary` and the borrowed-operand
variants were owed regardless of where the arithmetic came from.

## 2. Backend: implemented in-crate, with `ark-ff` as a test oracle

**Decided:** the 254/255-bit field is zeebra's own code. `ark-ff` is a **dev-dependency only**,
used as a differential oracle in the role Singular already plays for Gröbner bases. Nothing
third-party ships.

Two reasons, one standing and one measured. The standing one is that every other primitive in
this crate is hand-written — big integers, Montgomery prime fields, binary and extension fields,
integer factoring — and large-field arithmetic sits in the hot path of everything M20 and after
is built on, including representation changes a third-party trait would make awkward. The
measured one is §2.2: the gap to hand-written assembly is small enough that owning the code costs
little.

An external backend was also never dependency-only. It needs a local newtype plus `FiniteField`,
`KnownOrder`, `Arbitrary`, serde and the borrowed-operand macros regardless, so a good part of
the work was owed either way.

Measurement conditions throughout: AMD Ryzen Threadripper PRO 5995WX, `rustc 1.97.0`, `--release`
with the crate's `lto = "fat"` / `codegen-units = 1`, `-C target-cpu=native`.

### 2.1 Why `ark-ff` is the oracle, and not `ff`/`bls12_381`

`bls12_381::Scalar` (zkcrypto, `ff` 0.14) **does not implement `Hash`**, which `FiniteField`
requires and which `SparseMultiPoly` uses (`sparse_multivariate_polynomial.rs:256` hand-writes
`Hash` over its coefficients). `ark-ff`'s `Fp` does. `ff` 0.14 also pulls `rand_core` 0.9+
against zeebra's rand 0.8 / `rand_core` 0.6 — the version split §18 of the plan anticipated —
whereas `ark-std` 0.6 is on rand 0.8.8.

Those were the criteria for a *shipped* backend and they decided the comparison before the
decision changed. They still apply to an oracle: it must be instantiable over exactly these two
fields and comparable without an adaptation layer.

The oracle declares the two fields from their decimal moduli through `ark-ff`'s `MontConfig`
derive rather than depending on `ark-bn254` and `ark-bls12-381`, which pull `ark-ec` and the
whole curve stack unconditionally even under `--no-default-features --features scalar_field`
(111 packages against 76). Elliptic curves and pairings are out of scope, and a test oracle
should not drag them in.

`test_the_oracle_is_over_the_same_fields` asserts that `ark-ff` derived the same modulus limbs
this crate compiled in. Without it, agreement on arithmetic would only show that two
implementations agree over *some* field.

### 2.2 What the in-crate field costs against hand-written assembly

A prototype measured before committing to the decision, against `ark-ff` with its `asm` feature
on, in the loop shape `benches/field_arithmetic.rs` uses:

| BN254 `Fr`, ns/op | mul | add | sub |
|---|---:|---:|---:|
| `ark-ff`, hand-written asm | 17.25 | 2.18 | 2.61 |
| zeebra prototype | 20.96 | 5.74 | 4.92 |
| ratio | **1.22x** | 2.64x | 1.89x |

Two things were learned while tuning that the shipped code reflects:

- **Masking the conditional subtraction instead of branching made `add` slower** — 6.78 ns to
  8.80 ns. The branch predicts well enough and the mask lengthens the dependency chain. The
  comment in `montgomery_256::mul` records this so it is not re-tried.
- **The carry chain must be `carrying_add`, not two `overflowing_add`s joined by `||`.** That one
  change took `add` from 6.78 ns to 5.74 ns and `sub` from 7.41 to 4.92. `Ux64` already uses the
  carrying operations; the first draft did not.

### 2.3 The two hazards the plan called out, and what was done

§7.2 and §7.3 of the plan warn about Montgomery leakage in serialization and about biased
sampling. Implementing the field means both are this crate's problem rather than a backend's:

- **Serialization is the canonical residue.** `Serialize` writes `canonical_limbs()`, never the
  stored Montgomery value, so the encoding does not depend on an internal representation choice
  and round-trips against any other implementation of the field.
  `test_serialization_is_the_canonical_residue` pins it on a value — seven encodes as seven.
  Deserialization rejects any encoding at or above p rather than reducing it, matching the
  `reduced_residue` guard `PrimeFieldElement128` already applies; `from_limbs_reduced` is the
  separately named constructor for when reduction is what is wanted.
- **Sampling is masked rejection, not reduction.** Reducing a uniform 256-bit draw modulo a
  254-bit prime would favour the low residues. `test_random_is_unbiased_in_the_low_bits` runs a
  chi-squared test over 16 buckets of the low limb across 200,000 draws, which is exactly where
  that bias would appear.

### 2.4 Risk, resolved

`ark-ff` 0.6's `MontConfig` derive does emit an `unexpected_cfgs` warning in the dependent crate,
as anticipated. CI runs `cargo clippy --all-targets --all-features -- -D warnings`, so it would
have failed the build. It is confined to the test module that declares the oracle, which carries
an `#[allow(unexpected_cfgs)]` with a comment saying why.

## 3. Architecture: split the cardinality out of `FiniteField` — landed

The plan (§6.1) proposes a new minimal `AlgebraField` plus a compatibility blanket impl, and
migrating generic bounds across the crate. Given §1's finding, that buys nothing the cheaper
change does not, and costs 253 bound edits plus a coherence problem (a blanket
`impl<T: FiniteField> AlgebraField for T` conflicts with any direct impl for the wide-field
adapter — the plan's own §6.3 warning).

**Done instead:** `FiniteField` stays the one coefficient trait, and the cardinality moves out of
it.

```rust
// src/fields/finite_field.rs — unchanged except for what left
pub trait FiniteField: Ring + /* …operators, Hash, Serde, Display… */ {
    fn new(val: u64) -> Self;
    fn from_str(value: &str) -> Result<Self, ParseFieldElementError>;
    fn random<R: RngCore + CryptoRng>(rng: &mut R) -> Self;
    fn pow(&self, b: u128) -> Self;        // small exponents; no cardinality
    fn inverse(&self) -> Self;             // REQUIRED, not provided — see below
    fn neg(&self) -> Self;
    fn checked_div(&self, rhs: &Self) -> Option<Self>;
}

pub trait KnownOrder: FiniteField {
    /// q = p^k, little-endian limbs, no trailing zero limb.
    fn order_limbs() -> &'static [u64];
    /// p, little-endian limbs. Not the order unless k = 1.
    fn characteristic_limbs() -> &'static [u64];

    /// For the callers that need a machine integer and may fail without one.
    fn order_u128() -> Option<u128> { /* from the limbs */ }
    fn characteristic_u128() -> Option<u128> { /* from the limbs */ }

    fn primitive_element<R: RngCore + CryptoRng>(rng: &mut R) -> Self { /* HAC 4.80 */ }
    fn root_of_unity<R: RngCore + CryptoRng>(n: u64, rng: &mut R) -> Self { /* … */ }
}
```

`&'static [u64]` with no allocation and no fixed width: an implementation holds its order in an
associated const array — which may depend on a const generic, and `&Self::ORDER_LIMBS` promotes
to `'static` — and passes it through `trim_limbs` to drop the trailing zero limb.

```rust
impl<const P: u128> PrimeFieldElement128<P> {
    const ORDER_LIMBS: [u64; 2] = [P as u64, (P >> 64) as u64];
}

impl<const P: u128> KnownOrder for PrimeFieldElement128<P> {
    fn order_limbs() -> &'static [u64] { trim_limbs(&Self::ORDER_LIMBS) }
    // ...
}
```

What it cost, measured against the plan's estimate of ~253 bound edits:

| | sites |
|---|---:|
| `poly/multivariate`, `linalg`, `grobner/f4`, `grobner/fglm`, `buchberger`, `pairs`, `s_polynomial` | **0** |
| `FiniteField` → `KnownOrder` bounds, non-test | 16 |
| `KnownOrder` impls (the four field types) | 4 |
| `inverse` bodies moved out of the trait | 4 |

The 16 are `roots`; `factorize`, `is_irreducible` and the Frobenius/splitting helpers they share;
`solve` and its enumeration helpers; the `solve_one` / `solve_zero_dimensional` pipeline, which
reaches `roots` through `candidate_values`; `verify_case` and `check_system` in the differential
harness. Nothing else.

Two corrections to §3 as first written:

1. **The solving pipeline needs `KnownOrder`, not just the small-field enumerator.**
   `solve_zero_dimensional → search → candidate_values → roots` is a hard dependency, so
   `solve_one` carries the bound permanently. That is not a restriction on wide fields — the
   adapter implements `KnownOrder` too — but it does make M20-D a gate rather than a polish step.
2. **`solve.rs` stays small-field by assertion, not by construction.** Its `MAX_FIELD_ORDER` check
   is now `F::order_u128().is_some_and(|q| q <= MAX_FIELD_ORDER)`, which fails closed for a field
   too wide to measure, but it is still a runtime check.

`k` is preserved: `order_limbs` is q = p^k and `characteristic_limbs` is p, so the extension and
binary fields keep the distinction. `BinaryFieldElement` reports characteristic `[2]` against an
order of `2^m`, and `factorize`'s characteristic-two branch is now
`F::characteristic_limbs() == [2]` rather than `F::characteristic() == 2`.

### 3.1 Public API break, stated plainly

`FiniteField::order()` and `characteristic()` leave the trait; `inverse()` stops having a default.
Downstream code generic over `F: FiniteField` that calls `F::order()` must add `F: KnownOrder`.
Concrete small-field uses are unaffected, since `KnownOrder` is implemented for every existing
field type. `order_u128()` is the migration path for anything that wants the old `u128`.

### 3.2 Inversion of zero

Keep today's contract: `inverse()` panics on zero, `checked_div` returns `None`. Pivot
normalization in `src/linalg/sparse/elimination.rs` and `src/grobner/f4/reduction.rs` already
inverts only pivots, which are nonzero by construction. No `Option` enters the hot path.
`ark_ff::Field::inverse` returns `Option<Self>`; the adapter unwraps with the same panic message.

### 3.3 `Ring`'s `Arbitrary` bound: leave it

The plan asks whether `Arbitrary` belongs in `Ring`. It does not, conceptually. But the adapter
can implement it in about six lines, the bound is load-bearing for
`SparseMultiPoly: Arbitrary` (`sparse_multivariate_polynomial.rs:282`), and removing it touches
every `Ring` user to no measured end. **Do not move it in M20.** Revisit only if the adapter
hits a real conflict — which the probe says it will not.

### 3.4 How the split is kept

`grobner::mod`'s `test_the_grobner_stack_needs_no_field_cardinality` runs Buchberger, F4 and FGLM
through a function generic over `F: FiniteField` alone and checks Buchberger's criterion on each
result. The assertions are a sanity check; the content of the test is that it compiles. Adding
`F: KnownOrder` to `f4` was tried and breaks it, along with three sites in `f4/tests.rs`, so the
property is pinned rather than merely documented.

`roots` and `factorize` took their exponents as `u128` for the length of M20-A, through one
helper that failed loudly for a wider field. M20-D replaced it; see §5.1.

### 3.5 What M20-A did *not* solve, and M20-D did

M20-A left `roots` unable to run over a wide field, and the solving pipeline goes straight
through it:

```
solve_zero_dimensional → search → candidate_values (solve.rs:157)
                                → roots (roots.rs:54) → pow_mod(x, F::order(), f)
```

So wide-field root finding was a **mandatory integration gate**, as the plan's closing note
argued. A Gröbner basis over BN254 that cannot produce a solution does not meet the objective.
That gate is now passed — `test_the_whole_pipeline_over_bn254_fr` and its BLS12-381 twin take a
planted system through F4, FGLM and `solve_one` and re-evaluate the returned point against the
original system.

## 4. Measurements

### 4.1 Field arithmetic, every field in the crate

`cargo bench --bench field_arithmetic`, 256 operations per iteration, divided out. `p31` =
`Zp2147483647`, `p64` = `Zp18446744073709551557`, `p68` =
`PrimeFieldElement128<221360928884514619393>` (3·2^66+1).

| field | width | mul | add | sub | inverse |
|---|---:|---:|---:|---:|---:|
| p31 | 31 | 1.76 ns | 1.10 ns | 0.95 ns | 246 ns |
| p64 | 64 | 1.71 ns | 1.05 ns | 0.97 ns | 509 ns |
| p68 | 68 | **130.6 ns** | 2.10 ns | 1.90 ns | **17.84 µs** |
| BN254 `Fr` | 254 | 18.71 ns | 3.69 ns | 3.41 ns | 3.77 µs |
| BLS12-381 `Fr` | 255 | 19.34 ns | 3.52 ns | 3.27 ns | 3.97 µs |

Three things worth stating plainly:

1. **A 254-bit multiply is 7.0x faster than the crate's own 68-bit multiply**, and inversion is
   4.7x faster. `PrimeFieldElement128` reduces a 256-bit product by allocating software long
   division; the new field reduces with CIOS and allocates nothing. The milestone's framing — that
   wide fields cost more — holds against the 64-bit Montgomery fields (10.9x on multiply) and is
   inverted against the 68-bit one. **Any "cost of width" claim has to name its baseline.**
2. **Inversion is 202 multiplies.** Pivot normalization over a wide field should multiply by a
   precomputed inverse, never divide per entry. Batch inversion is worth measuring.
3. **Addition is only 3.5x a 64-bit addition, while multiplication is 11x.** A computation
   dominated by row updates will degrade less than the multiply ratio suggests.

### 4.2 Against hand-written assembly

`ark-ff` with `asm`, at BN254 `Fr`: 17.25 ns multiply, 3.58 µs inverse. Against this crate's
18.71 ns and 3.77 µs, that is **1.08x on multiply and 1.05x on inversion**.

Caveat the comparison rather than quoting the ratio alone: the zeebra figures above are Criterion,
the `ark-ff` ones were taken in a hand-rolled loop of the same shape (256 operands,
`acc += a[i] * b[i]`) because `ark-ff` is a dev-dependency and has no bench target here. The two
harnesses agree to a few percent on the same code, so the ratio is indicative, not matched. The
honest claim is that the gap is small — not that it is exactly 8%.

### 4.3 Still to measure

- **F4, FGLM and end-to-end solving over the wide fields.** The correctness tests run on systems
  small enough to be instant; nothing here yet says what a cryptographically interesting system
  costs. That is M20-E.
- **Byte-accounted resource limits.** `size_of::<(usize, F)>()` is 40 bytes for a wide field
  against 16 for a 64-bit one, so the same nonzero-entry budget admits 2.5x the memory. F4's
  budget is still counted in entries only. FGLM already has `max_operator_bytes`.
- **F4/FGLM baselines on the merged M19.** M19 is still not on `main`.

### 4.4 Dependency and build cost

| | packages (normal + build) |
|---|---:|
| zeebra, shipped | **51 — unchanged** |
| `+ ark-ff` as a dev-dependency | 76 at test time |
| `+ ark-bn254`/`ark-bls12-381` instead | 111+ |

The shipped dependency count did not move, which was the point of implementing the field rather
than adapting one.

## 5. Revised sub-milestone plan

The structure of the plan survives; the sizes change.

| ID | Deliverable | Change from the plan |
|---|---|---|
| **M20-0** | This document | done |
| **M20-A** | `KnownOrder` split, `inverse` required | **done**, and much smaller than planned — 16 bound edits, none in the core |
| **M20-B** | `PrimeFieldElement256`, BN254 + BLS12-381 `Fr`, oracle tests | **done**, but implemented in-crate rather than adapted — see §2 |
| **M20-C** | F4/Buchberger/quotient/FGLM over both fields; byte-accounted limits | **partly done** — the core needed no changes at all, as predicted; the end-to-end test passes over BN254. Byte accounting outstanding |
| **M20-D** | Limb-exponent `pow_mod`, Frobenius, `roots`, `factorize`, `solve_one` | **done** — one new function and five call-site changes; see §5.1 |
| **M20-E** | Crypto corpus, oracle, measurements | as planned, starts now |
| **M20-I** | Integration, benchmarks, report | as planned |

### 5.1 M20-D, as landed

`pow_mod` keeps its `u128` signature as a wrapper over a limb-slice form:

```rust
pub fn pow_mod<F: FiniteField>(base: &P<F>, exponent: u128, modulus: &P<F>) -> P<F> {
    pow_mod_limbs(base, &[exponent as u64, (exponent >> 64) as u64], modulus)
}

pub fn pow_mod_limbs<F: FiniteField>(base: &P<F>, exponent: &[u64], modulus: &P<F>) -> P<F>;
```

Square-and-multiply over the exponent's bits, stopping at the highest set bit so that trailing
zero limbs cost nothing and a caller may pass a fixed-width order unpadded. `O(log q)` polynomial
multiplications, never materializing degree q — the existing loop with the bit source swapped.
`roots` then calls `pow_mod_limbs(&x, F::order_limbs(), f)` and needs **no other change**.

Note the bound: `pow_mod_limbs` is on `FiniteField`, not `KnownOrder`. The exponent is a
parameter, so the function itself has no opinion about where it came from.

`factorize` needed more:

| Was | Is |
|---|---|
| `let q = F::order()` (`u128`) | `let q = F::order_limbs()` (`&'static [u64]`) |
| `pow_mod(.., (q - 1) / 2, ..)` | `pow_mod_limbs(.., &half_of_q_minus_one::<F>(), ..)` — subtract one, shift right one bit across the limbs |
| `frobenius_iterated(.., q: u128, ..)` | `q: &[u64]` |
| `frobenius_norm` reading `F::order()` | reads `F::order_limbs()` |
| `F::order().trailing_zeros()` in `trace_to_gf2` | `characteristic_two_degree::<F>()`, the single set bit's index across limbs |

`half_of_q_minus_one` asserts that q is odd, which is what makes the halving exact — in
characteristic two the splitter takes the trace branch instead and never reaches it.
`prime_divisors(n)` operates on the *degree* n, not on q, so it is untouched: §9.4's "do not
factor q - 1" was already satisfied.

What this buys, tested: `roots` recovers planted roots over both target fields, including a
39-digit one and `p - 1`; `pow_mod_limbs` is checked against the `u128` form where both apply and
against 192 explicit squarings where only it applies; and `solve_one` returns a verified point
over both fields.

### 5.2 How the dependencies actually ran

The plan's §14 expected M20-B, M20-D and M20-E to proceed in parallel after M20-A. In the event
the order was strictly sequential and each step was small enough that parallelism would have cost
more in coordination than it saved: M20-A was 16 bound edits, M20-B two new modules, M20-D one new
function and five call-site changes. The reason is §1 — the audit found far less coupling than the
plan assumed, so there was less work to divide.

M20-E is genuinely independent and still outstanding.

## 6. Defects found

The first two came out of the audit and are in code M20 touches; the third is M20's own, found in
review.

1. **`PrimeFieldElement128::random` returned zero on every draw for any modulus below 2^64** —
   **fixed.** The sampler built its rejection mask from two 64-bit halves:

   ```rust
   mask_low = u64::MAX.checked_shr(num_zero_bits).unwrap_or(0);
   ```

   Any `P < 2^64` leaves more than 64 leading zero bits, so the shift is out of range,
   `checked_shr` yields `None`, and the mask collapses to zero. A chi-squared test over
   `PrimeFieldElement128<61>` measured 200,000 draws, all of them zero. The only 128-bit field
   alias in the crate is `Zp221360928884514619393` (68 bits), which took the other branch and
   masked correctly, which is why the bug survived.

   The same loop also accepted `val == P` and mapped it to zero through `new`, drawing zero at
   2/(P+1) against 1/P. Both are now one masked rejection loop over the full 128 bits, accepting
   strictly below `P` and constructing the reduced representative directly.
   `PrimeFieldElement64::random` uses `rng.gen_range(0..P)` and was never affected.

   The `#[ignore]`d `unimplemented!()` placeholder that asked for exactly this test
   (`test_random_distribution`) is now that test.

2. **No field type overrides `inverse`.** Every inversion in the crate is `pow(q-2)`: 252 ns on a
   31-bit field where `ark-ff` does 254 bits in 3.58 µs by binary extended Euclid, and 18.4 µs on
   the 68-bit field. M19 territory, not M20's, but §4.1 is the measurement that motivates it.

3. **`PrimeFieldElement256` assumed its modulus filled all four limbs** — found in review of
   PR #64, fixed. Two places read the width wrongly:

   - `new(val: u64)` asserted that any `u64` is below the modulus. True for the two provided
     fields at 254 and 255 bits, false for the one-limb moduli the trait also promises: `new(8)`
     over GF(7) panicked instead of giving 1. It now reduces, through `BigUInt` on the path that
     needs it — `new` is a constructor from a small integer, not a hot path.
   - `random()` took its rejection mask from `MODULUS[LIMBS - 1]`. For any modulus below 2^192
     that limb is zero, so `leading_zeros()` is 64 and the shift overflowed; past that, the draw
     filled limbs the modulus cannot reach, so every draw would have been rejected and the loop
     would not have terminated. The mask now comes from `highest_occupied_limb`, and the limbs
     above it stay zero.

   Neither could be caught by the two provided fields, which is the general lesson: a type
   parameterized over a width needs a test at more than one width. The regression tests sit at
   one, two, three and four limbs — GF(7) checked *exhaustively* against the unrelated
   `PrimeFieldElement64<7>`, and 2^127-1 and the NIST P-192 prime against `BigUInt`'s plain long
   arithmetic, which shares no Montgomery logic with the code under test.

### 6.1 What the in-crate field is made of

For a reader who wants to find the code rather than the argument:

| File | Contents |
|---|---|
| `src/fields/montgomery_256.rs` | `n_prime`, `power_of_two_mod_p` (the `const fn` that gives `R` and `R^2` by doubling, since `multi_word_div` allocates and so cannot run in a constant), CIOS `mul`, `add`, `sub`, `halve`, and the binary extended Euclid `inverse` |
| `src/fields/prime_field_256.rs` | `PrimeModulus256`, `PrimeFieldElement256`, the canonical/reduced constructors, byte and decimal conversion, serde, `Arbitrary`, masked rejection sampling, `FiniteField`, `KnownOrder`, and the two moduli |
| `src/poly/univariate/pow_mod.rs` | `pow_mod_limbs` and the `pow_mod` wrapper |
| `src/poly/univariate/factorize.rs` | `half_of_q_minus_one`, `characteristic_two_degree`, and the limb-exponent call sites |

`inverse` seeds the loop with `R^2 mod p` rather than with one, which is what makes the result
come out already in Montgomery form — the invariant carried through is `a*b = u*R^2` and
`a*c = -v*R^2` modulo p, so when `u` reaches one, `b` holds `a^{-1} * R`. That is worth stating
because it looks like a bug otherwise.

## 7. Decisions, and what is left open

Settled:

1. ~~`KnownOrder` split over a new `AlgebraField`~~ — landed (§3).
2. ~~`inverse` as a required method~~ — landed; the one public break (§3.1).
3. ~~Where the 254-bit arithmetic comes from~~ — **implemented in-crate**, with `ark-ff` as a
   dev-dependency oracle (§2). The moduli are therefore zeebra's responsibility, checked by test
   against the published decimals.

Open:

4. **Re-base `PrimeFieldElement128` on `montgomery_256`, or retire it.** §4.1 is the argument:
   its multiply is 130.6 ns against 18.71 ns for a field four times as wide, because it allocates
   and long-divides. The 4-limb code generalizes to 2 limbs with no new mathematics. The one
   obstacle is that `PrimeFieldElement128` takes its modulus as a `const P: u128` generic while
   `PrimeFieldElement256` takes a trait, so converting changes its public shape. Worth an issue;
   out of M20's scope as written.
5. **Byte-accounted resource limits** (§4.3). F4's budget is still counted in entries, and a
   wide-field entry is 2.5x the bytes of a 64-bit one. M20-C.
6. **Whether a generator is ever needed over a wide field.** `primitive_element` and
   `root_of_unity` are `unimplemented!()` for `PrimeFieldElement256`, since finding one means
   factoring a 254-bit `q - 1`. Nothing in the crate needs them, and the FFT's uses are
   test-only. If an FFT over a wide field is ever wanted, the two-adic root of unity is derivable
   from the field's two-adicity without factoring — 28 for BN254, 32 for BLS12-381.

## 8. Acceptance criteria

### M20-0

- [x] Every `order`/`characteristic`/`pow`/`inverse`/`random`/`primitive_element`/`root_of_unity`
      use inventoried and classified (§1)
- [x] `ark-ff` and `ff` evaluated against the trait requirements, with the deciding facts recorded
      (§1.2, §2.1)
- [x] Backend chosen, dependency footprint measured (§2, §4.4)
- [x] Field-arithmetic baselines recorded for 31-, 64- and 68-bit fields, and for both candidate
      wide fields (§4.1, §4.2)
- [x] Trait architecture specified, with the public break stated (§3)
- [x] Architecture approved — the exit criterion
- [ ] F4/FGLM/solving baselines — deferred to the merged M19 (§4.3)

### M20-A

- [x] Existing field types compile through the new abstraction, with unchanged arithmetic and
      serialization behaviour
- [x] The algebraic core is instantiable with a coefficient type that has no cardinality, pinned
      by a test that fails to compile otherwise (§3.4)
- [x] Small-field algorithms return identical results; the Singular differential fixtures pass
      unchanged
- [x] No duplicated wide-field Gröbner implementation introduced
- [x] The public break documented, in the README and in §3.1
- [x] Instantiated with a field whose order exceeds `u128` — done in M20-B

### M20-B

- [x] BN254 `Fr` and BLS12-381 `Fr` usable as coefficient types
- [x] Arithmetic agrees with an independent implementation — 20,000 random cases per field on
      add, sub, mul, square, negate, invert and divide, plus the nine edge pairs over
      {0, 1, p-1}, against `ark-ff` as a dev-dependency
- [x] Both moduli checked against the published decimals **without** the oracle, and the oracle
      separately confirmed to be over the same two fields
- [x] Uniform sampling correctly defined — masked rejection, with a chi-squared test on the low
      bits where reduction would show a bias
- [x] Canonical serialization and parsing tested; non-canonical encodings rejected by both the
      constructor and the deserializer; a separately named reducing constructor provided
- [x] Field elements satisfy the polynomial and linear-algebra types' requirements
- [x] No new multiprecision arithmetic engine — `montgomery_256` is 4-limb Montgomery, not a
      general bignum, and the existing `BigUInt` handles decimal conversion at the boundary
- [x] Fixed-width, stack-allocated representation: `size_of::<Bn254Fr>() == 32`, nothing on the
      heap in the hot path
- [x] `PrimeModulus256`'s documented range — any odd prime up to 256 bits — actually works, with
      tests at one, two, three and four limbs (§6, defect 3)

### M20-D

- [x] Wide-exponent modular polynomial arithmetic correct — checked against the `u128` form where
      both apply, and against explicit repeated squaring beyond it
- [x] Root finding supports both target fields
- [x] `solve_one` recovers a known witness over both fields, verified against the original system
- [x] No-solution stays distinct from a resource error — `Ok(None)` for a system with no
      base-field point, tested with a non-square found by search rather than assumed
- [x] The complete F4 → FGLM → solving pipeline works
- [x] No enumeration of a 254-bit field occurs; `solve.rs`'s enumerator fails closed on a field
      too wide to measure
      which such a field exists
