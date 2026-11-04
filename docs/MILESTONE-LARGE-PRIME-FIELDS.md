# Milestone: Large Prime Fields and Cryptographic Algebra Readiness

**Status:** M20-0 complete (audit, backend choice, baselines, architecture) — awaiting approval
before M20-A changes generic bounds.
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

## 2. Backend choice: `ark-ff` 0.6, scalar fields declared locally

Measured, not inferred. All figures from an AMD Ryzen Threadripper PRO 5995WX, `rustc 1.97.0`,
`--release` with the crate's `lto = "fat"` / `codegen-units = 1`, `-C target-cpu=native`.

### 2.1 `ark-ff` against `ff`/`bls12_381`

`bls12_381::Scalar` (zkcrypto, `ff` 0.14) **does not implement `Hash`**, which `FiniteField`
requires and which `SparseMultiPoly` uses (`sparse_multivariate_polynomial.rs:256` hand-writes
`Hash` over its coefficients). `ark-ff`'s `Fp` does. `ff` 0.14 also pulls `rand_core` 0.9+,
against zeebra's rand 0.8 / `rand_core` 0.6 — the version split §18 of the plan anticipated.
`ark-std` 0.6 depends on **rand 0.8.8**, so `UniformRand::rand(&mut rng)` takes zeebra's own
`R: RngCore + CryptoRng` with no adaptation layer.

`ark-ff` is the primary provider. No second production backend.

### 2.2 Declare the two fields locally, don't depend on the curve crates

`ark-bn254` and `ark-bls12-381` both depend on `ark-ec` unconditionally, even under
`--no-default-features --features scalar_field`: 111 packages in the lock file, and elliptic
curves and pairings are explicitly out of scope. Declaring the moduli with `ark-ff`'s
`MontConfig` derive gives both fields from `ark-ff` alone — 30 packages total, **+25 over
zeebra's current 51** — and puts the modulus in zeebra's own source where a test can check it
against the published value:

```rust
#[derive(MontConfig)]
#[modulus = "21888242871839275222246405745257275088548364400416034343698204186575808495617"]
#[generator = "5"]
pub struct Bn254FrConfig;
pub type Bn254Fr = Fp256<MontBackend<Bn254FrConfig, 4>>;
```

Verified: BN254 `Fr` modulus is 254 bits, BLS12-381 `Fr` is 255, both `size_of == 32`,
two-adicity 28 and 32 respectively (so `root_of_unity` remains available for FFT sizes up to
2^28 / 2^32 — a bonus, not a requirement).

Enable `ark-ff`'s `asm` feature. Measured on BN254 `Fr`: multiplication 20.6 ns with it against
21.6 ns without, inversion 3.58 µs against 4.02 µs. Small but free, and it works on stable.

### 2.3 Sampling and serialization are already canonical

Two of the plan's explicit hazards (§7.2, §7.3) turn out to be handled by the backend, which the
adapter must preserve rather than reimplement:

- **Uniform sampling is unbiased.** `ark-ff`'s `Standard` distribution for `Fp`
  (`fields/models/fp/mod.rs:525`) masks the unused high bits and rejects any draw `>= MODULUS`,
  looping until one lands in range. It does place the random limbs directly as the *Montgomery*
  representation, which looks wrong and is not: `r ↦ r·R⁻¹ mod p` is a bijection on `[0,p)`, so
  uniform in the Montgomery domain is uniform in the canonical one. Zeebra's `random` wraps this
  rather than rolling its own rejection loop.
- **Serialization is the canonical residue.** `CanonicalSerialize for Fp` writes
  `self.into_bigint()`, not the internal limbs, so the Montgomery-leak hazard does not arise.
  The adapter's serde impl goes over those canonical little-endian bytes, and the deserializer
  rejects any encoding `>= p` — matching the `reduced_residue` guard
  `PrimeFieldElement128` already applies (`prime_field_128.rs:36`). A reducing constructor, if
  wanted, is a separately named one.

### 2.4 Risk accepted

`ark-ff` 0.6's `MontConfig` derive emits an `unexpected_cfgs` warning in the dependent crate.
CI runs `cargo clippy --all-targets --all-features -- -D warnings`, so M20-B must confirm the
warning does not escalate there, and add `#[allow(unexpected_cfgs)]` on the declaring module if
it does.

## 3. Architecture: split the cardinality out of `FiniteField`

The plan (§6.1) proposes a new minimal `AlgebraField` plus a compatibility blanket impl, and
migrating generic bounds across the crate. Given §1's finding, that buys nothing the cheaper
change does not, and costs 253 bound edits plus a coherence problem (a blanket
`impl<T: FiniteField> AlgebraField for T` conflicts with any direct impl for the wide-field
adapter — the plan's own §6.3 warning).

**Recommended instead:** leave `FiniteField` as the one coefficient trait and move the
cardinality out of it.

```rust
// src/fields/finite_field.rs — unchanged except for what leaves
pub trait FiniteField: Ring + /* …operators, Hash, Serde, Display… */ {
    fn new(val: u64) -> Self;
    fn from_str(value: &str) -> Result<Self, ParseFieldElementError>;
    fn random<R: RngCore + CryptoRng>(rng: &mut R) -> Self;
    fn pow(&self, b: u128) -> Self;        // small exponents; no cardinality
    fn inverse(&self) -> Self;             // REQUIRED, not provided — see below
    fn neg(&self) -> Self;
    fn checked_div(&self, rhs: &Self) -> Option<Self>;
}

/// A finite field whose order and characteristic are known as little-endian 64-bit limbs.
///
/// Separate from `FiniteField` because the algebraic core never needs it: only root finding,
/// factorization and field enumeration do.
pub trait KnownOrder: FiniteField {
    /// q = p^k, little-endian limbs, no trailing zero limb.
    fn order_limbs() -> &'static [u64];
    /// p, little-endian limbs.
    fn characteristic_limbs() -> &'static [u64];

    fn primitive_element<R: RngCore + CryptoRng>(rng: &mut R) -> Self;
    fn root_of_unity<R: RngCore + CryptoRng>(n: u64, rng: &mut R) -> Self;

    /// q as a `u128`, or `None` if it does not fit. For the call sites that genuinely need a
    /// machine integer — `MAX_FIELD_ORDER`, the Singular fixture check.
    fn order_u128() -> Option<u128>;
}
```

Consequences:

- **Zero bound edits in `poly/multivariate`, `linalg`, `grobner/f4`, `grobner/fglm`,
  `grobner/buchberger`.** They already require exactly what they use.
- `roots`, `factorize`, `is_irreducible` gain `F: KnownOrder`. `solve` (the brute-force
  extension in `solve.rs`) and the differential harness gain it too, and stay small-field by
  construction rather than by assertion.
- `inverse` becomes a **required** method. That is the breaking change, and it is the point: the
  current provided body is the thing that cannot exist for a wide field. All four existing field
  types get a one-line `fn inverse(&self) -> Self { self.pow(Self::order_u128().unwrap() - 2) }`
  moved out of the trait, preserving behaviour exactly; the adapter delegates to
  `ark_ff::Field::inverse`.
- Limbs, not a `BigUInt`: `order_limbs()` returning `&'static [u64]` costs no allocation, and
  `pow_mod` consumes it as a bit iterator (§5.1).
- `k` is preserved. `order_limbs` is q = p^k and `characteristic_limbs` is p; the extension and
  binary fields keep the distinction they have now.

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

### 3.4 What this does *not* solve

Nothing here makes `roots` work. §1's four files still need wide exponents, and the solving
pipeline goes straight through them:

```
solve_zero_dimensional → search → candidate_values (solve.rs:157)
                                → roots (roots.rs:54) → pow_mod(x, F::order(), f)
```

So wide-field root finding is a **mandatory integration gate**, as the plan's closing note
argues. A Gröbner basis over BN254 that cannot produce a solution does not meet the objective.

## 4. Baselines

### 4.1 Field arithmetic, existing fields

`cargo bench --bench field_arithmetic`, 256 operations per iteration, divided out. `p31` =
`Zp2147483647`, `p64` = `Zp18446744073709551557`, `p68` = `PrimeFieldElement128<221360928884514619393>`
(3·2^66+1, 68 bits).

| field | width | mul | add | sub | inverse |
|---|---:|---:|---:|---:|---:|
| p31 | 31 | 1.76 ns | 1.06 ns | 0.99 ns | 252 ns |
| p64 | 64 | 1.76 ns | 1.02 ns | 1.01 ns | 562 ns |
| p68 | 68 | **134.8 ns** | 2.09 ns | 1.89 ns | **18.4 µs** |

### 4.2 The candidate wide fields

Same loop shape, same operand count, same `black_box` placement as the bench above, run outside
Criterion. Treat as indicative to one significant figure, not as Criterion intervals; M20-E
re-measures these inside the real harness.

| field | width | mul | add | sub | inverse |
|---|---:|---:|---:|---:|---:|
| BN254 `Fr` | 254 | 20.6 ns | 2.42 ns | 2.90 ns | 3.58 µs |
| BLS12-381 `Fr` | 255 | 20.1 ns | 2.43 ns | 2.39 ns | 3.62 µs |

Two things fall out of this table that the plan did not anticipate:

1. **A 254-bit `ark-ff` multiply is 6.5× faster than zeebra's existing 68-bit multiply.**
   `PrimeFieldElement128` reduces by software long division; `ark-ff` uses Montgomery. The
   milestone's framing — that wide fields will be slower — holds against the 64-bit fields
   (12×) and is inverted against the 68-bit one. Any "cost of width" claim must say which
   baseline it means.
2. **Inversion is ~174 multiplications.** Pivot normalization over a wide field should multiply
   by a precomputed inverse, never divide per entry, and batch inversion is worth measuring in
   M20-C. (`ark-ff`'s `inverse` is already a Euclidean one, not exponentiation — the 3.58 µs is
   not a `pow(q-2)` artifact.)

### 4.3 Baselines still to take

The F4/FGLM/solving baselines of §5.3 of the plan are **not** recorded here: they must be taken
on the merged M19, and M19 is not on `main` yet. Taking them against this worktree would date
them immediately. The commands are unchanged from M19:

```
cargo bench --bench grobner
cargo bench --bench f4_stages
cargo bench --bench fglm
cargo bench --bench polynomial_solving
```

### 4.4 Dependency and build cost

| | packages (normal + build) |
|---|---:|
| zeebra today | 51 |
| `+ ark-ff` with locally declared fields | 76 |
| `+ ark-bn254`/`ark-bls12-381` instead | 111+ |

`num-bigint` for the arithmetic oracle (§11.1 of the plan) is a **dev-dependency** and does not
enter the figures above. Note `ark-ff` already carries `num-bigint` 0.4 internally, so the oracle
must be a separate direct dev-dependency to be genuinely independent of the backend.

## 5. Revised sub-milestone plan

The structure of the plan survives; the sizes change.

| ID | Deliverable | Change from the plan |
|---|---|---|
| **M20-0** | This document | done |
| **M20-A** | `KnownOrder` split, `inverse` required, four files gain the bound | **much smaller** — no core bound migration, no new `AlgebraField`, no blanket impl |
| **M20-B** | `ark-ff` adapter newtype, BN254 + BLS12-381 `Fr`, oracle property tests | as planned |
| **M20-C** | F4/Buchberger/quotient/FGLM over both fields; byte-accounted limits | as planned, but expect **no code changes** in the core — it is a test-and-measure sub-milestone |
| **M20-D** | Limb-exponent `pow_mod`, Frobenius, `roots`, `factorize`, `solve_one` | **the critical path**, and the real risk |
| **M20-E** | Crypto corpus, oracle, measurements | as planned, starts now |
| **M20-I** | Integration, benchmarks, report | as planned |

### 5.1 M20-D, concretely

`pow_mod` keeps its `u128` signature as a wrapper over a limb-slice form:

```rust
pub fn pow_mod<F: FiniteField>(base: &P<F>, exponent: u128, modulus: &P<F>) -> P<F> {
    pow_mod_limbs(base, &[exponent as u64, (exponent >> 64) as u64], modulus)
}

pub fn pow_mod_limbs<F: FiniteField>(base: &P<F>, exponent: &[u64], modulus: &P<F>) -> P<F>;
```

Square-and-multiply over the limbs' bits, high limb first, costs `O(log q)` polynomial
multiplications and never materializes degree q — exactly what the existing loop does, with the
bit source swapped. `roots` then calls `pow_mod_limbs(&x, F::order_limbs(), f)` and is done:
**no other change to the root-finding algorithm.**

`factorize` needs more care. `(q-1)/2` becomes a limb subtract-one and a one-bit right shift;
`frobenius_norm` and `frobenius_iterated` take `&[u64]` instead of `u128`;
`F::characteristic() == 2` becomes a `characteristic_limbs() == [2]` check; `trace_to_gf2`'s
`order().trailing_zeros()` is characteristic-two only and so never runs for a prime field, but
must still compile. `prime_divisors(n)` operates on the *degree* `n`, not on q, so it is
untouched — §9.4's "do not factor q-1" is already satisfied.

### 5.2 Parallelism

Phase 1 (M20-A) is sequential and owns `src/fields/finite_field.rs` and `src/rings/mod.rs`.
After it lands, M20-B (adapter), M20-D (univariate) and M20-E (corpus) are independent; M20-C
depends on M20-B only. That matches §14 of the plan, with M20-C demoted from implementation to
validation.

## 6. Defects found during the audit

Neither is M20 work; both are in the code M20 touches.

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
   the 68-bit field. M19 territory, not M20's, but §4.2 is the measurement that motivates it.

## 7. Open decisions

1. **Approve the `KnownOrder` split over a new `AlgebraField`** (§3). This is the one decision
   M20-A cannot start without. The argument for it is §1: the core needs no new trait because it
   already asks for nothing beyond arithmetic.
2. **`inverse` as a required method** is the one unavoidable public break. The alternative — keep
   the default and have it panic for wide fields — trades a compile error for a runtime one.
   Recommend the break.
3. **Locally declared moduli over `ark-bn254`/`ark-bls12-381`** (§2.2), accepting that the
   moduli are then zeebra's responsibility to get right, checked by test against the published
   constants.
4. Whether to re-base `PrimeFieldElement128` on `ark-ff` once the adapter exists, given §4.2.
   Out of M20's scope as written; worth an issue.

## 8. Acceptance criteria for M20-0

- [x] Every `order`/`characteristic`/`pow`/`inverse`/`random`/`primitive_element`/`root_of_unity`
      use inventoried and classified (§1)
- [x] `ark-ff` and `ff` evaluated against the trait requirements, with the deciding facts recorded
      (§1.2, §2.1)
- [x] Backend chosen, dependency footprint measured (§2, §4.4)
- [x] Field-arithmetic baselines recorded for 31-, 64- and 68-bit fields, and for both candidate
      wide fields (§4.1, §4.2)
- [x] Trait architecture specified, with the public break stated (§3)
- [ ] F4/FGLM/solving baselines — deferred to the merged M19 (§4.3)
- [ ] **Architecture approved** (§7) — the exit criterion
