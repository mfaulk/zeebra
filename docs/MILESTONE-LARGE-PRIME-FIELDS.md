# Milestone: Large Prime Fields and Cryptographic Algebra Readiness

**Status:** M20-0, M20-A, M20-B, M20-C and M20-D landed. The milestone's primary demonstration
passes over both target fields: a planted zero-dimensional system goes through F4, the quotient
algebra, FGLM and `solve_one`, and the returned point is verified against the original system.
Remaining: M20-E's benchmark corpus.
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

That follow-up is #160, and §4.1.1 is its measurement: the exponentiation was not the problem, the
*recursive* `pow` it went through was, and routing the four Fermat fields to the iterative
`pow_limbs` instead is 2.0x to 2.3x for one line each.

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
   precomputed inverse, never divide per entry. Batch inversion is worth measuring. The 202 is the
   254-bit fields; the 64-bit ones read 298 here, and #160 found that most of *that* was the
   recursion in `pow` rather than arithmetic — see §4.1.1, which re-derives both.
3. **Addition is only 3.5x a 64-bit addition, while multiplication is 11x.** A computation
   dominated by row updates will degrade less than the multiply ratio suggests.

### 4.1.1 Inversion through the iterative `pow_limbs`, and the Euclid that does not pay

§4.1's inversion column is the figure §1.1 predicted: no field overrides `inverse`, so every one of
them inverts by Fermat through `FiniteField::pow` — and that default was *recursive*. An odd bit of
the exponent cost a recursion level rather than being folded into the walk, so the call depth was
about `2 log2(q)`: ~62 non-inlined frames at p31 and ~128 at p64, each doing `u128` arithmetic on
the exponent. `pow_limbs`, thirty lines away in the same trait, is the iterative
square-and-multiply over the same exponent. #160 is the one-line-per-field substitution.

`cargo bench --bench field_arithmetic -- field/inverse`, release profile (`lto = "fat"`,
`codegen-units = 1`) with `.cargo/config.toml`'s `-C target-cpu=x86-64-v3`, pinned with
`taskset --cpu-list 0-7` as `tools/scoreboard.sh` does, 256 operations per iteration divided out.
Two binaries built from the same tree and alternated — before, after, before, after, before,
after — so a thermal or scheduling drift hits both sides; the figure is the median of the three
repetitions. `before` is `origin/main` at 418d080, and `git diff 418d080..26a6c19` is empty under
`src/fields/`, `src/integers/` and `benches/field_arithmetic.rs`, so these figures are the merge
base's as well as the measurement base's.

| field | `inverse` before | `inverse` after | factor |
|---|---:|---:|---:|
| p31, `Zp2147483647` | 261.6 ns | **124.1 ns** | **2.11x** |
| p31, `Mersenne31` (u32-backed) | 224.5 ns | **100.3 ns** | **2.24x** |
| p64, largest 64-bit prime | 538.2 ns | **236.4 ns** | **2.28x** |
| p68, `PrimeFieldElement128` | 18.58 µs | 18.62 µs | 1.00x |
| BN254 `Fr` | 3.78 µs | 3.80 µs | 0.99x |
| BLS12-381 `Fr` | 3.83 µs | 3.77 µs | 1.02x |

The bottom three rows are **controls, not results**: #160 does not touch `PrimeFieldElement128`,
which still calls `pow`, and the 254-bit fields invert by binary extended Euclid in
`montgomery_256`. They move by at most 2%, which is this harness's noise floor on this
machine, and they are what licenses reading the top three. `isolated/inverse` over the same
operands agrees — 2.13x, 2.23x and 2.29x, against 1.01x, 1.01x and 1.00x on the controls — so the
gain is not an artifact of the accumulating addition in the `inverse` arm.

**What it does to batch inversion.** The case for `batch_invert` is the ratio between an inversion
and three multiplications, so halving inversion halves the ratio. `isolated/inverse` against
`batch/inverse` over the same 256 operands, before and after: **30.1x to 15.3x** at p31, **29.6x to
14.8x** at `Mersenne31`, **54.6x to 27.6x** at p64 — against **60.4x to 60.7x** at BN254 `Fr` and
**37.5x to 38.1x** at p68, which hold still and are the controls again. Montgomery's trick still wins by more than an order of
magnitude in every field; the conclusions in §5 and in `docs/research/batch-inversion.md` are
unchanged, and only the size of the win moves. That document's table is a separate instrument at
varying n and has not been re-run; its Mersenne-31 and Goldilocks columns should be read as roughly
halved, and its n = 2 crossover is unaffected because the crossover is set by the copy.

One honest caveat on the spread: the three `before` repetitions at p64 were 499, 550 and 538 ns, a
±5% band, against 219, 237 and 236 ns after, and an earlier run of the same protocol at the
previous merge base put `before` at 500, 620 and 551 ns — a ±11% band — for an `after` that held
inside ±1.5%. The recursive route is the noisier of the two as well as the slower, which is what a
call chain that deep through `u128` arithmetic would predict. The factor is stable across the two
runs regardless: 2.05x/2.29x/2.34x then, 2.11x/2.24x/2.28x now.

**§4.1's "inversion is 202 multiplies", re-derived.** A second pass measured `field/mul` and
`field/inverse` in *one* criterion process, so the ratio is within a process rather than across
harnesses:

| field | multiplies before | multiplies after | the chain actually needs |
|---|---:|---:|---:|
| p31 | 150 | **69** | 60 — 30 squarings + 30 products |
| p31, u32-backed | 150 | **66** | 60 |
| p64 | **299** | **131** | 123 — 63 squarings + 60 products |
| p68 | 134 | unchanged | 134 — 67 squarings + 67 products |
| BN254 `Fr` | 193 | 184 | — extended Euclid, not a chain |
| BLS12-381 `Fr` | 194 | 194 | — extended Euclid, not a chain |

p64's `before` column reproduces §4.1's 298 as 299, and p68's reproduces its chain length exactly.
The `after` cell for p68 is "unchanged" rather than a number because this single-repetition pass
caught an outlier there — 23.9 µs against the three-repetition median of 18.6 µs — and the arm is
one #160 does not touch, so the median above is the figure. Against the 123 multiplications that
square-and-multiply over `q - 2` genuinely performs — 63 squarings, and one product per set bit of
an exponent with popcount 60 — the recursion was charging **176 multiply-equivalents of pure
overhead**, more than the arithmetic itself. After the change the gap is 8, about 6%, which is the
bit test and the loop. The 202 figure itself was always about the 254-bit fields, and it still
holds: they read 184–194 here and are unchanged by #160.

**`pow`'s own default body is left recursive, on measurement.** The obvious follow-on is to make
the default every field inherits iterative too, since nothing wants the recursion. A third binary
was built with exactly that — `pow` delegating to `pow_limbs(&[b as u64, (b >> 64) as u64])` — and
measured in the same interleave. It buys nothing anywhere. Against the earlier run's `after`
column, which is the one it was interleaved with: p31 125.2 ns against 125.4 — that arm no longer
reaches `pow` at all — p68 18.67 µs against 19.11, and BN254 4.14 µs against 3.94. All inside the
noise band the control rows establish. p68 is the explanation: a 137 ns multiply means its
134-operation chain dominates 19 µs completely, and the ~136 recursive frames at a few nanoseconds
each are about 1% of it. The recursion only mattered where the multiply was cheap, and those are exactly the
fields #160 already fixed. So the wider change — `pow` is `pub`, and `substitute`, `compose`,
`Monomial::eval` and `PowerPermutation` all go through it — is deferred to #181 rather than taken
for a measured nothing. The one call site with a large exponent and a plausible gain is
`PowerPermutation::invert`'s `pow(inverse_exponent)`, which is not measured here.

**Binary extended Euclid does not pay at single-limb width.** Recorded so that the question is not
reopened without new evidence. `montgomery_256` inverts with binary extended Euclid, and the
natural next step looks like using it at 31 and 64 bits too. A straightforward division-free
implementation measured *slower* than iterative Fermat on every field tried: **222 ns against
120 ns at p31, and 458 ns against 254 ns at p64** (#160's probe, same profile and flags, 20 000
random nonzero operands, all routes asserted to agree before any timing). The reason is structural
rather than a weak implementation. Fermat at 31 bits is ~60 Montgomery multiplies at ~1.7 ns
throughput with independent work for the pipeline to overlap; binary extended Euclid is
~`2 log2(p)` iterations of a serial, branchy loop that can overlap nothing. The arithmetic that
makes Euclid win at four limbs — where a multiply is 19.7 ns and the loop body is still a shift —
inverts at one limb.

So: **do the cheap thing and stop.** If someone does pursue a better inversion, the candidate worth
measuring is not binary extended Euclid but an addition-chain exponent for a specific modulus,
which for Mersenne-31 is 30 squarings and 5 products rather than the ~60 operations above.

Not measured, and worth noting rather than quietly leaving: `benches/field_arithmetic.rs` has no
KoalaBear and no Goldilocks arm, so neither appears in any table here. Adding them would have
changed the binary mid-measurement.

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
- ~~**Byte-accounted resource limits.**~~ Done — `size_of::<(usize, F)>()` is 40 bytes for a wide
  field against 16 for a 64-bit one, so the same nonzero-entry budget admitted 2.5x the memory, and
  FGLM's span cells were worse at 4x. `F4Options::max_live_bytes` and `FglmOptions::max_span_bytes`
  are the fix; see §5.2 for the figures and for what is reported rather than budgeted.
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
| **M20-C** | F4/Buchberger/quotient/FGLM over both fields; byte-accounted limits | **done** — the core needed no changes at all, as predicted; the end-to-end test passes over BN254. Byte accounting landed as three new budgets beside the existing entry ones, §5.2 |
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

### 5.2 M20-C's byte accounting, as landed

The defect §4.3 named: every memory budget in the Gröbner stack counted *representation entries*,
and an entry's size depends on the field. So one configuration meant different quantities of
memory at different field widths, and the wide field — the one the budget exists to protect
against — got the loosest one.

| budget | counts | 64-bit prime field | BN254 `Fr` | factor |
|---|---|---:|---:|---:|
| `F4Options::max_live_nonzeros` | `(usize, F)` entries | 16 B | 40 B | **2.5x** |
| `FglmOptions::max_operator_entries` | `(usize, F)` entries | 16 B | 40 B | **2.5x** |
| `FglmOptions::max_span_entries` | `F` cells | 8 B | 32 B | **4x** |

`max_operator_bytes` already existed beside the first of those, from M18-3. M20-C adds the other
two, in the same shape and for the same stated reason: **a second budget, never a redefinition.**
Changing what an entry budget counts would make every figure M16 and M18 recorded against it
ambiguous, which is a worse outcome than carrying two numbers.

```rust
pub struct F4Options {
    pub max_live_nonzeros: usize,   // 20,000,000
    pub max_live_bytes: usize,      // 320,000,000 — new
    // ...
}

pub struct FglmOptions {
    pub max_span_entries: usize,    // 20,000,000
    pub max_span_bytes: usize,      // 320,000,000 — new
    // ...
}
```

Both default to 320 MB, which is the quantity the entry budgets already described at 16 bytes an
entry. The consequence is that **the defaults are unchanged over a 64-bit prime field and tighten
over a wide one**, which is the whole intent:

| | entries admitted, 64-bit | entries admitted, BN254 |
|---|---:|---:|
| F4 live entries | 20,000,000 (320 MB) | **8,000,000** (320 MB), was 20,000,000 at 800 MB |
| FGLM span cells | 20,000,000 (160 MB) — cells bind | **10,000,000** (320 MB), was 20,000,000 at 640 MB |

Over a 64-bit field the F4 budgets are exactly equal, so the older `TooManyNonzeros` is still what
a crossing reports and no M16 figure changes meaning. The byte budget is reported —
`F4Error::TooManyLiveBytes`, `FglmError::SpanBytesExceeded` — only where it is the one that bound.

F4 collapses its two budgets to one entry allowance, `F4Options::live_entry_allowance::<F>()`,
rather than threading a second counter through construction and elimination. Two counters checked
in two places is two things to keep in step; one allowance cannot drift, and which budget produced
it is a property of the options rather than of the check.

#### What is reported rather than budgeted

The one place entries badly understate bytes is `Backend::Dense`, which densifies the matrix whole
and so allocates `rows * columns` cells however sparse it is. Katsura-7's largest grevlex matrix is
6810x6862: **374 MB of cells against roughly 22 MB of entries.** That is not charged to
`max_live_bytes`, deliberately — doing so would make the default refuse a computation the entry
budget admits, and under that backend the figure is a function of the shape alone, which the row and
column budgets already bound. It is reported instead, as
`F4Statistics::max_dense_buffer_bytes`, with `max_estimated_bytes` adding it to the entries per
batch and taking the maximum over batches.

So the accounting now distinguishes four things, which M21-C needs kept apart: mathematical
dimensions (`max_live_nonzeros`, `quotient_dimension`), representation entries and cells,
estimated allocated bytes (`peak_live_bytes`, `max_estimated_bytes`, `FglmMemory`), and measured
process RSS (`util::peak_resident_bytes`). None of the first three is a ceiling on the process.

### 5.3 How the dependencies actually ran

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
5. ~~**Byte-accounted resource limits**~~ — landed in M20-C (§5.2). Two new budgets beside the
   entry ones, `F4Options::max_live_bytes` and `FglmOptions::max_span_bytes`, both defaulting to
   the 320 MB the entry budgets already described at 16 bytes an entry. The `Backend::Dense`
   densification is reported rather than budgeted, and §5.2 says why.
6. ~~**Whether a generator is ever needed over a wide field.**~~ Resolved in D2 (#83): a
   *generator* is still never needed, but a *root of unity* is, and it needs no generator. The
   two-adic construction in `src/fields/two_adic.rs` derives s and the odd part of `q - 1` by
   shifting, then raises a non-square to the odd part — no factorization anywhere.
   `PrimeFieldElement256::root_of_unity` now serves any power-of-two order, so there is an NTT
   over both wide fields; `primitive_element` remains `unimplemented!()`, and a non-power-of-two
   order still panics. The two-adicity values this section quoted as a note — 28 for BN254, 32 for
   BLS12-381 — are now computed from the moduli and checked three ways, including against
   `ark_ff::FftField::TWO_ADICITY`. See [`docs/research/fast-univariate.md`](research/fast-univariate.md)
   §1, which also records what each univariate stage then costs against degree.

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

### M20-C

- [x] F4, Buchberger, the quotient algebra and FGLM all run over both target fields, with no
      wide-field fork of any of them — the core needed no changes at all (§1)
- [x] The complete F4 → quotient → FGLM → `solve_one` pipeline passes over BN254 and BLS12-381,
      with the returned point verified against the original system
- [x] Resource limits are byte-accounted: `F4Options::max_live_bytes` and
      `FglmOptions::max_span_bytes`, beside the entry budgets rather than redefining them (§5.2)
- [x] A budget means the same quantity of memory at every field width — asserted end to end, by
      running one system over a 64-bit field and over BN254 and checking that a byte budget sized
      for the first refuses the second while an entry budget admits both
- [x] The error names which budget bound, and the older `TooManyNonzeros` is still what a crossing
      reports wherever the two budgets are equal
- [x] Entry-count-to-byte conversion saturates rather than wrapping
- [x] What the budgets do **not** cover is reported rather than silently omitted —
      `F4Statistics::max_dense_buffer_bytes` for the dense backend's shape-determined allocation,
      which is 374 MB against 22 MB of entries on katsura-7 grevlex

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
