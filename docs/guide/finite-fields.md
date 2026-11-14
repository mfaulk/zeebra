# Finite fields

Prime fields from 31 to 255 bits, binary and extension fields, and what their arithmetic costs.

`PrimeFieldElement64<P>` holds elements in **Montgomery form** when `P` is odd and at least
2^32, storing `a * 2^64 mod P` rather than `a`. Below 2^32 it stores the canonical residue: the
product of two residues then fits a `u64`, whose remainder by a constant LLVM lowers to a
reciprocal multiply, and `P = 2^31 - 1` reduces by shift and add. That made `Zp2147483647`'s F4
call on MQ10 25% faster (#270; [the measurements](../research/field-arithmetic-specialization.md)). This is an internal representation and is not observable through
the public API: `value()`, `Display`, and the serialized form all give the canonical residue in
`[0, P)`, and the serialized bytes are unchanged by it.

The reason is that multiplication used to compute `(a as u128 * b as u128) % P as u128`. A
const-generic modulus does not save that — LLVM does not strength-reduce a 128-bit remainder, so
every field multiplication compiled to a call to `__umodti3`, compiler-rt's *software* 128-bit
division. Montgomery reduction replaces the division with two multiplications and a shift.

Two consequences worth knowing:

- `value()` is a Montgomery reduction, not a field read. A hot loop should hold field elements and
  convert at the boundary rather than call `value()` per iteration.
- `P = 2` is supported and takes the canonical path, because `2^64` is not invertible modulo
  an even number. The branch is on a const generic, so it is resolved at compile time.

`PrimeFieldElement128<P>` reduces a 256-bit product by allocating software long division, which
made it the slowest field in the crate — slower than one four times as wide. It is **deprecated**
rather than converted (#163); the paragraph after the table says why, and
[`Proth68Fr`](../../src/fields/prime_field_256.rs) is the replacement.
`cargo bench --bench field_arithmetic`, per operation:

| field | width | mul | add | sub | inverse |
|---|---:|---:|---:|---:|---:|
| `Mersenne31` | 31, in 4 bytes | 1.35 ns | 0.75 ns | 0.75 ns | **100 ns** |
| `Zp2147483647` | 31 | 1.76 ns | 1.10 ns | 0.95 ns | **124 ns** |
| `Zp18446744073709551557` | 64 | 1.71 ns | 1.05 ns | 0.97 ns | **236 ns** |
| `PrimeFieldElement128` — deprecated | 68 | **130.6 ns** | 2.10 ns | 1.90 ns | **17.84 µs** |
| `Bn254Fr` | 254 | 18.71 ns | 3.69 ns | 3.41 ns | 3.77 µs |
| `Bls12_381Fr` | 255 | 19.34 ns | 3.52 ns | 3.27 ns | 3.97 µs |

The `Zp2147483647` row predates #270's move off Montgomery form for moduli below 2^32 and has not
been re-measured through this bench; `examples/field_reduction` has the current per-kernel figures.
The three bold inversion figures are from #160 and replace 227, 246 and 509 ns. Those three fields
invert by Fermat, and Fermat went through a *recursive* `pow` when the trait already had the
iterative `pow_limbs` next to it — 2.0x to 2.3x for one line per field, with no change to the
result. The other three rows do not use that route and are unchanged;
`docs/MILESTONE-LARGE-PRIME-FIELDS.md` §4.1.1 has the before/after table, the controls, and why
replacing Fermat with binary extended Euclid measured *slower* at these widths.

Read the last three rows together: a 254-bit multiply is **7.0x faster** than the 68-bit one, and
10.9x slower than the 64-bit one. A claim about what field width costs has to say which baseline
it means. Inversion over a wide field is 202 multiplies, so pivot normalization should multiply by
a precomputed inverse rather than divide per entry.

### Why the 128-bit field is deprecated rather than converted

#163 asked whether to put `PrimeFieldElement128` into Montgomery form, and the question it asked
be settled first was: *is there a modulus between 2^64 and 2^128 that this crate wants to compute
over, which `PrimeFieldElement256` does not already serve better?* The answer is no.

The type has **no non-test caller** — its only consumers are the field conformance tests, the
`for_each_field!` arm, and the benchmark that measures how slow it is. And `PrimeModulus256` takes
its modulus as `[u64; 4]`, so any prime in that range is simply the low two limbs with the top two
zero. The one candidate justification was an NTT-friendly prime in the range, since `two_adicity`
is a property of the order rather than of the backing width; `Proth68Fr` is exactly that prime
(3*2^66 + 1, two-adicity 66) over `PrimeFieldElement256`.

Measured at `ece0d05`, `cargo bench --bench field_arithmetic` under `tools/benchlock.sh` with
`taskset --cpu-list 0-7`, one criterion process, 256 operations per iteration divided out. The
same modulus on both 68-bit rows, so the comparison is the representation alone:

| field | backing | mul | inverse |
|---|---|---:|---:|
| `Zp18446744073709551557` | 64-bit Montgomery | 1.81 ns | 274 ns |
| `PrimeFieldElement128` — deprecated | `u128`, long division | **136.8 ns** | **18.36 µs** |
| `Proth68Fr` — the replacement | 2-limb CIOS | **14.01 ns** | **847 ns** |
| `Bn254Fr` | 4-limb CIOS | 19.78 ns | 3.825 µs |

Same field, same modulus: **9.8x on multiplication and 21.7x on inversion**, for declaring it as
two limbs of a `PrimeModulus256` instead of a `u128`. `Proth68Fr` also beats `Bn254Fr` by 1.4x and
4.5x, which is what two CIOS limbs against four should do — so the "cost of width" really is a
cost of limbs, and the 68-bit field was never paying it.

The outer rows are **controls**: nothing in this change touches them, and they reproduce the table
above to within this machine's noise (1.81 against 1.71 ns, 19.78 against 18.71 ns), which is what
licenses reading the two middle rows against each other.

Deprecated rather than deleted, because the type is `pub`. The field laws still run over it, and
the `p68` bench row is kept beside the new `p68_mont` so the cost of a dividing multiply stays
visible as recorded history.

Two other field types gained the same treatment, each measured on the operation rather than on a
whole computation, because at the time both modules were private and no bench target could reach
them:

- `BinaryFieldElement<P>` multiplies with `PCLMULQDQ` and reduces by Barrett rather than by a
  bit-at-a-time loop and long division — **212.70 to 2.02 ns** per multiply over GF(2^63). The
  instruction is probed at run time, since it is not implied by the `x86-64-v3` floor, and the
  scalar fallback is kept and tested.
- `ExtensionFieldElement<P, N, M>` reduces once per output coefficient instead of once per partial
  product, O(N) instead of O(N^2), under a compile-time overflow bound; the per-multiplication heap
  allocation is gone.

Both are public now. `Gf32`, `Gf256`, `Gf13Pow4` and `Gf256Mq` are the declared instantiations.

**`Gf256` and `Gf256Mq` are both GF(2^8) and are not interchangeable.** `Gf256` reduces modulo
`x^8 + x^4 + x^3 + x + 1` (`0x11B`, the AES polynomial); `Gf256Mq` modulo
`x^8 + x^4 + x^3 + x^2 + 1` (`0x11D`), which is what the Fukuoka MQ Challenge specifies for its
GF(2^8) families. The two are isomorphic and the arithmetic differs: over the first
`0x57 * 0x83 = 0xc1` (FIPS-197 §4.2), over the second it does not, and more than fifty thousand of
the 65025 nonzero operand pairs separate them. An order check cannot tell them apart — both have
order 256 — so the field is named at the type level rather than inferred.
The Fukuoka MQ Challenge files use the second, which is why an importer for them must name it.

**An integer names an element of an extension field in two different ways, and the API keeps them
apart.** `FiniteField::new` is the image of an integer under the unique ring homomorphism from the
integers — `val mod p` — so over an extension it only ever reaches the prime subfield, and walking
it over `0..q` is not an enumeration. `KnownOrder::element_at` is the bijection from `0..q`, and
`FiniteField::from_str` reads the text `Display` writes, which is the coefficient bit pattern over
GF(2^m) and the bracketed coefficient list over GF(p^k):

```rust
use zeebra::{fields::{Gf13Pow4, Gf256}, FiniteField, KnownOrder, One};

// `new` is the embedding: 5 copies of one, which in characteristic two is one.
assert_eq!(<Gf256 as FiniteField>::new(5), Gf256::one());

// `from_str` is the representation, and inverts `Display`.
let x2_plus_1 = <Gf256 as FiniteField>::from_str("5").unwrap();
assert_eq!(x2_plus_1.to_string(), "5");
assert_eq!(Gf256::element_at(5), Some(x2_plus_1));

// Out of range is a `Result`, not a panic.
assert!(<Gf256 as FiniteField>::from_str("256").is_err());

// Over GF(13^4) a bare decimal is the base-13 digits; `Display`'s own form reads back too.
assert_eq!(
    <Gf13Pow4 as FiniteField>::from_str("170").unwrap().to_string(),
    "[1, 0, 1, 0]",
);
assert_eq!(
    <Gf13Pow4 as FiniteField>::from_str("[1, 0, 1, 0]"),
    <Gf13Pow4 as FiniteField>::from_str("170"),
);
```

`element_at`'s default is `new`, which is that bijection exactly when `q = p`, and returns `None`
for every index over a field whose order and characteristic differ — so a field that has not
overridden it reports that it cannot be enumerated rather than enumerating its prime subfield and
returning a count that is wrong rather than failed.

## Characteristic two in the solver, and field equations

The Gröbner stack is generic over `FiniteField` and had never been run in even characteristic. It
works: `grobner::tests::test_the_whole_pipeline_over_gf2` and its `Gf256` twin take a planted
system through F4, agreement with Buchberger, FGLM, both routes to lex, and `solve_one`, with the
recovered point re-evaluated against the original system. Neither needed a change to the solver.

One trap, asserted rather than described. `benchmark_systems::planted` **degenerates in
characteristic two**: its first generator per variable pair is `x^2 + y^2 - (a^2 + b^2)`, and since
`x^2 + y^2 = (x + y)^2` here that is a perfect square, so the ideal is nonradical. A reader who
assumed the generator behaves the same in every characteristic would mis-read every
characteristic-two measurement taken with it, so
`grobner::tests::test_planted_degenerates_to_a_square_in_characteristic_two` pins it.

A system over `F_q` has two different solution sets — the points of the variety over the algebraic
closure, and the points with coordinates in `F_q` itself. Cryptanalysis asks for the second, which
is cut out by adjoining the field equations `x_i^q - x_i`:

```rust
use zeebra::{
    fields::Zp2,
    grobner::{classify_ideal, f4, field_equations::with_field_equations, IdealClass},
    MonomialOrder, Monomial, MultivariatePolynomial, One,
};

let grevlex = MonomialOrder::GradedReverseLexicographic;

// x*y, in two Boolean variables: positive-dimensional over the closure.
let system: Vec<MultivariatePolynomial<2, Zp2>> =
    vec![MultivariatePolynomial::new(&[(Monomial::new(&[1, 1]), Zp2::one())])];
let bare = f4(&system, grevlex).unwrap();
assert_eq!(classify_ideal(&bare, grevlex), IdealClass::PositiveDimensional);

// Adjoining x^2 - x per variable forces zero dimension.
let extended = with_field_equations(&system).unwrap();
let basis = f4(&extended, grevlex).unwrap();
assert_eq!(classify_ideal(&basis, grevlex), IdealClass::ZeroDimensional);
```

Because `x^q - x` is squarefree and splits completely over `F_q`, the extended ideal is **radical**,
so `dim F_q[x]/I` is exactly the number of `F_q`-rational points — counted once each, however many
times they occur in `I`. That makes a solution count a machine-independent invariant, and
`field_equations`' tests check it against exhaustive enumeration at `n = 8` over GF(2).

**Adjoining them is a judgement about `q`, not a default, and nothing here chooses for the caller.**
The generator has degree `q`, so it only pays when `q` is below the degree the computation would
reach anyway. Over GF(2) that is degree 2 and the answer is essentially always yes. Over GF(31) —
Fukuoka MQ types III and VI — it is degree 31 against measured solving degrees of 4 to 9, so the
answer is no. Over GF(65521), the Courtois MinRank challenge field, degree 65521 is absurd.
`field_equations` refuses outright only when `q` exceeds a monomial exponent, which is a
representation limit rather than a policy.

The *solving* half is covered end to end over both characteristic-two fields by
`tests/boolean_readiness.rs`. Over GF(2), `fglm_to_lex` converts the field-equation ideal and
`solve_zero_dimensional` returns **exactly** the point set an exhaustive walk of all 256 assignments
finds — no dropped solution and none invented over an extension. Over GF(2^8) the degree-256
equations are usable rather than merely representable, and `roots` works, which exercises the
characteristic-two trace splitter at `m = 8` where every earlier test had `m = 1`.

Three caveats a caller should know, each asserted rather than described:

- **GF(2) is `Zp2`, not `BinaryFieldElement<0b11>`.** The two are the same field — the full operation
  tables agree — but `Zp2` is 4 bytes to the other's 8 and needs no carry-less multiply for a field
  where multiplication is `and`.
- **A GF(2^8) coefficient is written as its bit pattern.** `MultivariatePolynomial::parse` works over
  `Gf256`, reading each decimal `0..255` as the coefficient bit pattern `Display` writes — so
  `from_str` inverts `Display` over every field, and over an extension it is deliberately not
  `FiniteField::new`, which only ever reaches the prime subfield. `KnownOrder::element_at` is the
  route that enumerates all `q` elements. #377.
- **Omitting the field equations is diagnosed on both routes, but the default route pays to find
  out.** `SolveStrategy::GrevlexF4ThenFglm` classifies the basis it already has; the default
  `DirectLexF4` exhausts a Macaulay-matrix budget first, and only then computes a grevlex basis to
  tell a crossed budget from a positive-dimensional ideal. Both report `PositiveDimensional`, whose
  remedy is `with_field_equations` rather than a larger limit, and a zero-dimensional ideal that
  really is out of budget still reports a *resource* failure. #376.

[`docs/research/boolean-solving.md`](../research/boolean-solving.md) is the readiness write-up:
what runs in characteristic two, what does not and why, and the Singular oracle's position (it has
covered GF(2) all along — 40 of the 240 committed differential fixtures are at characteristic 2 —
and is prime-field only, so there is no GF(2^8) oracle yet: #378).

## A 32-bit prime field

`PrimeFieldElement32<P>` is the same field as `PrimeFieldElement64<P>` for any modulus both can
hold, in half the bytes. Montgomery form with R = 2^32, the representation unobservable in the same
two ways; the one place the arithmetic is not a mechanical substitution is that `t + m*P` needs 65
bits only when P exceeds 2^31, and that predicate is on the const generic, so every declared
modulus gets a reduction with no carry handling in it.

```rust
use zeebra::{fields::{BabyBear, Mersenne31, Zp2147483647}, FiniteField, KnownOrder};

assert_eq!(std::mem::size_of::<Mersenne31>(), 4);
assert_eq!(std::mem::size_of::<Zp2147483647>(), 8);
assert_eq!(Mersenne31::order_u128(), Zp2147483647::order_u128());

let a = Mersenne31::new(827376);
assert_eq!(a.pow(2).value(), 1651245630);   // the canonical residue, not the Montgomery form
assert_eq!(BabyBear::order_u128(), Some(2013265921));
```

Declared: `Zp2` (GF(2) — Fukuoka MQ types I and IV, LowMC, HFE), `Zp31` (Fukuoka MQ types III and
VI), `Zp32003` (the cross-library corpus's small-prime reference characteristic, and the field every
published Gröbner timing table uses), `Zp65537_32`, `Mersenne31`, `BabyBear` (`2^31 - 2^27 + 1`) and
`KoalaBear` (`2^31 - 2^24 + 1`, the 2026 Poseidon challenge prime). The two Bear fields are NTT-friendly;
`Zp65537_32` and `Zp2147483647` are the same mathematical fields as `Zp65537` and `Mersenne31`'s
64-bit twin, so a caller picks a width rather than a field. `Zp2` is the one declared modulus that
is not odd, so it keeps the wide-remainder path rather than reaching Montgomery form.

**What it is worth, and where.** `cargo run --release --example field_width`. The kernel is
`target -= factor * source` with the nonzero counters the dense backend maintains, at a fixed
*entry* count so that both widths do the same number of cell updates:

| working set (u32/u64) | u64 ns/entry | u32 ns/entry | u32 GB/s | AVX2 8 lanes | AVX2 GB/s |
|---|---:|---:|---:|---:|---:|
| 8 / 16 KB | 1.802 | 0.765 | 15.7 | **0.264** | 45.4 |
| 256 / 512 KB | 1.770 | 0.751 | 16.0 | **0.253** | 47.5 |
| 16 / 32 MB | 1.783 | 0.753 | 15.9 | **0.262** | 45.8 |
| 128 / 256 MB | 1.897 | 0.786 | 15.3 | **0.446** | 26.9 |

Two things in that table correct the premise it was built on. **The scalar kernel is ALU-bound at
both widths, not bandwidth-bound**: ns/entry is flat to within 7% over a working set spanning four
orders of magnitude — the 256 MB row re-ran at 1.804 — and 15.9 GB/s is well under what one core
can pull. So the 2.36x is not
halved bytes — it is that a 64-bit Montgomery reduction is 128-bit arithmetic that does not
vectorize, and a 32-bit one is 64-bit arithmetic that does. **Only the AVX2 kernel is fast enough
for the bytes to bind**, and it is where halving them pays: 45 GB/s in cache falling to 26.9 GB/s
out of it, which at 24 bytes an entry would have been 0.89 ns rather than 0.446.

That also reverses M19-D's answer. At four lanes over `u64` hand-written AVX2 ran 0.86x to 1.07x
against autovectorization; at eight lanes over `u32` it runs **1.7x to 3.0x**, against a scalar
comparand LLVM did vectorize (`vpmuludq` present in both, verified in the artifact). No intrinsics
are shipped — the kernel lives in the example, cross-checked cell for cell and counter for counter
against the scalar one — but the question is no longer closed.

Whole eliminations, same matrices at both widths:

| | u64 | u32 | ratio |
|---|---:|---:|---:|
| dense echelon, 1500x1500 at 5% | 2515.6 ms, 17.2 MB | 882.9 ms, 8.6 MB | 2.85x |
| dense echelon, 3000x3000 at 2% | 19789.6 ms, 68.7 MB | 6868.0 ms, 34.3 MB | 2.88x |
| F4 elimination, katsura-6 grevlex, `Backend::Dense` | 70.78 ms | 25.27 ms | 2.80x |
| F4 elimination, katsura-6 grevlex, `Backend::Sparse` | 35.03 ms | 25.90 ms | 1.35x |
| F4 elimination, katsura-6 grevlex, `Backend::Adaptive` | 6.60 ms | 6.41 ms | 1.03x |

**The last row is why no benchmark switched its field.** `Backend::Adaptive` is what
`F4Options::default()` selects and it is 4x faster than the dense backend at either width, so it is
the configuration that matters — and it gains nothing, because its cost is sparse-index traversal
and scatter/gather into a buffer rather than cell traffic. The sparse backend gains little for a
related reason: a sparse entry is `(usize, F)`, which the index's alignment pads to **16 bytes at
either width**, so sparse storage does not shrink at all and `F4Options::live_entry_allowance` is
unchanged. The narrower field is a 2-3x win on the dense path, a memory halving wherever cells are
stored bare, and the enabler for eight-lane SIMD. It is not a free 2x on F4 as shipped.

The dense entry-budget conversion in `linalg::dense::rows` does move, and not by the factor a
reader would guess: `cells_per_entry` goes from two to **four**, since the entry cost is pinned at
16 bytes by the index while the cell cost halves.

## 254- and 255-bit prime fields

`PrimeFieldElement256<M>` is the scalar field of a pairing-friendly curve, held in Montgomery form
over four 64-bit limbs — CIOS multiplication, binary extended Euclid inversion, and `R mod p` /
`R^2 mod p` as compile-time constants. Two fields are provided:

```rust
use zeebra::{fields::{Bls12_381Fr, Bn254Fr}, FiniteField, KnownOrder, One};

let a = <Bn254Fr as FiniteField>::from_str("123456789012345678901234567890").unwrap();
assert_eq!(a * a.inverse(), Bn254Fr::one());

// The order does not fit in a machine integer, which is why `KnownOrder` reports limbs.
assert_eq!(Bn254Fr::order_u128(), None);
assert_eq!(Bn254Fr::order_limbs().len(), 4);
assert_eq!(Bls12_381Fr::order_limbs().len(), 4);
```

The modulus arrives through the `PrimeModulus256` trait rather than a const generic, because a
const generic parameter cannot be 256 bits wide — the same device `IrreduciblePolynomial` already
uses for extension fields. A new field is its modulus limbs and nothing else:

```rust
use zeebra::fields::{PrimeFieldElement256, PrimeModulus256};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
struct MyModulus;

impl PrimeModulus256 for MyModulus {
    // Must be an odd prime: R = 2^256 is not invertible modulo an even number.
    const MODULUS: [u64; 4] = [0xffffffff00000001, 0x53bda402fffe5bfe,
                               0x3339d80809a1d805, 0x73eda753299d7d48];
}

type MyField = PrimeFieldElement256<MyModulus>;
```

Any odd prime up to 256 bits works, not only one that fills all four limbs. A narrower modulus
leaves its high limbs zero, and the bit width that `new` and `random` depend on is derived from the
highest occupied limb rather than assumed — the tests cover moduli at one, two, three and four
limbs, with GF(7) checked exhaustively against `PrimeFieldElement64<7>`. Below 2^128 the order
fits a machine integer again, so `KnownOrder::order_u128` starts returning `Some`.

`BN254_FR_MODULUS_DECIMAL` and `BLS12_381_FR_MODULUS_DECIMAL` are public so the compiled-in limbs
can be checked against the published values, which the module's own tests do.

What the representation means for a caller:

- `canonical_limbs()`, `to_bytes_le()` and `Display` are Montgomery reductions, not field reads.
  Hold field elements in a hot loop and convert at the boundary.
- Serialization and `to_bytes_le` emit the **canonical residue**, never the stored Montgomery
  value, so an encoding does not depend on an internal representation choice.
- `from_canonical_limbs` and `try_from_bytes_le` **reject** an input at or above the modulus, as
  does deserialization. `from_limbs_reduced` is the separately named constructor that reduces.
- `random` is masked rejection sampling. Reducing a uniform 256-bit draw modulo a 254-bit prime
  would favour the low residues.
- `try_primitive_element` returns `Err(RootOfUnityError::NoKnownGenerator)`: finding a generator of
  the multiplicative group means factoring a 254-bit `q - 1`, which no algorithm here needs and
  which should not start by accident. `try_root_of_unity` works for any **power-of-two** order,
  through the two-adic construction below, and refuses any other — that order is the one that
  needs the factorization. Its `n: u64` names no order above `2^63`, so over a modulus of
  two-adicity beyond 63 the higher power-of-two roots are reachable only through
  `try_two_adic_root_of_unity`, which takes `log_n: u32`.

## A generator under an explicit effort budget

`try_primitive_element` has nowhere to put an effort bound, so it still declines. The opt-in entry
point is `try_primitive_element_with_budget::<F>(&EcmBudget, rng)`, which factors `q - 1` with
Lenstra ECM (`integers::factor_with_budget`) and either returns a generator certified against the
**complete** factorization or reports the cofactors the budget could not split:

```rust
use zeebra::{
    fields::{try_primitive_element_with_budget, Bls12_381Fr, Bn254Fr, GeneratorSearchError},
    integers::EcmBudget,
};
use rand::{prelude::StdRng, SeedableRng};

let mut rng = StdRng::seed_from_u64(5);

// BLS12-381's r - 1 = 2^32 * 3 * 11 * 19 * 10177 * 125527 * 859267 * 906349^2 * 2508409
//                     * 2529403 * 52437899 * 254760293^2 — nine decimal digits at worst.
let g = try_primitive_element_with_budget::<Bls12_381Fr, _>(&EcmBudget::for_digits(9), &mut rng);
assert!(g.is_ok());

// BN254's r - 1 has a 29-digit prime factor, past what this ECM reaches. The honest answer names
// what a larger budget would have to split.
let refused = try_primitive_element_with_budget::<Bn254Fr, _>(&EcmBudget::for_digits(9), &mut rng);
assert!(matches!(
    refused,
    Err(GeneratorSearchError::IncompleteFactorization { .. })
));
```

**The cost is not a function of the field's width.** Both fields above are 255 bits and they land on
opposite sides of this, because what the search pays for is the largest prime factor of `q - 1` and
not the size of `q`. So the budget is the caller's to choose, and a budget that does not finish is
an error rather than a weaker guarantee — a partial factorization cannot certify a generator,
since an untested prime divisor is one whose quotient the candidate might fix.

The search itself is HAC Algorithm 4.80, the same one `KnownOrder::try_primitive_element`'s default
runs, lifted off `u128` exponents onto `FiniteField::pow_limbs` so that it reaches a field whose
order a `u128` cannot hold. It is generic over `KnownOrder`, so it is not limited to the 256-bit
fields; it is simply the only place the refusal was load-bearing.

The whole stack works over these fields, not just the arithmetic:
`grobner::mod`'s `test_the_whole_pipeline_over_bn254_fr` and its BLS12-381 twin take a planted
zero-dimensional system through F4, check the basis against Buchberger's criterion, convert to lex
with FGLM, compare that against a direct lex F4, and then recover a solution with `solve_one` and
re-evaluate it against the original system.

Root finding over a wide field works because `pow_mod_limbs` takes its exponent as little-endian
limbs rather than a `u128`; `roots` passes `F::order_limbs()` straight through. `pow_mod` is now a
thin wrapper over it and is unchanged for callers.

The arithmetic is checked against `ark-ff` as a **dev-dependency oracle**, in the role Singular
already plays for Gröbner bases: 20,000 random cases per field on add, sub, mul, square, negate,
invert and divide, plus the edge residues. Nothing third-party is in the shipped crate.

## `FiniteField` and `KnownOrder`

A coefficient type implements `FiniteField`: arithmetic, inversion, parsing, uniform sampling,
`new`, and exponentiation by a `u128`. The field's *order* is not there. It lives in a separate
trait:

```rust
use zeebra::{fields::Zp2147483647, KnownOrder};

assert_eq!(Zp2147483647::order_limbs(), &[2147483647]);
assert_eq!(Zp2147483647::order_u128(), Some(2147483647));
```

`KnownOrder` gives the order q and the characteristic p as little-endian 64-bit limbs — a width
that covers 64-, 128- and 256-bit orders without allocating — plus `order_u128` and
`characteristic_u128` for callers that need a machine integer and can fail without one, plus
`primitive_element`, `root_of_unity`, `two_adicity`, `two_adic_root_of_unity`, the predicates
`is_generator` and `is_primitive_nth_root`, and `sqrt`. For an extension field q = p^k, so the
order and the characteristic are genuinely different; both are reported.

Constructing a generator or a root of unity **fails as a value**. Whether `n` divides `q - 1`, and
whether a field has a generator this crate will look for **without being asked**, are facts about
the field and the requested order rather than programmer errors, so `try_primitive_element`,
`try_root_of_unity` and `try_two_adic_root_of_unity` return `Result<Self, RootOfUnityError>`.
`NoKnownGenerator` is a statement about what the trait method will start unprompted, not about the
field: `try_primitive_element_with_budget` is the opt-in route, and the 256-bit-field section above
has the two cases it separates. The failures as values:

```rust
use zeebra::{fields::{RootOfUnityError, Zp13}, KnownOrder};
use rand::{prelude::StdRng, SeedableRng};

let mut rng = StdRng::seed_from_u64(1);

// 6 divides 12, so Z/13 holds an element of order exactly 6.
let w = Zp13::try_root_of_unity(6, &mut rng).expect("6 divides q - 1");
assert!(w.is_primitive_nth_root(6, &mut rng));

// 5 does not.
assert_eq!(
    Zp13::try_root_of_unity(5, &mut rng),
    Err(RootOfUnityError::OrderDoesNotDivide { n: 5 }),
);
```

The names without `try_` are kept as thin panicking wrappers, so existing call sites are
unchanged; the fallible form is the one an implementation overrides. `is_generator` needs the
factorization of `q - 1` and so is fallible for the same reason, while `is_primitive_nth_root`
factors only `n` and therefore works over the 254-bit fields — which is what makes it the
independent check on the two-adic construction rather than a restatement of it.

### Square roots, and which elements have one

`sqrt` is Tonelli-Shanks, and one implementation covers every field in the crate because what
changes between them is the two-adicity of `q - 1` rather than the algorithm:

```rust
use zeebra::{fields::{legendre_symbol, Zp65537}, FiniteField, KnownOrder};
use rand::{prelude::StdRng, SeedableRng};

let mut rng = StdRng::seed_from_u64(1);
let x = Zp65537::new(7);

match x.sqrt(&mut rng) {
    Some(r) => assert_eq!(r * r, x),
    None => assert_eq!(legendre_symbol(&x), -1),
}
```

`legendre_symbol` is Euler's criterion: 0 on zero, 1 on the squares, -1 on the rest. Over a prime
field it is the Legendre symbol; over an extension field of odd characteristic it is the same
character on the larger group. In characteristic two squaring is a bijection, so every element is a
square and the root is `x^(q/2)` — a different computation, reached by the same call.

With `q = 3 (mod 4)` the two-adicity is 1, Tonelli-Shanks degenerates to the single exponentiation
`a^((q+1)/4)`, and no random element is consumed at all; the rng is drawn from only to find a
quadratic non-residue, which only the correction loop needs. Of the two roots `±r`, which one is
returned is unspecified.

`integers::jacobi_symbol` is the integer counterpart, by the binary algorithm, so it needs no
factorization. For prime `n` it agrees with `legendre_symbol` on the same residue — two
computations sharing no code, which is how each is checked — and for composite `n` it is not a
residue test at all: `(2/15) = 1` though 2 is not a square mod 15.

The split is there because a 254-bit prime field has no order that fits in a machine integer, and
because **nothing in the algebraic core asks for one**: the multivariate polynomials, the linear
algebra, F4, FGLM and Buchberger are all generic over `FiniteField` alone. Only root finding,
factorization and enumerating the field itself need `KnownOrder`, and they say so in their bounds.
`grobner::mod`'s `test_the_grobner_stack_needs_no_field_cardinality` fails to compile if that
stops being true.

Every field type in the crate implements both traits. Two consequences for anything generic over
`F: FiniteField`:

- `F::order()` and `F::characteristic()` are gone. Add `F: KnownOrder` and call `order_limbs()`,
  or `order_u128()` where the old `u128` is what you want.
- `inverse()` is a required method rather than a provided one. Its only sensible default was
  `a^(q-2)`, which needs the order — and the order is in `KnownOrder`, not here. A field that has
  one writes Fermat as `pow_limbs` over a `q - 2` subtracted on the limbs, so no width caps that
  route; a field without one, or with a faster inversion, writes its own.

`docs/MILESTONE-LARGE-PRIME-FIELDS.md` records the audit this came out of.

## Batch inversion

Inversion is the most expensive operation a prime field has. `batch_invert` and `batch_inverse`
apply Montgomery's trick — prefix products turn n inversions into **one** inversion and `3(n-1)`
multiplications:

```rust
use zeebra::{fields::{batch_inverse, batch_invert, Bn254Fr}, FiniteField, One, Zero};

let values = [Bn254Fr::new(3), Bn254Fr::zero(), Bn254Fr::new(5)];
let inverses = batch_inverse(&values);

// Each nonzero element is inverted...
assert!((values[0] * inverses[0]).is_one());
assert!((values[2] * inverses[2]).is_one());
// ...and a zero is left as zero rather than panicking.
assert!(inverses[1].is_zero());

// The in-place form, for a vector you already own.
let mut owned = vec![Bn254Fr::new(7); 4];
batch_invert(&mut owned);
assert!(owned.iter().all(|x| (*x * Bn254Fr::new(7)).is_one()));
```

**A zero is left as zero.** A batch comes from a container, and a container of field elements may
legitimately hold zeros, so panicking would make the routine unusable where it is most wanted.
`FiniteField::inverse` keeps its panic because there the caller named the one element it was asking
about.

The crossover is **n = 2** in every field; a single-element batch loses by a few percent to the
copy. The plateau is the ratio between an inversion and three multiplications, so it tracks
whatever inversion costs — and #160 halved inversion over the fields that invert by Fermat.
`field_arithmetic`'s `isolated/inverse` against its `batch/inverse` over the same 256 operands,
before and after #160: **29.6x to 14.8x** over `Mersenne31`, **54.6x to 27.6x** over the largest
64-bit prime, against **60.4x to 60.7x** over BN254 `Fr`, which does not use that route and holds
still. Montgomery's trick still wins by more than an order of magnitude everywhere; it has less to
beat. `docs/research/batch-inversion.md`'s table predates #160 and is its own instrument, so read
its Mersenne-31 and Goldilocks columns as roughly halved rather than substituting these figures
for them.

`FFTDomain::inverse` is where it is wired in, and `fft::interpolate` additionally hoists the one
`1/n` it used to compute per coefficient. Together those make the inverse transform cost what the
forward transform costs; see "Number-Theoretic Transform" below and
[`docs/research/batch-inversion.md`](../research/batch-inversion.md) for the measurements and for
why F4's pivot normalization is deliberately *not* batched.
