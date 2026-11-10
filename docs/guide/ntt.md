# Number-theoretic transform and univariate arithmetic

The NTT over prime fields, the sizes it supports, and the univariate operations built on it —
multiplication, division, evaluation, interpolation and root finding.

`fft::evaluate` and `fft::interpolate` are the forward and inverse transforms over an `FFTDomain`
of any size `n`, built from a primitive `n`th root of unity. At a power-of-two size — the common
case, and the fast one — both are the same iterative in-place radix-2 kernel — a bit-reversal permutation followed by `log n` passes of butterflies over the
domain's own powers, read with a stride — so there is no recursion, no per-level allocation, and
one twiddle multiplication per two outputs. `interpolate` is that kernel over the batch-inverted
domain, scaled by `1/n`. Any other size is decomposed into coprime factors first; see
[Sizes that are not a power of two](#sizes-that-are-not-a-power-of-two).

**`1/n` is where the inverse transform can be ill-posed, and it is refused by name.** In
characteristic `p` the scalar `n` is zero whenever `p | n`, so `1/n` does not exist and no inverse
transform of that length is defined — over `GF(2^m)` that is every even size. A domain built from a
primitive root never has this problem, since an `n`th root of unity needs `n | q - 1`; the
unchecked `FFTDomain::new` is the route that reaches it. `try_interpolate` returns
`InterpolateError::SizeNotInvertible` there and `interpolate` panics with the same message, rather
than failing deeper down with "the zero element does not have a multiplicative inverse", which named
the symptom and not the cause ([#396](https://github.com/mfaulk/zeebra/issues/396)). Over `GF(2^m)`
an odd size works: `Gf256`'s group order is `255 = 3 * 5 * 17`, so it hosts 3-, 5-, 15-, 17-point
transforms and no even one at all.

**The transform zero-pads internally.** A polynomial of any degree below `n` is extended to the
domain size inside `evaluate`, so a caller hands over unpadded operands and chooses only `n` — the
domain size is the caller's because only the caller knows how large a result it needs. A polynomial
of degree `n` or more still panics: `n` evaluations cannot determine it. That stays a panic rather
than becoming a `DomainError`-style typed failure because of where #120 drew that line — a fact
about the field is a value, a programmer error is a panic, and a caller that supplied both the
polynomial and the domain already knows whether `deg(p) < n`. The transform also panics on a domain
that is not the powers of a *primitive* `n`th root of unity: `try_from_generator` rejects those, but
`FFTDomain::new` takes a vector of powers unchecked and `FFTDomain::split` returns domains that are
not power sequences at all.

Over a 254-bit field there was no way to obtain one: the generic construction raises a *generator*
of the multiplicative group to `(q - 1) / n`, and finding a generator means factoring a 254-bit
`q - 1`. The two-adic construction needs no generator. Writing `q - 1 = 2^s * m` with m odd — both
read off `q - 1` by shifting — the 2-Sylow subgroup is cyclic of order `2^s`, and `z^m` generates it
for any non-square z, which half the field is:

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    evaluate, fields::Bn254Fr, interpolate, FFTDomain, KnownOrder, Polynomial,
    UnivariatePolynomial,
};

// Derived from the compiled-in modulus, so it cannot disagree with the field.
assert_eq!(Bn254Fr::two_adicity(), 28);

let mut rng = StdRng::seed_from_u64(1);
// A primitive 8th root of unity. `root_of_unity(8, &mut rng)` reaches the same construction.
let w = Bn254Fr::two_adic_root_of_unity(3, &mut rng);
let domain = FFTDomain::from_generator(w, 8);

let p = UnivariatePolynomial::<Bn254Fr>::rand(7, &mut rng);
let values = evaluate(&p, &domain);
assert_eq!(interpolate(&values, &domain), p);
```

`two_adicity()` is the ceiling on every power-of-two transform over the field, since a primitive
`2^k`-th root of unity exists exactly for `k <= s`:

| field | s | largest transform |
|---|---|---|
| `Mersenne31` / `Zp2147483647` — `2^31 - 1` | **1** | 2 |
| `KoalaBear` — `2^31 - 2^24 + 1` | 24 | 2^24 |
| `BabyBear` — `2^31 - 2^27 + 1` | 27 | 2^27 |
| `Zp18446744069414584321` — Goldilocks | 32 | 2^32 |
| `Bn254Fr` | 28 | 2^28 |
| `Bls12_381Fr` | 32 | 2^32 |

`two_adicity` is a provided method on `KnownOrder`, so it reads the same from a 32-bit, 64-bit or
254-bit backing; `Mersenne31` and `Zp2147483647` are the same field at two storage widths and
report the same s.

**Mersenne-31 admits no power-of-two transform above size two**, which matters because it is the
field most of this crate's F4 benchmarks use. `BabyBear` and `KoalaBear` — the latter being the
prime the 2026 Poseidon challenges are over — are NTT-friendly by construction and are what to
reach for when a transform is wanted over a small field. Sizes drawn from the *odd* part of `q - 1`
are a separate matter and are available on Mersenne-31 too, as the next section shows.

`FiniteField::pow_limbs` takes its exponent as little-endian limbs, which is what makes the above
possible at all: the odd part of BN254's `q - 1` is 226 bits, so `pow`'s `u128` cannot hold it.

## Sizes that are not a power of two

A size `n` with `n | q - 1` needs no padding, whatever its factorization:

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    evaluate, fields::PrimeFieldElement64, interpolate, FFTDomain, KnownOrder, Polynomial,
    UnivariatePolynomial,
};

// 65520 = 2^4 * 3^2 * 5 * 7 * 13, so this field hosts a domain of size 12, 105, 2520, ...
type F = PrimeFieldElement64<65521>;

let mut rng = StdRng::seed_from_u64(125);
let w = F::root_of_unity(12, &mut rng);
let domain = FFTDomain::from_generator(w, 12);

let p = UnivariatePolynomial::<F>::rand(11, &mut rng);
let values = evaluate(&p, &domain);
for (i, value) in values.iter().enumerate() {
    assert_eq!(*value, p.eval(&domain[i]));
}
assert_eq!(interpolate(&values, &domain), p);
```

The decomposition is **prime-factor (Good–Thomas)**: for `n = n1 * n2` with `gcd(n1, n2) = 1`,
re-indexing the input by the Chinese remainder isomorphism `Z/n = Z/n1 x Z/n2` turns the length-`n`
DFT into a 2-D transform of `n1`- and `n2`-point DFTs **with no twiddle factors between the
stages** — the entire cost of the split is two permutations. Writing `i = i1 (mod n1)`,
`i = i2 (mod n2)` and `k = k1*n2 + k2*n1 (mod n)`:

```text
w^(i k) = w^(n2 i k1) * w^(n1 i k2) = w_n1^(i1 k1) * w_n2^(i2 k2)
```

since `w_n1 = w^n2` has order `n1` and so only sees its exponent modulo `n1`. Each axis is then
dispatched the same way, recursively, and what it costs depends on the factor:

| factor | route | cost of that stage |
|---|---|---|
| a power of two | the radix-2 kernel | `n log n_i` |
| composite with coprime parts | recurse | — |
| an odd prime power (9, 25, 27) | the `O(m^2)` definition | `n * n_i` |

So `2520 = 2^3 * 3^2 * 5 * 7` costs `n log 8` plus `n * (9 + 5 + 7)`, which is why a size whose
odd factors are small is cheap and **a large prime size is quadratic through this route**.
[Bluestein](#bluestein-a-large-prime-size-without-the-quadratic-cost) is what removes that case,
and since #375 the dispatcher **does** reach it on its own — above a measured size, and for a
domain that was prepared to. See below for what preparing means and why it is a property of the
domain rather than a bound on the transform.

Two consequences of allowing any size, both visible in the API:

- `DomainError::SizeNotPowerOfTwo` is gone, since the size is no longer a reason to refuse. A
  domain is refused only when the generator does not have order exactly `n` (`NotAnNthRoot`,
  `NotPrimitive`) or the size is zero (`SizeZero`). Primitivity now costs one `g^(n/p)` check per
  distinct prime `p | n` rather than the single `g^(n/2)`; a root of order 6 at `n = 12` satisfies
  `g^6 != 1` and would otherwise have been accepted.
- `FFTDomain::split` — the radix-2 even/odd split — panics on an odd size, where the halves would
  not be the same length.

## Bluestein: a large prime size without the quadratic cost

Bluestein's algorithm turns a length-`n` transform into a **convolution**, which the radix-2 kernel
runs at a padded power-of-two length. It is `O(n log n)` at every size, prime included, so it is
what the quadratic row of the table above gives way to.

The textbook identity is `jk = (j^2 + k^2 - (k - j)^2) / 2`, whose halved squares need a `2n`-th
root of unity to write down. This uses the **triangular numbers** `T(m) = m(m - 1) / 2` instead:

```text
T(j) + T(k) - T(k - j) = jk - j,     so     jk = T(j) + j + T(k) - T(k - j)
```

giving

```text
X_k = w^T(k) * sum_j (x_j w^(T(j) + j)) * w^(-T(k - j)).
```

Every exponent is an integer and every factor is a power of the `n`th root the caller already
holds, so there is no second root to construct, validate, or fail to find. Nothing is lost by it:
for odd `n`, `n | q - 1` already implies `2n | q - 1`, and for even `n` the convolution length
needs two-adicity at least `log2(n) + 1` — because `2n - 1` is odd and above one, so it is not a
power of two and `L >= 2n` — which is never less than the `2n`-th root's own `v2(n) + 1`. A field
that can host the convolution always has a `2n`-th root; one that cannot never gets far enough to
want it.

So the convolution length is the single demand on the field, and `bluestein_convolution_domain`
is where it is either met or reported:

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    bluestein_convolution_domain, bluestein_convolution_length, bluestein_transform,
    fields::KoalaBear, FFTDomain, FiniteField, KnownOrder, Zero,
};

// KoalaBear: q - 1 = 2^24 * 127, so 127 is a size this field has a root of unity for — and the
// one the prime-factor route would spend 127^2 multiplications on.
type F = KoalaBear;
let n = 127;

let mut rng = StdRng::seed_from_u64(127);
let domain = FFTDomain::from_generator(F::root_of_unity(n as u64, &mut rng), n);

// The convolution runs at the least power of two at or above 2n - 1, so that the cyclic
// convolution does not alias the two ends of the chirp onto each other.
assert_eq!(bluestein_convolution_length(n), 256);
let convolution_domain = bluestein_convolution_domain::<F, _>(n, &mut rng).unwrap();

let coefficients: Vec<F> = (0..n).map(|i| F::new(i as u64 + 1)).collect();
let mut values = coefficients.clone();
bluestein_transform(&mut values, &domain, &convolution_domain);

// The same thing the Vandermonde definition gives, in n log n rather than n^2.
for (k, value) in values.iter().enumerate() {
    let mut expected = F::zero();
    for (j, c) in coefficients.iter().enumerate() {
        expected += *c * domain[(j * k) % n];
    }
    assert_eq!(*value, expected);
}
```

A field too shallow in two-adicity to hold a primitive `L`-th root is a fact about the field, so it
is a value rather than a panic — the same line #120 drew for `DomainError`, in the existing
`RootOfUnityError` vocabulary:

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    bluestein_convolution_domain,
    fields::{Mersenne31, RootOfUnityError},
    FFTDomain, KnownOrder,
};

// Mersenne-31: q - 1 = 2 * (2^30 - 1), so its two-adicity is 1 and there is no transform here
// beyond size two. A size-5 Bluestein would want a 16-point convolution.
assert_eq!(Mersenne31::two_adicity(), 1);
let mut rng = StdRng::seed_from_u64(2);
assert_eq!(
    bluestein_convolution_domain::<Mersenne31, _>(5, &mut rng),
    Err(RootOfUnityError::TwoAdicityExceeded { log_n: 4, two_adicity: 1 }),
);
```

**It is dispatched to automatically, for a domain that carries a convolution domain.** #375 closed
the two reasons it was not.

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::fields::PrimeFieldElement64;
use zeebra::{
    evaluate, with_bluestein, FFTDomain, FiniteField, KnownOrder, Polynomial, UnivariatePolynomial,
};

// Goldilocks, whose q - 1 = 2^32 * 3 * 5 * 17 * 257 * 65537 hosts a 257-point domain.
type F = PrimeFieldElement64<18_446_744_069_414_584_321>;
let mut rng = StdRng::seed_from_u64(375);

let root = F::try_root_of_unity(257, &mut rng).unwrap();
let plain = FFTDomain::from_generator(root, 257);
let prepared = with_bluestein(plain.clone(), &mut rng).unwrap();

// The same transform either way; `prepared` takes Bluestein and `plain` takes the definition.
let p = UnivariatePolynomial::<F>::rand(200, &mut rng);
assert_eq!(evaluate(&p, &prepared), evaluate(&p, &plain));
```

**The bound problem is solved by moving the capability, not by widening a signature.** Building a
convolution domain needs a primitive power-of-two root, hence `KnownOrder` and an rng; the
*transform* needs neither. Tightening `transform_any` would have propagated through `evaluate` and
`interpolate` into the polynomial API and ruled the FFT out over every field that is not
`KnownOrder`. Instead the convolution domain is attached to the **domain**, where the size already
lives, by `with_bluestein` — which carries the bound alone — and threaded down the decomposition as
an `Option`. `evaluate` and `interpolate` keep their `FiniteField` bounds, nothing is breaking, and
an unprepared domain behaves exactly as it did before.

Threading rather than reading it off a domain per node is forced by the recursion: `good_thomas`
builds its sub-domains as strided `Vec<F>` copies, so there is no domain object at a recursive site
— and a *nested* odd prime power is reached only through that path. One prepared domain serves
every factor, because the convolution length's contract admits a larger `L` than a given factor
needs.

**The crossover is 64, and it is one constant rather than a tier per element width.** That is a
property of the fields: a size `m` needs `m | q - 1`, the dispatch is reached only at an odd prime
power, and Bluestein needs the two-adicity to cover `log2 L`. What survives all three is
`3, 5, 17, 257` over Goldilocks, `127` over KoalaBear, `3, 5` over BabyBear and **nothing at all**
over BN254 `Fr` — one field per width, none at the widest. Measured, `dft` wins at `m = 17` (0.25x)
and loses at `m = 257` (3.06x), so Goldilocks brackets the crossover to `[17, 257)`; KoalaBear's
only size, 127, favours Bluestein by **3.55x**, capping the constant below 127; BabyBear's 3 and 5
both favour `dft`, flooring it at 5. Any constant in **`[17, 127)`** therefore dispatches
identically on every field that can exercise it, and 64 is the middle of that range.

```text
cargo run --release --example bluestein_crossover
```

reproduces that, and reports which sizes each field could host so the bracket is visible rather
than implied. A field that cannot host a convolution domain at all — Mersenne-31, whose two-adicity
is 1 — keeps the quadratic route at every size, which is why `with_bluestein` returns a `Result`
and an absent convolution domain is an ordinary state rather than an error.

## What the univariate stages cost

`cargo run --release --example univariate_scaling` sweeps seven stages by doubling degree until a
wall-clock budget is exceeded, reporting time, the local scaling exponent, and **peak live heap
bytes** from a counting allocator. Six of them, on a 64-core/300 GB workstation at one second per
measurement; the seventh is `fftmul`, which only means anything against `mul` at the same degree
and so is in the crossover section below:

| stage | exponent | KoalaBear | BN254 `Fr` | peak bytes |
|---|---|---|---|---|
| `mul`, schoolbook | 2 | 2^15 | 2^13 | `4 n B` |
| `div`, dispatched (#193) | **1.6** | **2^16** | **2^14** | `6 n B` / `10 n B` |
| `evaluate` (NTT) | 1 | **2^24** | **2^22** | `1 n B` |
| `interpolate` (iNTT) | 1 | **2^24** | **2^22** | `2 n B` |
| `lagrange_interpolate`, dispatched (#162) | **1.6** | **2^16** | **2^14** | `5 n B` / `~30 n B` |
| `roots` | **1.5–1.9** | **2^13** | **2^9** | `12 n B` / `16 n B` |

The `lagrange_interpolate` row moved in #162 stage 2, which builds `prod (x - x_i)` as a balanced
binary tree and runs multipoint evaluation down it and the transposed interpolation up it. That took
the exponent from 2 to **1.6** and the reachable point count up a further 4x on both fields — 64x
against the cubic form the issue started from. It could not have been written before #193: with
long division the tree's levels sum to `n^2 * sum_k 2^-k`, so it would not have moved the exponent
at all. The two peak figures are the two arms, and the step between them is visible in the sweep's
own bytes-per-element column exactly at the crossover. `multipoint_evaluate` is the public entry
point for the evaluation half, which is the thing `fft::evaluate` cannot do: its domain has to be
geometric, and an evaluation–interpolation resultant needs an arbitrary point set.

## Is the NTT access-bound? — `ntt_access`

`cargo run --release --example ntt_access` sweeps transform sizes by doubling and reports
`ns/butterfly` against the coefficient array's size, with the field's **own multiply rate
re-measured immediately before each row** as the denominator. The question is #68's one untested
premise — that the post-elimination regime is bound by memory *access* rather than arithmetic —
specified in `docs/research/graeffe-root-finding.md` §6.3 and answered in §6.3.1.

Taken under `tools/benchlock.sh` on one pinned core at a one-minute load of **5.55**, against the
binary's own publishable gate of 8:

| coefficient array | KoalaBear (8 B) | Goldilocks (8 B) | BN254 `Fr` (32 B) |
|---|---:|---:|---:|
| 8–64 KB | 105% | 95% | 94–120% |
| 4 MB | 90% | 83% | 83% |
| **16 MB** | **93%** | **74%** | 78% |
| **32 MB** | **61%** | **65%** | **73%** |
| 128 MB | 63% | 55% | 80% |
| 512 MB | — (two-adicity) | 46% | 77% |
| 2 GB | — | — | 75% |

Four results:

- **The transform allocates its output and nothing else.** `peak bytes / coeff bytes` is **1.00** at
  every one of 49 rows across three fields; the recursive kernel's `7nB` peak is gone. A counter, so
  exact and machine-independent.
- **Below a few MB the NTT is arithmetic-bound**, at 83–105% of its field's own multiply rate. The
  pre-#161 figure for the same quantity was **8.7–9.6%**, and that deficit was the allocator rather
  than the cache.
- **Access binds at 16–32 MB of coefficients, and *not* at the 256 MB L3.** Both 8-byte fields step
  down hard there — KoalaBear 93% → 61%, Goldilocks 74% → 65% — on a quiet box, so this is not
  ambient eviction. Crossing the nominal L3 boundary costs Goldilocks 16.3% and BN254 **2.7%**, far
  less than the step. A radix-2 transform revisits the whole array `log2 n` times with a doubling
  stride, so what must stay resident is not bounded by the array's size alone.
- **The degradation saturates, and lowest for the field with the most arithmetic per byte.** BN254's
  multiply is 9x slower over a 4x wider element, and it is flat at 73–80% from 32 MB to 2 GB — six
  doublings, four of them past the L3. An access-bound transform would degrade *more* for the field
  carrying more bytes per operation.

The binary **refuses to measure** above a one-minute load of 8 and exits 3, the same gate
`determinant_width` uses, because the subject is shared-cache traffic. `load-gate=N` raises it for
exercising the sweep, and a raised-gate run prints "**These numbers are not figures.**" above its
own tables. The arithmetic denominator is paired per row rather than per field after an unpaired
version read 105–165% — §6.3.2 has that method note; it is why the sweep also prints how far the
denominator moved over its own run.

```bash
tools/benchlock.sh ntt-access cargo run --release --example ntt_access -- budget=30
```

Mersenne-31 is excluded and the exclusion printed: two-adicity 1, so no power-of-two transform above
size 2. KoalaBear is swept as the registered challenge's field but **cannot** answer the access
question on this box — its two-adicity caps `n` at `2^24`, which is 128 MB in eight bytes and inside
the L3 — so Goldilocks and BN254 are the fields that reach past it.
`benches/field_arithmetic.rs` gained `p31_koalabear` and `p64_goldilocks` arms for the same reason:
`p31` is the Mersenne-31 modulus and `p64` is `2^64 - 59`, whose two-adicity is 2, so neither could
supply a committed comparand for an NTT-friendly field.

The exponent is **1.6 and not 1**, and that is a bound rather than a shortfall: near 1 needs the
transform, the transform needs `KnownOrder` and an RNG, and #162's own scope requires the
`FiniteField` bound this is written against. #559 settled that in favour of the bound — the
criterion now asks for the multiplication exponent, which `log2(3) = 1.585` against a measured
1.46 – 1.62 meets — and #606 holds the deferred `KnownOrder` specialization, gated on a measurement
of what a transform would buy. Mersenne-31 has two-adicity 1, so the Karatsuba path stays whatever
that measurement says.

The `div` and `roots` rows moved in #193, which put Newton inversion of the reversed divisor behind
a measured crossover: `div`'s exponent fell from 2 to 1.6, its reach doubled over KoalaBear and
quadrupled over BN254 `Fr`, and `roots` doubled on both fields because it is `O(log q)`
multiplications **and divisions** at the working degree. The two peak figures per row are the two
routes — long division's `6 n B` below the crossover and Newton's `10 n B` above it — and the step
between them is visible in the sweep's own bytes-per-element column, exactly at the constant. See
the crossover section below.

`fftmul` reaches operand `2^22` over KoalaBear at the same one-second budget, peak `12 n B`. It
used to stop at `2^18`, and that was **its own verification**: the stage asserted the transform's
product against schoolbook, which is `O(n^2)` against a quasi-linear subject, so the reported
ceiling got lower as the multiply got faster. It now checks against schoolbook up to `n = 2^12`
and by evaluation agreement at four random points above that, and **prints which it did** under
each curve — a ceiling set by a checker is not the same figure as one set by the stage. See
[`docs/research/fast-univariate.md`](../research/fast-univariate.md) §3.

`B = size_of::<F>()` — 8 bytes for a 64-bit field, 32 for a 254-bit one, so **4x**. That is not
the 2.5x the F4 budgets are written in: those count sparse `(usize, F)` entries, whose 8-byte index
word is paid whatever the field is and dilutes the ratio. A dense coefficient array has no index
word, so a byte budget carried over from the F4 side under-estimates this layer by 1.6x.

**Division is an operator.** `/` and `%` on `UnivariatePolynomial` are the quotient and the
remainder of that `div` row, in all four owned/borrowed combinations plus `/=` and `%=`. Each runs
the whole division, so a caller wanting both halves should call `Polynomial::div_with_remainder`,
which returns the pair. `/` is **not** a projection of that pair: on the Newton route the remainder
costs a full extra multiplication, so `/` takes a quotient-only path that skips it, while `%`
cannot. Below the crossover the two are the same code, since long division forms the remainder in
its working array whether or not anybody reads it. That trait method used to be named `div`; it carries its full name now
because an inherent `div(&self, ..)` loses method resolution to `Div::div`, which takes `self` by
value, and every `p.div(&q)` would otherwise have silently become the quotient alone. `lcm(a, b)`
is `a * b / gcd(a, b)` renormalized monic, and zero when either argument is zero:

```rust
use zeebra::{fields::Zp7, gcd, lcm, Polynomial, UnivariatePolynomial};

type P = UnivariatePolynomial<Zp7>;
let f = P::try_from("1 + 2x + x^2").unwrap(); // (x + 1)^2
let g = P::try_from("6 + x^2").unwrap(); // x^2 - 1 = (x + 1)(x + 6), since 6 = -1 mod 7

assert_eq!(gcd(&f, &g), P::try_from("1 + x").unwrap());
// (x + 1)^2 (x + 6) = x^3 + x^2 - x - 1
assert_eq!(lcm(&f, &g), P::try_from("6 + 6x + x^2 + x^3").unwrap());

// `/` and `%` are the two halves of one division; `div_with_remainder` returns both.
let (quotient, remainder) = f.div_with_remainder(&g);
assert_eq!(&f / &g, quotient);
assert_eq!(&f % &g, remainder);
```

**The Bézout cofactors, and the middle of the sequence.** `xgcd(a, b)` returns `(g, u, v)` with
`g = u*a + v*b`, and `partial_bezout(a, b, degree_bound)` returns the Euclidean sequence *halted*
at the first remainder of degree below the bound, as the pair `(v, r)`. The halted form is the
primitive: Reed-Solomon decoding solves the key equation `Λ(x)S(x) ≡ Ω(x) mod x^{2t}` by running it
on `(x^{2t}, S(x))` with `degree_bound = t`, taking `Ω` as the remainder and `Λ` as the cofactor,
and rational reconstruction and Padé approximation want the same thing. Only the cofactor of the
second argument is carried through the loop, because that is the one those consumers read; `xgcd`
recovers `u` from the identity with one exact division rather than paying for a second cofactor row
at every step.

```rust
use zeebra::{fields::Zp13, gcd, partial_bezout, xgcd, Polynomial, UnivariatePolynomial};

type P = UnivariatePolynomial<Zp13>;
let a = P::try_from("2 + 3x + x^2").unwrap(); // (x + 1)(x + 2)
let b = P::try_from("3 + 4x + x^2").unwrap(); // (x + 1)(x + 3)

let (g, u, v) = xgcd(&a, &b);
assert_eq!(g, gcd(&a, &b));
assert_eq!(&(&u * &a) + &(&v * &b), g);

// Halted at the first remainder of degree below 2, with its cofactor against `b`.
let (v, r) = partial_bezout(&a, &b, 2);
assert!(r.degree() < 2);
```

**Division is no longer one of them.** Newton inversion is `O(M(d))`, which is only worth writing
when `M` is subquadratic *where a division can call it* — and that became true when #231 put the
schoolbook-or-Karatsuba dispatcher on `Mul`. #193 then landed it: `div_with_remainder` chooses
between long division and Newton inversion of the reversed divisor on a measured per-width
crossover, and the exponent fell from 2 to 1.6.

The crossover is asymmetric in the quotient length `k` and the divisor length `m`, which is the
part worth knowing before reaching for it. `k` is the precision the power series is carried to, so
Newton pays `M(k)` however long the divisor is; only the remainder recovery sees `m`, and it sees
it as the long operand of an asymmetric product. A long quotient against a short divisor therefore
belongs on long division — dividing degree `10^6` by degree `250` is 2.5e8 multiplications
long-hand against `M(10^6)` by Newton — while a short quotient against a long divisor belongs on
Newton, where it measures 2.2x to 7.8x faster. A single threshold on `deg(g)`, or on
`min(k, m)`, gets one of those two wrong; the shipped rule is `m > t^(2-e) * k^(e-1)` with
`e = log2 3` and one measured `t` per element width.

**The floor on `k` was separately 16x-32x too high, and #527 measured it.** The rule also carries a
floor that the inequality does not imply — at `k = 2`, `m = 10^6` the inequality holds and only the
floor refuses Newton. #193 put that floor at `t`, the one length it had measured, and guessed the
true value near `t/68`; both were wrong. Sweeping `k` downward at a fixed `m = 65536`, long
division's last win is at `k = 32 / 8 / 16 / 4` across the four fields and Newton wins by more than
10% from `64 / 16 / 32 / 8` — so the floor refused 1.2x to 3.7x across a 16x band of `k`, and of 44
rows the rule picked the slower route on 22.

The floor is now **`karatsuba_base_case`** — 48 / 16 / 4 — which is not a new constant but the one
§4.1.1 already measured, and the right anchor: below the base case every product inside the Newton
iteration is schoolbook, so the route is long division with allocations. Re-measured with it
shipped, the rule picks the slower route on **1 row of 44**.

**`gcd` stays quadratic**, and that is now a smaller gap than it was. Half-GCD is `O(M(d) log d)`,
which against Euclid's `d^2` is a real crossing rather than the `d^2 log d`-against-`d^2`
non-crossing it was under a schoolbook `M`; it also needs a fast division to recurse on, and that
now exists. It is #194. §4.5 of
[`docs/research/fast-univariate.md`](../research/fast-univariate.md) has the arithmetic, the
per-width constants and the one part of the rule that is still unmeasured (#527).

The two transforms are the only quasi-linear stages, and they now cost the same: at a matched
`2^18`, `interpolate` is within 2–10% of `evaluate` over all three fields, where it used to be
2.4x, 5.2x and 8.6x. The whole gap was the `2n` inversions batch inversion removed — see
[`docs/research/batch-inversion.md`](../research/batch-inversion.md) §2.3. Replacing the
recursive split with the iterative kernel was worth a further **3.7x to 6.1x on the narrow fields
and 2.0x to 2.7x on BN254**, took the peaks from `7 n B` and `9 n B` to `1 n B` and `2 n B`, and
removed the `n log n` hardware integer divisions the recursion's `i % k` compiled to —
`tools/div_census.sh` counts them in the release artifact, 4 before and 0 after:

```text
cargo build --release --example univariate_scaling
tools/div_census.sh target/release/examples/univariate_scaling
tools/div_census.sh target/release/examples/univariate_scaling zeebra::poly   # any symbol prefix
```

KoalaBear's forward transform now covers the field's entire two-adic range inside one second, and
the schoolbook/NTT crossing moved **down one doubling** — measured product degree 1022 to 510 on an
8-byte element and 510 to 254 on a 32-byte one. The dispatch work recalibrated
`fft_multiplication_crossover` from that observation and found it could not simply adopt those
numbers: the threshold has to be measured against **Karatsuba**, which is the route the dispatcher
actually takes below it. It is now 4096 / 512 / 512 by element width; see the crossover section
below.

Interpolation at arbitrary abscissae — what an evaluation-interpolation resultant needs — is
**sub-quadratic**: it was cubic, at 2^10 and 2^9, until #162 stage 1 built the numerator product
`prod (x - x_i)` once and divided it down by synthetic division, and stage 2 added the subproduct
tree above a measured crossover. An evaluation-interpolation resultant turns out not
to need arbitrary abscissae at all, since it chooses where it samples — `bivariate_resultant_ntt`
takes its Sylvester determinants on a power-of-two subgroup and recovers the polynomial with one
`interpolate` — but on the CICO slices the determinants dominate either way.
[`docs/research/fast-univariate.md`](../research/fast-univariate.md) has the full curves, the
superseded figures, the gap list, and what each stage would need to go further; what the tree
reaches is `O(M(n) log n)` with a Karatsuba `M` and not `O(n log^2 n)`, because its bound is
`FiniteField` — see the `lagrange_interpolate` row above and #559.

The published Graeffe-transform root finder that those stages serve is read and scoped in
[`docs/research/graeffe-root-finding.md`](../research/graeffe-root-finding.md), with the algorithm
as pseudocode, the transform size each registered challenge requires against the ceilings above, and
a measured answer to whether this crate's NTT is access-bound. That document's §7.2 no-go was
retracted in part: the disclosed solve's working degree is `3^13`, not a resultant's `3^18`, and it
fits inside KoalaBear's `2^24`. The next section is the implementation.

## Root finding by the Graeffe transform

`graeffe_root` finds one root of a univariate polynomial in `F_p` in `O(M(d) log p)` rather than the
`O(log q * d^2)` of `roots`, over a field whose `q - 1` has a large power of two and a **small odd
part**. `graeffe_2` is the order-2 transform on its own and `graeffe_l` the order-`l` one.

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    fields::KoalaBear, graeffe_2, graeffe_root, FiniteField, Polynomial, UnivariatePolynomial, Zero,
};

let mut rng = StdRng::seed_from_u64(1);
let f = UnivariatePolynomial::<KoalaBear>::from_zeros(&[KoalaBear::new(7), KoalaBear::new(11)]);

// GT_2 squares the roots, so the transform of (x - 7)(x - 11) is (x - 49)(x - 121).
let squared = UnivariatePolynomial::from_zeros(&[KoalaBear::new(49), KoalaBear::new(121)]);
assert_eq!(graeffe_2(&f, &mut rng).unwrap(), squared);

let root = graeffe_root(&f, &mut rng).unwrap().expect("f has roots in the field");
assert!(f.eval(&root).is_zero());
```

`GT_2(f) = (-1)^d (f_e^2 - x f_o^2)` for `f(x) = f_e(x^2) + x f_o(x^2)`, which is **three transforms
of size `d + 1`, not of `2d + 1`** — half the size an ordinary product of two degree-`d`
polynomials needs. The `(-1)^d` makes a monic input transform to a monic output, so `prod (x - r_i)`
maps to exactly `prod (x - r_i^2)` and `GT_2 . GT_2 = GT_4` composes without a unit.

Iterating it does **not** separate roots by magnitude, which is what the real-number original is
for. With `q - 1 = 2^k * s`, every base-field root `alpha` has `alpha^(2^k)` in the subgroup of
order `s`, so `k` transforms drive the roots into a subgroup small enough to search outright. The
descent back down is decided by the polynomial rather than guessed: `G_(2^(i-1))` reduced modulo
`x^2 - mu_i` is `a x + b`, and `-b/a` is the one of `mu_i`'s two square roots it vanishes at.

`cargo run --release --example graeffe_root` measures it. On a 64-core/300 GB workstation, one core,
KoalaBear in a `u64`:

| degree | transforms | largest | forward | subgroup | descent | **total** | peak heap |
|---:|---:|---:|---:|---:|---:|---:|---:|
| `3^11` = 177 147 | 72 | `2^18` | 0.38 s | 0.09 ms | 7.5 ms | **0.39 s** | 27 MB |
| `3^12` = 531 441 | 72 | `2^20` | 1.50 s | 0.09 ms | 20.7 ms | **1.53 s** | 80 MB |
| **`3^13`** = 1 594 323 | 72 | **`2^21`** | 3.04 s | 0.10 ms | 58.8 ms | **3.11 s** | 195 MB |

Against `roots` on the same shape of input: it reaches degree 32 768 in 86.8 s and goes no further
inside a 60 s budget, and extrapolating its measured quadratic growth to `3^13` gives **57 hours**.
So about four to five orders of magnitude at that degree — with the quadratic side extrapolated, not
measured.

**97.7% of the time is the forward iteration, i.e. the NTT**, which is why #161 moved this stage
more than it moved anything else: the same rows were **13.85 s and 384 MB** before the iterative
kernel landed, so `3^13` is **4.45x faster and 1.97x smaller** for a change in a file this module
only calls. `docs/research/graeffe-root-finding.md` §4.4 keeps both revisions and §4.4.3 is the
difference. The `u32`-backed KoalaBear — the registered challenge's own type — is **2.27 s and
97 MB**.

**Only over a field whose odd part is small.** KoalaBear's is 127; Goldilocks' is `2^32 - 1`, so the
progressive reduction never bites and the subgroup search falls back to `roots` on a polynomial of
the input's degree — 5.07 s of a 5.09 s call at degree 4 096, so **99.6%** of it. The method is
exact there and buys nothing, which is why the papers give Goldilocks a separate algorithm built on
odd-order transforms. #161 sharpened that finding rather than softening it: making the transforms
5.9x faster made the whole call 3% faster.

### The multiplication crossover, measured

`multiply` dispatches over three routes by measured threshold — the schoolbook `Mul`, Karatsuba,
then the transform — and the fallback for a field that cannot host a domain is Karatsuba rather
than schoolbook. Where it should switch between Karatsuba and the transform is **not** one number:

| element | Karatsuba base case | transform threshold | measured crossing |
|---|---:|---:|---|
| 4 bytes (KoalaBear) | 48 | **4096** | (2046, 4094] |
| 8 bytes (Goldilocks) | 16 | **512** | (254, 510] |
| 32 bytes (BN254 `Fr`) | 4 | **512** | (254, 510] |

Those thresholds had to be measured against **Karatsuba**, not against schoolbook, and doing so
moved two of the three tiers from where the schoolbook figure would have put them: the 4-byte tier
fell 4x from an unverified 16384, and the 32-byte tier stayed at 512 rather than falling to 256,
because Karatsuba is still 1.18x ahead at product degree 254 there.

```text
cargo run --release --example multiplication_dispatch
cargo run --release --example multiplication_dispatch -- koalabear max_log=17
```

Over **Mersenne-31**, whose two-adicity of 1 rules the transform out at every degree, the fallback
is the whole of what the dispatcher buys: **1.80x** at operand length 16 rising to **11.19x** at
16384, from a route that was previously unreachable there.

The older schoolbook-versus-transform figures are kept below, because they are what the `fftmul`
rows above were taken against. Median of interleaved runs, pinned to one core, product degree
against the ratio of schoolbook to transform time:

| product degree | KoalaBear (4 B) | Zp65537 (8 B) | Goldilocks (8 B) | BN254 `Fr` (32 B) |
|---:|---:|---:|---:|---:|
| 256 | 0.03x | 0.23x | 0.20x | 0.61x |
| 1024 | 0.10x | 0.84x | 0.73x | **2.1x** |
| 2048 | 0.19x | **1.5x** | **1.4x** | 4.1x |
| 8192 | 0.70x | 5.7x | 5.5x | 12.7x |
| 16384 | **1.3x** | 11.7x | 10.4x | 23.6x |

Above 1x the transform is ahead. Schoolbook therefore wins until degree ~460 over a 254-bit field,
~1500 over a 64-bit one, and ~12000 over a 32-bit one — a 26x spread, which is why
`fft_multiplication_crossover::<F>()` is indexed by `size_of::<F>()`. The thresholds those figures
produced — 512, 2048 and 16384 — have since been replaced by the Karatsuba-relative ones above.

Those ratios are medians of 21 interleaved runs pinned to one core, which is what it takes to
resolve a 1.1x difference on this machine; the single-shot sweep above cannot.

The spread is also a finding about the transform rather than about the fields. At degree 16384 it
takes the same 13 ms over KoalaBear, Zp65537 and Goldilocks — three fields whose schoolbook times
at that degree differ by 9x — so this NTT is bound by allocation and recursion, not by field
arithmetic: `evaluate` rebuilds coefficient vectors and splits the domain at every level. The
sweep's `fftmul` row says the same thing in bytes: exponent 1.0 as expected, but a peak of
**26 `n B`** against 4 for schoolbook and 7 for a single `evaluate`, for a computation that is
three transforms. An in-place iterative transform is the work that would move all three crossovers
at once. **#161 did it**, and the re-taken sweep measures `12 n B`; the 26 is the pre-#161 figure,
kept because the ratios in the table above were taken against that transform.

`Mul` covers the first two routes and cannot cover the third. Choosing a domain needs a primitive
`2^k`-th root of unity, which needs `KnownOrder` and a source of randomness — neither of which
`Mul`'s signature can carry, and the first of which the Gröbner core deliberately does not require
of a coefficient type. So the transform is reached through `multiply`, `multiply_above` with an
explicit threshold, or `multiply_over_domain` when one domain serves many products:

```rust
use zeebra::{fields::Zp65537, multiply, FiniteField, Polynomial, UnivariatePolynomial};
use rand::{prelude::StdRng, SeedableRng};

let mut rng = StdRng::seed_from_u64(1);
let a = UnivariatePolynomial::<Zp65537>::new(&[Zp65537::new(1), Zp65537::new(2)]);
let b = UnivariatePolynomial::<Zp65537>::new(&[Zp65537::new(3), Zp65537::new(4)]);

// Degree 2, so this is the schoolbook route — and the same answer either way.
assert_eq!(multiply(&a, &b, &mut rng), &a * &b);
```

Karatsuba owns the band between them. Unlike the transform it needs nothing of the field but a
ring, so it is available over Mersenne-31; at `2^14` it is 10.7x to 22.9x faster than schoolbook,
at a measured exponent of 1.58–1.61 against 2.00, for `6 n B` against `Mul`'s `4 n B`.

```text
cargo run --release --example karatsuba_crossover
```

is the kernel measurement; [`docs/research/fast-univariate.md`](../research/fast-univariate.md)
§4.1.1 has the per-width tables and §4.1.2 the dispatched ones.

**Division has its own crossover**, measured the same way and for the same reason — one number
would be wrong, because the trade depends on the element width:

```text
cargo run --release --example division_crossover
```

sweeps both routes interleaved at each size, in two tables: a balanced sweep `deg f = 2d - 2` by
`deg g = d - 1`, which is the shape every `pow_mod` squaring produces and which the shipped
constant is read off, and a skew check that moves `k` and `m` apart to test the rule's asymmetry
rather than only its balanced point. The skew table is what caught a symmetric `min(k, m)` rule
taking long division at `k = 1024, m = 65536`, where Newton is 3.6x faster. Measured `t`: **1024**
for a 4-byte element, **256** for 5–8 bytes, **128** above that. §4.5 has the tables.

**`Mul` dispatches too**, since #231: schoolbook below the Karatsuba base case and Karatsuba above
it, so a caller who writes only `a * b` gets the subquadratic route without opting in. Below the
base case it *is* the schoolbook loop, so the operator is bit-identical to what it replaced at
every size.

| stage | KoalaBear | BN254 `Fr` |
|---|---:|---:|
| `roots`, the binding univariate stage | **1.32x–1.67x** | **1.44x–1.66x** |
| `lcm` | 1.17x–1.65x | 1.14x–1.66x |
| `from_zeros` *(superseded by #560, below)* | **2.83x** | 1.04x |
| one product | 2.08x–6.49x | 2.56x–7.31x |
| `div_with_remainder` *(control, no longer one)* | 0.99x | 1.00x |

The control row is a control only as of #231. `div_with_remainder` was unaffected because long
division is a coefficient loop that never forms a product; #193 then built a second route on top of
this kernel, so the same measurement re-taken today would not be flat. That is the point of the
control rather than a defect in it — it recorded that the dispatcher cost nothing where it was not
called, which is what made the later route's gain attributable.

Getting there needed two things first, both of which are the interesting part. The agreement tests
in `karatsuba` and `fft::multiply` compared against `&a * &b`, which would have made them check an
implementation against itself, so they were re-based onto an independent oracle in
**The `from_zeros` row is superseded.** #560 gave it the subproduct tree above a measured
per-width crossover, because the fold is `O(n^2)` however good the multiplication gets — it
multiplies a growing product by a two-coefficient operand, below every Karatsuba base-case tier, so
every step is the schoolbook loop. The exponent goes from ~1.99 to 1.30–1.58 and the product of
4 096 factors is **5.6x to 12.5x** faster depending on the width. Three tiers and not one: the
crossover moves 32x across the widths here (256 / 32 / 8) where interpolation's barely moves, and a
single constant would have made the 4-byte field 1.6x *slower* at n = 64. Note that `from_zeros` has
no library caller — every use in `src/` outside its definition is a doc comment, a re-export or a
test — so this is a public-API improvement and not a stage one.

And dispatching the operator initially measured **0.74x** on `from_zeros` — the
small-product regression the issue predicted — which turned out to be `schoolbook_into` iterating
the longer operand outside; swapping that made the same shape **2.5x** instead. The transform still
cannot live on `Mul`, because choosing a domain needs `KnownOrder` and randomness.
