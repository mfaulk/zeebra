//! Which modular reduction each prime-field width should use, measured in one build (#270).
//!
//! Every arm is a same-build control: the shipped field type, a raw replica of its arithmetic, and
//! the candidate reductions all run through the same generic kernels, interleaved, in one process.
//! The replica separates what the representation costs from what the `FiniteField` wrapper costs.
//! Every arm is checked against `u128` (or, at 254 bits, `ark-ff`) arithmetic on random and
//! boundary operands before any timing is taken, so a fast wrong kernel cannot be reported.
//!
//! Kernels, all over cache-resident operands so they measure arithmetic and not bandwidth:
//!
//! - `chain`   — `x = x * y[i] + z[i]`, a dependent chain: latency.
//! - `map`     — `c[i] = a[i] * b[i]`, independent: throughput, and the autovectorizable case.
//! - `scatter` — `row[col[i]] -= f * coef[i]`, the shape of `DenseAccumulator::subtract_scaled`.
//! - `dot`     — `sum a[i] * b[i]`, reduced per product or delayed into a wide accumulator.
//!
//! ```text
//! cargo run --release --example field_reduction            # every width
//! cargo run --release --example field_reduction -- 32     # one width: 32, 64 or 256
//! ```
//!
//! Output is one tab-separated line per (prime, kernel, arm) with the minimum ns/op over the
//! in-process repetitions. Run it several times in fresh processes and take medians of those
//! minima; `docs/research/field-arithmetic-specialization.md` records the protocol.

use std::{
    hint::black_box,
    time::{Duration, Instant},
};

use ark_ff::{
    fields::{Fp256, MontBackend, MontConfig},
    AdditiveGroup, BigInteger, Field, PrimeField,
};
use rand::{prelude::StdRng, Rng, SeedableRng};
use zeebra::{
    fields::{
        Bn254Fr, PrimeFieldElement256, PrimeFieldElement32, PrimeFieldElement64,
    },
    FiniteField,
};

const N: usize = 4096;
const ROW_WIDTH: usize = 16384;
const REPS: usize = 31;

/// One modular representation of `Z/pZ` for a word-sized `p`: encode, decode, and the two
/// operations the elimination kernels use.
trait Repr {
    const NAME: &'static str;
    type E: Copy + Default + PartialEq + std::fmt::Debug;
    fn modulus() -> u128;
    fn enc(canonical: u64) -> Self::E;
    fn dec(e: Self::E) -> u64;
    fn mul(a: Self::E, b: Self::E) -> Self::E;
    fn add(a: Self::E, b: Self::E) -> Self::E;
    fn sub(a: Self::E, b: Self::E) -> Self::E;
}

// ---------------------------------------------------------------------------------------------
// 32-bit storage

/// The shipped type, through its public operators.
struct Shipped32<const P: u32>;
impl<const P: u32> Repr for Shipped32<P> {
    const NAME: &'static str = "shipped-montgomery";
    type E = PrimeFieldElement32<P>;
    fn modulus() -> u128 {
        P as u128
    }
    fn enc(c: u64) -> Self::E {
        PrimeFieldElement32::<P>::new(c)
    }
    fn dec(e: Self::E) -> u64 {
        e.value() as u64
    }
    #[inline(always)]
    fn mul(a: Self::E, b: Self::E) -> Self::E {
        a * b
    }
    #[inline(always)]
    fn add(a: Self::E, b: Self::E) -> Self::E {
        a + b
    }
    #[inline(always)]
    fn sub(a: Self::E, b: Self::E) -> Self::E {
        a - b
    }
}

#[inline(always)]
const fn add32<const P: u32>(a: u32, b: u32) -> u32 {
    // Every prime measured here is below 2^31, so the sum stays inside 32 bits.
    let s = a + b;
    if s >= P {
        s - P
    } else {
        s
    }
}

#[inline(always)]
const fn sub32<const P: u32>(a: u32, b: u32) -> u32 {
    let (d, borrow) = a.overflowing_sub(b);
    if borrow {
        d.wrapping_add(P)
    } else {
        d
    }
}

const fn n_prime32(p: u32) -> u32 {
    // -p^{-1} mod 2^32 by Newton iteration.
    let mut inv: u32 = 1;
    let mut i = 0;
    while i < 5 {
        inv = inv.wrapping_mul(2u32.wrapping_sub(p.wrapping_mul(inv)));
        i += 1;
    }
    inv.wrapping_neg()
}

/// Montgomery with R = 2^32 on raw words, the shipped algorithm without the wrapper.
struct Mont32<const P: u32>;
impl<const P: u32> Mont32<P> {
    const NP: u32 = n_prime32(P);
    const R2: u32 = (((1u64 << 32) % P as u64) * ((1u64 << 32) % P as u64) % P as u64) as u32;
    #[inline(always)]
    fn redc(t: u64) -> u32 {
        let m = (t as u32).wrapping_mul(Self::NP);
        let h = ((t + m as u64 * P as u64) >> 32) as u32;
        if h >= P {
            h - P
        } else {
            h
        }
    }
}
impl<const P: u32> Repr for Mont32<P> {
    const NAME: &'static str = "montgomery-raw";
    type E = u32;
    fn modulus() -> u128 {
        P as u128
    }
    fn enc(c: u64) -> u32 {
        Self::redc(c % P as u64 * Self::R2 as u64)
    }
    fn dec(e: u32) -> u64 {
        Self::redc(e as u64) as u64
    }
    #[inline(always)]
    fn mul(a: u32, b: u32) -> u32 {
        Self::redc(a as u64 * b as u64)
    }
    #[inline(always)]
    fn add(a: u32, b: u32) -> u32 {
        add32::<P>(a, b)
    }
    #[inline(always)]
    fn sub(a: u32, b: u32) -> u32 {
        sub32::<P>(a, b)
    }
}

/// Canonical residues and `%` by the constant modulus, which LLVM lowers to a multiply by a
/// precomputed reciprocal — Barrett reduction emitted by the compiler.
struct Rem32<const P: u32>;
impl<const P: u32> Repr for Rem32<P> {
    const NAME: &'static str = "canonical-rem-const";
    type E = u32;
    fn modulus() -> u128 {
        P as u128
    }
    fn enc(c: u64) -> u32 {
        (c % P as u64) as u32
    }
    fn dec(e: u32) -> u64 {
        e as u64
    }
    #[inline(always)]
    fn mul(a: u32, b: u32) -> u32 {
        ((a as u64 * b as u64) % P as u64) as u32
    }
    #[inline(always)]
    fn add(a: u32, b: u32) -> u32 {
        add32::<P>(a, b)
    }
    #[inline(always)]
    fn sub(a: u32, b: u32) -> u32 {
        sub32::<P>(a, b)
    }
}

/// Canonical residues and an explicit Barrett reduction, `mu = floor(2^64 / p)`.
///
/// For `t < p^2 < 2^62` the quotient estimate `(t * mu) >> 64` is at most one short, so one
/// conditional subtraction finishes it.
struct Barrett32<const P: u32>;
impl<const P: u32> Barrett32<P> {
    const MU: u64 = (u64::MAX / P as u64) + if u64::MAX % P as u64 == P as u64 - 1 { 1 } else { 0 };
}
impl<const P: u32> Repr for Barrett32<P> {
    const NAME: &'static str = "canonical-barrett";
    type E = u32;
    fn modulus() -> u128 {
        P as u128
    }
    fn enc(c: u64) -> u32 {
        (c % P as u64) as u32
    }
    fn dec(e: u32) -> u64 {
        e as u64
    }
    #[inline(always)]
    fn mul(a: u32, b: u32) -> u32 {
        let t = a as u64 * b as u64;
        let q = ((t as u128 * Self::MU as u128) >> 64) as u64;
        let r = (t - q * P as u64) as u32;
        if r >= P {
            r - P
        } else {
            r
        }
    }
    #[inline(always)]
    fn add(a: u32, b: u32) -> u32 {
        add32::<P>(a, b)
    }
    #[inline(always)]
    fn sub(a: u32, b: u32) -> u32 {
        sub32::<P>(a, b)
    }
}

const M31: u32 = (1 << 31) - 1;

/// Canonical residues mod 2^31 - 1, reduced by the Mersenne identity 2^31 = 1.
///
/// `t < (p-1)^2 < 2^62`, so `(t & p) + (t >> 31) < 2^31 + 2^31 - 1 = 2p + 1`; the only value at
/// or above `2p` would need `t & p = p` and `t >> 31 = p`, i.e. `t = 2^62 - 1`, which exceeds
/// `(p-1)^2`. One conditional subtraction therefore suffices.
struct Mersenne31Repr;
impl Repr for Mersenne31Repr {
    const NAME: &'static str = "canonical-mersenne";
    type E = u32;
    fn modulus() -> u128 {
        M31 as u128
    }
    fn enc(c: u64) -> u32 {
        (c % M31 as u64) as u32
    }
    fn dec(e: u32) -> u64 {
        e as u64
    }
    #[inline(always)]
    fn mul(a: u32, b: u32) -> u32 {
        let t = a as u64 * b as u64;
        let r = ((t & M31 as u64) + (t >> 31)) as u32;
        if r >= M31 {
            r - M31
        } else {
            r
        }
    }
    #[inline(always)]
    fn add(a: u32, b: u32) -> u32 {
        add32::<M31>(a, b)
    }
    #[inline(always)]
    fn sub(a: u32, b: u32) -> u32 {
        sub32::<M31>(a, b)
    }
}

// ---------------------------------------------------------------------------------------------
// 64-bit storage

struct Shipped64<const P: u64>;
impl<const P: u64> Repr for Shipped64<P> {
    const NAME: &'static str = "shipped-montgomery";
    type E = PrimeFieldElement64<P>;
    fn modulus() -> u128 {
        P as u128
    }
    fn enc(c: u64) -> Self::E {
        PrimeFieldElement64::<P>::new(c)
    }
    fn dec(e: Self::E) -> u64 {
        e.value()
    }
    #[inline(always)]
    fn mul(a: Self::E, b: Self::E) -> Self::E {
        a * b
    }
    #[inline(always)]
    fn add(a: Self::E, b: Self::E) -> Self::E {
        a + b
    }
    #[inline(always)]
    fn sub(a: Self::E, b: Self::E) -> Self::E {
        a - b
    }
}

#[inline(always)]
const fn add64<const P: u64>(a: u64, b: u64) -> u64 {
    let (s, carry) = a.overflowing_add(b);
    if carry || s >= P {
        s.wrapping_sub(P)
    } else {
        s
    }
}

#[inline(always)]
const fn sub64<const P: u64>(a: u64, b: u64) -> u64 {
    let (d, borrow) = a.overflowing_sub(b);
    if borrow {
        d.wrapping_add(P)
    } else {
        d
    }
}

const fn n_prime64(p: u64) -> u64 {
    let mut inv: u64 = 1;
    let mut i = 0;
    while i < 6 {
        inv = inv.wrapping_mul(2u64.wrapping_sub(p.wrapping_mul(inv)));
        i += 1;
    }
    inv.wrapping_neg()
}

/// Montgomery with R = 2^64 on raw words.
struct Mont64<const P: u64>;
impl<const P: u64> Mont64<P> {
    const NP: u64 = n_prime64(P);
    const R2: u64 = {
        let r = ((1u128 << 64) % P as u128) as u64;
        ((r as u128 * r as u128) % P as u128) as u64
    };
    #[inline(always)]
    fn redc(t: u128) -> u64 {
        let m = (t as u64).wrapping_mul(Self::NP);
        let (s, carry) = t.overflowing_add(m as u128 * P as u128);
        let h = (s >> 64) as u64;
        if carry {
            h.wrapping_sub(P)
        } else if h >= P {
            h - P
        } else {
            h
        }
    }
}
impl<const P: u64> Repr for Mont64<P> {
    const NAME: &'static str = "montgomery-raw";
    type E = u64;
    fn modulus() -> u128 {
        P as u128
    }
    fn enc(c: u64) -> u64 {
        Self::redc((c % P) as u128 * Self::R2 as u128)
    }
    fn dec(e: u64) -> u64 {
        Self::redc(e as u128)
    }
    #[inline(always)]
    fn mul(a: u64, b: u64) -> u64 {
        Self::redc(a as u128 * b as u128)
    }
    #[inline(always)]
    fn add(a: u64, b: u64) -> u64 {
        add64::<P>(a, b)
    }
    #[inline(always)]
    fn sub(a: u64, b: u64) -> u64 {
        sub64::<P>(a, b)
    }
}

/// Canonical residues and `u128 % P`: the representation `PrimeFieldElement64` replaced. A
/// control, since LLVM does not strength-reduce a 128-bit remainder and this calls `__umodti3`.
struct Rem64<const P: u64>;
impl<const P: u64> Repr for Rem64<P> {
    const NAME: &'static str = "canonical-rem-u128";
    type E = u64;
    fn modulus() -> u128 {
        P as u128
    }
    fn enc(c: u64) -> u64 {
        c % P
    }
    fn dec(e: u64) -> u64 {
        e
    }
    #[inline(always)]
    fn mul(a: u64, b: u64) -> u64 {
        ((a as u128 * b as u128) % P as u128) as u64
    }
    #[inline(always)]
    fn add(a: u64, b: u64) -> u64 {
        add64::<P>(a, b)
    }
    #[inline(always)]
    fn sub(a: u64, b: u64) -> u64 {
        sub64::<P>(a, b)
    }
}

/// Canonical residues and the Möller–Granlund two-word-by-one-word division with a precomputed
/// reciprocal of the normalized modulus (Möller and Granlund, "Improved division by invariant
/// integers", 2011, Algorithm 4) — the reduction FLINT's `nmod` layer and NTL's `zz_p` use.
struct Preinv64<const P: u64>;
impl<const P: u64> Preinv64<P> {
    const SHIFT: u32 = P.leading_zeros();
    const D: u64 = P << Self::SHIFT;
    const V: u64 = (u128::MAX / Self::D as u128 - (1u128 << 64)) as u64;
}
impl<const P: u64> Repr for Preinv64<P> {
    const NAME: &'static str = "canonical-preinv";
    type E = u64;
    fn modulus() -> u128 {
        P as u128
    }
    fn enc(c: u64) -> u64 {
        c % P
    }
    fn dec(e: u64) -> u64 {
        e
    }
    #[inline(always)]
    fn mul(a: u64, b: u64) -> u64 {
        // Shift the product so the divisor is normalized; the high word stays below D.
        let t = (a as u128 * b as u128) << Self::SHIFT;
        let (u1, u0) = ((t >> 64) as u64, t as u64);
        let q = (Self::V as u128 * u1 as u128).wrapping_add(((u1 as u128 + 1) << 64) | u0 as u128);
        let (q1, q0) = ((q >> 64) as u64, q as u64);
        let mut r = u0.wrapping_sub(q1.wrapping_mul(Self::D));
        if r > q0 {
            r = r.wrapping_add(Self::D);
        }
        if r >= Self::D {
            r -= Self::D;
        }
        r >> Self::SHIFT
    }
    #[inline(always)]
    fn add(a: u64, b: u64) -> u64 {
        add64::<P>(a, b)
    }
    #[inline(always)]
    fn sub(a: u64, b: u64) -> u64 {
        sub64::<P>(a, b)
    }
}

/// Canonical residues in 8-byte storage for a modulus below 2^32, where the product fits a `u64`
/// and `%` by the constant lowers to a reciprocal multiply rather than a `u128` reduction.
struct Narrow64<const P: u64>;
impl<const P: u64> Repr for Narrow64<P> {
    const NAME: &'static str = "canonical-narrow-u64";
    type E = u64;
    fn modulus() -> u128 {
        P as u128
    }
    fn enc(c: u64) -> u64 {
        c % P
    }
    fn dec(e: u64) -> u64 {
        e
    }
    #[inline(always)]
    fn mul(a: u64, b: u64) -> u64 {
        debug_assert!(P < 1 << 32);
        (a * b) % P
    }
    #[inline(always)]
    fn add(a: u64, b: u64) -> u64 {
        add64::<P>(a, b)
    }
    #[inline(always)]
    fn sub(a: u64, b: u64) -> u64 {
        sub64::<P>(a, b)
    }
}

/// The Mersenne reduction of [`Mersenne31Repr`] in 8-byte storage, as `Zp2147483647` holds it.
struct Mersenne31In64;
impl Repr for Mersenne31In64 {
    const NAME: &'static str = "canonical-mersenne-u64";
    type E = u64;
    fn modulus() -> u128 {
        M31 as u128
    }
    fn enc(c: u64) -> u64 {
        c % M31 as u64
    }
    fn dec(e: u64) -> u64 {
        e
    }
    #[inline(always)]
    fn mul(a: u64, b: u64) -> u64 {
        Mersenne31Repr::mul(a as u32, b as u32) as u64
    }
    #[inline(always)]
    fn add(a: u64, b: u64) -> u64 {
        add64::<{ M31 as u64 }>(a, b)
    }
    #[inline(always)]
    fn sub(a: u64, b: u64) -> u64 {
        sub64::<{ M31 as u64 }>(a, b)
    }
}

const GOLDILOCKS: u64 = 0xFFFF_FFFF_0000_0001;
const EPS: u64 = 0xFFFF_FFFF;

/// Canonical residues mod 2^64 - 2^32 + 1 by the identities 2^64 = 2^32 - 1 and 2^96 = -1.
///
/// For `t = h_hi * 2^96 + h_lo * 2^64 + l`: `t = l - h_hi + h_lo * (2^32 - 1)`. Each wrap of 2^64
/// is corrected by adding or subtracting `2^32 - 1`, and the result is made canonical at the end.
struct GoldilocksRepr;
impl Repr for GoldilocksRepr {
    const NAME: &'static str = "canonical-goldilocks";
    type E = u64;
    fn modulus() -> u128 {
        GOLDILOCKS as u128
    }
    fn enc(c: u64) -> u64 {
        c % GOLDILOCKS
    }
    fn dec(e: u64) -> u64 {
        e
    }
    #[inline(always)]
    fn mul(a: u64, b: u64) -> u64 {
        let t = a as u128 * b as u128;
        let (lo, hi) = (t as u64, (t >> 64) as u64);
        let (hi_hi, hi_lo) = (hi >> 32, hi & EPS);
        let (mut t0, borrow) = lo.overflowing_sub(hi_hi);
        if borrow {
            t0 = t0.wrapping_sub(EPS);
        }
        let (mut r, carry) = t0.overflowing_add(hi_lo * EPS);
        if carry {
            r = r.wrapping_add(EPS);
        }
        if r >= GOLDILOCKS {
            r - GOLDILOCKS
        } else {
            r
        }
    }
    #[inline(always)]
    fn add(a: u64, b: u64) -> u64 {
        add64::<GOLDILOCKS>(a, b)
    }
    #[inline(always)]
    fn sub(a: u64, b: u64) -> u64 {
        sub64::<GOLDILOCKS>(a, b)
    }
}

// ---------------------------------------------------------------------------------------------
// Kernels

struct Operands<E> {
    a: Vec<E>,
    b: Vec<E>,
    cols: Vec<usize>,
    row: Vec<E>,
    factor: E,
}

/// Random residues plus the boundary operands 0, 1, p-1 and p-2 at fixed positions.
fn canonical_operands(p: u128, seed: u64) -> (Vec<u64>, Vec<u64>, Vec<usize>, Vec<u64>, u64) {
    let mut rng = StdRng::seed_from_u64(seed);
    let draw = |rng: &mut StdRng| (rng.gen::<u64>() as u128 % p) as u64;
    let mut a: Vec<u64> = (0..N).map(|_| draw(&mut rng)).collect();
    let mut b: Vec<u64> = (0..N).map(|_| draw(&mut rng)).collect();
    let edges = [0, 1, (p - 1) as u64, (p - 2) as u64];
    for (i, e) in edges.iter().enumerate() {
        a[i] = *e;
        b[i] = (p - 1) as u64;
        a[N - 1 - i] = (p - 1) as u64;
        b[N - 1 - i] = *e;
    }
    // Distinct sorted columns, as a sparse row stores them.
    let mut cols: Vec<usize> = (0..ROW_WIDTH).collect();
    for i in 0..N {
        let j = rng.gen_range(i..ROW_WIDTH);
        cols.swap(i, j);
    }
    cols.truncate(N);
    cols.sort_unstable();
    let row: Vec<u64> = (0..ROW_WIDTH).map(|_| draw(&mut rng)).collect();
    let factor = (p - 1) as u64;
    (a, b, cols, row, factor)
}

fn operands<R: Repr>(seed: u64) -> Operands<R::E> {
    let (a, b, cols, row, factor) = canonical_operands(R::modulus(), seed);
    Operands {
        a: a.into_iter().map(R::enc).collect(),
        b: b.into_iter().map(R::enc).collect(),
        cols,
        row: row.into_iter().map(R::enc).collect(),
        factor: R::enc(factor),
    }
}

#[inline(never)]
fn chain<R: Repr>(a: &[R::E], b: &[R::E]) -> R::E {
    let mut x = a[N / 2];
    for i in 0..N {
        x = R::add(R::mul(x, a[i]), b[i]);
    }
    x
}

#[inline(never)]
fn map<R: Repr>(a: &[R::E], b: &[R::E], out: &mut [R::E]) {
    for ((o, x), y) in out.iter_mut().zip(a).zip(b) {
        *o = R::mul(*x, *y);
    }
}

#[inline(never)]
fn scatter<R: Repr>(row: &mut [R::E], cols: &[usize], coefs: &[R::E], factor: R::E) {
    for (c, x) in cols.iter().zip(coefs) {
        row[*c] = R::sub(row[*c], R::mul(factor, *x));
    }
}

#[inline(never)]
fn dot<R: Repr>(a: &[R::E], b: &[R::E]) -> R::E {
    let mut s = R::E::default();
    for (x, y) in a.iter().zip(b) {
        s = R::add(s, R::mul(*x, *y));
    }
    s
}

// Kernels that need canonical words rather than a `Repr`: Shoup's precomputed-multiplier scatter
// and delayed-reduction dot products.

/// `floor(f * 2^32 / p)` for Shoup multiplication by the fixed factor `f`.
fn shoup32(f: u32, p: u32) -> u32 {
    (((f as u64) << 32) / p as u64) as u32
}

/// Shoup scatter at 32 bits: per factor one division, per entry two multiplies and a correction.
#[inline(never)]
fn scatter_shoup32<const P: u32>(row: &mut [u32], cols: &[usize], coefs: &[u32], f: u32) {
    let fs = shoup32(f, P);
    for (c, x) in cols.iter().zip(coefs) {
        let q = ((*x as u64 * fs as u64) >> 32) as u32;
        let mut r = x.wrapping_mul(f).wrapping_sub(q.wrapping_mul(P));
        if r >= P {
            r -= P;
        }
        row[*c] = sub32::<P>(row[*c], r);
    }
}

/// `floor(f * 2^64 / p)` for Shoup multiplication at 64 bits; requires `p < 2^63`.
fn shoup64(f: u64, p: u64) -> u64 {
    (((f as u128) << 64) / p as u128) as u64
}

#[inline(never)]
fn scatter_shoup64<const P: u64>(row: &mut [u64], cols: &[usize], coefs: &[u64], f: u64) {
    let fs = shoup64(f, P);
    for (c, x) in cols.iter().zip(coefs) {
        let q = ((*x as u128 * fs as u128) >> 64) as u64;
        let mut r = x.wrapping_mul(f).wrapping_sub(q.wrapping_mul(P));
        if r >= P {
            r -= P;
        }
        row[*c] = sub64::<P>(row[*c], r);
    }
}

/// How many raw `(p-1)^2` products fit on top of one residue below `p` in an accumulator of
/// `bits` bits; the delayed dot folds after that many.
fn delay_budget(p: u128, bits: u32) -> u128 {
    let max = if bits == 128 { u128::MAX } else { (1u128 << bits) - 1 };
    let sq = (p - 1).checked_mul(p - 1);
    match sq {
        Some(sq) if sq > 0 => (max - (p - 1)) / sq,
        _ => 0,
    }
}

/// Dot product of canonical 32-bit residues, summing raw products in a `u64` and folding with one
/// `%` every `budget` products.
#[inline(never)]
fn dot_delayed32<const P: u32>(a: &[u32], b: &[u32], budget: usize) -> u32 {
    let mut s: u64 = 0;
    for (ca, cb) in a.chunks(budget).zip(b.chunks(budget)) {
        for (x, y) in ca.iter().zip(cb) {
            s += *x as u64 * *y as u64;
        }
        s %= P as u64;
    }
    s as u32
}

/// Dot product of canonical 64-bit residues into a `u128`, folding every `budget` products.
#[inline(never)]
fn dot_delayed64<const P: u64>(a: &[u64], b: &[u64], budget: usize) -> u64 {
    let mut s: u128 = 0;
    for (ca, cb) in a.chunks(budget).zip(b.chunks(budget)) {
        for (x, y) in ca.iter().zip(cb) {
            s += *x as u128 * *y as u128;
        }
        s %= P as u128;
    }
    s as u64
}

// ---------------------------------------------------------------------------------------------
// Oracle: u128 reference values for every kernel, compared against each arm before timing.

struct Expected {
    chain: u64,
    map: Vec<u64>,
    scatter: Vec<u64>,
    dot: u64,
}

fn expected(p: u128, seed: u64) -> Expected {
    let (a, b, cols, mut row, f) = canonical_operands(p, seed);
    let (mulm, addm) = (|x: u64, y: u64| (x as u128 * y as u128 % p) as u64, |x: u64, y: u64| {
        ((x as u128 + y as u128) % p) as u64
    });
    let mut x = a[N / 2];
    for i in 0..N {
        x = addm(mulm(x, a[i]), b[i]);
    }
    let map = a.iter().zip(&b).map(|(x, y)| mulm(*x, *y)).collect();
    for (c, y) in cols.iter().zip(&a) {
        let prod = mulm(f, *y);
        row[*c] = ((row[*c] as u128 + p - prod as u128) % p) as u64;
    }
    let dot = a.iter().zip(&b).fold(0u64, |s, (x, y)| addm(s, mulm(*x, *y)));
    Expected { chain: x, map, scatter: row, dot }
}

fn check<R: Repr>(seed: u64) {
    let p = R::modulus();
    let want = expected(p, seed);
    let ops = operands::<R>(seed);
    let ctx = |k: &str| format!("{} p={p} kernel={k}", R::NAME);
    assert_eq!(R::dec(chain::<R>(&ops.a, &ops.b)), want.chain, "{}", ctx("chain"));
    let mut out = vec![R::E::default(); N];
    map::<R>(&ops.a, &ops.b, &mut out);
    let got: Vec<u64> = out.iter().map(|e| R::dec(*e)).collect();
    assert_eq!(got, want.map, "{}", ctx("map"));
    let mut row = ops.row.clone();
    scatter::<R>(&mut row, &ops.cols, &ops.a, ops.factor);
    let got: Vec<u64> = row.iter().map(|e| R::dec(*e)).collect();
    assert_eq!(got, want.scatter, "{}", ctx("scatter"));
    assert_eq!(R::dec(dot::<R>(&ops.a, &ops.b)), want.dot, "{}", ctx("dot"));
}

fn check_special32<const P: u32>(seed: u64) {
    let want = expected(P as u128, seed);
    let (a, b, cols, row, f) = canonical_operands(P as u128, seed);
    let (a, b): (Vec<u32>, Vec<u32>) =
        (a.iter().map(|x| *x as u32).collect(), b.iter().map(|x| *x as u32).collect());
    let mut row: Vec<u32> = row.iter().map(|x| *x as u32).collect();
    scatter_shoup32::<P>(&mut row, &cols, &a, f as u32);
    assert!(row.iter().zip(&want.scatter).all(|(g, w)| *g as u64 == *w), "shoup32 p={P}");
    let budget = delay_budget(P as u128, 64).min(N as u128) as usize;
    assert!(budget >= 1, "a u64 holds at least one product for p < 2^32");
    assert_eq!(dot_delayed32::<P>(&a, &b, budget) as u64, want.dot, "delayed32 p={P}");
}

fn check_special64<const P: u64>(seed: u64) {
    let want = expected(P as u128, seed);
    let (a, b, cols, mut row, f) = canonical_operands(P as u128, seed);
    if P < 1 << 63 {
        scatter_shoup64::<P>(&mut row, &cols, &a, f);
        assert_eq!(row, want.scatter, "shoup64 p={P}");
    }
    let budget = delay_budget(P as u128, 128).min(N as u128) as usize;
    if budget >= 1 {
        assert_eq!(dot_delayed64::<P>(&a, &b, budget), want.dot, "delayed64 p={P}");
    }
}

// ---------------------------------------------------------------------------------------------
// Timing

/// Minimum ns per element over `REPS` repetitions of `f`, each sized to run for at least ~0.2 ms.
fn time_min(mut f: impl FnMut()) -> f64 {
    let mut inner = 1usize;
    loop {
        let t = Instant::now();
        for _ in 0..inner {
            f();
        }
        if t.elapsed() >= Duration::from_micros(200) {
            break;
        }
        inner *= 2;
    }
    let mut best = f64::INFINITY;
    for _ in 0..REPS {
        let t = Instant::now();
        for _ in 0..inner {
            f();
        }
        best = best.min(t.elapsed().as_nanos() as f64 / (inner * N) as f64);
    }
    best
}

fn emit(width: &str, p: u128, kernel: &str, arm: &str, ns: f64) {
    println!("{width}\t{p}\t{kernel}\t{arm}\t{ns:.4}");
}

fn bench_repr<R: Repr>(width: &str, seed: u64) {
    check::<R>(seed);
    let ops = operands::<R>(seed);
    let p = R::modulus();
    let mut out = vec![R::E::default(); N];
    let mut row = ops.row.clone();
    emit(width, p, "chain", R::NAME, time_min(|| {
        black_box(chain::<R>(black_box(&ops.a), black_box(&ops.b)));
    }));
    emit(width, p, "map", R::NAME, time_min(|| {
        map::<R>(black_box(&ops.a), black_box(&ops.b), black_box(&mut out));
    }));
    emit(width, p, "scatter", R::NAME, time_min(|| {
        scatter::<R>(black_box(&mut row), black_box(&ops.cols), black_box(&ops.a), ops.factor);
    }));
    emit(width, p, "dot", R::NAME, time_min(|| {
        black_box(dot::<R>(black_box(&ops.a), black_box(&ops.b)));
    }));
}

fn bench_special32<const P: u32>(seed: u64) {
    check_special32::<P>(seed);
    let (a, b, cols, row, f) = canonical_operands(P as u128, seed);
    let (a, b): (Vec<u32>, Vec<u32>) =
        (a.iter().map(|x| *x as u32).collect(), b.iter().map(|x| *x as u32).collect());
    let mut row: Vec<u32> = row.iter().map(|x| *x as u32).collect();
    let budget = delay_budget(P as u128, 64).min(N as u128) as usize;
    emit("32", P as u128, "scatter", "canonical-shoup", time_min(|| {
        scatter_shoup32::<P>(black_box(&mut row), black_box(&cols), black_box(&a), f as u32);
    }));
    let arm = format!("delayed-u64(fold/{budget})");
    emit("32", P as u128, "dot", &arm, time_min(|| {
        black_box(dot_delayed32::<P>(black_box(&a), black_box(&b), budget));
    }));
}

fn bench_special64<const P: u64>(seed: u64) {
    check_special64::<P>(seed);
    let (a, b, cols, mut row, f) = canonical_operands(P as u128, seed);
    if P < 1 << 63 {
        emit("64", P as u128, "scatter", "canonical-shoup", time_min(|| {
            scatter_shoup64::<P>(black_box(&mut row), black_box(&cols), black_box(&a), f);
        }));
    }
    let budget = delay_budget(P as u128, 128).min(N as u128) as usize;
    if budget >= 1 {
        let arm = format!("delayed-u128(fold/{budget})");
        emit("64", P as u128, "dot", &arm, time_min(|| {
            black_box(dot_delayed64::<P>(black_box(&a), black_box(&b), budget));
        }));
    }
}

fn width32(seed: u64) {
    // GF(32003), the classical benchmark prime; 2^31 - 1; BabyBear.
    bench_repr::<Shipped32<32003>>("32", seed);
    bench_repr::<Mont32<32003>>("32", seed);
    bench_repr::<Rem32<32003>>("32", seed);
    bench_repr::<Barrett32<32003>>("32", seed);
    bench_special32::<32003>(seed);

    bench_repr::<Shipped32<M31>>("32", seed);
    bench_repr::<Mont32<M31>>("32", seed);
    bench_repr::<Rem32<M31>>("32", seed);
    bench_repr::<Barrett32<M31>>("32", seed);
    bench_repr::<Mersenne31Repr>("32", seed);
    bench_special32::<M31>(seed);

    bench_repr::<Shipped32<2013265921>>("32", seed);
    bench_repr::<Mont32<2013265921>>("32", seed);
    bench_repr::<Rem32<2013265921>>("32", seed);
    bench_repr::<Barrett32<2013265921>>("32", seed);
    bench_special32::<2013265921>(seed);
}

fn width64_at<const P: u64>(seed: u64) {
    bench_repr::<Shipped64<P>>("64", seed);
    bench_repr::<Mont64<P>>("64", seed);
    bench_repr::<Rem64<P>>("64", seed);
    bench_repr::<Preinv64<P>>("64", seed);
    bench_special64::<P>(seed);
}

fn width64(seed: u64) {
    // 2^31 - 1 in 8-byte storage (`Zp2147483647`), a non-Mersenne 31-bit prime, a 62-bit NTT
    // prime, Goldilocks, 2^64 - 59.
    width64_at::<2147483647>(seed);
    bench_repr::<Narrow64<2147483647>>("64", seed);
    bench_repr::<Mersenne31In64>("64", seed);
    width64_at::<1481823929>(seed);
    bench_repr::<Narrow64<1481823929>>("64", seed);
    width64_at::<4611624995532046337>(seed);
    width64_at::<GOLDILOCKS>(seed);
    bench_repr::<GoldilocksRepr>("64", seed);
    width64_at::<18446744073709551557>(seed);
}

// ---------------------------------------------------------------------------------------------
// 254 bits: the shipped 4-limb CIOS Montgomery against ark-ff's, the mature Rust reference.

// `MontConfig` expands to a check of ark-ff's own `asm` feature, which this crate does not declare.
#[allow(unexpected_cfgs)]
mod ark_bn254 {
    use super::{Fp256, MontBackend, MontConfig};

    #[derive(MontConfig)]
    #[modulus = "21888242871839275222246405745257275088548364400416034343698204186575808495617"]
    #[generator = "5"]
    pub struct ArkBn254FrConfig;
    pub type ArkBn254Fr = Fp256<MontBackend<ArkBn254FrConfig, 4>>;
}
use ark_bn254::ArkBn254Fr;

macro_rules! wide_kernels {
    ($name:ident, $ty:ty) => {
        mod $name {
            use super::*;
            #[inline(never)]
            pub fn chain(a: &[$ty], b: &[$ty]) -> $ty {
                let mut x = a[N / 2];
                for i in 0..N {
                    x = x * a[i] + b[i];
                }
                x
            }
            #[inline(never)]
            pub fn map(a: &[$ty], b: &[$ty], out: &mut [$ty]) {
                for ((o, x), y) in out.iter_mut().zip(a).zip(b) {
                    *o = *x * *y;
                }
            }
            #[inline(never)]
            pub fn scatter(row: &mut [$ty], cols: &[usize], coefs: &[$ty], f: $ty) {
                for (c, x) in cols.iter().zip(coefs) {
                    row[*c] = row[*c] - f * *x;
                }
            }
        }
    };
}
wide_kernels!(zb256, Bn254Fr);
wide_kernels!(ark256, ArkBn254Fr);

fn width256(seed: u64) {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut bytes = || {
        let mut b = [0u8; 32];
        rng.fill(&mut b);
        b
    };
    let ark: Vec<ArkBn254Fr> =
        (0..2 * N + ROW_WIDTH).map(|_| ArkBn254Fr::from_le_bytes_mod_order(&bytes())).collect();
    let mut ark = ark;
    ark[0] = ArkBn254Fr::ZERO;
    ark[1] = -ArkBn254Fr::ONE;
    let to_zb = |x: &ArkBn254Fr| {
        PrimeFieldElement256::from_canonical_limbs(x.into_bigint().0).expect("reduced")
    };
    let zb: Vec<Bn254Fr> = ark.iter().map(to_zb).collect();
    let (aa, ab, arow) = (&ark[..N], &ark[N..2 * N], &ark[2 * N..]);
    let (za, zbb, zrow) = (&zb[..N], &zb[N..2 * N], &zb[2 * N..]);
    let (_, _, cols, _, _) = canonical_operands(5, seed);
    let (af, zf) = (-ArkBn254Fr::ONE - ark[5], -Bn254Fr::one() - zb[5]);

    // Oracle agreement on every kernel before timing.
    let same = |z: &Bn254Fr, a: &ArkBn254Fr| z.canonical_limbs() == a.into_bigint().0;
    assert!(same(&zb256::chain(za, zbb), &ark256::chain(aa, ab)), "256 chain");
    let (mut zo, mut ao) = (vec![Bn254Fr::zero(); N], vec![ArkBn254Fr::ZERO; N]);
    zb256::map(za, zbb, &mut zo);
    ark256::map(aa, ab, &mut ao);
    assert!(zo.iter().zip(&ao).all(|(z, a)| same(z, a)), "256 map");
    let (mut zr, mut ar) = (zrow.to_vec(), arow.to_vec());
    zb256::scatter(&mut zr, &cols, za, zf);
    ark256::scatter(&mut ar, &cols, aa, af);
    assert!(zr.iter().zip(&ar).all(|(z, a)| same(z, a)), "256 scatter");
    assert!(ar.iter().any(|a| a.into_bigint().is_odd()), "nontrivial row");

    let p = 0u128; // the modulus does not fit; the column records the width instead
    for (arm, z) in [("shipped-cios", true), ("ark-ff-0.6", false)] {
        let ns = if z {
            time_min(|| {
                black_box(zb256::chain(black_box(za), black_box(zbb)));
            })
        } else {
            time_min(|| {
                black_box(ark256::chain(black_box(aa), black_box(ab)));
            })
        };
        emit("256", p, "chain", arm, ns);
        let ns = if z {
            time_min(|| zb256::map(black_box(za), black_box(zbb), black_box(&mut zo)))
        } else {
            time_min(|| ark256::map(black_box(aa), black_box(ab), black_box(&mut ao)))
        };
        emit("256", p, "map", arm, ns);
        let ns = if z {
            time_min(|| zb256::scatter(black_box(&mut zr), black_box(&cols), black_box(za), zf))
        } else {
            time_min(|| ark256::scatter(black_box(&mut ar), black_box(&cols), black_box(aa), af))
        };
        emit("256", p, "scatter", arm, ns);
    }
}

use zeebra::{One, Zero};

fn main() {
    let which = std::env::args().nth(1);
    let seed = 0x5eed_0270;
    eprintln!("# isa floor: {}", zeebra::util::isa_floor());
    println!("width\tp\tkernel\tarm\tns_per_op");
    let all = which.is_none();
    if all || which.as_deref() == Some("32") {
        width32(seed);
    }
    if all || which.as_deref() == Some("64") {
        width64(seed);
    }
    if all || which.as_deref() == Some("256") {
        width256(seed);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every 32-bit arm agrees with u128 arithmetic on random and boundary operands at three primes.
    #[test]
    fn every_32_bit_arm_matches_the_u128_oracle() {
        for seed in 0..4 {
            check::<Shipped32<32003>>(seed);
            check::<Mont32<32003>>(seed);
            check::<Rem32<32003>>(seed);
            check::<Barrett32<32003>>(seed);
            check_special32::<32003>(seed);
            check::<Mont32<M31>>(seed);
            check::<Barrett32<M31>>(seed);
            check::<Mersenne31Repr>(seed);
            check_special32::<M31>(seed);
            check::<Barrett32<2013265921>>(seed);
            check_special32::<2013265921>(seed);
        }
    }

    /// Every 64-bit arm agrees with u128 arithmetic, including the top-bit modulus 2^64 - 59.
    #[test]
    fn every_64_bit_arm_matches_the_u128_oracle() {
        for seed in 0..4 {
            check::<Mont64<4611624995532046337>>(seed);
            check::<Preinv64<4611624995532046337>>(seed);
            check_special64::<4611624995532046337>(seed);
            check::<Preinv64<2147483647>>(seed);
            check::<Narrow64<2147483647>>(seed);
            check::<Narrow64<1481823929>>(seed);
            check::<Mersenne31In64>(seed);
            check_special64::<2147483647>(seed);
            check::<GoldilocksRepr>(seed);
            check::<Preinv64<GOLDILOCKS>>(seed);
            check::<Mont64<18446744073709551557>>(seed);
            check::<Preinv64<18446744073709551557>>(seed);
            check_special64::<18446744073709551557>(seed);
        }
    }

    /// The Mersenne and Goldilocks reductions are exact on the largest possible product.
    #[test]
    fn special_reductions_are_exact_at_the_maximal_product() {
        assert_eq!(Mersenne31Repr::mul(M31 - 1, M31 - 1), 1);
        assert_eq!(GoldilocksRepr::mul(GOLDILOCKS - 1, GOLDILOCKS - 1), 1);
        assert_eq!(GoldilocksRepr::mul(GOLDILOCKS - 1, 1), GOLDILOCKS - 1);
        assert_eq!(GoldilocksRepr::mul(1 << 32, 1 << 32), EPS);
    }

    /// The delayed-reduction budgets are the exact u64/u128 headroom bounds.
    #[test]
    fn delay_budgets_are_the_exact_headroom() {
        assert_eq!(delay_budget(32003, 64), 18_012_146_920);
        assert_eq!(delay_budget(M31 as u128, 64), 4);
        assert_eq!(delay_budget(18446744073709551557, 64), 0);
        assert_eq!(delay_budget(18446744073709551557, 128), 1);
        assert_eq!(delay_budget(GOLDILOCKS as u128, 128), 1);
    }
}
