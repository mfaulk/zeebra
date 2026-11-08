//! Polynomial division with remainder.
//!
//! Both `Div` and `Rem` on `DensePolynomial` are one call to this and a projection, so a caller
//! that wants the quotient *and* the remainder must come here rather than write `f / g` and
//! `f % g`, which would run the division twice.
//!
//! Two routes, selected by [`newton_is_cheaper`]:
//!
//! - **Long division** over a coefficient array. Each step subtracts `c * x^e * divisor` from the
//!   working remainder in place, which is `deg(divisor) + 1` multiplications, so dividing degree
//!   `2d` by degree `d` costs `d^2` of them. It allocates nothing beyond its two output arrays and
//!   its inner loop vectorizes.
//! - **Newton inversion of the reversed divisor** (#193), which is `O(M(d))` for whatever product
//!   `M` the crate reaches. Since #231 that product is Karatsuba above a measured base case, so
//!   `M(d) = d^1.585` and this route is genuinely sub-quadratic.
//!
//! Long division is written out rather than expressed with the polynomial operators because doing
//! the latter made it **cubic**. Forming `c * x^e` as a polynomial and multiplying by the divisor
//! ran the schoolbook product over all `e + 1` coefficients of a term that has one, so a step cost
//! `(e + 1) * (deg(divisor) + 1)` rather than `deg(divisor) + 1`, and the sum over e was
//! `d^3 / 2`. Measured at exponent 2.99 by `examples/univariate_scaling.rs` against a predicted
//! 2, which is how it was found: every caller of `pow_mod_limbs` reduces once per squaring, so
//! root finding over a 254-bit field paid `254 * d^3 / 2`.
//!
//! # Why the crossover is a shape and not a number
//!
//! Write `k` for the quotient length `deg f - deg g + 1` and `m` for the divisor length
//! `deg g + 1`. Long division costs `k * m` multiplications, exactly.
//!
//! Newton's cost is driven by **`k` alone**, which is the one thing about this that is not
//! obvious. `k` is the precision the power series is carried to, and the iteration's second
//! product multiplies two series that are both as long as the precision — so the inversion pays
//! `M(k)` no matter how long the divisor is. Only the final `r = f - q*g` sees `m`, and it sees it
//! as the *long* operand of an asymmetric product, which costs `(m/k) * M(k)` rather than `M(m)`.
//! Together:
//!
//! ```text
//!   long division   k * m
//!   Newton          C * M(k)  +  (m/k) * M(k)
//! ```
//!
//! Dividing through by `k * m` with `M(d) = d^e`, `e = log2 3`, the second Newton term becomes
//! `k^(e-1)/k`, which is below 1 for every `k` past the Karatsuba base case. **The recovery never
//! blocks the route; only the inversion does.** Newton therefore wins exactly when
//!
//! ```text
//!   C * k^e < k * m   <=>   m > C * k^(e - 1)
//! ```
//!
//! and the condition is asymmetric in `k` and `m` — which is what the measurement found, in both
//! directions:
//!
//! - **A long quotient against a short divisor must stay on long division.** Dividing degree
//!   `10^6` by degree `250` is 2.5e8 multiplications long-hand against `M(10^6)` by Newton, three
//!   orders of magnitude worse. A gate reading only `deg(g) >= t` would take it.
//! - **A short quotient against a long divisor must take Newton**, and this is the case a
//!   `min(k, m)` rule gets wrong. Measured on this workstation at `k = 1024`, Newton is 3.6x
//!   faster than long division at `m = 65536` over Mersenne-31 and 7.8x over BN254 `Fr` — because
//!   it never pays `M(m)` at all, while long division pays every one of the `k * m` steps.
//!
//! Fixing `C` so that the balanced case `k = m = d` crosses exactly at `d = t` gives
//! `C = t^(2 - e)` and leaves **one** measured constant, [`newton_crossover`], in the same
//! three-tier per-element-width shape as `karatsuba_base_case`. The exponent is the crate's
//! multiplication exponent rather than a second knob.
//!
//! # The floor on `k`, and what is not measured
//!
//! The rule above also carries `k > t`, which is **not** implied by the inequality: at `k = 2`
//! and `m = 10^6` the inequality holds and the floor is what refuses it. The reason is the `C` the
//! derivation dropped. Newton runs five products at the precision before the recovery, so at small
//! `k` that fixed cost is not amortized, and `C * M(k)` is a worse model than `C * k^2` — at which
//! point Newton is long division with allocations. The model says the true floor is near `t/68`;
//! no measurement here covers `k < t`, so the floor sits at the one length that *was* measured.
//! That is conservative in the safe direction — it can forgo a win, never cause a regression — and
//! #527 is the issue to close the gap with a sweep over `k` at fixed large `m`.

use crate::{
    poly::univariate::{karatsuba::multiply_karatsuba, Polynomial, UnivariatePolynomial},
    FiniteField,
};

/// `log2 3`, the exponent of the product the iteration below calls.
///
/// `Mul` dispatches to `multiply_karatsuba` above its own base case (#231), so this is a property
/// of the crate's multiplication rather than a tuning constant — which is why fixing it does not
/// make the crossover rule two-parameter.
const KARATSUBA_EXPONENT: f64 = 1.584_962_500_721_156;

/// Quotient length at which Newton inversion overtakes long division on a balanced division, for
/// an element of at most 4 bytes. Measured by `examples/division_crossover.rs`, not derived.
///
/// The dispatch is on `k > t`, so each constant is the largest swept length at which Newton does
/// *not* win by more than 10%. Not the largest at which it loses: inside 10% the two routes cost
/// the same to within this workstation's run-to-run variation, and the tiebreak is then peak
/// memory, where long division's measured `6 n B` beats Newton's `10 n B`. Over Mersenne-31 in a
/// `u32` the balanced row at `d = 1024` is 1.01x, which is that tie exactly, and the first clear
/// win is 1.31x at `d = 2048`.
pub(crate) const NEWTON_CROSSOVER_32_BIT: usize = 1024;

/// The same, for an element of 5 to 8 bytes.
///
/// 256 rather than 512 because the two 8-byte fields disagreed and 256 is the choice that costs
/// neither: at `d = 512` Newton is 1.23x over Mersenne-31 in a `u64` and 1.09x over Goldilocks, so
/// selecting it there wins clearly on one field and ties on the other, while 512 would forgo the
/// 1.23x. At `d = 256` both are losses (0.92x, 0.81x), which is what puts the floor here.
pub(crate) const NEWTON_CROSSOVER_64_BIT: usize = 256;

/// The same, for an element wider than 8 bytes. Measured over BN254 `Fr`, where an element is 32
/// bytes; the 16-byte `PrimeFieldElement128` is not separately measured and takes this figure.
pub(crate) const NEWTON_CROSSOVER_WIDE: usize = 128;

/// The measured balanced crossover for `F`, the single source of truth for the dispatch.
///
/// Three tiers because `karatsuba_base_case` found three, and the crossover falls with width for
/// the same reason the base case does: long division's inner loop is a vectorizable
/// `remainder[i] -= c * b` that gets relatively less help the wider the element, while Newton's
/// cost is multiplications, which a wide element makes expensive on both sides alike. The measured
/// fall is 8x across the widths this crate uses, in the same direction as the base case's 12x.
pub(crate) fn newton_crossover<F: FiniteField>() -> usize {
    match std::mem::size_of::<F>() {
        0..=4 => NEWTON_CROSSOVER_32_BIT,
        5..=8 => NEWTON_CROSSOVER_64_BIT,
        _ => NEWTON_CROSSOVER_WIDE,
    }
}

/// Whether Newton inversion is the cheaper route for a quotient of length `quotient_len` against a
/// divisor of length `divisor_len`. See the module comment for the derivation.
fn newton_is_cheaper<F: FiniteField>(quotient_len: usize, divisor_len: usize) -> bool {
    newton_is_cheaper_at(quotient_len, divisor_len, newton_crossover::<F>())
}

/// [`newton_is_cheaper`] with the crossover supplied, so that a sweep can move it.
fn newton_is_cheaper_at(quotient_len: usize, divisor_len: usize, crossover: usize) -> bool {
    // The floor on the precision, which is a genuine extra condition rather than a restatement of
    // the inequality below — see the module comment's second section for why it is here and for
    // what it knowingly gives up. It doubles as an integer pre-filter that keeps the floating
    // point off every small division, and small divisions are most of them: every `pow_mod`
    // squaring reduces once.
    //
    // `<` rather than `<=` would leave the balanced case `quotient_len = divisor_len = crossover`
    // to be decided by the rounding of two `powf` calls on two sides that are equal in exact
    // arithmetic, and it fell the wrong way — selecting Newton *at* the measured crossover rather
    // than above it. Taking that case integrally makes the balanced crossover exactly the constant
    // by construction instead of to within a rounding error.
    if quotient_len <= crossover {
        return false;
    }
    let c = (crossover as f64).powf(2.0 - KARATSUBA_EXPONENT);
    (divisor_len as f64) > c * (quotient_len as f64).powf(KARATSUBA_EXPONENT - 1.0)
}

/// Computes dividend = quotient * divisor + remainder.
///
/// # Panics
/// Panics if `divisor` is the zero polynomial.
pub fn div_with_remainder<F: FiniteField>(
    dividend: &UnivariatePolynomial<F>,
    divisor: &UnivariatePolynomial<F>,
) -> (UnivariatePolynomial<F>, UnivariatePolynomial<F>) {
    let Some((f, g)) = reducible(dividend, divisor) else {
        return (UnivariatePolynomial::zero(), dividend.clone());
    };

    let (quotient, remainder) = if newton_is_cheaper::<F>(f.len() - g.len() + 1, g.len()) {
        divide_newton(f, g)
    } else {
        divide_long(f, g)
    };

    (
        UnivariatePolynomial::new(&quotient),
        UnivariatePolynomial::new(&remainder),
    )
}

/// The quotient alone, skipping the work that only the remainder needs.
///
/// This is not the same saving on both routes, which is why it is a separate entry point rather
/// than a projection of [`div_with_remainder`]. Long division produces the remainder *in* its
/// working array, so dropping it saves nothing. Newton produces the quotient first and recovers
/// `r = f - q*g` with a **full multiplication**, so dropping it saves an `M(deg f)` — which is a
/// third of the route's cost at the balanced shape. `Div` takes this; `Rem` cannot.
pub fn quotient<F: FiniteField>(
    dividend: &UnivariatePolynomial<F>,
    divisor: &UnivariatePolynomial<F>,
) -> UnivariatePolynomial<F> {
    let Some((f, g)) = reducible(dividend, divisor) else {
        return UnivariatePolynomial::zero();
    };

    let quotient = if newton_is_cheaper::<F>(f.len() - g.len() + 1, g.len()) {
        quotient_newton(f, g)
    } else {
        divide_long(f, g).0
    };
    UnivariatePolynomial::new(&quotient)
}

/// The two coefficient slices, or `None` when the dividend is already the remainder.
///
/// Both routes need `deg(f) >= deg(g)` and a non-zero divisor, and both need the slices trimmed so
/// that `len() - 1` is the true degree — which `UnivariatePolynomial::new` guarantees.
///
/// # Panics
/// Panics if `divisor` is the zero polynomial.
fn reducible<'a, F: FiniteField>(
    dividend: &'a UnivariatePolynomial<F>,
    divisor: &'a UnivariatePolynomial<F>,
) -> Option<(&'a [F], &'a [F])> {
    // TODO: return a Result instead of panicking.
    assert!(
        !divisor.is_zero(),
        "Divisor must not be zero: {:?}",
        divisor
    );
    if dividend.is_zero() || dividend.degree() < divisor.degree() {
        return None;
    }
    Some((dividend.coefficients(), divisor.coefficients()))
}

/// Long division. `(deg f - deg g + 1) * (deg g + 1)` multiplications, no allocation beyond the
/// two outputs.
fn divide_long<F: FiniteField>(dividend: &[F], divisor: &[F]) -> (Vec<F>, Vec<F>) {
    let divisor_degree = divisor.len() - 1;
    // One inversion for the whole division rather than one division per step.
    let leading_inverse = divisor[divisor_degree].inverse();

    let mut remainder = dividend.to_vec();
    let mut quotient = vec![F::zero(); remainder.len() - divisor_degree];

    // High-order term first. After each step `remainder[exponent + divisor_degree]` is exactly
    // zero, so the next leading coefficient is the next one down.
    for exponent in (0..quotient.len()).rev() {
        let c = remainder[exponent + divisor_degree] * leading_inverse;
        if c.is_zero() {
            continue;
        }
        quotient[exponent] = c;
        for (i, b) in divisor.iter().enumerate() {
            remainder[exponent + i] -= c * *b;
        }
    }

    (quotient, remainder)
}

/// Division by Newton inversion of the reversed divisor, then one multiplication to recover the
/// remainder.
fn divide_newton<F: FiniteField>(dividend: &[F], divisor: &[F]) -> (Vec<F>, Vec<F>) {
    let q = quotient_newton(dividend, divisor);
    // r = f - q*g. The product has length exactly `dividend.len()`, and its top `deg g + 1`
    // coefficients cancel the dividend's, so the result is left untrimmed for the caller's `new`.
    let mut remainder = dividend.to_vec();
    for (slot, c) in remainder.iter_mut().zip(multiply_karatsuba(&q, divisor)) {
        *slot -= c;
    }
    (q, remainder)
}

/// The quotient by Newton inversion, with no remainder recovery.
///
/// Reversing `f = qg + r` through `x -> 1/x` and multiplying by `x^deg f` gives
///
/// ```text
///   rev(f) = rev(q) * rev(g) + x^k * rev(r),    k = deg f - deg g + 1
/// ```
///
/// so `rev(q) = rev(f) * rev(g)^-1 mod x^k`, and the remainder term is annihilated by the
/// truncation rather than computed. `rev(g)`'s constant term is `g`'s leading coefficient, which is
/// non-zero for every non-zero `g`, so the inverse always exists — the same quantity long division
/// inverts.
fn quotient_newton<F: FiniteField>(dividend: &[F], divisor: &[F]) -> Vec<F> {
    let k = dividend.len() - divisor.len() + 1;

    let reversed_divisor: Vec<F> = divisor.iter().rev().copied().collect();
    let inverse = invert_mod_xk(&reversed_divisor, k);

    // Only the leading `k` coefficients of the dividend survive the truncation, which is the whole
    // saving when the divisor is long: the product is `M(k)`, not `M(deg f)`.
    let reversed_dividend: Vec<F> = dividend.iter().rev().take(k).copied().collect();
    let mut quotient = multiply_truncated(&reversed_dividend, &inverse, k);
    quotient.reverse();
    quotient
}

/// `1/g mod x^k` by Newton iteration, doubling the precision each step.
///
/// `h <- h * (2 - g*h) mod x^(2^i)` from `h = 1/g(0)`. Each step is two truncated products at the
/// new precision, so the cost telescopes to a constant multiple of `M(k)`.
///
/// # Panics
/// Panics if `k` is zero, or if `g`'s constant term is zero.
fn invert_mod_xk<F: FiniteField>(g: &[F], k: usize) -> Vec<F> {
    assert!(
        k > 0,
        "a power series inverse needs a precision of at least 1"
    );
    assert!(
        !g[0].is_zero(),
        "a power series is invertible only when its constant term is not"
    );

    let mut h = vec![g[0].inverse()];
    let mut precision = 1;
    while precision < k {
        let next = (2 * precision).min(k);
        // `g*h` is 1 mod x^precision, so negating and adding two leaves `2 - g*h` with the right
        // constant term without a special case for it.
        let mut error = multiply_truncated(g, &h, next);
        for c in error.iter_mut() {
            *c = c.neg();
        }
        error[0] += F::one() + F::one();
        h = multiply_truncated(&h, &error, next);
        precision = next;
    }
    h
}

/// `a * b mod x^k`, as a vector of length exactly `k`.
fn multiply_truncated<F: FiniteField>(a: &[F], b: &[F], k: usize) -> Vec<F> {
    let mut product = multiply_karatsuba(&a[..a.len().min(k)], &b[..b.len().min(k)]);
    product.resize(k, F::zero());
    product
}

/// [`div_with_remainder`] forced down the long-division route, so the two can be differentially
/// tested at degrees on both sides of the crossover.
#[doc(hidden)]
pub fn div_with_remainder_long_unstable<F: FiniteField>(
    dividend: &UnivariatePolynomial<F>,
    divisor: &UnivariatePolynomial<F>,
) -> (UnivariatePolynomial<F>, UnivariatePolynomial<F>) {
    match reducible(dividend, divisor) {
        None => (UnivariatePolynomial::zero(), dividend.clone()),
        Some((f, g)) => {
            let (q, r) = divide_long(f, g);
            (UnivariatePolynomial::new(&q), UnivariatePolynomial::new(&r))
        }
    }
}

/// [`div_with_remainder`] forced down the Newton route, likewise.
#[doc(hidden)]
pub fn div_with_remainder_newton_unstable<F: FiniteField>(
    dividend: &UnivariatePolynomial<F>,
    divisor: &UnivariatePolynomial<F>,
) -> (UnivariatePolynomial<F>, UnivariatePolynomial<F>) {
    match reducible(dividend, divisor) {
        None => (UnivariatePolynomial::zero(), dividend.clone()),
        Some((f, g)) => {
            let (q, r) = divide_newton(f, g);
            (UnivariatePolynomial::new(&q), UnivariatePolynomial::new(&r))
        }
    }
}

/// [`newton_crossover`], reachable from an example binary.
#[doc(hidden)]
pub fn newton_crossover_unstable<F: FiniteField>() -> usize {
    newton_crossover::<F>()
}

/// [`newton_is_cheaper`] with the crossover supplied, so a sweep can report what the shipped
/// constant would have chosen.
#[doc(hidden)]
pub fn newton_is_cheaper_at_unstable(
    quotient_len: usize,
    divisor_len: usize,
    crossover: usize,
) -> bool {
    newton_is_cheaper_at(quotient_len, divisor_len, crossover)
}

#[cfg(test)]
mod tests {
    use crate::poly::univariate::PolynomialParams;
    use proptest::prelude::*;
    use rand::SeedableRng;

    use super::{
        div_with_remainder, div_with_remainder_long_unstable, div_with_remainder_newton_unstable,
        invert_mod_xk, multiply_truncated, newton_crossover, newton_is_cheaper,
        newton_is_cheaper_at, quotient, KARATSUBA_EXPONENT,
    };
    use crate::{
        fields::{PrimeFieldElement64, Zp7},
        identities::{One, Zero},
        poly::univariate::{dense_polynomial::DensePolynomial, Polynomial, UnivariatePolynomial},
        FiniteField,
    };

    #[test]
    #[should_panic]
    fn divide_by_zero_should_panic() {
        type F = PrimeFieldElement64<541>;
        type P = DensePolynomial<F>;
        let p = P::try_from("x^2 + 1").unwrap();
        let (_q, _r) = div_with_remainder(&p, &P::zero());
    }

    proptest! {
        #[test]
        // Dividing by 1 should return the dividend with remainder zero.
        fn test_divide_by_1(
            p in ((0..=100usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<DensePolynomial<Zp7>>))) {
            let one = DensePolynomial::<Zp7>::one();
            let (q, r) = div_with_remainder(&p, &one);
            assert_eq!(q, p);
            assert_eq!(r, DensePolynomial::<Zp7>::zero());
        }
    }

    #[test]
    // For f = g*q + r, if deg(f) < deg(g), then q = 0 and r = f.
    fn test_divide_quotient_is_zero() {
        type F = PrimeFieldElement64<7>;
        let zero = UnivariatePolynomial::zero();

        // 1 + x
        let dividend = UnivariatePolynomial::new(&[F::one(), F::one()]);

        // x^2
        let divisor = UnivariatePolynomial::new(&[F::zero(), F::zero(), F::one()]);
        let (quotient, remainder) = div_with_remainder(&dividend, &divisor);
        assert_eq!(quotient, zero);
        assert_eq!(remainder, dividend);
    }

    /// For f = g*q + r with deg(f) >= deg(g), the quotient has degree deg(f) - deg(g).
    #[test]
    fn test_degree_of_quotient() {
        type F = Zp7;
        type P = DensePolynomial<F>;

        let dividend = P::new(&[F::new(1), F::new(2), F::new(3), F::new(4), F::new(5)]);
        for divisor in [
            P::new(&[F::new(3)]),                       // degree 0
            P::new(&[F::new(1), F::new(1)]),            // degree 1
            P::new(&[F::new(2), F::new(0), F::new(6)]), // degree 2
        ] {
            let (quotient, remainder) = div_with_remainder(&dividend, &divisor);
            assert_eq!(
                quotient.degree(),
                dividend.degree() - divisor.degree(),
                "divisor {:?}",
                divisor
            );
            // The remainder's degree stays strictly below the divisor's, unless it is zero.
            if !remainder.is_zero() {
                assert!(remainder.degree() < divisor.degree() || divisor.degree() == 0);
            }
            assert_eq!(&(&quotient * &divisor) + &remainder, dividend);
        }
    }

    /// Division at a degree the cubic implementation could not reach.
    ///
    /// The regression guard for the cost of this function, and the closest practical one: the
    /// quantity that changed is the number of field multiplications, which nothing here can
    /// count, and a wall-clock assertion in the test suite would be flaky. What makes this a
    /// guard is the size. Long division of degree 2d by degree d is `d^2` multiplications; the
    /// implementation this replaced was `d^3 / 2`, which at d = 3000 is 1.35e10 and does not
    /// finish in a test run. The measured exponent column of
    /// `cargo run --release --example univariate_scaling` is the direct evidence.
    #[test]
    fn test_division_at_a_degree_the_cubic_implementation_could_not_reach() {
        type F = Zp7;
        type P = DensePolynomial<F>;
        let mut rng = rand::rngs::StdRng::seed_from_u64(20261105);

        let divisor = P::rand(3_000, &mut rng);
        let dividend = P::rand(6_000, &mut rng);
        let (quotient, remainder) = div_with_remainder(&dividend, &divisor);

        assert_eq!(quotient.degree(), 3_000);
        assert!(remainder.is_zero() || remainder.degree() < divisor.degree());
        assert_eq!(&(&quotient * &divisor) + &remainder, dividend);
    }

    /// The two routes, named so a failure says which one disagreed.
    fn assert_routes_agree<F: FiniteField>(
        dividend: &UnivariatePolynomial<F>,
        divisor: &UnivariatePolynomial<F>,
        what: &str,
    ) {
        let long = div_with_remainder_long_unstable(dividend, divisor);
        let newton = div_with_remainder_newton_unstable(dividend, divisor);
        assert_eq!(long.0, newton.0, "quotient disagrees: {}", what);
        assert_eq!(long.1, newton.1, "remainder disagrees: {}", what);
        // Ground truth, so that agreement on a shared mistake cannot pass.
        assert_eq!(
            &(&newton.0 * divisor) + &newton.1,
            *dividend,
            "f = qg + r fails: {}",
            what
        );
        if !newton.1.is_zero() && divisor.degree() > 0 {
            assert!(
                newton.1.degree() < divisor.degree(),
                "remainder too big: {}",
                what
            );
        }
        // And the dispatcher agrees with whichever route it picked.
        assert_eq!(
            div_with_remainder(dividend, divisor),
            long,
            "dispatch: {}",
            what
        );
        assert_eq!(dividend / divisor, long.0, "`/` disagrees: {}", what);
    }

    /// Newton inversion satisfies `g*h = 1 mod x^k` at every precision, including `k = 1`.
    #[test]
    fn test_invert_mod_xk_is_the_inverse_to_its_precision() {
        type F = PrimeFieldElement64<2_147_483_647>;
        let mut rng = rand::rngs::StdRng::seed_from_u64(0x1_9300);
        for length in 1..=20usize {
            // A unit of the power series ring: anything with a non-zero constant term.
            let mut g: Vec<F> = (0..length).map(|_| F::random(&mut rng)).collect();
            if g[0].is_zero() {
                g[0] = F::one();
            }
            for k in 1..=24usize {
                let h = invert_mod_xk(&g, k);
                assert_eq!(h.len(), k, "precision, length {} k {}", length, k);
                let product = multiply_truncated(&g, &h, k);
                let mut expected = vec![F::zero(); k];
                expected[0] = F::one();
                assert_eq!(product, expected, "length {} k {}", length, k);
            }
        }
    }

    /// A power series with a zero constant term is rejected deliberately, not silently inverted.
    #[test]
    #[should_panic(expected = "invertible only when its constant term is not")]
    fn test_invert_mod_xk_rejects_a_non_unit() {
        type F = Zp7;
        let _h = invert_mod_xk(&[F::zero(), F::one()], 4);
    }

    /// The Newton route reproduces long division exactly on the degenerate shapes: a dividend of
    /// lower degree than the divisor, a constant divisor, a non-monic divisor, and a zero dividend.
    #[test]
    fn test_the_routes_agree_on_the_degenerate_shapes() {
        type F = Zp7;
        type P = DensePolynomial<F>;

        let f = P::new(&[F::new(1), F::new(2), F::new(3), F::new(4), F::new(5)]);

        // deg(f) < deg(g): the quotient is zero and the dividend is the remainder.
        let bigger = P::new(&[F::new(1); 9]);
        assert_routes_agree(&f, &bigger, "deg(f) < deg(g)");

        // A constant divisor, monic and not. k = deg(f) + 1 here, so the inversion runs to full
        // precision against a single-coefficient series.
        assert_routes_agree(&f, &P::one(), "divisor 1");
        assert_routes_agree(&f, &P::new(&[F::new(5)]), "constant non-monic divisor");

        // Non-monic of positive degree: `rev(g)`'s constant term is the leading coefficient, which
        // is the quantity long division inverts, so the two must agree without a special case.
        assert_routes_agree(
            &f,
            &P::new(&[F::new(1), F::new(1), F::new(3)]),
            "non-monic divisor",
        );

        // Equal degrees, so k = 1 and the inversion does not iterate at all.
        assert_routes_agree(
            &f,
            &P::new(&[F::new(6), F::new(1), F::new(2), F::new(3), F::new(4)]),
            "k = 1",
        );

        // A zero dividend.
        assert_routes_agree(&P::zero(), &f, "zero dividend");

        // A divisor with a zero constant term, which is a unit nowhere but is divided by fine.
        assert_routes_agree(
            &f,
            &P::new(&[F::zero(), F::zero(), F::new(2)]),
            "divisor x^2 * 2",
        );
    }

    /// A zero divisor panics identically on both routes and on the quotient-only path.
    #[test]
    fn test_a_zero_divisor_panics_on_every_route() {
        type F = PrimeFieldElement64<541>;
        type P = DensePolynomial<F>;
        let f = P::try_from("x^2 + 1").unwrap();
        for (route, call) in [
            (
                "dispatch",
                Box::new(|| {
                    div_with_remainder(&f, &P::zero());
                }) as Box<dyn Fn()>,
            ),
            (
                "long",
                Box::new(|| {
                    div_with_remainder_long_unstable(&f, &P::zero());
                }),
            ),
            (
                "newton",
                Box::new(|| {
                    div_with_remainder_newton_unstable(&f, &P::zero());
                }),
            ),
            (
                "quotient",
                Box::new(|| {
                    quotient(&f, &P::zero());
                }),
            ),
        ] {
            let panicked = std::panic::catch_unwind(std::panic::AssertUnwindSafe(call));
            assert!(
                panicked.is_err(),
                "{} did not panic on a zero divisor",
                route
            );
        }
    }

    /// Both routes agree over a narrow 31-bit field, at every degree pair up to 24.
    #[test]
    fn test_the_routes_agree_over_a_narrow_field() {
        type F = PrimeFieldElement64<2_147_483_647>;
        let mut rng = rand::rngs::StdRng::seed_from_u64(0x1_9301);
        for n in 0..24u64 {
            for m in 0..=n {
                let dividend = UnivariatePolynomial::<F>::rand(n, &mut rng);
                let divisor = UnivariatePolynomial::<F>::rand(m, &mut rng);
                if divisor.is_zero() {
                    continue;
                }
                assert_routes_agree(&dividend, &divisor, &format!("n {} m {}", n, m));
            }
        }
    }

    /// Both routes agree over a 64-bit field.
    #[test]
    fn test_the_routes_agree_over_goldilocks() {
        type F = PrimeFieldElement64<18_446_744_069_414_584_321>;
        let mut rng = rand::rngs::StdRng::seed_from_u64(0x1_9302);
        for n in 0..24u64 {
            let dividend = UnivariatePolynomial::<F>::rand(n, &mut rng);
            let divisor = UnivariatePolynomial::<F>::rand(n / 2, &mut rng);
            if divisor.is_zero() {
                continue;
            }
            assert_routes_agree(&dividend, &divisor, &format!("n {}", n));
        }
    }

    /// Both routes agree over the wide BN254 scalar field, where the element is 32 bytes and the
    /// crossover is lowest.
    #[test]
    fn test_the_routes_agree_over_bn254() {
        use crate::fields::Bn254Fr;
        let mut rng = rand::rngs::StdRng::seed_from_u64(0x1_9303);
        for n in 0..24u64 {
            let dividend = UnivariatePolynomial::<Bn254Fr>::rand(n, &mut rng);
            let divisor = UnivariatePolynomial::<Bn254Fr>::rand(n / 3, &mut rng);
            if divisor.is_zero() {
                continue;
            }
            assert_routes_agree(&dividend, &divisor, &format!("n {}", n));
        }
    }

    /// Exhaustive over GF(7): every pair of polynomials of degree at most 3, both routes.
    #[test]
    fn test_the_routes_agree_exhaustively_over_gf7() {
        const Q: u64 = 7;
        let all: Vec<DensePolynomial<Zp7>> = (0..Q.pow(4))
            .map(|code| {
                let c: Vec<Zp7> = (0..4).map(|i| Zp7::new(code / Q.pow(i) % Q)).collect();
                DensePolynomial::new(&c)
            })
            .collect();
        for dividend in &all {
            for divisor in &all {
                if divisor.is_zero() {
                    continue;
                }
                assert_routes_agree(dividend, divisor, "exhaustive gf7");
            }
        }
    }

    /// The dispatcher agrees with long division on both sides of the crossover, so the shipped
    /// constant cannot silently select a wrong route. The degrees are chosen from the crossover
    /// rather than hard-coded, so this keeps testing both sides if the constant is re-measured.
    #[test]
    fn test_the_dispatcher_agrees_either_side_of_the_crossover() {
        type F = PrimeFieldElement64<2_147_483_647>;
        let crossover = newton_crossover::<F>();
        let mut rng = rand::rngs::StdRng::seed_from_u64(0x1_9304);
        // Balanced, so the crossover rule reduces to `min = max > crossover`.
        for degree in [crossover / 2, crossover - 1, crossover + 1, 2 * crossover] {
            let dividend = UnivariatePolynomial::<F>::rand(2 * degree as u64, &mut rng);
            let divisor = UnivariatePolynomial::<F>::rand(degree as u64, &mut rng);
            let chose_newton = newton_is_cheaper::<F>(degree + 1, degree + 1);
            assert_eq!(
                chose_newton,
                degree + 1 > crossover,
                "the balanced rule is not the crossover at degree {}",
                degree
            );
            assert_routes_agree(&dividend, &divisor, &format!("degree {}", degree));
        }
    }

    /// The crossover rule is exactly the measured constant on a balanced division.
    #[test]
    fn test_the_balanced_crossover_is_the_constant() {
        for crossover in [4usize, 16, 96, 384, 512, 1000] {
            assert!(
                !newton_is_cheaper_at(crossover, crossover, crossover),
                "crossover {} should be long division at the constant itself",
                crossover
            );
            assert!(
                newton_is_cheaper_at(crossover + 1, crossover + 1, crossover),
                "crossover {} should be Newton one above it",
                crossover
            );
        }
    }

    /// A long quotient against a short divisor stays on long division — dividing degree 10^6 by
    /// degree 250 is 2.5e8 multiplications long-hand and `M(10^6)` by Newton — while a short
    /// quotient against a long divisor takes Newton, which is the case a `min(k, m)` rule got
    /// wrong and the measurement caught.
    #[test]
    fn test_the_rule_is_asymmetric_in_the_quotient_and_the_divisor() {
        let crossover = 1024;
        // A long quotient against a short divisor: long division, by three orders of magnitude.
        assert!(!newton_is_cheaper_at(1_000_000, 251, crossover));
        assert!(!newton_is_cheaper_at(65_536, 1024, crossover));
        // The same lengths the other way round: Newton, measured at 3.6x on this workstation.
        assert!(newton_is_cheaper_at(1025, 65_536, crossover));
        // Balanced and above the crossover: Newton.
        assert!(newton_is_cheaper_at(4096, 4096, crossover));
        // Balanced and below it: long division.
        assert!(!newton_is_cheaper_at(512, 512, crossover));
    }

    /// The floor on the quotient length is what refuses a tiny precision against a huge divisor,
    /// where the inequality alone would say Newton and the un-amortized fixed cost says otherwise.
    #[test]
    fn test_the_floor_on_the_precision_refuses_a_tiny_quotient() {
        const E: f64 = KARATSUBA_EXPONENT;
        let crossover = 1024;
        // The inequality on its own is satisfied here...
        let c = (crossover as f64).powf(2.0 - E);
        assert!((1_000_000.0_f64) > c * (2.0_f64).powf(E - 1.0));
        // ...and the floor is what declines it anyway.
        assert!(!newton_is_cheaper_at(2, 1_000_000, crossover));
        assert!(!newton_is_cheaper_at(crossover, usize::MAX / 2, crossover));
        // One above the floor, the inequality decides again.
        assert!(newton_is_cheaper_at(
            crossover + 1,
            usize::MAX / 2,
            crossover
        ));
    }

    /// `/` is the quotient of `div_with_remainder` on both routes, which is what makes skipping
    /// the Newton remainder recovery safe rather than merely cheaper.
    #[test]
    fn test_the_quotient_only_path_matches_the_full_division() {
        type F = PrimeFieldElement64<2_147_483_647>;
        let crossover = newton_crossover::<F>();
        let mut rng = rand::rngs::StdRng::seed_from_u64(0x1_9305);
        for degree in [1usize, 7, crossover - 1, crossover + 1] {
            let dividend = UnivariatePolynomial::<F>::rand(2 * degree as u64, &mut rng);
            let divisor = UnivariatePolynomial::<F>::rand(degree as u64, &mut rng);
            assert_eq!(
                quotient(&dividend, &divisor),
                div_with_remainder(&dividend, &divisor).0,
                "degree {}",
                degree
            );
        }
        // And on the shapes with no quotient at all.
        let f = UnivariatePolynomial::<F>::rand(3, &mut rng);
        let g = UnivariatePolynomial::<F>::rand(9, &mut rng);
        assert_eq!(quotient(&f, &g), UnivariatePolynomial::zero());
    }

    proptest! {
        /// Over GF(7), the Newton route is long division's quotient and remainder exactly.
        #[test]
        fn proptest_the_routes_agree_over_gf7(
            p in ((0..=60usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<DensePolynomial<Zp7>>)),
            q in ((0..=60usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<DensePolynomial<Zp7>>)),
        ) {
            if q.is_zero() {
                return Ok(());
            }
            prop_assert_eq!(
                div_with_remainder_newton_unstable(&p, &q),
                div_with_remainder_long_unstable(&p, &q)
            );
        }

        /// The same over a 31-bit field, where the coefficients are not almost all small.
        #[test]
        fn proptest_the_routes_agree_over_mersenne31(seed: u64, n in 0u64..60, m in 0u64..60) {
            type F = PrimeFieldElement64<2_147_483_647>;
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let dividend = UnivariatePolynomial::<F>::rand(n, &mut rng);
            let divisor = UnivariatePolynomial::<F>::rand(m, &mut rng);
            if divisor.is_zero() {
                return Ok(());
            }
            prop_assert_eq!(
                div_with_remainder_newton_unstable(&dividend, &divisor),
                div_with_remainder_long_unstable(&dividend, &divisor)
            );
        }
    }

    proptest! {
        #[test]
        fn test_recover_dividend(
            p in ((0..=100usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<DensePolynomial<Zp7>>)),
            q in ((0..=100usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<DensePolynomial<Zp7>>)),
        ) {
            if q.is_zero() {
                return Ok(())
            }
            let (quotient, remainder) = div_with_remainder(&p, &q);
            let recovered = (quotient * q) + remainder;
            prop_assert_eq!(p, recovered)
        }
    }
}
