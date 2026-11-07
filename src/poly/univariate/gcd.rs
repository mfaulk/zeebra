//! Greatest common divisor and least common multiple of two univariate polynomials over a field F.
//!
//! The greatest common divisor of two polynomials f(x) and g(x) over a field F, denoted gcd(f, g),
//! is a highest-degree polynomial d(x) that divides both f(x) and g(x). The gcd is unique up to
//! multiplication by a nonzero constant in F. Typically, gcd(f, g) is defined to be the unique
//! monic polynomial d(x) such that d(x) divides both f(x) and g(x). The least common multiple is
//! normalized the same way, and is `f * g / gcd(f, g)`.
//!
//! The Euclidean algorithm below is classical, so it is `O(d^2)` in the division it drives.
//! Half-GCD would be `O(M(d) log d)` and is not written: `M` at the `Mul` operator is still
//! schoolbook, which makes the recursive algorithm the slower one. See §4.5 of
//! `docs/research/fast-univariate.md`.

use crate::{FiniteField, Polynomial, UnivariatePolynomial};

/// The monic greatest common divisor of two polynomials.
pub fn gcd<F: FiniteField>(
    a: &UnivariatePolynomial<F>,
    b: &UnivariatePolynomial<F>,
) -> UnivariatePolynomial<F> {
    let mut f = a.clone();
    let mut g = b.clone();

    // Euclidean algorithm
    while !g.is_zero() {
        let remainder = &f % &g;
        f = g;
        g = remainder;
    }

    // "The" GCD is chosen to be monic (i.e. the leading coefficient is 1).
    make_monic(&f)
}

/// The monic least common multiple of two polynomials, or zero if either is zero.
///
/// `a * b / gcd(a, b)`, dividing before the normalization so that the product is formed once.
pub fn lcm<F: FiniteField>(
    a: &UnivariatePolynomial<F>,
    b: &UnivariatePolynomial<F>,
) -> UnivariatePolynomial<F> {
    // gcd(0, b) is b, so the quotient below would be well defined and equal to zero — but only
    // when b is nonzero too, and gcd(0, 0) is the zero polynomial the division would panic on.
    if a.is_zero() || b.is_zero() {
        return UnivariatePolynomial::zero();
    }

    make_monic(&(&(a * b) / &gcd(a, b)))
}

/// The Euclidean remainder sequence on `(a, b)`, halted at the first remainder of degree below
/// `degree_bound`: the pair `(v, r)` with `r = u*a + v*b` for some `u` and `deg(r) <
/// degree_bound`.
///
/// `a` is expected to have degree at least `degree_bound`, so that the sequence takes at least one
/// step and `v` is nonzero. The Bézout cofactor `u` of `a` is not computed, because the consumers
/// of the halted form do not read it; [`xgcd`] recovers it with one division when it is wanted.
///
/// A zero remainder ends the sequence early — `b` divides `a`, and there is nothing of lower
/// degree to reach — so a zero `r` is a possible answer and callers must handle it.
///
/// Reed-Solomon decoding solves the key equation `Λ(x)S(x) ≡ Ω(x) mod x^{2t}` by running this on
/// `(x^{2t}, S(x))` with `degree_bound = t`, which yields `Ω` as the remainder and `Λ` as the
/// cofactor. Rational reconstruction and Padé approximation want the same primitive.
pub fn partial_bezout<F: FiniteField>(
    a: &UnivariatePolynomial<F>,
    b: &UnivariatePolynomial<F>,
    degree_bound: u32,
) -> (UnivariatePolynomial<F>, UnivariatePolynomial<F>) {
    let (_, current) = bezout_rows(a, b, degree_bound);
    (current.cofactor, current.remainder)
}

/// The monic greatest common divisor of two polynomials together with cofactors witnessing it:
/// `(g, u, v)` with `g = u*a + v*b`.
///
/// Running [`partial_bezout`]'s sequence to completion rather than halting it: the last nonzero
/// remainder is the gcd, and `degree_bound = 0` is what "run to completion" means, since every
/// nonzero remainder has degree at least zero.
pub fn xgcd<F: FiniteField>(
    a: &UnivariatePolynomial<F>,
    b: &UnivariatePolynomial<F>,
) -> (
    UnivariatePolynomial<F>,
    UnivariatePolynomial<F>,
    UnivariatePolynomial<F>,
) {
    // gcd(a, 0) = monic(a), and the sequence below cannot produce it: with b zero the loop takes
    // no step, so the last nonzero remainder is `a` itself, sitting in a row that carries no
    // cofactor. The normalization is the whole content of `u` here. gcd(0, 0) = 0 falls out with
    // zero cofactors, which is also what keeps the `/ a` below away from a zero divisor.
    if b.is_zero() {
        if a.is_zero() {
            let zero = UnivariatePolynomial::zero();
            return (zero.clone(), zero.clone(), zero);
        }
        let scale = a.coefficients().last().unwrap().inverse();
        return (
            a.scale(&scale),
            UnivariatePolynomial::new(&[scale]),
            UnivariatePolynomial::zero(),
        );
    }

    let (previous, _) = bezout_rows(a, b, 0);

    // `previous` holds the last nonzero remainder, which is the gcd up to a constant. Scaling the
    // row — remainder and cofactor together — preserves the identity r = u*a + v*b.
    let scale = previous.remainder.coefficients().last().unwrap().inverse();
    let g = previous.remainder.scale(&scale);
    let v = previous.cofactor.scale(&scale);

    // `u` was never tracked, so it is recovered from the identity: g - v*b is a multiple of `a`
    // by construction, and one exact division is cheaper than carrying a second cofactor row
    // through every step. `a` is zero only when b is too, which returned above.
    if a.is_zero() {
        // gcd(0, b) = monic(b), reached through the sequence: the single step leaves b as the last
        // nonzero remainder with cofactor one. Nothing is a multiple of the zero polynomial, so
        // `u` is read off as zero instead of divided out.
        return (g, UnivariatePolynomial::zero(), v);
    }
    let u = &(&g - &(&v * b)) / a;

    (g, u, v)
}

/// One row of the extended Euclidean sequence: a remainder and its Bézout cofactor against the
/// sequence's second argument.
struct BezoutRow<F: FiniteField> {
    remainder: UnivariatePolynomial<F>,
    cofactor: UnivariatePolynomial<F>,
}

/// The two rows the halt lands between: the last one of degree at least `degree_bound`, and the
/// first one below it (or zero). Only the cofactor of `b` is carried; the invariant maintained is
/// `remainder = u*a + cofactor*b` with `u` never materialized.
fn bezout_rows<F: FiniteField>(
    a: &UnivariatePolynomial<F>,
    b: &UnivariatePolynomial<F>,
    degree_bound: u32,
) -> (BezoutRow<F>, BezoutRow<F>) {
    let mut previous = BezoutRow {
        remainder: a.clone(),
        cofactor: UnivariatePolynomial::zero(),
    };
    let mut current = BezoutRow {
        remainder: b.clone(),
        cofactor: UnivariatePolynomial::one(),
    };

    while !current.remainder.is_zero() && current.remainder.degree() >= degree_bound {
        let (quotient, remainder) = previous.remainder.div_with_remainder(&current.remainder);
        let cofactor = &previous.cofactor - &(&quotient * &current.cofactor);
        previous = current;
        current = BezoutRow {
            remainder,
            cofactor,
        };
    }

    (previous, current)
}

/// Scale a polynomial to be monic.
fn make_monic<F: FiniteField>(f: &UnivariatePolynomial<F>) -> UnivariatePolynomial<F> {
    let leading_coefficient = f.coefficients().last().unwrap();
    if !leading_coefficient.is_zero() && !leading_coefficient.is_one() {
        f.scale(&leading_coefficient.inverse())
    } else {
        f.clone()
    }
}

#[cfg(test)]
mod tests {
    use crate::poly::univariate::PolynomialParams;
    use proptest::{prelude::*, proptest};

    use crate::{
        fields::{Zp1091, Zp13},
        poly::univariate::gcd::{gcd, lcm, make_monic, partial_bezout, xgcd},
        FiniteField, One, Polynomial, UnivariatePolynomial, Zero,
    };

    /// A polynomial from its coefficients in ascending degree order.
    fn poly<F: FiniteField>(coefficients: &[u64]) -> UnivariatePolynomial<F> {
        let elements: Vec<F> = coefficients.iter().map(|c| F::new(*c)).collect();
        UnivariatePolynomial::new(&elements)
    }

    // The returned pair satisfies r = u*a + v*b for some u, verified as r - v*b being divisible
    // by a, and r's degree is below the requested bound.
    #[test]
    fn test_the_halted_sequence_satisfies_the_bezout_identity() {
        type F = Zp13;
        // a = x^4, b = 1 + 2x + 3x^2 + 4x^3.
        let a = poly::<F>(&[0, 0, 0, 0, 1]);
        let b = poly::<F>(&[1, 2, 3, 4]);
        let (v, r) = partial_bezout(&a, &b, 2);
        assert!(r.degree() < 2);
        let residue = &(&r - &(&v * &b)) % &a;
        assert!(residue.is_zero(), "r - v*b is not a multiple of a");
    }

    // A `b` that already has degree below the bound is returned untouched, with cofactor one.
    #[test]
    fn test_a_remainder_already_below_the_bound_takes_no_steps() {
        type F = Zp13;
        let a = poly::<F>(&[0, 0, 0, 0, 1]);
        let b = poly::<F>(&[7]);
        let (v, r) = partial_bezout(&a, &b, 2);
        assert_eq!(r, b);
        assert_eq!(v, UnivariatePolynomial::<F>::one());
    }

    // A `b` dividing `a` drives the remainder to zero, which halts the loop rather than dividing
    // by the zero polynomial.
    #[test]
    fn test_an_exact_division_halts_at_a_zero_remainder() {
        type F = Zp13;
        // a = x^4, b = x^2, so the first remainder is already zero.
        let a = poly::<F>(&[0, 0, 0, 0, 1]);
        let b = poly::<F>(&[0, 0, 1]);
        let (_v, r) = partial_bezout(&a, &b, 1);
        assert!(r.is_zero());
    }

    // xgcd returns the same monic gcd that `gcd` does, together with cofactors witnessing it.
    #[test]
    fn test_xgcd_agrees_with_gcd_and_witnesses_it() {
        type F = Zp13;
        // a = (x+1)(x+2) = 2 + 3x + x^2, b = (x+1)(x+3) = 3 + 4x + x^2; gcd is x + 1.
        let a = poly::<F>(&[2, 3, 1]);
        let b = poly::<F>(&[3, 4, 1]);
        let (g, u, v) = xgcd(&a, &b);
        assert_eq!(g, gcd(&a, &b));
        assert_eq!(g, poly::<F>(&[1, 1]));
        assert_eq!(&(&u * &a) + &(&v * &b), g);
    }

    // xgcd of a polynomial with zero is that polynomial made monic, with the scaling carried in
    // the cofactor of the nonzero argument and a zero cofactor on the other side.
    #[test]
    fn test_xgcd_with_zero_on_either_side() {
        type F = Zp13;
        // 3 + 6x^2 is not monic, so the normalization is observable in the cofactor.
        let a = poly::<F>(&[3, 0, 6]);
        let zero = UnivariatePolynomial::<F>::zero();

        let (g, u, v) = xgcd(&a, &zero);
        assert_eq!(g, gcd(&a, &zero));
        assert!(v.is_zero());
        assert_eq!(&(&u * &a) + &(&v * &zero), g);

        let (g, u, v) = xgcd(&zero, &a);
        assert_eq!(g, gcd(&zero, &a));
        assert!(u.is_zero());
        assert_eq!(&(&u * &zero) + &(&v * &a), g);
    }

    // xgcd(0, 0) is the zero polynomial with zero cofactors, rather than a division by zero.
    #[test]
    fn test_xgcd_of_zero_and_zero() {
        let zero = UnivariatePolynomial::<Zp13>::zero();
        let (g, u, v) = xgcd(&zero, &zero);
        assert!(g.is_zero());
        assert!(u.is_zero());
        assert!(v.is_zero());
    }

    #[test]
    /// gcd(0, 0) = 0
    fn test_gcd_of_zero_and_zero() {
        let zero = UnivariatePolynomial::<Zp1091>::zero();
        assert_eq!(gcd(&zero, &zero), zero);
    }

    #[test]
    /// lcm(0, 0) = 0
    fn test_lcm_of_zero_and_zero() {
        let zero = UnivariatePolynomial::<Zp1091>::zero();
        assert_eq!(lcm(&zero, &zero), zero);
    }

    proptest! {

        #[test]
        /// gcd(a,b) is a monic polynomial (i.e. the leading coefficient is 1).
        fn test_gcd_is_monic(
            a in ((0..=100usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>)),
            b in ((0..=100usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>))) {
            let gcd = gcd(&a, &b);
            prop_assert_eq!(gcd.coefficients().last().unwrap(), &Zp1091::one());
        }

        #[test]
        /// gcd(a, b) divides a and b.
        fn test_gcd_divides_a_and_b(
            a in ((0..=100usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>)),
            b in ((0..=100usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>))) {
            let gcd = gcd(&a, &b);
            prop_assert_eq!(&a % &gcd, UnivariatePolynomial::<Zp1091>::zero());
            prop_assert_eq!(&b % &gcd, UnivariatePolynomial::<Zp1091>::zero());
        }

        #[test]
        /// gcd(0, a) = gcd(a, 0) = a, up to a constant factor.
        fn test_gcd_with_zero(
            a in ((0..=100usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>))) {
            let zero = UnivariatePolynomial::<Zp1091>::zero();
            let a_monic = make_monic(&a);
            prop_assert_eq!(gcd(&zero, &a), a_monic.clone());
            prop_assert_eq!(gcd(&a, &zero), a_monic.clone());
        }

        #[test]
        /// gcd(1, a) = gcd(a, 1) = 1
        fn test_gcd_with_one(a: UnivariatePolynomial<Zp1091>) {
            let one = UnivariatePolynomial::<Zp1091>::one();
            prop_assert_eq!(gcd(&one, &a), one.clone());
            prop_assert_eq!(gcd(&a, &one), one);
        }

        #[test]
        /// gcd(a, b) = gcd(b, a)
        fn test_gcd_is_symmetric(
            a in ((0..=100usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>)),
            b in ((0..=100usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>))) {
            prop_assert_eq!(gcd(&a, &b), gcd(&b, &a));
        }

        #[test]
        /// lcm(a, b) is monic whenever it is nonzero.
        fn test_lcm_is_monic(
            a in ((0..=50usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>)),
            b in ((0..=50usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>))) {
            let lcm = lcm(&a, &b);
            if !lcm.is_zero() {
                prop_assert_eq!(lcm.coefficients().last().unwrap(), &Zp1091::one());
            }
        }

        #[test]
        /// a and b both divide lcm(a, b).
        fn test_lcm_is_divisible_by_a_and_b(
            a in ((1..=50usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>)),
            b in ((1..=50usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>))) {
            if a.is_zero() || b.is_zero() {
                return Ok(());
            }
            let lcm = lcm(&a, &b);
            prop_assert!((&lcm % &a).is_zero());
            prop_assert!((&lcm % &b).is_zero());
        }

        #[test]
        /// lcm(a, b) * gcd(a, b) = a * b, up to the monic normalization of each side.
        fn test_lcm_times_gcd_is_the_product(
            a in ((1..=50usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>)),
            b in ((1..=50usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>))) {
            if a.is_zero() || b.is_zero() {
                return Ok(());
            }
            prop_assert_eq!(&lcm(&a, &b) * &gcd(&a, &b), make_monic(&(&a * &b)));
        }

        #[test]
        /// lcm(a, a) = a, up to a constant factor.
        fn test_lcm_of_a_with_itself(
            a in ((1..=50usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>))) {
            if a.is_zero() {
                return Ok(());
            }
            prop_assert_eq!(lcm(&a, &a), make_monic(&a));
        }

        #[test]
        /// lcm(1, a) = lcm(a, 1) = a, up to a constant factor.
        fn test_lcm_with_one(
            a in ((1..=50usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>))) {
            if a.is_zero() {
                return Ok(());
            }
            let one = UnivariatePolynomial::<Zp1091>::one();
            let a_monic = make_monic(&a);
            prop_assert_eq!(lcm(&one, &a), a_monic.clone());
            prop_assert_eq!(lcm(&a, &one), a_monic);
        }

        #[test]
        /// lcm(0, a) = lcm(a, 0) = 0: zero has no nonzero multiple in common with anything.
        fn test_lcm_with_zero(
            a in ((0..=50usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>))) {
            let zero = UnivariatePolynomial::<Zp1091>::zero();
            prop_assert_eq!(lcm(&zero, &a), zero.clone());
            prop_assert_eq!(lcm(&a, &zero), zero);
        }

        #[test]
        /// xgcd(a, b) returns gcd(a, b) with cofactors satisfying u*a + v*b = gcd(a, b).
        fn test_xgcd_cofactors_witness_the_gcd(
            a in ((0..=50usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>)),
            b in ((0..=50usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>))) {
            let (g, u, v) = xgcd(&a, &b);
            prop_assert_eq!(&g, &gcd(&a, &b));
            prop_assert_eq!(&(&u * &a) + &(&v * &b), g);
        }

        #[test]
        /// The halted sequence's remainder is below the bound and lies in the ideal (a, b).
        fn test_partial_bezout_halts_below_the_bound(
            b in ((0..=20usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>)),
            bound in 1..=10u32) {
            // a = x^{2*bound}, the shape the key equation uses, so deg a >= bound holds.
            let mut coefficients = vec![Zp1091::zero(); (2 * bound + 1) as usize];
            coefficients[(2 * bound) as usize] = Zp1091::one();
            let a = UnivariatePolynomial::new(&coefficients);

            let (v, r) = partial_bezout(&a, &b, bound);
            prop_assert!(r.is_zero() || r.degree() < bound);
            prop_assert!((&(&r - &(&v * &b)) % &a).is_zero());
        }

        #[test]
        // gcd(a,b)= gcd(a,b+ra) for any polynomial r.
        fn test_gcd_is_linear_combination(
            a in ((0..=100usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>)),
            b in ((0..=100usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>)),
            r in ((0..=100usize).prop_map(PolynomialParams::from).prop_flat_map(any_with::<UnivariatePolynomial<Zp1091>>))) {
            let gcd_ab = gcd(&a, &b);
            let gcd_a_b_plus_ra = gcd(&a, &(b + &a * &r));
            prop_assert_eq!(gcd_ab, gcd_a_b_plus_ra);
        }
    }
}
