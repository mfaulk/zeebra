//! The extended Euclidean algorithm on univariate polynomials, stopped early.
//!
//! `gcd` in [`crate::gcd`] runs the Euclidean remainder sequence to completion and keeps only the
//! last nonzero remainder. A Reed-Solomon decoder needs the *middle* of that sequence instead:
//! the key equation `Λ(x)S(x) ≡ Ω(x) mod x^{2t}` is solved by running the sequence on
//! `(x^{2t}, S(x))` and halting at the first remainder of degree below `t`, at which point the
//! remainder is `Ω` and its Bézout cofactor against `S` is `Λ`. Only the cofactor of the *second*
//! argument is tracked, because the cofactor of `x^{2t}` is never read.

use crate::{FiniteField, Polynomial, UnivariatePolynomial};

/// One step of the Euclidean sequence on `(a, b)`, halted at the first remainder of degree below
/// `degree_bound`: the pair `(v, r)` with `r = u*a + v*b` and `deg(r) < degree_bound`.
///
/// `a` is expected to have degree at least `degree_bound`, so that the sequence takes at least one
/// step and `v` is nonzero. The Bézout cofactor `u` of `a` is not computed.
pub(crate) fn partial_bezout<F: FiniteField>(
    a: &UnivariatePolynomial<F>,
    b: &UnivariatePolynomial<F>,
    degree_bound: u32,
) -> (UnivariatePolynomial<F>, UnivariatePolynomial<F>) {
    // r_prev = a with cofactor v_prev = 0; r_cur = b with cofactor v_cur = 1. The invariant
    // r = u*a + v*b is maintained for both rows, with u never materialized.
    let mut r_prev = a.clone();
    let mut r_cur = b.clone();
    let mut v_prev = UnivariatePolynomial::zero();
    let mut v_cur = UnivariatePolynomial::one();

    // A zero remainder ends the sequence: b divides a, and there is nothing of lower degree to
    // reach. The caller treats a zero Ω as "no error" or "uncorrectable" as its own case needs.
    while !r_cur.is_zero() && r_cur.degree() >= degree_bound {
        let (quotient, remainder) = r_prev.div_with_remainder(&r_cur);
        r_prev = r_cur;
        r_cur = remainder;
        let v_next = &v_prev - &(&quotient * &v_cur);
        v_prev = v_cur;
        v_cur = v_next;
    }

    (v_cur, r_cur)
}

#[cfg(test)]
mod tests {
    use super::partial_bezout;
    use crate::{codes::reed_solomon::tests::poly, fields::Zp13, Polynomial, UnivariatePolynomial};

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
}
