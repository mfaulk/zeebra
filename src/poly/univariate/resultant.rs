//! `Res(f, g)` by the Euclidean algorithm, in `O(d²)` rather than the `O(d³)` of a Sylvester
//! determinant.
//!
//! The bivariate elimination route of `src/grobner/research/resultant.rs` recovers `Res_y(f, g)`
//! by taking one order-`(n + m)` Sylvester determinant per sample point. Its module docs record
//! why a Euclidean algorithm was not used: the specialization trap, which is that
//! `Res(f(a,·), g(a,·))` is **not** `Res_y(f, g)(a)` when a leading coefficient in `y` vanishes at
//! `a`, where a determinant commutes with evaluation unconditionally. That decision was made at a
//! Sylvester order of 18, where the stage cost milliseconds.
//!
//! [`resultant_at_formal_degrees`] is the trap closed in `O(1)` per sample: the determinant of the
//! Sylvester matrix at *formal* degrees `n` and `m` differs from the true resultant of the
//! specialized pair by a known power of a known leading coefficient, and is zero when both
//! coefficients vanish. So the asymptotic win is available without the case analysis being left to
//! the caller. See `docs/research/structured-sylvester.md`.

use crate::{FiniteField, Polynomial, UnivariatePolynomial};

/// `Res(f, g)`, the resultant of two univariate polynomials, by the Euclidean algorithm.
///
/// Zero if either argument is the zero polynomial, and zero exactly when `f` and `g` share a root
/// in an extension of `F` (equivalently, when `gcd(f, g)` is nonconstant).
///
/// Drives `f mod g` down the remainder sequence using the identity
/// `Res(f, g) = (−1)^{deg f · deg g} · lc(g)^{deg f − deg r} · Res(g, r)`, so the cost is that of
/// the classical Euclidean algorithm: `O(d²)` field operations against a Sylvester determinant's
/// `O(d³)`.
pub fn resultant<F: FiniteField>(f: &UnivariatePolynomial<F>, g: &UnivariatePolynomial<F>) -> F {
    if f.is_zero() || g.is_zero() {
        return F::zero();
    }
    let mut a = f.clone();
    let mut b = g.clone();
    let mut accumulated = F::one();

    loop {
        let (n, m) = (a.degree(), b.degree());
        // Res(f, c) = c^{deg f} for a nonzero constant c, which is also the right answer when
        // both are constants: the empty Sylvester determinant is one.
        if m == 0 {
            return accumulated * leading(&b).pow(u128::from(n));
        }
        let remainder = &a % &b;
        if remainder.is_zero() {
            // b divides a and deg b >= 1, so the two share a root.
            return F::zero();
        }
        if (n * m) % 2 == 1 {
            accumulated = -accumulated;
        }
        accumulated *= leading(&b).pow(u128::from(n - remainder.degree()));
        a = b;
        b = remainder;
    }
}

/// `det Syl_{n,m}(f, g)`, the Sylvester determinant taken at *formal* degrees `n` and `m`.
///
/// This is the quantity a bivariate elimination needs per sample: the formal degrees come from the
/// bivariate coefficient-vector lengths and are fixed across samples, while the specialized
/// polynomials may have lower true degree at particular points. Evaluating the matrix and taking
/// its determinant gives this; [`resultant`] alone does not.
///
/// Returns zero when `f` or `g` is the zero polynomial, and when both fall below their formal
/// degrees — in that case the matrix is singular by inspection, since its first column vanishes.
///
/// # Panics
/// If `n < deg f` or `m < deg g`, which would not be formal degrees for these polynomials.
pub fn resultant_at_formal_degrees<F: FiniteField>(
    f: &UnivariatePolynomial<F>,
    g: &UnivariatePolynomial<F>,
    n: u32,
    m: u32,
) -> F {
    if f.is_zero() || g.is_zero() {
        return F::zero();
    }
    let (true_n, true_m) = (f.degree(), g.degree());
    assert!(
        n >= true_n && m >= true_m,
        "formal degree below true degree"
    );

    match (n == true_n, m == true_m) {
        (true, true) => resultant(f, g),
        // Expanding along the first column leaves one nonzero entry, lc(g), in row m, so each
        // unit of degree deficit in f contributes (−1)^m · lc(g) and drops the formal degree by
        // one.
        (false, true) => {
            let deficit = n - true_n;
            let sign = if (m * deficit) % 2 == 1 {
                -F::one()
            } else {
                F::one()
            };
            sign * leading(g).pow(u128::from(deficit)) * resultant(f, g)
        }
        // The mirror case carries no sign: the two reflections through
        // `Res(f, g) = (−1)^{nm} Res(g, f)` cancel.
        (true, false) => leading(f).pow(u128::from(m - true_m)) * resultant(f, g),
        (false, false) => F::zero(),
    }
}

fn leading<F: FiniteField>(p: &UnivariatePolynomial<F>) -> F {
    p.coefficients()[p.degree() as usize]
}

#[cfg(test)]
mod tests {
    use super::{resultant, resultant_at_formal_degrees};
    use crate::{
        fields::Zp2147483647,
        identities::{One, Zero},
        linalg::Matrix,
        FiniteField, Polynomial, UnivariatePolynomial,
    };
    use rand::{prelude::StdRng, Rng, SeedableRng};

    type F = Zp2147483647;

    fn poly(coefficients: &[u64]) -> UnivariatePolynomial<F> {
        let elements: Vec<F> = coefficients.iter().map(|c| F::new(*c)).collect();
        UnivariatePolynomial::new(&elements)
    }

    /// `det Syl_{n,m}(f, g)` built explicitly, as the independent reference the tests compare to.
    fn sylvester_reference(
        f: &UnivariatePolynomial<F>,
        g: &UnivariatePolynomial<F>,
        n: usize,
        m: usize,
    ) -> F {
        let size = n + m;
        if size == 0 {
            return F::one();
        }
        // Coefficients padded to the formal degree, highest power first.
        let row_of = |p: &UnivariatePolynomial<F>, formal: usize| -> Vec<F> {
            let coefficients = p.coefficients();
            (0..=formal)
                .rev()
                .map(|i| coefficients.get(i).copied().unwrap_or(F::zero()))
                .collect()
        };
        let f_row = row_of(f, n);
        let g_row = row_of(g, m);
        let mut elements = vec![F::zero(); size * size];
        for row in 0..m {
            for (offset, value) in f_row.iter().enumerate() {
                elements[row * size + row + offset] = *value;
            }
        }
        for row in 0..n {
            for (offset, value) in g_row.iter().enumerate() {
                elements[(m + row) * size + row + offset] = *value;
            }
        }
        Matrix::new(size, size, &elements)
            .determinant()
            .expect("square")
    }

    #[test]
    // The Euclidean resultant agrees with an explicitly built Sylvester determinant on random
    // full-degree pairs, over a range of degrees.
    fn euclidean_resultant_matches_the_sylvester_determinant() {
        let mut rng = StdRng::seed_from_u64(20261106);
        for degree_f in 1..=7usize {
            for degree_g in 1..=7usize {
                for _ in 0..4 {
                    let mut fc: Vec<u64> = (0..=degree_f).map(|_| rng.gen_range(0..1000)).collect();
                    let mut gc: Vec<u64> = (0..=degree_g).map(|_| rng.gen_range(0..1000)).collect();
                    // Force the true degree to equal the formal degree.
                    fc[degree_f] = rng.gen_range(1..1000);
                    gc[degree_g] = rng.gen_range(1..1000);
                    let (f, g) = (poly(&fc), poly(&gc));
                    assert_eq!(
                        resultant(&f, &g),
                        sylvester_reference(&f, &g, degree_f, degree_g),
                        "f = {fc:?}, g = {gc:?}"
                    );
                }
            }
        }
    }

    #[test]
    // The formal-degree correction reproduces the Sylvester determinant when one or both
    // specialized polynomials fall below their formal degree -- the specialization trap.
    fn formal_degree_correction_handles_vanishing_leading_coefficients() {
        let mut rng = StdRng::seed_from_u64(7);
        for formal_f in 1..=6usize {
            for formal_g in 1..=6usize {
                for drop_f in 0..=formal_f {
                    for drop_g in 0..=formal_g {
                        let true_f = formal_f - drop_f;
                        let true_g = formal_g - drop_g;
                        let mut fc: Vec<u64> =
                            (0..=true_f).map(|_| rng.gen_range(0..500)).collect();
                        let mut gc: Vec<u64> =
                            (0..=true_g).map(|_| rng.gen_range(0..500)).collect();
                        fc[true_f] = rng.gen_range(1..500);
                        gc[true_g] = rng.gen_range(1..500);
                        let (f, g) = (poly(&fc), poly(&gc));
                        let expected = sylvester_reference(&f, &g, formal_f, formal_g);
                        let got =
                            resultant_at_formal_degrees(&f, &g, formal_f as u32, formal_g as u32);
                        assert_eq!(
                            got, expected,
                            "formal ({formal_f}, {formal_g}), true ({true_f}, {true_g}), \
                             f = {fc:?}, g = {gc:?}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    // The resultant vanishes exactly when the two polynomials share a root.
    fn resultant_vanishes_on_a_shared_root() {
        let shared = poly(&[7, 1]); // x + 7
        let f = &poly(&[3, 1]) * &shared;
        let g = &poly(&[11, 1]) * &shared;
        assert_eq!(resultant(&f, &g), F::zero());
        assert_ne!(resultant(&poly(&[3, 1]), &poly(&[11, 1])), F::zero());
    }

    #[test]
    // Res(f, c) = c^{deg f} for a nonzero constant, and the zero polynomial gives zero.
    fn constant_and_zero_arguments() {
        let f = poly(&[1, 2, 3]);
        assert_eq!(resultant(&f, &poly(&[5])), F::new(5).pow(2));
        assert_eq!(resultant(&poly(&[5]), &f), F::new(5).pow(2));
        assert_eq!(resultant(&poly(&[0]), &f), F::zero());
        assert_eq!(resultant(&f, &poly(&[0])), F::zero());
    }
}
