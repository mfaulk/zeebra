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

/// Trailing zeros removed, so the length is the true degree plus one. Empty is the zero polynomial.
fn trimmed<F: FiniteField>(coefficients: &[F]) -> Vec<F> {
    let mut out = coefficients.to_vec();
    while out.last().is_some_and(|c| c.is_zero()) {
        out.pop();
    }
    out
}

/// `a mod b`, trimmed, over raw coefficients. `b` must be nonzero.
fn remainder<F: FiniteField>(a: &[F], b: &[F]) -> Vec<F> {
    let n = b.len() - 1;
    let inverse = b[n].inverse();
    let mut r = a.to_vec();
    while r.len() > n {
        let top = r.len() - 1;
        let factor = r[top] * inverse;
        if !factor.is_zero() {
            for i in 0..=n {
                let value = factor * b[i];
                r[top - n + i] -= value;
            }
        }
        r.pop();
        while r.last().is_some_and(|c| c.is_zero()) {
            r.pop();
        }
    }
    r
}

/// `Res(a, b)` over raw coefficients, both trimmed and nonzero so the degrees are exact.
///
/// Iterative, and the same recurrence [`resultant`] uses. The difference is that this one never
/// builds a [`UnivariatePolynomial`]: the sequence is as long as the degree, so at the orders a
/// six-round elimination reaches, one allocation per step is the dominant cost of the step.
fn exact_resultant<F: FiniteField>(a: &[F], b: &[F]) -> F {
    let mut a = a.to_vec();
    let mut b = b.to_vec();
    let mut accumulated = F::one();

    // Applied once so the loop can assume `deg a >= deg b`.
    if a.len() < b.len() {
        if ((a.len() - 1) * (b.len() - 1)) % 2 == 1 {
            accumulated = -accumulated;
        }
        std::mem::swap(&mut a, &mut b);
    }

    loop {
        let n = a.len() - 1;
        let m = b.len() - 1;
        if m == 0 {
            return accumulated * b[0].pow(n as u128);
        }
        if (n * m) % 2 == 1 {
            accumulated = -accumulated;
        }
        let r = remainder(&a, &b);
        if r.is_empty() {
            // `b` divides `a` and `deg b >= 1`, so the two share a root.
            return F::zero();
        }
        accumulated *= b[m].pow((n - (r.len() - 1)) as u128);
        // `deg b = m > deg r`, so the `deg a >= deg b` invariant is preserved.
        a = b;
        b = r;
    }
}

/// `det Syl_{n,m}(a, b)` where the **formal** degrees are the slice lengths minus one.
///
/// The allocation-free form of [`resultant_at_formal_degrees`], for callers that already hold
/// coefficients rather than polynomials — which is what a bivariate elimination has at each sample
/// point, once per point, with the formal degrees fixed across the whole sweep.
///
/// The three corrections are the same ones [`resultant_at_formal_degrees`] applies, and the two
/// agree by differential test:
///
/// - `deg a = n' < n` with `lc(b) != 0`: `(-1)^(m(n-n')) · lc(b)^(n-n') · det Syl_{n',m}`.
/// - `deg b = m' < m` with `lc(a) != 0`: `lc(a)^(m-m') · det Syl_{n,m'}`, with no sign, because the
///   two reflections through `Res(a, b) = (-1)^(nm) Res(b, a)` cancel.
/// - both falling below their formal degrees: the first column vanishes, so zero.
///
/// # Panics
/// If either slice is empty. A polynomial has at least a constant term; the zero polynomial is
/// `&[F::zero()]`, not `&[]`.
pub fn resultant_from_coefficients<F: FiniteField>(a: &[F], b: &[F]) -> F {
    assert!(
        !a.is_empty() && !b.is_empty(),
        "a formal degree needs at least a constant term"
    );
    formal_determinant(a, a.len() - 1, b, b.len() - 1)
}

/// [`resultant_from_coefficients`] with the formal degrees passed explicitly, so the recursion can
/// lower them without reallocating the caller's slices.
fn formal_determinant<F: FiniteField>(a: &[F], n: usize, b: &[F], m: usize) -> F {
    // `Syl_{n,0}` is `n` rows of the constant `lc(b)` down the diagonal, and `Syl_{0,m}` likewise.
    // This also covers the empty matrix at `n = m = 0`, whose determinant is one.
    if m == 0 {
        return b[0].pow(n as u128);
    }
    if n == 0 {
        return a[0].pow(m as u128);
    }

    let a_true = trimmed(&a[..=n]);
    let b_true = trimmed(&b[..=m]);
    if a_true.is_empty() || b_true.is_empty() {
        // A vanishing argument makes its whole block of rows zero.
        return F::zero();
    }
    let n_true = a_true.len() - 1;
    let m_true = b_true.len() - 1;

    if n_true < n && m_true < m {
        return F::zero();
    }
    if n_true < n {
        let deficit = n - n_true;
        let corrected = b[m].pow(deficit as u128) * formal_determinant(&a_true, n_true, b, m);
        return if (m * deficit) % 2 == 1 {
            -corrected
        } else {
            corrected
        };
    }
    if m_true < m {
        let deficit = m - m_true;
        return a[n].pow(deficit as u128) * formal_determinant(a, n, &b_true, m_true);
    }

    exact_resultant(&a_true, &b_true)
}

#[cfg(test)]
mod tests {
    use super::{resultant, resultant_at_formal_degrees, resultant_from_coefficients};
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

    /// The coefficient form agrees with the explicit Sylvester determinant on exact degrees.
    #[test]
    fn coefficient_form_matches_the_sylvester_determinant_on_exact_degrees() {
        let a = [F::new(3), F::new(5), F::new(1)];
        let b = [F::new(2), F::new(7)];
        assert_eq!(
            resultant_from_coefficients(&a, &b),
            sylvester_reference(&poly(&[3, 5, 1]), &poly(&[2, 7]), 2, 1)
        );
    }

    /// A vanishing leading coefficient in either argument is corrected, not ignored.
    #[test]
    fn coefficient_form_corrects_a_dropped_leading_coefficient() {
        // Formal degree 2, true degree 1 — the specialization trap, on each side in turn.
        let a = [F::new(3), F::new(5), F::zero()];
        let b = [F::new(2), F::new(7)];
        assert_eq!(
            resultant_from_coefficients(&a, &b),
            sylvester_reference(&poly(&[3, 5]), &poly(&[2, 7]), 2, 1)
        );

        let a = [F::new(3), F::new(5), F::new(4)];
        let b = [F::new(2), F::new(7), F::zero()];
        assert_eq!(
            resultant_from_coefficients(&a, &b),
            sylvester_reference(&poly(&[3, 5, 4]), &poly(&[2, 7]), 2, 2)
        );
    }

    /// Both leading coefficients vanishing leaves a zero first column, so the determinant is zero.
    #[test]
    fn coefficient_form_is_zero_when_both_leading_coefficients_vanish() {
        let a = [F::new(3), F::new(5), F::zero()];
        let b = [F::new(2), F::new(7), F::zero()];
        assert!(resultant_from_coefficients(&a, &b).is_zero());
    }

    /// A shared factor terminates the remainder sequence early and the resultant is zero.
    #[test]
    fn coefficient_form_is_zero_on_a_common_factor() {
        // (y + 1)(y + 2) and (y + 1)(y + 3) share y + 1.
        let a = [F::new(2), F::new(3), F::new(1)];
        let b = [F::new(3), F::new(4), F::new(1)];
        assert!(resultant_from_coefficients(&a, &b).is_zero());
    }

    /// The zero polynomial as a coefficient vector gives a zero determinant.
    #[test]
    fn coefficient_form_is_zero_on_a_zero_argument() {
        let zero = [F::zero(), F::zero(), F::zero()];
        let b = [F::new(2), F::new(7)];
        assert!(resultant_from_coefficients(&zero, &b).is_zero());
        assert!(resultant_from_coefficients(&b, &zero).is_zero());
    }

    /// An empty coefficient slice is a caller bug, not the zero polynomial.
    #[test]
    #[should_panic(expected = "a formal degree needs at least a constant term")]
    fn coefficient_form_refuses_an_empty_slice() {
        resultant_from_coefficients::<F>(&[], &[F::one()]);
    }

    /// The two implementations agree over every combination of formal degrees up to 2 on a
    /// coefficient set containing zero — the sweep that fires each degree-drop case by
    /// construction, and the differential test between the polynomial and coefficient forms.
    #[test]
    fn the_two_forms_agree_over_a_coefficient_sweep() {
        // 0 is included deliberately: it is what produces the dropped degrees.
        let values = [0u64, 1, 2, 7, 12];
        let mut checked = 0usize;
        for a0 in values {
            for a1 in values {
                for a2 in values {
                    for b0 in values {
                        for b1 in values {
                            for b2 in values {
                                let a = [F::new(a0), F::new(a1), F::new(a2)];
                                let b = [F::new(b0), F::new(b1), F::new(b2)];
                                let coefficient_form = resultant_from_coefficients(&a, &b);
                                assert_eq!(
                                    coefficient_form,
                                    sylvester_reference(
                                        &poly(&[a0, a1, a2]),
                                        &poly(&[b0, b1, b2]),
                                        2,
                                        2
                                    ),
                                    "a={a:?} b={b:?}"
                                );
                                // And against the polynomial form, which derives the same three
                                // corrections independently.
                                if !(a.iter().all(F::is_zero) || b.iter().all(F::is_zero)) {
                                    assert_eq!(
                                        coefficient_form,
                                        resultant_at_formal_degrees(
                                            &poly(&[a0, a1, a2]),
                                            &poly(&[b0, b1, b2]),
                                            2,
                                            2
                                        ),
                                        "the two forms disagree at a={a:?} b={b:?}"
                                    );
                                }
                                checked += 1;
                            }
                        }
                    }
                }
            }
        }
        assert_eq!(checked, values.len().pow(6));
    }
}
