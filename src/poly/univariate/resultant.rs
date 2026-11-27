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

use super::gcd::{remainder_degrees_and_leads, HALF_GCD_BASE_CASE};
use crate::{FiniteField, Polynomial, UnivariatePolynomial};

/// `Res(f, g)` by half-GCD at every degree: the remainder sequence's degrees and leading
/// coefficients, which are all the resultant needs, without forming its remainders at full length.
///
/// The same value as [`resultant`], in `O(M(d) log d)` field operations rather than `O(d²)`, where
/// `M(d)` is the cost of a degree-`d` product. Which wins at a given degree is measured, not assumed:
/// see `docs/research/fast-univariate.md`.
pub fn resultant_half_gcd_unstable<F: FiniteField>(
    f: &UnivariatePolynomial<F>,
    g: &UnivariatePolynomial<F>,
) -> F {
    resultant_half_gcd_with_base_case_unstable(f, g, HALF_GCD_BASE_CASE as u32)
}

/// [`resultant_half_gcd_unstable`] with the classical base case's budget as a parameter, so tests
/// can force the recursion at small degrees and a sweep can tune it.
pub fn resultant_half_gcd_with_base_case_unstable<F: FiniteField>(
    f: &UnivariatePolynomial<F>,
    g: &UnivariatePolynomial<F>,
    base_case: u32,
) -> F {
    if f.is_zero() || g.is_zero() {
        return F::zero();
    }
    // `Res(f, g) = (−1)^{deg f · deg g} Res(g, f)`, so the operands can be put in the order the
    // trace needs.
    let (a, b, flip) = if f.degree() < g.degree() {
        (g, f, (f.degree() * g.degree()) % 2 == 1)
    } else {
        (f, g, false)
    };
    let value = resultant_of_trace(&remainder_degrees_and_leads(a, b, i64::from(base_case)));
    if flip {
        -value
    } else {
        value
    }
}

/// `Res(r_0, r_1)` from `(deg r_i, lc r_i)` over the whole nonzero remainder sequence.
///
/// Each step contributes `(−1)^{d_{i−1} d_i} · lc(r_i)^{d_{i−1} − d_{i+1}}`, the recurrence
/// [`resultant`] applies, and the sequence ending at a nonconstant remainder means a shared factor.
fn resultant_of_trace<F: FiniteField>(trace: &[(i64, F)]) -> F {
    let last = trace.len() - 1;
    if trace[last].0 > 0 {
        return F::zero();
    }
    let mut accumulated = F::one();
    for i in 1..=last {
        let (previous, (degree, lead)) = (trace[i - 1].0, trace[i]);
        let next = if i < last { trace[i + 1].0 } else { 0 };
        if (previous * degree) % 2 == 1 {
            accumulated = -accumulated;
        }
        accumulated *= lead.pow((previous - next) as u128);
    }
    accumulated
}

/// [`resultant_from_coefficients`] with the exact-degree resultant taken by half-GCD.
///
/// The formal-degree corrections are the same code [`resultant_from_coefficients`] runs, so the
/// specialization trap is closed identically; only the kernel under them differs.
///
/// # Panics
/// If either slice is empty, as [`resultant_from_coefficients`] does.
pub fn resultant_from_coefficients_half_gcd_unstable<F: FiniteField>(a: &[F], b: &[F]) -> F {
    assert!(
        !a.is_empty() && !b.is_empty(),
        "a formal degree needs at least a constant term"
    );
    formal_determinant(a, a.len() - 1, b, b.len() - 1, exact_resultant_half_gcd)
}

/// Smaller-operand degree from which the half-GCD resultant beats the Euclidean one, by element
/// width: at most 4 bytes, 5 to 8, and wider. Measured by `examples/resultant_crossover.rs` on an
/// unpinned M4 Pro (#1207); below these, half-GCD's base case allocates per step where the
/// Euclidean kernel runs in two buffers, and loses by 5–30%.
const HALF_GCD_RESULTANT_CROSSOVER: [usize; 3] = [2048, 1536, 1024];

/// The smaller-operand degree from which [`resultant_from_coefficients_auto_unstable`] takes
/// half-GCD for `F`.
pub fn half_gcd_resultant_crossover_unstable<F: FiniteField>() -> usize {
    match std::mem::size_of::<F>() {
        0..=4 => HALF_GCD_RESULTANT_CROSSOVER[0],
        5..=8 => HALF_GCD_RESULTANT_CROSSOVER[1],
        _ => HALF_GCD_RESULTANT_CROSSOVER[2],
    }
}

/// [`resultant_from_coefficients`], taking half-GCD once both true degrees reach
/// [`half_gcd_resultant_crossover_unstable`] and the Euclidean kernel below it.
///
/// # Panics
/// If either slice is empty, as [`resultant_from_coefficients`] does.
pub fn resultant_from_coefficients_auto_unstable<F: FiniteField>(a: &[F], b: &[F]) -> F {
    assert!(
        !a.is_empty() && !b.is_empty(),
        "a formal degree needs at least a constant term"
    );
    formal_determinant(a, a.len() - 1, b, b.len() - 1, exact_resultant_auto)
}

fn exact_resultant_auto<F: FiniteField>(a: &[F], b: &[F]) -> F {
    if a.len().min(b.len()) > half_gcd_resultant_crossover_unstable::<F>() {
        exact_resultant_half_gcd(a, b)
    } else {
        exact_resultant(a, b)
    }
}

fn exact_resultant_half_gcd<F: FiniteField>(a: &[F], b: &[F]) -> F {
    resultant_half_gcd_unstable(
        &UnivariatePolynomial::from_coefficients(a.to_vec()),
        &UnivariatePolynomial::from_coefficients(b.to_vec()),
    )
}

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

/// `a mod b`, trimmed, written back over `a`. `b` must be nonzero.
///
/// In place rather than returning a fresh vector because `a` only ever **shortens**: the whole
/// remainder sequence of [`exact_resultant`] therefore runs in the two buffers it starts with, and
/// no step after the first two allocates. Empty on exit means `b` divides `a`.
fn remainder_in_place<F: FiniteField>(a: &mut Vec<F>, b: &[F]) {
    let n = b.len() - 1;
    let inverse = b[n].inverse();
    while a.len() > n {
        let top = a.len() - 1;
        let factor = a[top] * inverse;
        if !factor.is_zero() {
            for i in 0..=n {
                let value = factor * b[i];
                a[top - n + i] -= value;
            }
        }
        a.pop();
        while a.last().is_some_and(|c| c.is_zero()) {
            a.pop();
        }
    }
}

/// `Res(a, b)` over raw coefficients, both trimmed and nonzero so the degrees are exact.
///
/// Iterative, and the same recurrence [`resultant`] uses. The differences are that this one never
/// builds a [`UnivariatePolynomial`], and that the sequence — as long as the degree — runs entirely
/// in the two buffers cloned here: each step rewrites `a` into `a mod b` in place and then swaps,
/// so no step allocates. Capacity never shrinks and each remainder is shorter than the divisor it
/// came from, which is what makes the two buffers sufficient.
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
        remainder_in_place(&mut a, &b);
        if a.is_empty() {
            // `b` divides `a` and `deg b >= 1`, so the two share a root.
            return F::zero();
        }
        accumulated *= b[m].pow((n - (a.len() - 1)) as u128);
        // `deg b = m > deg r`, so the `deg a >= deg b` invariant is preserved: after the swap the
        // new `a` is the old `b` and the new `b` is the remainder, each in the other's buffer.
        std::mem::swap(&mut a, &mut b);
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
    formal_determinant(a, a.len() - 1, b, b.len() - 1, exact_resultant)
}

/// [`resultant_from_coefficients`] with the formal degrees passed explicitly, so the recursion can
/// lower them without reallocating the caller's slices, and the exact-degree kernel as `exact`.
fn formal_determinant<F: FiniteField>(
    a: &[F],
    n: usize,
    b: &[F],
    m: usize,
    exact: fn(&[F], &[F]) -> F,
) -> F {
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
        let corrected =
            b[m].pow(deficit as u128) * formal_determinant(&a_true, n_true, b, m, exact);
        return if (m * deficit) % 2 == 1 {
            -corrected
        } else {
            corrected
        };
    }
    if m_true < m {
        let deficit = m - m_true;
        return a[n].pow(deficit as u128) * formal_determinant(a, n, &b_true, m_true, exact);
    }

    exact(&a_true, &b_true)
}

#[cfg(test)]
mod tests {
    use super::{
        half_gcd_resultant_crossover_unstable, remainder_in_place, resultant,
        resultant_at_formal_degrees, resultant_from_coefficients,
        resultant_from_coefficients_auto_unstable, resultant_from_coefficients_half_gcd_unstable,
        resultant_half_gcd_unstable, resultant_half_gcd_with_base_case_unstable,
    };
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

    /// `remainder_in_place` leaves `a` holding `a mod b`, trimmed, agreeing with the polynomial
    /// `%` on random pairs across a range of degrees.
    #[test]
    fn remainder_in_place_agrees_with_polynomial_division() {
        let mut rng = StdRng::seed_from_u64(599);
        for degree_a in 1..=9usize {
            for degree_b in 1..=degree_a {
                for _ in 0..4 {
                    let mut ac: Vec<u64> = (0..=degree_a).map(|_| rng.gen_range(0..1000)).collect();
                    let mut bc: Vec<u64> = (0..=degree_b).map(|_| rng.gen_range(0..1000)).collect();
                    ac[degree_a] = rng.gen_range(1..1000);
                    bc[degree_b] = rng.gen_range(1..1000);
                    let a: Vec<F> = ac.iter().map(|c| F::new(*c)).collect();
                    let b: Vec<F> = bc.iter().map(|c| F::new(*c)).collect();
                    let mut r = a.clone();
                    remainder_in_place(&mut r, &b);
                    let expected = &poly(&ac) % &poly(&bc);
                    let expected: Vec<F> = if expected.is_zero() {
                        Vec::new()
                    } else {
                        expected.coefficients()[..=expected.degree() as usize].to_vec()
                    };
                    assert_eq!(r, expected, "a = {ac:?}, b = {bc:?}");
                }
            }
        }
    }

    /// The remainder sequence runs in the two buffers it starts with: `remainder_in_place` only
    /// ever shortens its argument, so neither buffer reallocates once `exact_resultant` has
    /// cloned its inputs. This is the whole point of #599, and a `Vec` that grew would fail it.
    #[test]
    fn the_remainder_sequence_never_reallocates() {
        let mut rng = StdRng::seed_from_u64(600);
        // Coprime-by-construction is not needed; a sequence that terminates early just checks
        // fewer steps.
        let mut a: Vec<F> = (0..=40).map(|_| F::new(rng.gen_range(1..1000))).collect();
        let mut b: Vec<F> = (0..=37).map(|_| F::new(rng.gen_range(1..1000))).collect();
        let fingerprint = |v: &Vec<F>| (v.as_ptr() as usize, v.capacity());
        let (a_start, b_start) = (fingerprint(&a), fingerprint(&b));
        let mut steps = 0usize;
        while b.len() > 1 {
            remainder_in_place(&mut a, &b);
            if a.is_empty() {
                break;
            }
            std::mem::swap(&mut a, &mut b);
            steps += 1;
            // Both buffers are still the two originals, in one order or the other.
            let seen = [fingerprint(&a), fingerprint(&b)];
            assert!(
                seen.contains(&a_start) && seen.contains(&b_start),
                "a buffer reallocated after {steps} steps: {seen:?} vs {a_start:?}, {b_start:?}"
            );
        }
        assert!(
            steps > 2,
            "the sequence should run several steps, ran {steps}"
        );
    }

    /// A random polynomial of exactly `degree`.
    fn random_poly<G: FiniteField>(degree: usize, rng: &mut StdRng) -> UnivariatePolynomial<G> {
        let mut coefficients: Vec<G> = (0..=degree).map(|_| G::random(rng)).collect();
        while coefficients[degree].is_zero() {
            coefficients[degree] = G::random(rng);
        }
        UnivariatePolynomial::new(&coefficients)
    }

    /// Half-GCD against the Euclidean resultant over `G`, at base cases small enough that the
    /// recursion, its truncations and the middle step all run at these degrees.
    fn check_half_gcd_against_euclid<G: FiniteField>(seed: u64, max_degree: usize) {
        let mut rng = StdRng::seed_from_u64(seed);
        let mut zeros = 0usize;
        for degree_f in 0..=max_degree {
            for degree_g in [
                0,
                1,
                degree_f / 3,
                degree_f.saturating_sub(1),
                degree_f,
                degree_f + 3,
            ] {
                let mut f = random_poly::<G>(degree_f, &mut rng);
                let mut g = random_poly::<G>(degree_g, &mut rng);
                // Every fourth pair shares a planted factor, so the zero exit is exercised.
                if (degree_f + degree_g) % 4 == 0 {
                    let shared = random_poly::<G>(1 + degree_f % 3, &mut rng);
                    f = &f * &shared;
                    g = &g * &shared;
                }
                let expected = resultant(&f, &g);
                zeros += usize::from(expected.is_zero());
                for base_case in [1, 2, 3, 5, 64] {
                    assert_eq!(
                        resultant_half_gcd_with_base_case_unstable(&f, &g, base_case),
                        expected,
                        "deg f = {degree_f}, deg g = {}, base case {base_case}",
                        g.degree()
                    );
                }
            }
        }
        assert!(zeros > 0, "no pair exercised the zero exit");
    }

    /// Shared factors, planted explicitly: the sequence ends at a nonconstant remainder.
    fn check_planted_common_factor<G: FiniteField>(seed: u64) {
        let mut rng = StdRng::seed_from_u64(seed);
        for shared_degree in 1..=6 {
            let shared = random_poly::<G>(shared_degree, &mut rng);
            let f = &random_poly::<G>(17, &mut rng) * &shared;
            let g = &random_poly::<G>(11, &mut rng) * &shared;
            for base_case in [1, 2, 7] {
                assert!(resultant_half_gcd_with_base_case_unstable(&f, &g, base_case).is_zero());
            }
        }
    }

    #[test]
    fn half_gcd_resultant_matches_euclid_over_a_31_bit_prime() {
        check_half_gcd_against_euclid::<F>(1207, 40);
        check_planted_common_factor::<F>(1);
    }

    #[test]
    fn half_gcd_resultant_matches_euclid_in_characteristic_two() {
        // Tiny fields make shared factors and multi-degree drops frequent by chance. In
        // characteristic 2 a sign error is invisible, so GF(3) is here to catch one.
        check_half_gcd_against_euclid::<crate::fields::PrimeFieldElement64<2>>(2, 30);
        check_half_gcd_against_euclid::<crate::fields::PrimeFieldElement64<3>>(3, 30);
    }

    #[test]
    fn half_gcd_resultant_matches_euclid_over_wide_and_extension_fields() {
        check_half_gcd_against_euclid::<crate::fields::Bn254Fr>(4, 24);
        check_half_gcd_against_euclid::<crate::fields::KoalaBear>(5, 24);
        check_planted_common_factor::<crate::fields::Bn254Fr>(6);
        type Gf13Pow4 = crate::fields::ExtensionFieldElement<13, 4, crate::fields::Modulus13Pow4>;
        check_half_gcd_against_euclid::<Gf13Pow4>(7, 16);
    }

    /// Sparse operands, whose sequences drop many degrees in one step: `x^n - 1` against `x^k - 1`
    /// and `x^n + x` against `x^k + 1`. Exercises steps whose quotient spans a recursion boundary.
    #[test]
    fn half_gcd_resultant_matches_euclid_on_large_degree_drops() {
        for n in 2..=48usize {
            for k in 1..n {
                let mut a = vec![F::zero(); n + 1];
                a[n] = F::one();
                a[0] = -F::one();
                let mut b = vec![F::zero(); k + 1];
                b[k] = F::one();
                b[0] = F::new(5);
                a[1] += F::new(3);
                let (a, b) = (UnivariatePolynomial::new(&a), UnivariatePolynomial::new(&b));
                for base_case in [1, 2, 4] {
                    assert_eq!(
                        resultant_half_gcd_with_base_case_unstable(&a, &b, base_case),
                        resultant(&a, &b),
                        "n = {n}, k = {k}, base case {base_case}"
                    );
                }
            }
        }
    }

    /// Above the default base case, so the shipped configuration's recursion runs too.
    #[test]
    fn half_gcd_resultant_matches_euclid_above_the_default_base_case() {
        let mut rng = StdRng::seed_from_u64(64);
        for (degree_f, degree_g) in [(300, 299), (257, 128), (400, 1), (200, 200)] {
            let f = random_poly::<F>(degree_f, &mut rng);
            let g = random_poly::<F>(degree_g, &mut rng);
            assert_eq!(resultant_half_gcd_unstable(&f, &g), resultant(&f, &g));
            assert_eq!(resultant_half_gcd_unstable(&g, &f), resultant(&g, &f));
        }
    }

    #[test]
    fn half_gcd_resultant_on_zero_and_constant_arguments() {
        let f = poly(&[1, 2, 3]);
        assert_eq!(resultant_half_gcd_unstable(&f, &poly(&[5])), F::new(25));
        assert_eq!(resultant_half_gcd_unstable(&poly(&[5]), &f), F::new(25));
        assert_eq!(
            resultant_half_gcd_unstable(&poly(&[5]), &poly(&[7])),
            F::one()
        );
        assert!(resultant_half_gcd_unstable(&poly(&[0]), &f).is_zero());
        assert!(resultant_half_gcd_unstable(&f, &poly(&[0])).is_zero());
    }

    /// The half-GCD coefficient form agrees with the Euclidean one over the full formal-degree
    /// sweep, degree drops on either side included: the specialization trap is closed the same way.
    #[test]
    fn half_gcd_coefficient_form_agrees_over_planted_degree_drops() {
        let mut rng = StdRng::seed_from_u64(12075);
        for formal_a in 0..=20usize {
            for formal_b in 0..=20usize {
                for drop in [(0, 0), (1, 0), (0, 1), (3, 0), (0, 2), (1, 1)] {
                    let mut a: Vec<F> = (0..=formal_a).map(|_| F::random(&mut rng)).collect();
                    let mut b: Vec<F> = (0..=formal_b).map(|_| F::random(&mut rng)).collect();
                    for slot in a.iter_mut().rev().take(drop.0) {
                        *slot = F::zero();
                    }
                    for slot in b.iter_mut().rev().take(drop.1) {
                        *slot = F::zero();
                    }
                    assert_eq!(
                        resultant_from_coefficients_half_gcd_unstable(&a, &b),
                        resultant_from_coefficients(&a, &b),
                        "formal ({formal_a}, {formal_b}), drop {drop:?}"
                    );
                }
            }
        }
    }

    /// The dispatched form agrees with the Euclidean one either side of each width tier's
    /// crossover, so both of its branches run.
    #[test]
    fn auto_coefficient_form_agrees_across_the_crossover() {
        fn check<G: FiniteField>(seed: u64) {
            let mut rng = StdRng::seed_from_u64(seed);
            let crossover = half_gcd_resultant_crossover_unstable::<G>();
            for degree in [crossover - 1, crossover] {
                let a: Vec<G> = (0..=degree + 1).map(|_| G::random(&mut rng)).collect();
                let b: Vec<G> = (0..=degree).map(|_| G::random(&mut rng)).collect();
                assert_eq!(
                    resultant_from_coefficients_auto_unstable(&a, &b),
                    resultant_from_coefficients(&a, &b),
                    "degree {degree}"
                );
            }
        }
        check::<crate::fields::KoalaBear>(1);
        check::<crate::fields::Zp18446744069414584321>(2);
        check::<crate::fields::Bn254Fr>(3);
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
