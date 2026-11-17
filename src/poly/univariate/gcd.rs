//! `gcd` dispatches on the smaller operand's degree: classical Euclid below a width-indexed
//! crossover, half-GCD above it (`docs/research/fast-univariate.md` §4.5 has the sweep).

use crate::{FiniteField, Polynomial, UnivariatePolynomial};

/// Smallest degree at which `gcd` takes half-GCD, for a field element of at most 4 bytes.
const HALF_GCD_CROSSOVER_32_BIT: u32 = 8192;
/// As [`HALF_GCD_CROSSOVER_32_BIT`], for 5 to 8 bytes.
const HALF_GCD_CROSSOVER_64_BIT: u32 = 4096;
/// As [`HALF_GCD_CROSSOVER_32_BIT`], for wider elements.
const HALF_GCD_CROSSOVER_WIDE: u32 = 2048;

/// The degree of the smaller operand from which `gcd` takes half-GCD for `F`.
///
/// Tiered by element width like `karatsuba_base_case`, and for the same reason: half-GCD wins by
/// trading multiplications for Karatsuba products, which pay off sooner the dearer one
/// multiplication is.
pub(crate) fn half_gcd_crossover<F: FiniteField>() -> u32 {
    match std::mem::size_of::<F>() {
        0..=4 => HALF_GCD_CROSSOVER_32_BIT,
        5..=8 => HALF_GCD_CROSSOVER_64_BIT,
        _ => HALF_GCD_CROSSOVER_WIDE,
    }
}

/// The monic greatest common divisor of two polynomials: classical Euclid, or half-GCD once the
/// smaller operand reaches [`half_gcd_crossover`].
pub fn gcd<F: FiniteField>(
    a: &UnivariatePolynomial<F>,
    b: &UnivariatePolynomial<F>,
) -> UnivariatePolynomial<F> {
    let smaller = signed_degree(a).min(signed_degree(b));
    if smaller >= i64::from(half_gcd_crossover::<F>()) {
        gcd_half_unstable(a, b)
    } else {
        gcd_classical_unstable(a, b)
    }
}

/// The monic GCD by classical Euclid at every degree; [`gcd`]'s route below the crossover.
pub fn gcd_classical_unstable<F: FiniteField>(
    a: &UnivariatePolynomial<F>,
    b: &UnivariatePolynomial<F>,
) -> UnivariatePolynomial<F> {
    let mut f = a.clone();
    let mut g = b.clone();
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

// === half-GCD: the fast Euclidean algorithm ===

/// A `2x2` matrix over `F[x]`, the transition from one pair of the remainder sequence to a later
/// one.
///
/// `(c, d)^T = M * (a, b)^T` where `(c, d)` is a consecutive pair of the Euclidean remainder
/// sequence of `(a, b)`. Every matrix built here is a product of elementary steps
/// `[[0, 1], [1, -q]]`, each of determinant `-1`, so the product is unimodular and the pair it
/// produces really is in the sequence — which is what makes the recursion's output checkable.
#[derive(Clone)]
struct Transition<F: FiniteField> {
    rows: [[UnivariatePolynomial<F>; 2]; 2],
}

impl<F: FiniteField> Transition<F> {
    fn identity() -> Self {
        Transition {
            rows: [
                [UnivariatePolynomial::one(), UnivariatePolynomial::zero()],
                [UnivariatePolynomial::zero(), UnivariatePolynomial::one()],
            ],
        }
    }

    /// One Euclidean step with quotient `q`: `[[0, 1], [1, -q]]`; [`Transition::push_step`]'s
    /// reference.
    #[cfg(test)]
    fn step(quotient: &UnivariatePolynomial<F>) -> Self {
        Transition {
            rows: [
                [UnivariatePolynomial::zero(), UnivariatePolynomial::one()],
                [UnivariatePolynomial::one(), -quotient],
            ],
        }
    }

    /// `step(quotient) * self` in place: the new top row is the old bottom row, and the new
    /// bottom row is `top - quotient * bottom`.
    ///
    /// Two products where composing with [`Transition::step`] spends eight, four of them against
    /// the step's constant zero and one entries. The base case takes one Euclidean step per
    /// degree it drops, so this is the cost that dominates below the recursion.
    fn push_step(&mut self, quotient: &UnivariatePolynomial<F>) {
        let [top, bottom] = &mut self.rows;
        for (upper, lower) in top.iter_mut().zip(bottom.iter_mut()) {
            let next = &*upper - &(quotient * &*lower);
            *upper = std::mem::replace(lower, next);
        }
    }

    /// `self * other`, so that `other` is applied first.
    fn compose(&self, other: &Self) -> Self {
        let entry = |i: usize, j: usize| {
            &(&self.rows[i][0] * &other.rows[0][j]) + &(&self.rows[i][1] * &other.rows[1][j])
        };
        Transition {
            rows: [[entry(0, 0), entry(0, 1)], [entry(1, 0), entry(1, 1)]],
        }
    }

    /// `M * (a, b)^T`.
    fn apply(
        &self,
        a: &UnivariatePolynomial<F>,
        b: &UnivariatePolynomial<F>,
    ) -> (UnivariatePolynomial<F>, UnivariatePolynomial<F>) {
        (
            &(&self.rows[0][0] * a) + &(&self.rows[0][1] * b),
            &(&self.rows[1][0] * a) + &(&self.rows[1][1] * b),
        )
    }
}

/// The degree, with the zero polynomial at `-1` so that comparisons against a bound are total.
///
/// `Polynomial::degree` reports zero for the zero polynomial, which is the right answer for a
/// constant and the wrong one here: the recursion's halting conditions are all of the form
/// "degree below a bound", and a zero remainder has to be below every bound.
fn signed_degree<F: FiniteField>(p: &UnivariatePolynomial<F>) -> i64 {
    if p.is_zero() {
        -1
    } else {
        i64::from(p.degree())
    }
}

/// `floor(p / x^shift)`: the top coefficients, which is what a truncated recursion runs on.
fn drop_low<F: FiniteField>(p: &UnivariatePolynomial<F>, shift: usize) -> UnivariatePolynomial<F> {
    let coefficients = p.coefficients();
    if shift >= coefficients.len() {
        return UnivariatePolynomial::zero();
    }
    UnivariatePolynomial::new(&coefficients[shift..])
}

/// `p mod x^shift`: the coefficients a truncated recursion did not see.
fn low_part<F: FiniteField>(p: &UnivariatePolynomial<F>, shift: usize) -> UnivariatePolynomial<F> {
    let coefficients = p.coefficients();
    UnivariatePolynomial::new(&coefficients[..shift.min(coefficients.len())])
}

/// `high * x^shift + low`.
fn shifted_sum<F: FiniteField>(
    high: &UnivariatePolynomial<F>,
    shift: usize,
    low: &UnivariatePolynomial<F>,
) -> UnivariatePolynomial<F> {
    let (high, low) = (high.coefficients(), low.coefficients());
    let mut out = vec![F::zero(); (high.len() + shift).max(low.len())];
    out[..low.len()].copy_from_slice(low);
    for (slot, value) in out[shift..].iter_mut().zip(high) {
        *slot += *value;
    }
    UnivariatePolynomial::from_coefficients(out)
}

// Cutoff for the experimental algorithm's classical base case.
const HALF_GCD_BASE_CASE: i64 = 64;

/// A reduction's result: the pair `(c, d) = M * (a, b)` it reached, and `M` when it was asked for.
struct Reduced<F: FiniteField> {
    matrix: Option<Transition<F>>,
    c: UnivariatePolynomial<F>,
    d: UnivariatePolynomial<F>,
}

impl<F: FiniteField> Reduced<F> {
    /// The reduction of `(a, b)` from that of its top coefficients `(a, b) / x^shift`.
    ///
    /// `M * (a, b) = x^shift * M * (a_high, b_high) + M * (a_low, b_low)`, and the first term is
    /// the pair the truncated recursion already returned. Only the low `shift` coefficients are
    /// multiplied, where re-applying `M` would multiply all `shift + 2 * budget + 1` of them.
    fn lift(self, a: &UnivariatePolynomial<F>, b: &UnivariatePolynomial<F>, shift: usize) -> Self {
        let matrix = self
            .matrix
            .expect("a truncated reduction is always asked for its matrix");
        let (low_c, low_d) = matrix.apply(&low_part(a, shift), &low_part(b, shift));
        Reduced {
            c: shifted_sum(&self.c, shift, &low_c),
            d: shifted_sum(&self.d, shift, &low_d),
            matrix: Some(matrix),
        }
    }
}

/// The transition matrix that drops `budget` degrees from `a`, or as many as the sequence allows.
///
/// Returns `M` such that, with `(c, d) = M * (a, b)`, the pair `(c, d)` is consecutive in the
/// remainder sequence of `(a, b)` and
///
/// ```text
///     deg c >= deg a - budget > deg d
/// ```
///
/// — that is, `M` takes the sequence to the **last** pair whose first entry has not yet dropped
/// `budget` degrees. `budget = deg a` runs to the end and makes `c` the GCD up to a unit.
#[cfg(test)]
fn transition_for<F: FiniteField>(
    a: &UnivariatePolynomial<F>,
    b: &UnivariatePolynomial<F>,
    budget: i64,
) -> Transition<F> {
    reduce(a, b, budget, HALF_GCD_BASE_CASE, true)
        .matrix
        .expect("the matrix was asked for")
}

/// [`transition_for`]'s pair, with its matrix built only when `want_matrix` is set.
///
/// To recover the first half of the quotient sequence, truncate both inputs by the
/// same number of low coefficients. At a degree drop of at most `half`, the
/// transition entries have degree at most `half`. Thus a discarded coefficient
/// can affect a remainder only below the retained degree boundary if we keep the
/// top `2 * half + 1` coefficients. [`Reduced::lift`] then recovers the full-length pair.
///
/// A caller that reads only the pair skips every composition on the path where nothing was
/// truncated, which with `budget = deg a` is the whole top of the recursion.
fn reduce<F: FiniteField>(
    a: &UnivariatePolynomial<F>,
    b: &UnivariatePolynomial<F>,
    budget: i64,
    base_case: i64,
    want_matrix: bool,
) -> Reduced<F> {
    let degree = signed_degree(a);
    let target = degree - budget;

    // A zero budget still takes a step when a and b have the same degree.
    if signed_degree(b) < target {
        return Reduced {
            matrix: want_matrix.then(Transition::identity),
            c: a.clone(),
            d: b.clone(),
        };
    }

    if budget <= base_case {
        return classical_reduce(a, b, target, want_matrix);
    }

    // The truncation below sizes itself off `deg a`, so it needs `deg a >= deg b`. Otherwise the
    // sequence's first step has quotient zero and only swaps the pair: take it here, as the
    // column swap it is, and reduce `(b, a)` to the same target.
    if signed_degree(b) > degree {
        let mut swapped = reduce(b, a, signed_degree(b) - target, base_case, want_matrix);
        if let Some(matrix) = &mut swapped.matrix {
            for row in &mut matrix.rows {
                row.swap(0, 1);
            }
        }
        return swapped;
    }

    // Rounded up, so that `budget = deg a` (the top of every `gcd`) truncates nothing at odd
    // degree: rounding down leaves a one-coefficient shift, which buys nothing and forces the
    // matrix to be built for the lift.
    let half = (budget + 1) / 2;
    let shift = (degree - 2 * half).max(0) as usize;

    // First half, on the top `2 * half + 1` coefficients.
    let Reduced {
        mut matrix,
        mut c,
        mut d,
    } = reduce_truncated(a, b, shift, half, base_case, want_matrix);
    if !want_matrix {
        matrix = None;
    }
    if signed_degree(&d) < target {
        return Reduced { matrix, c, d };
    }

    // One full-length division step, to cross the boundary the truncation could not see past.
    let (quotient, remainder) = c.div_with_remainder(&d);
    if let Some(matrix) = &mut matrix {
        matrix.push_step(&quotient);
    }
    c = d;
    d = remainder;
    if signed_degree(&d) < target {
        return Reduced { matrix, c, d };
    }

    // Second half, on what is left of the budget after the first half and the step.
    let spent = degree - signed_degree(&c);
    let remaining = budget - spent;
    if remaining <= 0 {
        // Unreachable: control only arrives here with `deg d >= target`, hence
        // `deg c > deg d >= target`, hence `spent = deg a - deg c < budget`. Kept as a guard
        // because the alternative to an impossible branch here is an infinite recursion.
        return Reduced { matrix, c, d };
    }
    let shift = (signed_degree(&c) - 2 * remaining).max(0) as usize;
    let tail = reduce_truncated(&c, &d, shift, remaining, base_case, want_matrix);
    Reduced {
        matrix: matrix.map(|head| {
            tail.matrix
                .as_ref()
                .expect("a reduction that wants its matrix asks its parts for theirs")
                .compose(&head)
        }),
        c: tail.c,
        d: tail.d,
    }
}

/// [`reduce`] on `(a, b) / x^shift`, lifted back to the full-length pair.
fn reduce_truncated<F: FiniteField>(
    a: &UnivariatePolynomial<F>,
    b: &UnivariatePolynomial<F>,
    shift: usize,
    budget: i64,
    base_case: i64,
    want_matrix: bool,
) -> Reduced<F> {
    if shift == 0 {
        return reduce(a, b, budget, base_case, want_matrix);
    }
    reduce(
        &drop_low(a, shift),
        &drop_low(b, shift),
        budget,
        base_case,
        true,
    )
    .lift(a, b, shift)
}

/// [`reduce`] by classical Euclid, which is the recursion's base case and its reference.
fn classical_reduce<F: FiniteField>(
    a: &UnivariatePolynomial<F>,
    b: &UnivariatePolynomial<F>,
    target: i64,
    want_matrix: bool,
) -> Reduced<F> {
    let mut matrix = want_matrix.then(Transition::identity);
    let mut c = a.clone();
    let mut d = b.clone();
    while signed_degree(&d) >= target {
        let (quotient, remainder) = c.div_with_remainder(&d);
        if let Some(matrix) = &mut matrix {
            matrix.push_step(&quotient);
        }
        c = d;
        d = remainder;
    }
    Reduced { matrix, c, d }
}

/// Computes the monic GCD using recursive half-GCD with a classical base case.
///
/// This experimental route is exposed for benchmarking; `docs/research/fast-univariate.md` §4.5
/// records where it crosses [`gcd`].
pub fn gcd_half_unstable<F: FiniteField>(
    a: &UnivariatePolynomial<F>,
    b: &UnivariatePolynomial<F>,
) -> UnivariatePolynomial<F> {
    gcd_half_with_base_case_unstable(a, b, HALF_GCD_BASE_CASE as u32)
}

/// [`gcd_half_unstable`] with the classical base case's budget as a parameter, for sweeping it.
pub fn gcd_half_with_base_case_unstable<F: FiniteField>(
    a: &UnivariatePolynomial<F>,
    b: &UnivariatePolynomial<F>,
    base_case: u32,
) -> UnivariatePolynomial<F> {
    let (f, g) = if signed_degree(a) < signed_degree(b) {
        (b, a)
    } else {
        (a, b)
    };
    if g.is_zero() {
        return make_monic(f);
    }
    // `budget = deg f` runs the sequence to its end, leaving the last nonzero remainder in `c`.
    let budget = signed_degree(f);
    make_monic(&reduce(f, g, budget, i64::from(base_case.max(1)), false).c)
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

    mod half {
        use super::*;
        use crate::fields::{Bn254Fr, KoalaBear, PrimeFieldElement64, Zp18446744069414584321};
        use crate::poly::univariate::gcd::{
            gcd_classical_unstable, gcd_half_unstable, gcd_half_with_base_case_unstable,
            half_gcd_crossover, reduce, signed_degree, transition_for, Transition,
            HALF_GCD_BASE_CASE,
        };
        use rand::{prelude::StdRng, SeedableRng};

        type Gf2 = PrimeFieldElement64<2>;
        type Gf3 = PrimeFieldElement64<3>;

        /// Every polynomial of degree at most `max_degree` over a field of `order` elements.
        fn all_polynomials<F: FiniteField>(
            max_degree: usize,
            order: u64,
        ) -> Vec<UnivariatePolynomial<F>> {
            let slots = max_degree + 1;
            let total = order.pow(slots as u32);
            let mut out = Vec::with_capacity(total as usize);
            for mut index in 0..total {
                let mut coefficients = Vec::with_capacity(slots);
                for _ in 0..slots {
                    let digit = index % order;
                    index /= order;
                    let mut value = F::zero();
                    for _ in 0..digit {
                        value += F::one();
                    }
                    coefficients.push(value);
                }
                out.push(UnivariatePolynomial::new(&coefficients));
            }
            out
        }

        /// The transition matrix's contract: it lands on a consecutive pair of the remainder
        /// sequence, and it lands on the *last* one above the boundary.
        fn assert_transition_contract<F: FiniteField>(
            a: &UnivariatePolynomial<F>,
            b: &UnivariatePolynomial<F>,
            budget: i64,
        ) {
            let fast = transition_for(a, b, budget);
            let target = signed_degree(a) - budget;
            let (fc, fd) = fast.apply(a, b);
            // The pair the recursion lifts from its truncations is the matrix's pair, with or
            // without the matrix being built.
            for want_matrix in [true, false] {
                let reduced = reduce(a, b, budget, HALF_GCD_BASE_CASE, want_matrix);
                assert_eq!(
                    (&reduced.c, &reduced.d),
                    (&fc, &fd),
                    "the lifted pair is not M * (a, b) on a = {a}, b = {b}, budget = {budget}, \
                     want_matrix = {want_matrix}"
                );
                assert_eq!(reduced.matrix.is_some(), want_matrix);
            }
            let (mut sc, mut sd) = (a.clone(), b.clone());
            while signed_degree(&sd) >= target {
                let remainder = &sc % &sd;
                sc = sd;
                sd = remainder;
            }
            assert_eq!(
                (&fc, &fd),
                (&sc, &sd),
                "the recursion and classical Euclid reached different pairs on \
                 a = {a}, b = {b}, budget = {budget}"
            );
            if signed_degree(b) >= target {
                assert!(
                    signed_degree(&fc) >= target,
                    "the pair overshot: deg c = {} is below the target {target} on a = {a}, b = {b}",
                    signed_degree(&fc)
                );
                assert!(
                    signed_degree(&fd) < target,
                    "the pair undershot: deg d = {} is not below the target {target} on \
                     a = {a}, b = {b}",
                    signed_degree(&fd)
                );
            }
        }

        // Every pair of degree at most five over GF(2) agrees with classical Euclid.
        #[test]
        fn test_half_gcd_agrees_exhaustively_over_gf2() {
            let polynomials = all_polynomials::<Gf2>(5, 2);
            let mut checked = 0;
            for a in &polynomials {
                for b in &polynomials {
                    assert_eq!(
                        gcd_half_unstable(a, b),
                        gcd_classical_unstable(a, b),
                        "half-GCD disagrees on a = {a}, b = {b}"
                    );
                    checked += 1;
                }
            }
            assert_eq!(checked, 64 * 64, "every pair of the enumeration was tried");
        }

        // Every pair of degree at most three over GF(3) agrees with classical Euclid.
        #[test]
        fn test_half_gcd_agrees_exhaustively_over_gf3() {
            let polynomials = all_polynomials::<Gf3>(3, 3);
            for a in &polynomials {
                for b in &polynomials {
                    assert_eq!(
                        gcd_half_unstable(a, b),
                        gcd_classical_unstable(a, b),
                        "half-GCD disagrees on a = {a}, b = {b}"
                    );
                }
            }
        }

        // The transition reaches the last pair above the degree boundary for every small GF(2) pair.
        #[test]
        fn test_the_transition_contract_holds_exhaustively_over_gf2() {
            let polynomials = all_polynomials::<Gf2>(5, 2);
            for a in &polynomials {
                if a.is_zero() {
                    continue;
                }
                for b in &polynomials {
                    for budget in 0..=signed_degree(a) {
                        assert_transition_contract(a, b, budget);
                    }
                }
            }
        }

        // With base cases of one to three degrees, every small GF(2) pair and budget recurses, and
        // both the lifted pair and the matrix land where classical Euclid does.
        #[test]
        fn test_the_recursion_matches_euclid_exhaustively_over_gf2_with_tiny_base_cases() {
            let polynomials = all_polynomials::<Gf2>(6, 2);
            for base_case in 1..=3 {
                for a in &polynomials {
                    for b in &polynomials {
                        assert_eq!(
                            gcd_half_with_base_case_unstable(a, b, base_case as u32),
                            gcd_classical_unstable(a, b),
                            "half-GCD disagrees on a = {a}, b = {b}, base case {base_case}"
                        );
                        if a.is_zero() {
                            continue;
                        }
                        for budget in 0..=signed_degree(a) {
                            let target = signed_degree(a) - budget;
                            let (mut sc, mut sd) = (a.clone(), b.clone());
                            while signed_degree(&sd) >= target {
                                let remainder = &sc % &sd;
                                sc = sd;
                                sd = remainder;
                            }
                            let with = reduce(a, b, budget, base_case, true);
                            let without = reduce(a, b, budget, base_case, false);
                            let context =
                                format!("a = {a}, b = {b}, budget {budget}, base {base_case}");
                            assert_eq!((&with.c, &with.d), (&sc, &sd), "{context}");
                            assert_eq!((&without.c, &without.d), (&sc, &sd), "{context}");
                            let matrix = with.matrix.expect("asked for");
                            assert_eq!(matrix.apply(a, b), (sc, sd), "{context}");
                        }
                    }
                }
            }
        }

        // Stepping a transition in place equals composing it with the elementary step matrix.
        #[test]
        fn test_push_step_equals_composing_with_the_step() {
            let mut rng = StdRng::seed_from_u64(0x194_57e9);
            for (quotient_degree, entry_degree) in [(0, 0), (1, 5), (3, 2), (8, 40)] {
                let mut matrix = Transition::<KoalaBear>::identity();
                for _ in 0..3 {
                    matrix = Transition::step(&UnivariatePolynomial::rand(entry_degree, &mut rng))
                        .compose(&matrix);
                }
                let quotient = UnivariatePolynomial::rand(quotient_degree, &mut rng);
                let expected = Transition::step(&quotient).compose(&matrix);
                matrix.push_step(&quotient);
                assert_eq!(matrix.rows, expected.rows);
            }
        }

        // The public gcd agrees with classical Euclid on either side of the wide-field crossover,
        // where it switches routes, on coprime pairs and with a planted common factor.
        #[test]
        fn test_gcd_agrees_with_euclid_across_its_dispatch() {
            type F = Bn254Fr;
            let crossover = u64::from(half_gcd_crossover::<F>());
            let mut rng = StdRng::seed_from_u64(0x194_d15);
            let shared = UnivariatePolynomial::<F>::rand(13, &mut rng);
            for degree in [crossover - 1, crossover, crossover + 1] {
                // `b` sets the smaller degree, which is what the dispatch reads.
                let a = UnivariatePolynomial::<F>::rand(degree + 5, &mut rng);
                let b = UnivariatePolynomial::<F>::rand(degree, &mut rng);
                assert_eq!(
                    gcd(&a, &b),
                    gcd_classical_unstable(&a, &b),
                    "degree {degree}"
                );
                let (f, g) = (&a * &shared, &b * &shared);
                assert_eq!(gcd(&f, &g), make_monic(&shared), "degree {degree}, planted");
            }
        }

        // Recursive half-GCD agrees with Euclid across three coefficient widths and degree gaps.
        #[test]
        fn test_half_gcd_agrees_above_the_base_case() {
            check_recursive_pairs::<KoalaBear>();
            check_recursive_pairs::<Zp18446744069414584321>();
            check_recursive_pairs::<Bn254Fr>();
        }

        fn check_recursive_pairs<F: FiniteField>() {
            let mut rng = StdRng::seed_from_u64(0x194);
            for degree in [
                HALF_GCD_BASE_CASE + 1,
                HALF_GCD_BASE_CASE + 2,
                2 * HALF_GCD_BASE_CASE,
                2 * HALF_GCD_BASE_CASE + 1,
                4 * HALF_GCD_BASE_CASE + 3,
            ] {
                for offset in [0, 1, 7] {
                    let a = UnivariatePolynomial::<F>::rand(degree as u64, &mut rng);
                    let b = UnivariatePolynomial::<F>::rand((degree - offset) as u64, &mut rng);
                    assert_transition_contract(&a, &b, degree / 2);
                    assert_eq!(
                        gcd_half_unstable(&a, &b),
                        gcd_classical_unstable(&a, &b),
                        "half-GCD disagrees at degree {degree} against {}",
                        degree - offset
                    );
                    // And with a planted common factor, so the answer is not almost always one.
                    let shared = UnivariatePolynomial::<F>::rand(11, &mut rng);
                    let f = &a * &shared;
                    let g = &b * &shared;
                    assert_eq!(
                        gcd_half_unstable(&f, &g),
                        gcd_classical_unstable(&f, &g),
                        "half-GCD disagrees with a planted factor at degree {degree}"
                    );
                }
            }
        }

        // Half-GCD matches Euclid for zero, constant, equal, divisible, and repeated-factor inputs.
        #[test]
        fn test_half_gcd_handles_the_degenerate_sequences() {
            let mut rng = StdRng::seed_from_u64(0x194_dead);
            let big = 3 * HALF_GCD_BASE_CASE;
            let a = UnivariatePolynomial::<Zp13>::rand(big as u64, &mut rng);
            let zero = UnivariatePolynomial::<Zp13>::zero();
            let one = UnivariatePolynomial::<Zp13>::one();

            // Zero and constant arguments.
            assert_eq!(
                gcd_half_unstable(&a, &zero),
                gcd_classical_unstable(&a, &zero)
            );
            assert_eq!(
                gcd_half_unstable(&zero, &a),
                gcd_classical_unstable(&zero, &a)
            );
            assert_eq!(gcd_half_unstable(&zero, &zero), zero);
            assert_eq!(gcd_half_unstable(&a, &one), one);

            // Equal arguments, and one a multiple of the other: the quotient sequence is one step.
            assert_eq!(gcd_half_unstable(&a, &a), gcd_classical_unstable(&a, &a));
            let multiple = &a * &UnivariatePolynomial::<Zp13>::rand(17, &mut rng);
            assert_eq!(
                gcd_half_unstable(&multiple, &a),
                gcd_classical_unstable(&multiple, &a)
            );

            // A repeated factor, which makes the sequence degenerate late rather than early.
            let factor = UnivariatePolynomial::<Zp13>::rand(9, &mut rng);
            let squared = &factor * &factor;
            let f = &squared * &UnivariatePolynomial::<Zp13>::rand(big as u64, &mut rng);
            let g = &squared * &UnivariatePolynomial::<Zp13>::rand(big as u64 + 3, &mut rng);
            assert_eq!(gcd_half_unstable(&f, &g), gcd_classical_unstable(&f, &g));

            // Odd and even degrees straddling the base case, where the halving's parity changes.
            for degree in (HALF_GCD_BASE_CASE - 2)..=(HALF_GCD_BASE_CASE + 2) {
                let f = UnivariatePolynomial::<Zp13>::rand(degree as u64, &mut rng);
                let g = UnivariatePolynomial::<Zp13>::rand((degree - 1) as u64, &mut rng);
                assert_eq!(
                    gcd_half_unstable(&f, &g),
                    gcd(&f, &g),
                    "half-GCD disagrees at degree {degree}"
                );
            }
        }
    }
}
