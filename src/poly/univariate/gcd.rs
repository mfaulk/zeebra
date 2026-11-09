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
///
/// Classical Euclid below [`HALF_GCD_BASE_CASE`] and the fast Euclidean algorithm above it; the
/// threshold is measured rather than chosen, see `docs/research/fast-univariate.md` §4.5. Both
/// routes return the same value, so which one ran is not observable except in the time.
pub fn gcd<F: FiniteField>(
    a: &UnivariatePolynomial<F>,
    b: &UnivariatePolynomial<F>,
) -> UnivariatePolynomial<F> {
    if signed_degree(a).min(signed_degree(b)) > HALF_GCD_BASE_CASE {
        return gcd_half_unstable(a, b);
    }
    gcd_classical_unstable(a, b)
}

/// [`gcd`] by classical Euclid, whatever the degree.
///
/// `unstable` because it is here to be *measured against*, not called: it is the slower route above
/// the threshold by construction, and it is the reference the fast route is differentially tested
/// against. `examples/gcd_crossover.rs` is the one caller that wants it.
pub fn gcd_classical_unstable<F: FiniteField>(
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

    /// One Euclidean step with quotient `q`: `[[0, 1], [1, -q]]`.
    fn step(quotient: &UnivariatePolynomial<F>) -> Self {
        Transition {
            rows: [
                [UnivariatePolynomial::zero(), UnivariatePolynomial::one()],
                [UnivariatePolynomial::one(), -quotient],
            ],
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

/// Degree below which the recursion stops paying for itself and classical Euclid takes over.
///
/// Measured, not chosen: see `docs/research/fast-univariate.md` §4.5. The recursion's constant is
/// several polynomial multiplications and two matrix products per level, against one long division
/// per step for the classical route, so the crossover is well above the degree at which the
/// asymptotics cross.
pub const HALF_GCD_BASE_CASE: i64 = 64;

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
///
/// The recursion is the standard one and the only subtle line is the truncation. A remainder `r_j`
/// reached after quotients `q_0 … q_{j-1}` satisfies `deg r_j = deg a - sum deg q_i`, and the
/// matrix accumulating those steps has entries of degree at most `sum deg q_i = deg a - deg r_j`.
/// So reducing by `half` degrees needs a matrix of degree at most `half`, and a product of two
/// degree-`half` matrices with the operands is determined by the operands' top `2*half + 1`
/// coefficients. Hence `shift = deg a - 2*half`: the recursion runs on operands of degree `2*half`
/// rather than `deg a`, which is what makes the cost `O(M(d) log d)` instead of `O(d^2)`.
fn transition_for<F: FiniteField>(
    a: &UnivariatePolynomial<F>,
    b: &UnivariatePolynomial<F>,
    budget: i64,
) -> Transition<F> {
    let degree = signed_degree(a);
    let target = degree - budget;

    // Nothing to do: `b` is already past the boundary, so `(a, b)` is itself the last pair.
    //
    // The condition is on `b`'s degree alone and **not** also on the budget: a budget of zero
    // still has a step to take when `deg b >= deg a`, because the contract asks for the last pair
    // above the boundary rather than for a given number of steps. Guarding on `budget <= 0` here
    // returned the identity for `a = b = 1`, where the sequence does advance to `(1, 0)` —
    // `test_the_transition_contract_holds_exhaustively_over_gf2` is what found that.
    if signed_degree(b) < target {
        return Transition::identity();
    }

    if budget <= HALF_GCD_BASE_CASE {
        return classical_transition(a, b, target);
    }

    let half = budget / 2;
    let shift = (degree - 2 * half).max(0) as usize;

    // First half, on the top `2 * half + 1` coefficients.
    let mut matrix = transition_for(&drop_low(a, shift), &drop_low(b, shift), half);
    let (mut c, mut d) = matrix.apply(a, b);
    if signed_degree(&d) < target {
        return matrix;
    }

    // One full-length division step, to cross the boundary the truncation could not see past.
    let (quotient, remainder) = c.div_with_remainder(&d);
    matrix = Transition::step(&quotient).compose(&matrix);
    c = d;
    d = remainder;
    if signed_degree(&d) < target {
        return matrix;
    }

    // Second half, on what is left of the budget after the first half and the step.
    let spent = degree - signed_degree(&c);
    let remaining = budget - spent;
    if remaining <= 0 {
        // Unreachable: control only arrives here with `deg d >= target`, hence
        // `deg c > deg d >= target`, hence `spent = deg a - deg c < budget`. Kept as a guard
        // because the alternative to an impossible branch here is an infinite recursion.
        return matrix;
    }
    let shift = (signed_degree(&c) - 2 * remaining).max(0) as usize;
    let tail = transition_for(&drop_low(&c, shift), &drop_low(&d, shift), remaining);
    tail.compose(&matrix)
}

/// [`transition_for`] by classical Euclid, which is the recursion's base case and its reference.
fn classical_transition<F: FiniteField>(
    a: &UnivariatePolynomial<F>,
    b: &UnivariatePolynomial<F>,
    target: i64,
) -> Transition<F> {
    let mut matrix = Transition::identity();
    let mut c = a.clone();
    let mut d = b.clone();
    while signed_degree(&d) >= target {
        let (quotient, remainder) = c.div_with_remainder(&d);
        matrix = Transition::step(&quotient).compose(&matrix);
        c = d;
        d = remainder;
    }
    matrix
}

/// [`gcd`] through the fast Euclidean algorithm, whatever the degree.
///
/// Each round halves the degree with one [`transition_for`] call and then takes a single division
/// step, which is what guarantees progress: `transition_for` leaves `deg d` below half of `deg c`
/// but says nothing about `deg c`, so without the step a round could return the pair it was given.
///
/// `unstable` for the same reason as [`gcd_classical_unstable`]: below the threshold this is the
/// slower route, and the choice between them belongs to [`gcd`].
pub fn gcd_half_unstable<F: FiniteField>(
    a: &UnivariatePolynomial<F>,
    b: &UnivariatePolynomial<F>,
) -> UnivariatePolynomial<F> {
    let mut f = a.clone();
    let mut g = b.clone();
    if signed_degree(&f) < signed_degree(&g) {
        std::mem::swap(&mut f, &mut g);
    }

    while signed_degree(&g) > HALF_GCD_BASE_CASE {
        let budget = signed_degree(&f) / 2;
        let matrix = transition_for(&f, &g, budget);
        let (c, d) = matrix.apply(&f, &g);
        f = c;
        g = d;
        if g.is_zero() {
            break;
        }
        // The progress step. Without it a round whose transition is the identity would loop.
        let remainder = &f % &g;
        f = g;
        g = remainder;
    }

    // Classical Euclid finishes, which is also what runs for every input below the threshold.
    while !g.is_zero() {
        let remainder = &f % &g;
        f = g;
        g = remainder;
    }
    make_monic(&f)
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

    /// Half-GCD, against the classical algorithm it has to agree with exactly.
    ///
    /// The recursion is intricate and its failure mode is a silently wrong answer at some
    /// particular parity or quotient-degree pattern, so the tests here are an **enumeration**
    /// rather than a sample: over GF(2) and GF(3) every polynomial pair up to a small degree is
    /// tried, which is a proof by exhaustion at that size and is what catches an off-by-one in the
    /// truncation shift. The randomized tests above the base case are what catch an error that
    /// only the recursion reaches.
    mod half {
        use super::*;
        use crate::fields::{PrimeFieldElement64, Zp13};
        use crate::poly::univariate::gcd::{
            classical_transition, gcd_half_unstable, signed_degree, transition_for,
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
            let slow = classical_transition(a, b, target);
            let (fc, fd) = fast.apply(a, b);
            let (sc, sd) = slow.apply(a, b);
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

        /// Exhaustively over GF(2): every pair of degree at most 5 agrees with classical Euclid.
        #[test]
        fn test_half_gcd_agrees_exhaustively_over_gf2() {
            let polynomials = all_polynomials::<Gf2>(5, 2);
            let mut checked = 0;
            for a in &polynomials {
                for b in &polynomials {
                    assert_eq!(
                        gcd_half_unstable(a, b),
                        gcd(a, b),
                        "half-GCD disagrees on a = {a}, b = {b}"
                    );
                    checked += 1;
                }
            }
            assert_eq!(checked, 64 * 64, "every pair of the enumeration was tried");
        }

        /// Exhaustively over GF(3): a field where a leading coefficient can be a non-unit scale.
        #[test]
        fn test_half_gcd_agrees_exhaustively_over_gf3() {
            let polynomials = all_polynomials::<Gf3>(3, 3);
            for a in &polynomials {
                for b in &polynomials {
                    assert_eq!(
                        gcd_half_unstable(a, b),
                        gcd(a, b),
                        "half-GCD disagrees on a = {a}, b = {b}"
                    );
                }
            }
        }

        /// The transition matrix's contract holds exhaustively over GF(2) at every budget.
        ///
        /// This is the assertion that localizes a truncation error: `gcd_by_half` could agree with
        /// classical Euclid while `transition_for` landed on the wrong pair, because the progress
        /// step and the classical tail would hide it.
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

        /// Above the base case, where the recursion actually recurses, on three fields.
        ///
        /// The exhaustive tests are all below `HALF_GCD_BASE_CASE`, so they exercise only the
        /// classical base case and the plumbing around it. These degrees are what reach the
        /// recursive calls and the truncation.
        #[test]
        fn test_half_gcd_agrees_above_the_base_case() {
            let mut rng = StdRng::seed_from_u64(0x194);
            for degree in [
                HALF_GCD_BASE_CASE + 1,
                HALF_GCD_BASE_CASE + 2,
                2 * HALF_GCD_BASE_CASE,
                2 * HALF_GCD_BASE_CASE + 1,
                4 * HALF_GCD_BASE_CASE + 3,
            ] {
                for offset in [0, 1, 7] {
                    let a = UnivariatePolynomial::<Zp13>::rand(degree as u64, &mut rng);
                    let b = UnivariatePolynomial::<Zp13>::rand((degree - offset) as u64, &mut rng);
                    assert_eq!(
                        gcd_half_unstable(&a, &b),
                        gcd(&a, &b),
                        "half-GCD disagrees at degree {degree} against {}",
                        degree - offset
                    );
                    // And with a planted common factor, so the answer is not almost always one.
                    let shared = UnivariatePolynomial::<Zp13>::rand(11, &mut rng);
                    let f = &a * &shared;
                    let g = &b * &shared;
                    assert_eq!(
                        gcd_half_unstable(&f, &g),
                        gcd(&f, &g),
                        "half-GCD disagrees with a planted factor at degree {degree}"
                    );
                }
            }
        }

        /// The degenerate quotient sequences #194 names, each one deliberately.
        #[test]
        fn test_half_gcd_handles_the_degenerate_sequences() {
            let mut rng = StdRng::seed_from_u64(0x194_dead);
            let big = 3 * HALF_GCD_BASE_CASE;
            let a = UnivariatePolynomial::<Zp13>::rand(big as u64, &mut rng);
            let zero = UnivariatePolynomial::<Zp13>::zero();
            let one = UnivariatePolynomial::<Zp13>::one();

            // Zero and constant arguments.
            assert_eq!(gcd_half_unstable(&a, &zero), gcd(&a, &zero));
            assert_eq!(gcd_half_unstable(&zero, &a), gcd(&zero, &a));
            assert_eq!(gcd_half_unstable(&zero, &zero), zero);
            assert_eq!(gcd_half_unstable(&a, &one), one);

            // Equal arguments, and one a multiple of the other: the quotient sequence is one step.
            assert_eq!(gcd_half_unstable(&a, &a), gcd(&a, &a));
            let multiple = &a * &UnivariatePolynomial::<Zp13>::rand(17, &mut rng);
            assert_eq!(gcd_half_unstable(&multiple, &a), gcd(&multiple, &a));

            // A repeated factor, which makes the sequence degenerate late rather than early.
            let factor = UnivariatePolynomial::<Zp13>::rand(9, &mut rng);
            let squared = &factor * &factor;
            let f = &squared * &UnivariatePolynomial::<Zp13>::rand(50, &mut rng);
            let g = &squared * &UnivariatePolynomial::<Zp13>::rand(53, &mut rng);
            assert_eq!(gcd_half_unstable(&f, &g), gcd(&f, &g));

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
