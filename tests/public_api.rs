//! The crate's headline capabilities, used only through paths a downstream crate can name.

use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    fields::{Bn254Fr, Zp2147483647},
    grobner::{f4, f4_with_options, solve, F4Error, F4Options},
    FiniteField, MonomialOrder, MultivariatePolynomial, One, Polynomial, UnivariatePolynomial,
    Zero,
};

type F = Zp2147483647;
const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

fn parse<const N: usize>(text: &str, variables: [&str; N]) -> MultivariatePolynomial<N, F> {
    MultivariatePolynomial::parse(text, variables).expect("a polynomial")
}

/// Field elements in a small and a 254-bit prime field obey the field axioms the API promises.
#[test]
fn test_field_elements_in_a_small_and_a_wide_field() {
    let a = F::new(3);
    let b = F::new(5);
    assert_eq!(a * b, F::new(15));
    assert_eq!((a / b) * b, a);
    assert_eq!(
        F::new(2_147_483_646) + F::one(),
        F::zero(),
        "2^31 - 1 wraps to zero"
    );

    let x = Bn254Fr::new(7);
    assert_eq!(x.inverse() * x, Bn254Fr::one());
    assert_eq!(x - x, Bn254Fr::zero());
}

/// Univariate and multivariate arithmetic agree with hand-expanded results.
#[test]
fn test_polynomial_arithmetic() {
    let p = UnivariatePolynomial::new(&[F::new(1), F::new(1)]);
    let square = &p * &p;
    assert_eq!(
        square,
        UnivariatePolynomial::new(&[F::new(1), F::new(2), F::new(1)])
    );
    assert_eq!(square.eval(&F::new(4)), F::new(25));

    let vars = ["x", "y"];
    let product = &parse("x + y", vars) * &parse("x - y", vars);
    assert_eq!(product, parse("x^2 - y^2", vars));
}

/// F4 returns the reduced basis of an ideal whose basis is known in closed form.
#[test]
fn test_a_grobner_basis_by_f4() {
    let vars = ["x", "y"];
    let basis = f4(
        &[parse("x^2 + y - 3", vars), parse("x - y + 1", vars)],
        GREVLEX,
    )
    .expect("within the default budgets");
    // Under grevlex x - y + 1 leads with x, so x is eliminated and y^2 - y - 2 remains.
    let mut expected = vec![parse("x - y + 1", vars), parse("y^2 - y - 2", vars)];
    let mut got = basis;
    expected.sort_by_key(|p| p.to_string());
    got.sort_by_key(|p| p.to_string());
    assert_eq!(got, expected);
}

/// `solve` returns exactly the points of the variety over the field.
#[test]
fn test_solving_a_small_system() {
    let vars = ["x", "y"];
    let system = [parse("x^2 + y - 3", vars), parse("x - y + 1", vars)];
    let mut points = solve(&system, &mut StdRng::seed_from_u64(0));
    points.sort_by_key(|point| point[0].to_string());
    assert_eq!(
        points,
        vec![[F::new(1), F::new(2)], [-F::new(2), -F::new(1)]],
        "x^2 + x - 2 = 0 at x = 1 and x = -2, with y = x + 1"
    );
    for point in &points {
        assert!(system.iter().all(|p| p.eval(point).is_zero()));
    }
}

/// A crossed resource budget is a typed error naming the limit, not a hang or a panic.
#[test]
fn test_an_explicit_resource_limit_is_a_typed_error() {
    let vars = ["x", "y", "z"];
    let system = [
        parse("x^2 + 2*y^2 + 2*z^2 - x", vars),
        parse("2*x*y + 2*y*z - y", vars),
        parse("x + 2*y + 2*z - 1", vars),
    ];
    let tight = F4Options {
        max_matrix_rows: 2,
        ..F4Options::default()
    };
    match f4_with_options(&system, GREVLEX, &tight) {
        Err(F4Error::TooManyRows { limit }) => assert_eq!(limit, 2),
        other => panic!("expected a row budget refusal, got {other:?}"),
    }
    // The same system within the default budgets completes.
    assert!(f4(&system, GREVLEX).is_ok());
}

/// A public function's error type can be named downstream, so a caller can match on it.
#[test]
fn test_normal_form_errors_can_be_matched_downstream() {
    let vars = ["x", "y"];
    let f = parse("x^2 + y", vars);
    match f.normal_form_modulo(&[], GREVLEX) {
        Err(zeebra::NormalFormError::NoDivisors) => {}
        other => panic!("an empty basis has no divisors, got {other:?}"),
    }
}

/// The integers mod 4: a ring that is not a field, defined outside the crate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Z4(u8);

impl std::fmt::Display for Z4 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::ops::Add for Z4 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Z4((self.0 + rhs.0) % 4)
    }
}

impl std::ops::AddAssign for Z4 {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl std::ops::Mul for Z4 {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        Z4((self.0 * rhs.0) % 4)
    }
}

impl std::ops::MulAssign for Z4 {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl Zero for Z4 {
    const ZERO: Self = Z4(0);
}

impl One for Z4 {
    const ONE: Self = Z4(1);
}

impl zeebra::Ring for Z4 {}

/// A downstream type implements `Ring` without any proptest trait, and generic linear algebra accepts it.
#[test]
fn test_downstream_ring_needs_no_proptest() {
    let v = zeebra::linalg::Vector::new(&[Z4(1), Z4(2), Z4(3)]);
    let doubled = &v + &v;
    assert_eq!(doubled.elements(), &vec![Z4(2), Z4(0), Z4(2)]);
    assert_eq!((v * Z4(2)).elements(), &vec![Z4(2), Z4(0), Z4(2)]);
}
