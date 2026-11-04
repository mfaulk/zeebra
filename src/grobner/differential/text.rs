//! Monomials and polynomials as text an external system accepts.
//!
//! `Monomial`'s own `Display` names its variables `x_0`, `x_1`, which no caller of this module
//! chose and Singular would reject. These render with the caller's names instead, so that one set
//! of names is declared to Singular, written into fixtures, and parsed back by Zeebra.

use crate::{FiniteField, Monomial, MonomialOrder, MultivariatePolynomial};

/// `x1*x3^2`, with `1` for the constant monomial.
///
/// # Panics
/// If `variables` is shorter than the monomial's variable count.
pub fn monomial_to_string<const N: usize>(monomial: &Monomial<N>, variables: &[&str]) -> String {
    assert!(
        variables.len() >= N,
        "{} variable names for {} variables",
        variables.len(),
        N
    );

    let mut factors: Vec<String> = Vec::new();
    for (i, exponent) in monomial.exponents().iter().enumerate() {
        match exponent {
            0 => {}
            1 => factors.push(variables[i].to_string()),
            _ => factors.push(format!("{}^{}", variables[i], exponent)),
        }
    }
    if factors.is_empty() {
        // Not the empty string: `1` is what both parsers read as the constant monomial, and an
        // empty generator in a Singular ideal is a syntax error.
        return "1".to_string();
    }
    factors.join("*")
}

/// A polynomial with terms descending under `order`, coefficients as their residues.
///
/// For reports and fixtures, not for round-tripping through a field: a coefficient prints as its
/// representative in `[0, p)` rather than as the symmetric representative Singular would choose,
/// so this is not byte-identical to Singular's own output for the same polynomial. It parses back
/// to the same value, which is what either use needs.
pub fn polynomial_to_string<const N: usize, F: FiniteField>(
    polynomial: &MultivariatePolynomial<N, F>,
    variables: &[&str],
    order: MonomialOrder,
) -> String {
    if polynomial.is_zero() {
        return "0".to_string();
    }

    let mut terms: Vec<(&Monomial<N>, &F)> = polynomial.terms().iter().collect();
    terms.sort_by(|(a, _), (b, _)| order.cmp(b, a));

    terms
        .iter()
        .map(|(monomial, coefficient)| {
            if monomial.is_one() {
                return coefficient.to_string();
            }
            if coefficient.is_one() {
                return monomial_to_string(monomial, variables);
            }
            format!(
                "{}*{}",
                coefficient,
                monomial_to_string(monomial, variables)
            )
        })
        .collect::<Vec<String>>()
        .join("+")
}

#[cfg(test)]
mod tests {
    use super::{monomial_to_string, polynomial_to_string};
    use crate::{fields::Zp13, FiniteField, Monomial, MonomialOrder, MultivariatePolynomial, One};

    type F = Zp13;

    const VARIABLES: [&str; 3] = ["x1", "x2", "x3"];

    /// Exponents of zero are omitted, of one are bare, and above one carry a caret.
    #[test]
    fn test_a_monomial_renders_with_the_callers_names() {
        let monomial: Monomial<3> = Monomial::new(&[1, 0, 2]);
        assert_eq!(monomial_to_string(&monomial, &VARIABLES), "x1*x3^2");
    }

    /// The constant monomial renders as `1`, not as the empty string.
    #[test]
    fn test_the_constant_monomial_renders_as_one() {
        let monomial: Monomial<3> = Monomial::one();
        assert_eq!(monomial_to_string(&monomial, &VARIABLES), "1");
    }

    /// A rendered monomial parses back to itself.
    #[test]
    fn test_a_rendered_monomial_parses_back() {
        for exponents in [[0, 0, 0], [3, 0, 0], [1, 1, 1], [0, 2, 5]] {
            let monomial: Monomial<3> = Monomial::new(&exponents);
            let text = monomial_to_string(&monomial, &VARIABLES);
            let parsed: MultivariatePolynomial<3, F> =
                MultivariatePolynomial::parse(&text, VARIABLES).expect("parses");
            let expected = MultivariatePolynomial::new(&[(monomial, F::one())]);
            assert_eq!(parsed, expected, "{:?} rendered as {:?}", exponents, text);
        }
    }

    /// A rendered polynomial parses back to itself, over every term shape.
    #[test]
    fn test_a_rendered_polynomial_parses_back() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let cases: [&[(Monomial<3>, F)]; 4] = [
            &[(Monomial::new(&[2, 0, 0]), F::new(1))],
            &[(Monomial::one(), F::new(7))],
            &[
                (Monomial::new(&[1, 1, 0]), F::new(5)),
                (Monomial::one(), F::new(12)),
            ],
            &[
                (Monomial::new(&[0, 0, 3]), F::new(1)),
                (Monomial::new(&[1, 0, 0]), F::new(2)),
                (Monomial::one(), F::new(1)),
            ],
        ];

        for terms in cases {
            let polynomial: MultivariatePolynomial<3, F> = MultivariatePolynomial::new(terms);
            let text = polynomial_to_string(&polynomial, &VARIABLES, order);
            let parsed: MultivariatePolynomial<3, F> =
                MultivariatePolynomial::parse(&text, VARIABLES).expect("parses");
            assert_eq!(parsed, polynomial, "rendered as {:?}", text);
        }
    }

    /// The zero polynomial renders as `0`.
    #[test]
    fn test_the_zero_polynomial_renders_as_zero() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let zero: MultivariatePolynomial<3, F> = MultivariatePolynomial::zero();
        assert_eq!(polynomial_to_string(&zero, &VARIABLES, order), "0");
    }

    /// Terms descend under the order they were rendered with, so the text is canonical.
    #[test]
    fn test_terms_descend_under_the_order() {
        let polynomial: MultivariatePolynomial<3, F> = MultivariatePolynomial::new(&[
            (Monomial::new(&[0, 0, 1]), F::new(1)),
            (Monomial::new(&[2, 0, 0]), F::new(1)),
            (Monomial::new(&[1, 1, 0]), F::new(1)),
        ]);
        let text = polynomial_to_string(
            &polynomial,
            &VARIABLES,
            MonomialOrder::GradedReverseLexicographic,
        );
        assert_eq!(text, "x1^2+x1*x2+x3");
    }
}
