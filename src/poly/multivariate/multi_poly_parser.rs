//! Parse a string as a Multivariate polynomial over a finite field.

use crate::{
    poly::{multivariate::sparse_multivariate_polynomial::SparseMultiPoly, Monomial},
    FiniteField,
};
use pest::{error::Error, iterators::Pair, Parser};
use pest_derive::*;
use std::str::FromStr;

#[derive(Parser)]
#[grammar = "poly/multivariate/multi_poly.pest"]
struct MultivariatePolynomialParser;

/// Parse a string as a Multivariate polynomial over a finite field.
///
/// # Arguments
/// * `str` - A string to parse.
/// * `variables` - Variable names.
pub fn parse_multivariate_polynomial<const N: usize, F: FiniteField>(
    str: &str,
    variables: [&str; N],
) -> Result<SparseMultiPoly<N, F>, Error<Rule>> {
    // The result.
    let mut polynomial = SparseMultiPoly::<N, F>::zero();

    // Whitespace is not significant.
    let str: String = str.chars().filter(|c| !c.is_whitespace()).collect();
    // println!("Parsing {}", str);

    // This for loop shouldn't be necessary.
    for pair in MultivariatePolynomialParser::parse(Rule::polynomial, &str)? {
        match pair.as_rule() {
            Rule::polynomial => {
                polynomial = parse_polynomial(pair, variables);
                break;
            }
            Rule::EOI => break, // End of input.
            _ => panic!("Not a Multivariate polynomial: {}", str),
        }
    }

    Ok(polynomial)
}

// Parse a pair that has matched the 'univariate' rule.
fn parse_polynomial<const N: usize, F: FiniteField>(
    polynomial: Pair<Rule>,
    variables: [&str; N],
) -> SparseMultiPoly<N, F> {
    // println!("parsing univariate: {}", univariate.as_span().as_str());
    let mut result = SparseMultiPoly::<N, F>::zero();

    for pair in polynomial.into_inner() {
        match pair.as_rule() {
            Rule::term => {
                result = &result + &parse_term(pair, variables);
            }
            Rule::EOI => break, // End of Input.
            _ => panic!("A univariate should only contain terms: {:?}", pair),
        }
    }

    result
}

// Parse a Pair that has matched on the 'term' rule.
fn parse_term<const N: usize, F: FiniteField>(
    term: Pair<Rule>,
    variables: [&str; N],
) -> SparseMultiPoly<N, F> {
    // println!("parsing term: {}", term.as_span().as_str());

    // This for loop shouldn't be necessary?
    for pair in term.into_inner() {
        // A term is a monomial (i.e. c*x*y) or a constant.
        match pair.as_rule() {
            Rule::constant => {
                let c: F = parse_constant(&pair);
                return SparseMultiPoly::from(c);
            }
            Rule::monomial => {
                return parse_monomial(pair, variables);
            }
            _ => panic!("A term must be a monomial or a constant: {:?}", pair),
        }
    }

    unimplemented!()
}

// Parse a Pair that has matched on the 'constant' rule.
fn parse_constant<F: FiniteField>(matched: &Pair<Rule>) -> F {
    // TODO: clean this up using the `sign` and `integer` rules.
    let matched_string = matched.as_span().as_str();
    if matched_string.starts_with('+') {
        // Skip the "+" and parse the rest.
        return F::from_str(&matched_string[1..matched_string.len()]).unwrap();
    }

    if matched_string.starts_with('-') {
        // Skip the "-" and parse the rest.
        return F::zero() - F::from_str(&matched_string[1..matched_string.len()]).unwrap();
    }

    F::from_str(matched_string).unwrap()
}

// Parse a Pair that has matched on the 'monomial' rule.
fn parse_monomial<const N: usize, F: FiniteField>(
    monomial: Pair<Rule>,
    variables: [&str; N],
) -> SparseMultiPoly<N, F> {
    // println!("parsing monomial: {}", monomial.as_span().as_str());
    let mut c: Option<F> = None;
    let mut result = SparseMultiPoly::<N, F>::one();

    for pair in monomial.into_inner() {
        match pair.as_rule() {
            Rule::constant => {
                c = Some(parse_constant(&pair));
            }
            Rule::sign => {
                if pair.as_span().as_str() == "-" {
                    c = Some(F::one().neg());
                }
            }
            // Parse a power, (e.g. x^3)
            Rule::power => {
                result = &result * &parse_power(pair, variables);
            }
            Rule::EOI => continue,
            _ => panic!("Unexpected rule {:?}", pair),
        }
    }

    if let Some(constant) = c {
        // TODO: it should be possible to scale a Multivariate polynomial by a constant.
        result = &result * &SparseMultiPoly::from(constant);
    }

    // TODO: multiply this by c, if any, or negate, if necessary.
    result
}

fn parse_power<const N: usize, F: FiniteField>(
    power: Pair<Rule>,
    variables: [&str; N],
) -> SparseMultiPoly<N, F> {
    // println!("parsing power: {}", power.as_span().as_str());
    let mut exponents = [0u32; N];
    let mut variable_index = 0;
    let mut exponent = 1;

    // TODO: This for loop shouldn't be necessary: power contains one or two inner parts.
    for pair in power.into_inner() {
        match pair.as_rule() {
            // A power (e.g. x^3) should contain a variable and an integer.
            Rule::var => {
                let variable = pair.as_span().as_str();
                variable_index = variables.iter().position(|&v| v == variable).unwrap();
            }
            Rule::integer => {
                // By assumption, variable_index has already been set.
                // println!("Setting exponent {}", variable_index);
                exponent = u32::from_str(pair.as_span().as_str()).unwrap();
            }
            _ => panic!("Unexpected rule {:?}", pair),
        }
    }
    exponents[variable_index] = exponent;
    SparseMultiPoly::new(&[(F::one(), Monomial::new(&exponents))])
}

#[cfg(test)]
mod tests {
    use crate::{
        fields::PrimeFieldElement64,
        poly::{
            multivariate::{
                multi_poly_parser::parse_multivariate_polynomial,
                sparse_multivariate_polynomial::SparseMultiPoly,
            },
            Monomial,
        },
        FiniteField, One,
    };

    #[test]
    // Attempting to parse an empty string should return a ParsingError.
    fn test_parse_empty_string() {
        type F = PrimeFieldElement64<1091>;
        const N: usize = 3;
        let variables: [&str; N] = ["x", "y", "z"];

        match parse_multivariate_polynomial::<N, F>("", variables) {
            Err(_) => {} // Expected
            _ => panic!("Expected an error"),
        }
    }

    #[test]
    // Parsing an invalid string should fail.
    fn test_parse_invalid_strings() {
        let garbage = ["...", "x^", "x^y", "x/y"];
        for s in garbage.iter() {
            println!("parsing {}", s);
            match parse_multivariate_polynomial::<3, PrimeFieldElement64<1091>>(s, ["x", "y", "z"])
            {
                Err(_) => {} // Expected
                _ => panic!("Expected an error"),
            }
        }
    }

    #[test]
    // Should correctly parse a positive or negative constant.
    fn test_parse_constant() {
        type F = PrimeFieldElement64<1091>;
        const N: usize = 3;
        type P = SparseMultiPoly<N, F>;
        let variables: [&str; N] = ["x", "y", "z"];

        // 0
        assert_eq!(
            P::zero(),
            parse_multivariate_polynomial::<N, F>("0", variables).unwrap()
        );

        // 12
        assert_eq!(
            P::from(F::new(12)),
            parse_multivariate_polynomial::<N, F>("12", variables).unwrap()
        );

        // +12
        assert_eq!(
            P::from(F::new(12)),
            parse_multivariate_polynomial::<N, F>("+12", variables).unwrap()
        );

        // -12
        assert_eq!(
            P::from(F::new(12).neg()),
            parse_multivariate_polynomial::<N, F>("-12", variables).unwrap()
        );
    }

    #[test]
    // Multiple terms of the same degree are allowed, e.g. "1 + x*y + x*y" = "1 + 2*x*y".
    fn test_parse_multiple_terms_of_same_degree() {
        type F = PrimeFieldElement64<1091>;
        const N: usize = 3;
        type P = SparseMultiPoly<N, F>;
        let variables: [&str; N] = ["x", "y", "z"];

        assert_eq!(
            P::new(&[
                (Monomial::new(&[1, 1, 0]), F::new(2)),
                (Monomial::new(&[0, 0, 0]), F::one())
            ]), // 2*x*y + 1
            parse_multivariate_polynomial::<N, F>("1 + x*y + x*y", variables).unwrap()
        );
    }

    #[test]
    // E.g. x*y, x^3*z
    fn test_parse_monomial() {
        type F = PrimeFieldElement64<1091>;
        const N: usize = 3;
        type P = SparseMultiPoly<N, F>;
        let variables: [&str; N] = ["x", "y", "z"];

        // x*y
        assert_eq!(
            P::new(&[(Monomial::new(&[1, 1, 0]), F::one())]),
            parse_multivariate_polynomial::<N, F>("x*y", variables).unwrap()
        );

        // x^3*z
        assert_eq!(
            P::new(&[(Monomial::new(&[3, 0, 1]), F::one())]),
            parse_multivariate_polynomial::<N, F>("x^3*z", variables).unwrap()
        );

        // x^3*z + x*y
        assert_eq!(
            P::new(&[
                (Monomial::new(&[3, 0, 1]), F::one()),
                (Monomial::new(&[1, 1, 0]), F::one())
            ]),
            parse_multivariate_polynomial::<N, F>("x^3*z + x*y", variables).unwrap()
        );

        // 3*x
        assert_eq!(
            P::new(&[(Monomial::new(&[1, 0, 0]), F::new(3))]),
            parse_multivariate_polynomial::<N, F>("3*x", variables).unwrap()
        );

        // 3*x - y
        assert_eq!(
            P::new(&[
                (Monomial::new(&[1, 0, 0]), F::new(3)),
                (Monomial::new(&[0, 1, 0]), F::one().neg())
            ]),
            parse_multivariate_polynomial::<N, F>("3*x - y", variables).unwrap()
        );
    }

    #[test]
    fn test_parse_polynomial() {
        type F = PrimeFieldElement64<1091>;
        const N: usize = 3;
        type P = SparseMultiPoly<N, F>;
        let variables: [&str; N] = ["x", "y", "z"];

        // x + y + z
        assert_eq!(
            P::new(&[
                (Monomial::new(&[1, 0, 0]), F::one()),
                (Monomial::new(&[0, 1, 0]), F::one()),
                (Monomial::new(&[0, 0, 1]), F::one())
            ]),
            parse_multivariate_polynomial::<N, F>("x + y + z", variables).unwrap()
        );

        // -x - y - z
        assert_eq!(
            P::new(&[
                (Monomial::new(&[1, 0, 0]), F::one().neg()),
                (Monomial::new(&[0, 1, 0]), F::one().neg()),
                (Monomial::new(&[0, 0, 1]), F::one().neg())
            ]),
            parse_multivariate_polynomial::<N, F>("-x-y-z", variables).unwrap()
        );

        // x + y + z + 2*x^2 + 2*y^2 + 2*z^2
        assert_eq!(
            P::new(&[
                (Monomial::new(&[1, 0, 0]), F::one()),
                (Monomial::new(&[0, 1, 0]), F::one()),
                (Monomial::new(&[0, 0, 1]), F::one()),
                (Monomial::new(&[2, 0, 0]), F::new(2)),
                (Monomial::new(&[0, 2, 0]), F::new(2)),
                (Monomial::new(&[0, 0, 2]), F::new(2))
            ]),
            parse_multivariate_polynomial::<N, F>("x + y + z + 2*x^2 + 2*y^2 + 2*z^2", variables)
                .unwrap()
        );

        // x + y + z + 2*x^2 + 2*y^2 + 2*z^2 + 3*x*y + 3*y*z + 3*x*z
        assert_eq!(
            P::new(&[
                (Monomial::new(&[1, 0, 0]), F::one()),
                (Monomial::new(&[0, 1, 0]), F::one()),
                (Monomial::new(&[0, 0, 1]), F::one()),
                (Monomial::new(&[2, 0, 0]), F::new(2)),
                (Monomial::new(&[0, 2, 0]), F::new(2)),
                (Monomial::new(&[0, 0, 2]), F::new(2)),
                (Monomial::new(&[1, 1, 0]), F::new(3)),
                (Monomial::new(&[0, 1, 1]), F::new(3)),
                (Monomial::new(&[1, 0, 1]), F::new(3))
            ]),
            parse_multivariate_polynomial::<N, F>(
                "x + y + z + 2*x^2 + 2*y^2 + 2*z^2 + 3*x*y + 3*y*z + 3*x*z",
                variables
            )
            .unwrap()
        );

        // x + y + z + 2*x^2 + 2*y^2 + 2*z^2 + 3*x*y + 3*y*z + 3*x*z + 4*x*y*z
        assert_eq!(
            P::new(&[
                (Monomial::new(&[1, 0, 0]), F::one()),
                (Monomial::new(&[0, 1, 0]), F::one()),
                (Monomial::new(&[0, 0, 1]), F::one()),
                (Monomial::new(&[2, 0, 0]), F::new(2)),
                (Monomial::new(&[0, 2, 0]), F::new(2)),
                (Monomial::new(&[0, 0, 2]), F::new(2)),
                (Monomial::new(&[1, 1, 0]), F::new(3)),
                (Monomial::new(&[0, 1, 1]), F::new(3)),
                (Monomial::new(&[1, 0, 1]), F::new(3)),
                (Monomial::new(&[1, 1, 1]), F::new(4)),
            ]),
            parse_multivariate_polynomial::<N, F>(
                "x + y + z + 2*x^2 + 2*y^2 + 2*z^2 + 3*x*y + 3*y*z + 3*x*z + 4*x*y*z",
                variables
            )
            .unwrap()
        );
    }

    #[test]
    fn test_parse_variables_with_underscores() {
        type F = PrimeFieldElement64<1091>;
        const N: usize = 3;
        type P = SparseMultiPoly<N, F>;
        let variables: [&str; N] = ["x_0", "x_1", "x_2"];

        // x + y + z
        assert_eq!(
            P::new(&[
                (Monomial::new(&[1, 0, 0]), F::one()),
                (Monomial::new(&[0, 1, 0]), F::one()),
                (Monomial::new(&[0, 0, 1]), F::one())
            ]),
            parse_multivariate_polynomial::<N, F>("x_0 + x_1 + x_2", variables).unwrap()
        );
    }
}
