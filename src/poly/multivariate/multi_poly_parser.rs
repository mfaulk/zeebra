//! Parse a string as a Multivariate polynomial over a finite field.

use crate::{
    poly::{multivariate::sparse_multivariate_polynomial::SparseMultiPoly, Monomial},
    FiniteField,
};
use pest::{
    error::{Error, ErrorVariant},
    iterators::Pair,
    Parser, Span,
};
use pest_derive::*;

#[derive(Parser)]
#[grammar = "poly/multivariate/multi_poly.pest"]
struct MultivariatePolynomialParser;

/// A failure the grammar cannot express, reported against the span that caused it.
///
/// The grammar accepts any decimal integer, so whether a coefficient names an element of `F` or an
/// exponent fits a `u32` is only knowable once the field and the variable list are known. Those
/// used to be `unwrap`s, which made text input over GF(2^8) abort the process (#377).
fn semantic_error(span: Span<'_>, message: String) -> Box<Error<Rule>> {
    Box::new(Error::new_from_span(
        ErrorVariant::CustomError { message },
        span,
    ))
}

/// Parse a string as a Multivariate polynomial over a finite field.
///
/// # Arguments
/// * `str` - A string to parse.
/// * `variables` - Variable names.
// The error is boxed because `pest::error::Error` is several hundred bytes, which would otherwise
// inflate every `Ok` value in this `Result` to the same size.
pub fn parse_multivariate_polynomial<const N: usize, F: FiniteField>(
    str: &str,
    variables: [&str; N],
) -> Result<SparseMultiPoly<N, F>, Box<Error<Rule>>> {
    // The result.
    let mut polynomial = SparseMultiPoly::<N, F>::zero();

    // Whitespace is not significant.
    let str: String = str.chars().filter(|c| !c.is_whitespace()).collect();
    // println!("Parsing {}", str);

    // The grammar matches a single `polynomial` pair, so only the first is significant.
    if let Some(pair) = MultivariatePolynomialParser::parse(Rule::polynomial, &str)?.next() {
        match pair.as_rule() {
            Rule::polynomial => polynomial = parse_polynomial(pair, variables)?,
            Rule::EOI => {} // Empty input is the zero polynomial.
            _ => panic!("Not a Multivariate polynomial: {}", str),
        }
    }

    Ok(polynomial)
}

// Parse a pair that has matched the 'univariate' rule.
fn parse_polynomial<const N: usize, F: FiniteField>(
    polynomial: Pair<Rule>,
    variables: [&str; N],
) -> Result<SparseMultiPoly<N, F>, Box<Error<Rule>>> {
    let mut result = SparseMultiPoly::<N, F>::zero();

    for pair in polynomial.into_inner() {
        match pair.as_rule() {
            Rule::term => {
                result = &result + &parse_term(pair, variables)?;
            }
            Rule::EOI => break, // End of Input.
            _ => panic!("A univariate should only contain terms: {:?}", pair),
        }
    }

    Ok(result)
}

// Parse a Pair that has matched on the 'term' rule.
fn parse_term<const N: usize, F: FiniteField>(
    term: Pair<Rule>,
    variables: [&str; N],
) -> Result<SparseMultiPoly<N, F>, Box<Error<Rule>>> {
    // A term is a monomial (i.e. c*x*y) or a constant.
    let pair = term
        .into_inner()
        .next()
        .expect("A term must contain a monomial or a constant");
    match pair.as_rule() {
        Rule::constant => Ok(SparseMultiPoly::from(parse_constant::<F>(&pair)?)),
        Rule::monomial => parse_monomial(pair, variables),
        _ => panic!("A term must be a monomial or a constant: {:?}", pair),
    }
}

// Parse a Pair that has matched on the 'constant' rule.
//
// The digits go to `F::from_str`, whose accepted syntax is the field's own `Display` form: a
// residue over a prime field, a coefficient bit pattern over GF(2^m).
fn parse_constant<F: FiniteField>(matched: &Pair<Rule>) -> Result<F, Box<Error<Rule>>> {
    // TODO: clean this up using the `sign` and `integer` rules.
    let span = matched.as_span();
    let matched_string = span.as_str();
    let (negated, digits) = match matched_string.strip_prefix('-') {
        Some(digits) => (true, digits),
        None => (
            false,
            matched_string.strip_prefix('+').unwrap_or(matched_string),
        ),
    };

    let element = F::from_str(digits).map_err(|e| {
        semantic_error(
            span,
            format!("{digits} is not an element of this field: {e}"),
        )
    })?;
    Ok(if negated {
        F::zero() - element
    } else {
        element
    })
}

// Parse a Pair that has matched on the 'monomial' rule.
fn parse_monomial<const N: usize, F: FiniteField>(
    monomial: Pair<Rule>,
    variables: [&str; N],
) -> Result<SparseMultiPoly<N, F>, Box<Error<Rule>>> {
    let mut c: Option<F> = None;
    let mut result = SparseMultiPoly::<N, F>::one();

    for pair in monomial.into_inner() {
        match pair.as_rule() {
            Rule::constant => {
                c = Some(parse_constant(&pair)?);
            }
            Rule::sign => {
                if pair.as_span().as_str() == "-" {
                    c = Some(F::one().neg());
                }
            }
            // Parse a power, (e.g. x^3)
            Rule::power => {
                result = &result * &parse_power(pair, variables)?;
            }
            Rule::EOI => continue,
            _ => panic!("Unexpected rule {:?}", pair),
        }
    }

    if let Some(constant) = c {
        // TODO: it should be possible to scale a Multivariate polynomial by a constant.
        result = &result * &SparseMultiPoly::from(constant);
    }

    Ok(result)
}

fn parse_power<const N: usize, F: FiniteField>(
    power: Pair<Rule>,
    variables: [&str; N],
) -> Result<SparseMultiPoly<N, F>, Box<Error<Rule>>> {
    let mut exponents = [0u32; N];
    let mut variable_index = 0;
    let mut exponent = 1;

    // TODO: This for loop shouldn't be necessary: power contains one or two inner parts.
    for pair in power.into_inner() {
        match pair.as_rule() {
            // A power (e.g. x^3) should contain a variable and an integer.
            Rule::var => {
                let span = pair.as_span();
                let variable = span.as_str();
                variable_index =
                    variables
                        .iter()
                        .position(|&v| v == variable)
                        .ok_or_else(|| {
                            semantic_error(
                                span,
                                format!("{variable} is not one of the variables {variables:?}"),
                            )
                        })?;
            }
            Rule::integer => {
                // By assumption, variable_index has already been set.
                let span = pair.as_span();
                exponent = span.as_str().parse().map_err(|_| {
                    semantic_error(
                        span,
                        format!("the exponent {} does not fit a u32", span.as_str()),
                    )
                })?;
            }
            _ => panic!("Unexpected rule {:?}", pair),
        }
    }
    exponents[variable_index] = exponent;
    Ok(SparseMultiPoly::new(&[(
        F::one(),
        Monomial::new(&exponents),
    )]))
}

#[cfg(test)]
mod tests {
    use crate::{
        fields::{Gf256, PrimeFieldElement64},
        poly::{
            multivariate::{
                multi_poly_parser::parse_multivariate_polynomial,
                sparse_multivariate_polynomial::SparseMultiPoly,
            },
            Monomial,
        },
        FiniteField, One,
    };

    /// A system over GF(2^8) parses, with each coefficient read as its bit pattern.
    #[test]
    fn test_parse_over_a_binary_field() {
        let parsed =
            parse_multivariate_polynomial::<2, Gf256>("5*x0*x1 + 173*x0 + 1", ["x0", "x1"])
                .expect("well formed");
        assert_eq!(
            parsed,
            SparseMultiPoly::new(&[
                (Monomial::new(&[1, 1]), Gf256::new(5)),
                (Monomial::new(&[1, 0]), Gf256::new(173)),
                (Monomial::one(), Gf256::new(1)),
            ])
        );
    }

    /// A coefficient outside the field is a parse error rather than a panic (#377).
    #[test]
    fn test_a_coefficient_outside_the_field_is_an_error() {
        // 256 is not a bit pattern of degree below 8.
        let error = parse_multivariate_polynomial::<1, Gf256>("256*x0", ["x0"])
            .expect_err("256 is not an element of GF(2^8)");
        assert!(
            error.to_string().contains("256 is not an element"),
            "{error}"
        );
    }

    /// An unknown variable and an unrepresentable exponent are errors rather than panics.
    #[test]
    fn test_unknown_variables_and_oversized_exponents_are_errors() {
        assert!(parse_multivariate_polynomial::<1, PrimeFieldElement64<1091>>("y", ["x"]).is_err());
        assert!(
            parse_multivariate_polynomial::<1, PrimeFieldElement64<1091>>("x^99999999999", ["x"])
                .is_err()
        );
    }

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
