//! Parse a string as a univariate polynomial over a finite field.

use crate::{poly::univariate::UnivariatePolynomial, FiniteField};
use pest::{
    error::Error,
    iterators::{Pair, Pairs},
    Parser,
};
use pest_derive::*;
use std::str::FromStr;

#[derive(Parser)]
#[grammar = "poly/univariate/univariate.pest"]
struct UnivariatePolynomialParser;

// Parse a string representing a univariate polynomial.
pub fn parse_univariate_polynomial<F: FiniteField>(
    str: &str,
) -> Result<UnivariatePolynomial<F>, Error<Rule>> {
    // Whitespace is not significant.
    let str: String = str.chars().filter(|c| !c.is_whitespace()).collect();

    // The result.
    let mut polynomial = UnivariatePolynomial::new(&[F::zero()]);

    let pairs: Pairs<Rule> = UnivariatePolynomialParser::parse(Rule::polynomial, &str)?;
    for pair_1 in pairs {
        match pair_1.as_rule() {
            Rule::polynomial => {
                for pair_2 in pair_1.into_inner() {
                    // A polynomial should only contain terms.
                    match pair_2.as_rule() {
                        Rule::term => {
                            for pair_3 in pair_2.into_inner() {
                                // Parse one term.
                                match pair_3.as_rule() {
                                    Rule::constant => {
                                        let c = parse_constant(&pair_3);
                                        let constant_poly = UnivariatePolynomial::new(&[c]);
                                        polynomial = polynomial + constant_poly;
                                    }
                                    Rule::monomial => {
                                        polynomial = polynomial + parse_monomial(pair_3);
                                    }
                                    _ => panic!(
                                        "A term must be a monomial or a constant: {:?}",
                                        pair_3
                                    ),
                                }
                            }
                        }
                        Rule::EOI => continue, // End of Input.
                        _ => {
                            panic!("A polynomial should only contain terms: {:?}", pair_2)
                        }
                    }
                }
            }
            Rule::EOI => continue, // End of input.
            _ => panic!("Not a univariate polynomial: {:?}", &str),
        }
    }

    Ok(polynomial)
}

fn parse_constant<F: FiniteField>(matched: &Pair<Rule>) -> F {
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

fn parse_monomial<F: FiniteField>(matched: Pair<Rule>) -> UnivariatePolynomial<F> {
    let mut coefficient = F::one();
    let mut exponent = 1;
    for pair_1 in matched.into_inner() {
        match pair_1.as_rule() {
            Rule::constant => {
                coefficient = parse_constant(&pair_1);
            }
            Rule::sign => {
                if pair_1.as_span().as_str() == "-" {
                    coefficient = F::zero() - F::one();
                }
            }
            Rule::power => {
                // e.g. x^2, Y2^12, etc.
                for pair_2 in pair_1.into_inner() {
                    match pair_2.as_rule() {
                        Rule::var => continue, // TODO: The variable name is ignored.
                        Rule::integer => {
                            // println!("pair_2: {:?}", pair_2);
                            exponent = usize::from_str(pair_2.as_span().as_str()).unwrap();
                        }
                        _ => panic!("Unexpected rule {:?}", pair_2),
                    }
                }
            }
            Rule::EOI => continue,
            _ => panic!("Unexpected rule {:?}", pair_1),
        }
    }
    let mut coefficients = vec![F::zero(); exponent + 1];
    coefficients[exponent] = coefficient;
    UnivariatePolynomial::new(&coefficients)
}

#[cfg(test)]
mod tests {
    use crate::{
        fields::PrimeFieldElement64,
        identities::Zero,
        poly::univariate::{
            univariate_parser::parse_univariate_polynomial, Polynomial, UnivariatePolynomial,
        },
        FiniteField,
    };
    use pest::error::ErrorVariant::ParsingError;

    #[test]
    // Attempting to parse an empty string should return a ParsingError.
    fn test_parse_empty_string() {
        type F = PrimeFieldElement64<1091>;

        match parse_univariate_polynomial::<F>("") {
            Ok(p) => panic!("{:?}", p),
            Err(e) => match e.variant {
                ParsingError {
                    positives: _,
                    negatives: _,
                } => {} // This is expected,
                _ => panic!("Unexpected error {:?}", e),
            },
        }
    }

    #[ignore] // Currently, multivariate polynomials are parsed incorrectly.
    #[test]
    // Parsing a Multivariate polynomial should return an error.
    fn test_parsing_multivariate_polynomial() {
        type F = PrimeFieldElement64<1091>;

        match parse_univariate_polynomial::<F>("x + y") {
            Ok(p) => panic!("{:?}", p),
            Err(e) => match e.variant {
                ParsingError {
                    positives: _,
                    negatives: _,
                } => {} // This is expected,
                _ => panic!("Unexpected error {:?}", e),
            },
        }
    }

    #[test]
    // Parsing an invalid string should fail.
    fn test_parse_invalid_strings() {
        type F = PrimeFieldElement64<1091>;

        let invalid_strings = vec!["y=x", "3/x", "1+x^", "1+x^2^3", "x=1", "1+x^2^"];
        for invalid in invalid_strings {
            match parse_univariate_polynomial::<F>(invalid) {
                Ok(p) => panic!("{} parsed to {:?}", invalid, p),
                Err(e) => match e.variant {
                    ParsingError {
                        positives: _,
                        negatives: _,
                    } => {} // This is expected,
                    _ => panic!("Unexpected error {:?}", e),
                },
            }
        }
    }

    #[test]
    // Multiple terms of the same degree are allowed, e.g. "1 + x + x" = "1 + 2x".
    fn test_parse_multiple_terms_of_same_degree() {
        type F = PrimeFieldElement64<1091>;
        assert_eq!(
            parse_univariate_polynomial::<F>("1 + x + x").unwrap(),
            UnivariatePolynomial::new(&[F::new(1), F::new(2)]), // 1 + 2x
        );
    }

    #[test]
    // Should correctly parse a positive or negative constant.
    fn test_parse_constant() {
        type F = PrimeFieldElement64<1091>;
        type P = UnivariatePolynomial<F>;

        // 0
        assert_eq!(P::zero(), parse_univariate_polynomial::<F>("0").unwrap());

        // 12
        assert_eq!(
            P::new(&[F::new(12)]),
            parse_univariate_polynomial::<F>("12").unwrap()
        );

        // +12
        assert_eq!(
            P::new(&[F::new(12)]),
            parse_univariate_polynomial::<F>("+12").unwrap()
        );

        // -12
        assert_eq!(
            P::new(&[F::new(12).neg()]),
            parse_univariate_polynomial::<F>("-12").unwrap()
        );
    }

    #[test]
    fn test_parse_monomial() {
        type F = PrimeFieldElement64<1091>;
        type P = UnivariatePolynomial<F>;

        println!("x");
        assert_eq!(
            parse_univariate_polynomial::<F>("x").unwrap(),
            P::new(&[F::zero(), F::new(1)]), // 0 + x
        );

        // Variable names can have multiple characters.
        assert_eq!(
            parse_univariate_polynomial::<F>("meow").unwrap(),
            P::new(&[F::zero(), F::new(1)]), // 0 + x
        );

        println!("+x");
        assert_eq!(
            parse_univariate_polynomial::<F>("+x").unwrap(),
            P::new(&[F::zero(), F::new(1)]), // 0 + x
        );

        println!("-x");
        assert_eq!(
            parse_univariate_polynomial::<F>("-x").unwrap(),
            P::new(&[F::zero(), F::new(1090)]), // 0 - 1090x
        );

        // 2x
        assert_eq!(
            parse_univariate_polynomial::<F>("2x").unwrap(),
            P::new(&[F::zero(), F::new(2)]), // 0 + 2x
        );

        // 2*x
        assert_eq!(
            parse_univariate_polynomial::<F>("2*x").unwrap(),
            P::new(&[F::zero(), F::new(2)]), // 0 + 2x
        );

        // +2x
        assert_eq!(
            parse_univariate_polynomial::<F>("+2x").unwrap(),
            P::new(&[F::zero(), F::new(2)]), // 0 + 2x
        );

        // x^2
        assert_eq!(
            parse_univariate_polynomial::<F>("x^2").unwrap(),
            P::new(&[F::new(0), F::new(0), F::new(1)]), // 0 + 0x + x^2
        );

        // -x^2
        assert_eq!(
            parse_univariate_polynomial::<F>("-x^2").unwrap(),
            P::new(&[F::new(0), F::new(0), F::new(1090)]), // 0 + 0x + 1090x^2
        );

        // Multi-character variable name.
        assert_eq!(
            parse_univariate_polynomial::<F>("-xxx^2").unwrap(),
            P::new(&[F::new(0), F::new(0), F::new(1090)]), // 0 + 0x + 1090x^2
        );

        // Multi-digit exponent.
        let mut coefficients = [F::zero(); 13];
        coefficients[12] = F::new(2);
        assert_eq!(
            parse_univariate_polynomial::<F>("2x^12").unwrap(),
            P::new(&coefficients),
        );
    }

    #[test]
    fn test_parse_polynomial() {
        type F = PrimeFieldElement64<1091>;
        type P = UnivariatePolynomial<F>;

        // 1+x
        assert_eq!(
            parse_univariate_polynomial::<F>("1+x").unwrap(),
            P::new(&[F::new(1), F::new(1)]), // 1 + x
        );

        // 1 + x. Whitespace should not be significant.
        assert_eq!(
            parse_univariate_polynomial::<F>("1 + x").unwrap(),
            P::new(&[F::new(1), F::new(1)]), // 1 + x
        );

        // 1 + x^2
        assert_eq!(
            parse_univariate_polynomial::<F>("1+x^2").unwrap(),
            P::new(&[F::new(1), F::new(0), F::new(1)]), // 1 + 0x + x^2
        );

        // 1 + 4*x + 9*x^2
        assert_eq!(
            parse_univariate_polynomial::<F>("1 + 4*x + 9*x^2").unwrap(),
            P::new(&[F::new(1), F::new(4), F::new(9)]),
        );

        // 91+Y2^3+8Y2^12
        let mut coefficients = [F::zero(); 13];
        coefficients[0] = F::new(91);
        coefficients[3] = F::new(1);
        coefficients[12] = F::new(8);
        assert_eq!(
            parse_univariate_polynomial::<F>("91+Y2^3+8Y2^12").unwrap(),
            P::new(&coefficients),
        );
    }
}
