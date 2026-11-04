//! Deterministic random polynomial systems, as text.
//!
//! The systems cross a process boundary — Zeebra parses them and so does Singular — so the text is
//! the system rather than a rendering of it. Generating structure and rendering it once means both
//! sides are given the same characters, and a failing case can be pasted into a test or a Singular
//! session unchanged.
//!
//! Generation does not depend on the field type, only on its characteristic as an integer. The same
//! seed therefore produces the *same* system shape at every prime, which is what makes
//! "this ideal has the same quotient dimension over GF(13) and GF(2^31 - 1)" a statement about one
//! system rather than about two.

use rand::{prelude::StdRng, Rng, SeedableRng};

/// One term: an exponent per variable, and a coefficient in `[1, characteristic)`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GeneratedTerm {
    /// One exponent per variable, so `exponents.len()` is the variable count.
    pub exponents: Vec<u32>,

    /// Never zero, so a term is never silently absent. Reduced modulo the characteristic.
    pub coefficient: u64,
}

impl GeneratedTerm {
    /// The total degree.
    pub fn degree(&self) -> u32 {
        self.exponents.iter().sum()
    }

    /// Whether every exponent is zero, i.e. the term is a constant.
    pub fn is_constant(&self) -> bool {
        self.exponents.iter().all(|exponent| *exponent == 0)
    }

    /// `3*x1^2*x3`, or `3` for a constant.
    fn render(&self, variables: &[String]) -> String {
        let mut factors: Vec<String> = Vec::new();
        if self.coefficient != 1 || self.is_constant() {
            factors.push(self.coefficient.to_string());
        }
        for (variable, exponent) in variables.iter().zip(&self.exponents) {
            match exponent {
                0 => {}
                1 => factors.push(variable.clone()),
                _ => factors.push(format!("{}^{}", variable, exponent)),
            }
        }
        factors.join("*")
    }
}

/// How large a system to generate.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SystemShape {
    /// Variables, which is also the number of equations: square systems are where
    /// zero-dimensionality is common without being guaranteed.
    pub variables: usize,

    /// The largest total degree of any term.
    pub max_degree: u32,

    /// The most terms a polynomial may have, before duplicate monomials are merged.
    pub max_terms: usize,
}

/// A generated system, structurally, so that it can be shrunk as well as rendered.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GeneratedSystem {
    /// The seed this came from. Retained through every minimization step, since it is the only
    /// thing that reproduces the original.
    pub seed: u64,

    /// The field's characteristic, as an integer. Coefficients are reduced modulo it.
    pub characteristic: u64,

    /// `x1`, `x2`, ... — one per variable, in the order both sides declare them.
    pub variables: Vec<String>,

    /// The generators. A polynomial with no terms is the zero polynomial and is legal.
    pub polynomials: Vec<Vec<GeneratedTerm>>,
}

impl GeneratedSystem {
    /// A pseudorandom system, determined entirely by `seed`, `shape` and `characteristic`.
    ///
    /// The draws are taken in a fixed order that does not depend on the characteristic, so two
    /// primes give the same exponents and the same term count for a seed. Only the coefficients
    /// differ, and only because they are reduced into the field.
    ///
    /// # Panics
    /// If `characteristic` is below 2, or `shape.variables` is zero, or `shape.max_terms` is zero.
    pub fn generate(seed: u64, shape: SystemShape, characteristic: u64) -> Self {
        assert!(characteristic >= 2, "a field has at least two elements");
        assert!(shape.variables > 0, "a system has at least one variable");
        assert!(shape.max_terms > 0, "a polynomial has at least one term");

        let mut rng = StdRng::seed_from_u64(seed);
        let variables: Vec<String> = (1..=shape.variables).map(|i| format!("x{}", i)).collect();

        let mut polynomials = Vec::with_capacity(shape.variables);
        for _ in 0..shape.variables {
            let terms = rng.gen_range(1..=shape.max_terms);
            let mut polynomial: Vec<GeneratedTerm> = Vec::with_capacity(terms);
            for _ in 0..terms {
                // Degree first, then distributed over the variables: drawing each exponent
                // independently and rejecting what overshoots would make the number of draws
                // depend on the rejections, and so on the seed in a way that is hard to reason
                // about when minimizing.
                let degree = rng.gen_range(0..=shape.max_degree);
                let mut exponents = vec![0u32; shape.variables];
                for _ in 0..degree {
                    let variable = rng.gen_range(0..shape.variables);
                    exponents[variable] += 1;
                }

                // One fixed-width draw and then a reduction, rather than `gen_range`: a range's
                // rejection sampling consumes a number of bytes that depends on the range, which
                // would make the *monomials* downstream of it depend on the characteristic. The
                // resulting modulo bias is of no consequence to a test input.
                //
                // Never zero: a zero coefficient is an absent term, and a generator that silently
                // has fewer terms than the draw said makes minimization harder to interpret.
                let coefficient = 1 + rng.gen::<u64>() % (characteristic - 1);
                polynomial.push(GeneratedTerm {
                    exponents,
                    coefficient,
                });
            }
            polynomials.push(polynomial);
        }

        Self {
            seed,
            characteristic,
            variables,
            polynomials,
        }
    }

    /// The variable names, as the slices both parsers want.
    pub fn variable_names(&self) -> Vec<&str> {
        self.variables.iter().map(String::as_str).collect()
    }

    /// Each generator as a string both Zeebra's parser and Singular accept.
    ///
    /// Every coefficient is positive and below the characteristic, so no term needs a sign and the
    /// rendering is the same on both sides. The zero polynomial renders as `0`.
    pub fn render(&self) -> Vec<String> {
        self.polynomials
            .iter()
            .map(|polynomial| {
                if polynomial.is_empty() {
                    return "0".to_string();
                }
                polynomial
                    .iter()
                    .map(|term| term.render(&self.variables))
                    .collect::<Vec<String>>()
                    .join("+")
            })
            .collect()
    }

    /// A stable name for this system, for reports and fixture files.
    pub fn name(&self) -> String {
        format!(
            "seed-{}-p{}-n{}",
            self.seed,
            self.characteristic,
            self.variables.len()
        )
    }

    /// The largest total degree over all terms, or zero for a system of zero polynomials.
    pub fn degree(&self) -> u32 {
        self.polynomials
            .iter()
            .flatten()
            .map(GeneratedTerm::degree)
            .max()
            .unwrap_or(0)
    }

    /// Terms across all generators.
    pub fn terms(&self) -> usize {
        self.polynomials.iter().map(Vec::len).sum()
    }
}

#[cfg(test)]
mod tests {
    use super::{GeneratedSystem, GeneratedTerm, SystemShape};
    use crate::{
        fields::{Zp13, Zp2147483647},
        MultivariatePolynomial,
    };

    const SHAPE: SystemShape = SystemShape {
        variables: 3,
        max_degree: 3,
        max_terms: 4,
    };

    /// The same seed and characteristic give the same system, every time.
    #[test]
    fn test_generation_is_deterministic() {
        let a = GeneratedSystem::generate(12345, SHAPE, 13);
        let b = GeneratedSystem::generate(12345, SHAPE, 13);
        assert_eq!(a, b);
        assert_eq!(a.render(), b.render());
    }

    /// Different seeds give different systems, so a sweep is not one system repeated.
    #[test]
    fn test_different_seeds_give_different_systems() {
        let systems: Vec<Vec<String>> = (0..16)
            .map(|seed| GeneratedSystem::generate(seed, SHAPE, 65537).render())
            .collect();
        let distinct: std::collections::HashSet<&Vec<String>> = systems.iter().collect();
        assert!(
            distinct.len() >= 15,
            "{} distinct systems out of 16 seeds",
            distinct.len()
        );
    }

    /// Changing the characteristic changes only the coefficients, not the monomials.
    ///
    /// The property that makes a cross-field comparison a statement about one system.
    #[test]
    fn test_the_monomials_do_not_depend_on_the_characteristic() {
        for seed in 0..32 {
            let small = GeneratedSystem::generate(seed, SHAPE, 13);
            let large = GeneratedSystem::generate(seed, SHAPE, 2147483647);
            assert_eq!(small.variables, large.variables);
            let exponents = |s: &GeneratedSystem| -> Vec<Vec<Vec<u32>>> {
                s.polynomials
                    .iter()
                    .map(|p| p.iter().map(|t| t.exponents.clone()).collect())
                    .collect()
            };
            assert_eq!(exponents(&small), exponents(&large), "seed {}", seed);
        }
    }

    /// Every coefficient is a nonzero residue, so no term is secretly absent.
    #[test]
    fn test_coefficients_are_nonzero_residues() {
        for characteristic in [2u64, 3, 7, 13, 65537, 2147483647] {
            for seed in 0..24 {
                let system = GeneratedSystem::generate(seed, SHAPE, characteristic);
                for term in system.polynomials.iter().flatten() {
                    assert!(term.coefficient >= 1, "a zero coefficient was generated");
                    assert!(
                        term.coefficient < characteristic,
                        "{} is not a residue modulo {}",
                        term.coefficient,
                        characteristic
                    );
                }
            }
        }
    }

    /// No term exceeds the requested degree.
    #[test]
    fn test_no_term_exceeds_the_requested_degree() {
        for max_degree in 1..=4u32 {
            let shape = SystemShape {
                variables: 4,
                max_degree,
                max_terms: 5,
            };
            for seed in 0..24 {
                let system = GeneratedSystem::generate(seed, shape, 7);
                assert!(
                    system.degree() <= max_degree,
                    "degree {} exceeds {} at seed {}",
                    system.degree(),
                    max_degree,
                    seed
                );
            }
        }
    }

    /// What is rendered is what Zeebra parses: the terms survive the round trip.
    ///
    /// Checked by parsing the rendering and rebuilding the polynomial from the structure, which
    /// catches a rendering that drops a coefficient of one or mis-renders an exponent.
    #[test]
    fn test_the_rendering_parses_back_to_the_same_polynomial() {
        type F = Zp13;

        for seed in 0..64 {
            let system = GeneratedSystem::generate(seed, SHAPE, 13);
            let names = <[&str; 3]>::try_from(system.variable_names().as_slice()).expect("three");

            for (polynomial, text) in system.polynomials.iter().zip(system.render()) {
                let parsed: MultivariatePolynomial<3, F> =
                    MultivariatePolynomial::parse(&text, names)
                        .unwrap_or_else(|e| panic!("cannot parse {:?}: {}", text, e));

                let terms: Vec<(crate::Monomial<3>, F)> = polynomial
                    .iter()
                    .map(|term| {
                        let exponents =
                            <[u32; 3]>::try_from(term.exponents.as_slice()).expect("three");
                        (
                            crate::Monomial::new(&exponents),
                            <F as crate::FiniteField>::new(term.coefficient),
                        )
                    })
                    .collect();
                let expected = MultivariatePolynomial::new(&terms);

                assert_eq!(parsed, expected, "seed {}: {:?}", seed, text);
            }
        }
    }

    /// A polynomial with no terms renders as `0` and parses as the zero polynomial.
    #[test]
    fn test_the_zero_polynomial_round_trips() {
        let mut system = GeneratedSystem::generate(1, SHAPE, 13);
        system.polynomials[0].clear();
        assert_eq!(system.render()[0], "0");

        let parsed: MultivariatePolynomial<3, Zp2147483647> =
            MultivariatePolynomial::parse("0", ["x1", "x2", "x3"]).expect("parses");
        assert!(parsed.is_zero());
    }

    /// A constant term renders as its coefficient alone, with no dangling `*`.
    #[test]
    fn test_a_constant_term_renders_as_its_coefficient() {
        let term = GeneratedTerm {
            exponents: vec![0, 0, 0],
            coefficient: 5,
        };
        let variables = vec!["x1".to_string(), "x2".to_string(), "x3".to_string()];
        assert_eq!(term.render(&variables), "5");
    }

    /// A unit coefficient is omitted, and an exponent of one needs no `^1`.
    #[test]
    fn test_a_unit_coefficient_and_a_first_power_are_implicit() {
        let term = GeneratedTerm {
            exponents: vec![1, 0, 2],
            coefficient: 1,
        };
        let variables = vec!["x1".to_string(), "x2".to_string(), "x3".to_string()];
        assert_eq!(term.render(&variables), "x1*x3^2");
    }

    /// Over GF(2) every coefficient is 1, which is the only nonzero residue.
    #[test]
    fn test_characteristic_two_has_only_unit_coefficients() {
        let system = GeneratedSystem::generate(7, SHAPE, 2);
        for term in system.polynomials.iter().flatten() {
            assert_eq!(term.coefficient, 1);
        }
    }
}
