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
    /// primes draw the same monomials and the same term count for a seed — see
    /// [`Self::drawn_monomials`]. The *generated* monomials can still differ between primes,
    /// because two terms on one monomial are merged and their coefficients can cancel modulo one
    /// characteristic and not another.
    ///
    /// # Panics
    /// If `characteristic` is below 2, or `shape.variables` is zero, or `shape.max_terms` is zero.
    pub fn generate(seed: u64, shape: SystemShape, characteristic: u64) -> Self {
        assert!(characteristic >= 2, "a field has at least two elements");

        let polynomials = draw(seed, shape)
            .into_iter()
            .map(|polynomial| {
                let reduced: Vec<GeneratedTerm> = polynomial
                    .into_iter()
                    .map(|(exponents, coefficient)| GeneratedTerm {
                        exponents,
                        // Never zero: a zero coefficient is an absent term, and a generator that
                        // silently has fewer terms than the draw said makes minimization harder to
                        // interpret.
                        coefficient: 1 + coefficient % (characteristic - 1),
                    })
                    .collect();
                merge(reduced, characteristic)
            })
            .collect();

        Self {
            seed,
            characteristic,
            variables: (1..=shape.variables).map(|i| format!("x{}", i)).collect(),
            polynomials,
        }
    }

    /// The monomials a seed and a shape draw, before any field is chosen.
    ///
    /// Takes no characteristic, which is the point: it is what makes "this ideal has the same
    /// quotient dimension over GF(13) and over GF(2^31 - 1)" a statement about one system. A
    /// generated polynomial's monomials are these with the merged-and-cancelled ones removed, so
    /// they are a sub-multiset of these and nothing more can be said without the characteristic.
    ///
    /// # Panics
    /// As [`Self::generate`], for the shape.
    pub fn drawn_monomials(seed: u64, shape: SystemShape) -> Vec<Vec<Vec<u32>>> {
        draw(seed, shape)
            .into_iter()
            .map(|polynomial| {
                polynomial
                    .into_iter()
                    .map(|(exponents, _)| exponents)
                    .collect()
            })
            .collect()
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

    /// Whether every generator has distinct monomials, i.e. is canonical.
    ///
    /// The invariant [`Self::generate`] establishes and minimization preserves, since every shrink
    /// removes or lowers something rather than adding a monomial.
    pub fn is_canonical(&self) -> bool {
        self.polynomials.iter().all(|polynomial| {
            let distinct: std::collections::HashSet<&Vec<u32>> =
                polynomial.iter().map(|term| &term.exponents).collect();
            distinct.len() == polynomial.len()
        })
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

/// The raw draws for a seed and a shape: exponents, and an unreduced `u64` per coefficient.
///
/// The one place the random stream is consumed, so that [`GeneratedSystem::generate`] and
/// [`GeneratedSystem::drawn_monomials`] cannot drift. The coefficient draw is fixed-width on
/// purpose: `gen_range` rejection-samples, consuming a number of bytes that depends on the range,
/// which would make every monomial drawn *after* it depend on the characteristic.
///
/// # Panics
/// If `shape.variables` is zero, or `shape.max_terms` is zero.
fn draw(seed: u64, shape: SystemShape) -> Vec<Vec<(Vec<u32>, u64)>> {
    assert!(shape.variables > 0, "a system has at least one variable");
    assert!(shape.max_terms > 0, "a polynomial has at least one term");

    let mut rng = StdRng::seed_from_u64(seed);
    let mut polynomials = Vec::with_capacity(shape.variables);

    for _ in 0..shape.variables {
        let terms = rng.gen_range(1..=shape.max_terms);
        let mut polynomial: Vec<(Vec<u32>, u64)> = Vec::with_capacity(terms);
        for _ in 0..terms {
            // Degree first, then distributed over the variables: drawing each exponent
            // independently and rejecting what overshoots would make the number of draws depend on
            // the rejections, and so on the seed in a way that is hard to reason about when
            // minimizing.
            let degree = rng.gen_range(0..=shape.max_degree);
            let mut exponents = vec![0u32; shape.variables];
            for _ in 0..degree {
                let variable = rng.gen_range(0..shape.variables);
                exponents[variable] += 1;
            }
            polynomial.push((exponents, rng.gen::<u64>()));
        }
        polynomials.push(polynomial);
    }

    polynomials
}

/// Terms with the same monomial summed, in first-occurrence order, zeros dropped.
///
/// **Not cosmetic.** Two terms on the same monomial are two integer literals in the text, and
/// Singular sums bare integer literals in 32-bit arithmetic before coercing them into the ring: at
/// `p = 2^31 - 1`, `1870573936+1536614746+x1` reads back as `x1-887778614` where the ring sum is
/// `x1-887778612`. Zeebra's parser merges the terms and gets the second. So an unmerged polynomial
/// is a *different ideal* on the two sides, through no fault of either implementation.
///
/// Found by the harness itself, on seed 55770 over GF(2^31 - 1). The oracle-input check in
/// [`comparison`](super::comparison) is the belt to this brace — it verifies that Singular read the
/// system it was sent rather than trusting that it did.
fn merge(terms: Vec<GeneratedTerm>, characteristic: u64) -> Vec<GeneratedTerm> {
    let mut merged: Vec<GeneratedTerm> = Vec::with_capacity(terms.len());
    for term in terms {
        match merged
            .iter_mut()
            .find(|existing| existing.exponents == term.exponents)
        {
            // Both coefficients are below the characteristic, so the sum is below twice it and
            // cannot overflow a `u64` for any characteristic this crate's prime fields accept.
            Some(existing) => {
                existing.coefficient = (existing.coefficient + term.coefficient) % characteristic
            }
            None => merged.push(term),
        }
    }
    // A merge can cancel a monomial out entirely, and a zero coefficient is an absent term.
    merged.retain(|term| term.coefficient != 0);
    merged
}

#[cfg(test)]
mod tests {
    use super::{merge, GeneratedSystem, GeneratedTerm, SystemShape};
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

    /// The monomials a seed draws do not depend on the characteristic.
    ///
    /// The property that makes a cross-field comparison a statement about one system. Stated on the
    /// *draws* rather than on the generated polynomials, because merging can cancel a monomial
    /// modulo one characteristic and not another — which the next test shows really happens.
    #[test]
    fn test_the_drawn_monomials_do_not_depend_on_the_characteristic() {
        for seed in 0..64 {
            let drawn = GeneratedSystem::drawn_monomials(seed, SHAPE);
            for characteristic in [2u64, 3, 7, 13, 65537, 2147483647] {
                let system = GeneratedSystem::generate(seed, SHAPE, characteristic);

                // Every generated monomial was drawn, and nothing was drawn twice that is not
                // merged: so the generated monomials are the drawn ones less the cancellations.
                for (generated, drawn) in system.polynomials.iter().zip(&drawn) {
                    for term in generated {
                        assert!(
                            drawn.contains(&term.exponents),
                            "seed {} over GF({}): {:?} was not drawn",
                            seed,
                            characteristic,
                            term.exponents
                        );
                    }
                    assert!(
                        generated.len() <= drawn.len(),
                        "seed {} over GF({}): more terms than were drawn",
                        seed,
                        characteristic
                    );
                }
            }
        }
    }

    /// Merging really does cancel at a small characteristic and not at a large one.
    ///
    /// Asserted so that the weaker claim above is known to be the strongest one available, rather
    /// than a hedge against something that never happens. Over GF(2) two draws on one monomial
    /// cancel half the time; over GF(2^31 - 1) it takes a one-in-two-billion coincidence.
    #[test]
    fn test_cancellation_depends_on_the_characteristic() {
        // Distinct drawn monomials, not drawn terms: merging two terms on one monomial reduces the
        // count at every characteristic, and what varies is only whether the merged coefficient is
        // zero. Counting raw terms would measure the merging and call it cancellation.
        let cancelled = |characteristic: u64| -> usize {
            (0..256)
                .map(|seed| {
                    let distinct: usize = GeneratedSystem::drawn_monomials(seed, SHAPE)
                        .iter()
                        .map(|polynomial| {
                            polynomial
                                .iter()
                                .collect::<std::collections::HashSet<&Vec<u32>>>()
                                .len()
                        })
                        .sum();
                    let generated = GeneratedSystem::generate(seed, SHAPE, characteristic).terms();
                    distinct - generated
                })
                .sum()
        };

        assert!(
            cancelled(2) > 0,
            "no draw cancelled over GF(2), so the weaker claim is untested"
        );
        assert_eq!(
            cancelled(2147483647),
            0,
            "a coincidence modulo 2^31 - 1 would be remarkable"
        );
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

    /// Every generated polynomial has distinct monomials.
    ///
    /// Not a tidiness property. Two terms on one monomial are two integer literals in the text, and
    /// Singular sums bare literals in 32-bit arithmetic before coercing them into the ring — so at
    /// `p = 2^31 - 1` an unmerged polynomial is a different ideal on the two sides. See `merge`.
    #[test]
    fn test_every_generated_polynomial_is_canonical() {
        for characteristic in [2u64, 3, 7, 13, 65537, 2147483647] {
            for seed in 0..64 {
                let system = GeneratedSystem::generate(seed, SHAPE, characteristic);
                assert!(
                    system.is_canonical(),
                    "seed {} over GF({}) has a repeated monomial: {:?}",
                    seed,
                    characteristic,
                    system.render()
                );
            }
        }
    }

    /// Merging sums coefficients on a shared monomial, in first-occurrence order.
    #[test]
    fn test_merging_sums_a_shared_monomial() {
        let terms = vec![
            GeneratedTerm {
                exponents: vec![1, 0],
                coefficient: 3,
            },
            GeneratedTerm {
                exponents: vec![0, 0],
                coefficient: 5,
            },
            GeneratedTerm {
                exponents: vec![1, 0],
                coefficient: 4,
            },
        ];
        let merged = merge(terms, 13);
        assert_eq!(merged.len(), 2);
        assert_eq!(merged[0].exponents, vec![1, 0]);
        assert_eq!(merged[0].coefficient, 7);
        assert_eq!(merged[1].exponents, vec![0, 0]);
        assert_eq!(merged[1].coefficient, 5);
    }

    /// A merge that cancels drops the term rather than leaving a zero coefficient.
    #[test]
    fn test_merging_drops_a_cancelled_term() {
        let terms = vec![
            GeneratedTerm {
                exponents: vec![1, 0],
                coefficient: 6,
            },
            GeneratedTerm {
                exponents: vec![1, 0],
                coefficient: 7,
            },
        ];
        assert!(merge(terms, 13).is_empty());
    }

    /// The reconstruction a minimized failure's name implies still produces a canonical system.
    ///
    /// Shrinking only removes or lowers, so it cannot create a repeated monomial — but lowering an
    /// exponent *can* make two terms share one, which is the one case worth checking.
    #[test]
    fn test_lowering_an_exponent_can_collide_and_is_not_merged() {
        // Deliberate, and documented rather than fixed: a shrunk system is no longer canonical, and
        // the oracle-input check is what protects a comparison made on one. The generator's
        // guarantee is about what it generates.
        let mut system = GeneratedSystem::generate(3, SHAPE, 13);
        system.polynomials[0] = vec![
            GeneratedTerm {
                exponents: vec![2, 0, 0],
                coefficient: 1,
            },
            GeneratedTerm {
                exponents: vec![1, 0, 0],
                coefficient: 1,
            },
        ];
        assert!(system.is_canonical());
        system.polynomials[0][0].exponents[0] -= 1;
        assert!(!system.is_canonical());
    }
}
