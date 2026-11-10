//! Weighted Grobner bases computed by Singular, committed as literals.
//!
//! **Generated. Do not edit by hand.** Regenerate with
//!
//! ```text
//! Singular -q tools/weighted_reference_bases.sing > src/grobner/weighted_reference_bases.rs
//! ```
//!
//! Singular's `std` is Buchberger/slimgb lineage, so these are independent of Zeebra's F4 in
//! algorithm and not only in implementation. The spelling each row was computed under was
//! **measured and not assumed** -- see `tools/weighted_reference_bases.sing` for the table, and
//! for why `LastVariableFirst` is a reversed labelling rather than an ordering name.
//!
//! Every row is over `GF(32003)` in three variables under the Griffin weight vector
//! `(1, 7, 49)`. The prime is a surrogate: the FreeLunch round-4 system is at
//! 28407454060060787, above the `2^31` ceiling Singular's prime fields stop at, so the Griffin
//! system itself cannot be posed to Singular at all and what is pinned here is the convention.

use crate::WeightedTieBreak;

/// One ideal and the weighted Grobner basis Singular computed for it.
pub(crate) struct ReferenceWeightedBasis {
    /// The system's label, for an assertion message.
    pub name: &'static str,
    /// The tie-break Singular's spelling was verified to implement.
    pub tie_break: WeightedTieBreak,
    /// The generators, in Zeebra's parser syntax.
    pub system: &'static [&'static str],
    /// Singular's reduced basis under the weighted order.
    pub basis: &'static [&'static str],
}

/// The surrogate prime every row is over.
pub(crate) const WEIGHTED_REFERENCE_PRIME: u64 = 32003;

/// The variables every row is in, in Zeebra's index order.
pub(crate) const WEIGHTED_REFERENCE_VARIABLES: [&str; 3] = ["x", "y", "z"];

/// The weight vector every row is under.
pub(crate) const WEIGHTED_REFERENCE_WEIGHTS: [u32; 3] = [1, 7, 49];

pub(crate) const WEIGHTED_REFERENCE_BASES: &[ReferenceWeightedBasis] = &[
    ReferenceWeightedBasis {
        name: "griffin-shaped",
        tie_break: WeightedTieBreak::Lexicographic,
        system: &["x^7-y", "y^7-z", "x*z-1"],
        basis: &["x^7-y", "y^7-z", "x*z-1", "y*z-x^6", "z^2-x^6*y^6"],
    },
    ReferenceWeightedBasis {
        name: "tie-56",
        tie_break: WeightedTieBreak::Lexicographic,
        system: &["-x^7*z+y^8", "x*y-1"],
        basis: &["x*y-1", "x^7*z-y^8", "y^9-x^6*z"],
    },
    ReferenceWeightedBasis {
        name: "griffin-shaped",
        tie_break: WeightedTieBreak::ReverseLexicographic,
        system: &["x^7-y", "y^7-z", "x*z-1"],
        basis: &["x^7-y", "y^7-z", "x*z-1", "y*z-x^6", "z^2-x^6*y^6"],
    },
    ReferenceWeightedBasis {
        name: "tie-56",
        tie_break: WeightedTieBreak::ReverseLexicographic,
        system: &["y^8-x^7*z", "x*y-1"],
        basis: &["x*y-1", "y^8-x^7*z", "x^8*z-y^7"],
    },
    ReferenceWeightedBasis {
        name: "griffin-shaped",
        tie_break: WeightedTieBreak::LastVariableFirst,
        system: &["-y+x^7", "-z+y^7", "z*x-1"],
        basis: &["y-x^7", "z-x^49", "x^50-1"],
    },
    ReferenceWeightedBasis {
        name: "tie-56",
        tie_break: WeightedTieBreak::LastVariableFirst,
        system: &["-z*x^7+y^8", "y*x-1"],
        basis: &["y*x-1", "z*x^7-y^8", "y^9-z*x^6"],
    },
];

#[cfg(test)]
mod tests {
    use super::{
        WEIGHTED_REFERENCE_BASES, WEIGHTED_REFERENCE_PRIME, WEIGHTED_REFERENCE_VARIABLES,
        WEIGHTED_REFERENCE_WEIGHTS,
    };
    use crate::{
        fields::Zp32003, grobner::buchberger, FiniteField, KnownOrder, MonomialOrder,
        MultivariatePolynomial, WeightedTieBreak,
    };

    type F = Zp32003;

    fn parse_all(texts: &[&str]) -> Vec<MultivariatePolynomial<3, F>> {
        texts
            .iter()
            .map(|text| {
                MultivariatePolynomial::parse(text, WEIGHTED_REFERENCE_VARIABLES).unwrap_or_else(
                    |e| panic!("Singular emitted {text:?}, which did not parse: {e}"),
                )
            })
            .collect()
    }

    /// A basis as a comparable value: monic, zeros dropped, sorted by leading monomial.
    ///
    /// Two engines may return a reduced basis in any order and scaled by any unit, and neither is
    /// a disagreement. What is canonical is the set of monic elements.
    fn canonical(
        basis: &[MultivariatePolynomial<3, F>],
        order: MonomialOrder,
    ) -> Vec<MultivariatePolynomial<3, F>> {
        let mut monic: Vec<MultivariatePolynomial<3, F>> = basis
            .iter()
            .filter(|p| !p.is_zero())
            .map(|p| p.scale(&p.leading_coefficient(order).inverse()))
            .collect();
        monic.sort_by(|a, b| order.cmp(&a.leading_monomial(order), &b.leading_monomial(order)));
        monic
    }

    /// Zeebra's weighted basis equals Singular's, under each verified spelling — #624.
    ///
    /// The differential oracle weighted orders did not have. Until #624 a weighted basis was
    /// checked against its own axioms, against grlex/grevlex at unit weights, and against the
    /// published Griffin witnesses, but nothing independent recomputed one — every external
    /// adapter refuses a weighted order, because substituting `dp` answers a different question.
    ///
    /// The spelling each row was computed under is measured, not assumed, and the measurement is
    /// in `tools/weighted_reference_bases.sing`. The reason that matters is
    /// `WeightedTieBreak::LastVariableFirst`: it has **no** Singular ordering name, only a reversed
    /// variable labelling, and both the right spelling and the wrong one run and return a correct
    /// basis for *some* order.
    #[test]
    fn test_zeebra_agrees_with_singular_under_each_weighted_spelling() {
        // The field the references were computed over, read from the generated file rather than
        // assumed: a regeneration at another prime would otherwise be compared against `Zp32003`
        // and disagree for a reason that is not a disagreement.
        assert_eq!(
            F::characteristic_u128(),
            Some(WEIGHTED_REFERENCE_PRIME as u128),
            "the pinned references are over a different prime than this test's field"
        );

        for reference in WEIGHTED_REFERENCE_BASES {
            let order = MonomialOrder::weighted(&WEIGHTED_REFERENCE_WEIGHTS, reference.tie_break)
                .expect("the Griffin weight vector is positive");
            let system = parse_all(reference.system);
            let computed = canonical(&buchberger(&system, order), order);
            let pinned = canonical(&parse_all(reference.basis), order);

            assert_eq!(
                computed.len(),
                pinned.len(),
                "{} under {:?}: Zeebra returned {} elements, Singular {}",
                reference.name,
                reference.tie_break,
                computed.len(),
                pinned.len()
            );
            assert_eq!(
                computed, pinned,
                "{} under {:?}: the two engines disagree",
                reference.name, reference.tie_break
            );
        }
    }

    /// The two pinned systems separate all three tie-breaks, so a swapped spelling cannot pass.
    ///
    /// Neither system alone does it: `griffin-shaped` gives `Lexicographic` and
    /// `ReverseLexicographic` the same basis and isolates `LastVariableFirst`, whose basis is
    /// triangular; `tie-56` isolates `ReverseLexicographic`, whose leading monomial at weighted
    /// degree 56 is `y^8` where the other two lead with `x^7 z`. Together every pair differs
    /// somewhere, which is what makes the test above a check on the *spelling* and not only on the
    /// arithmetic.
    #[test]
    fn test_the_pinned_systems_distinguish_every_pair_of_tie_breaks() {
        let breaks = [
            WeightedTieBreak::Lexicographic,
            WeightedTieBreak::ReverseLexicographic,
            WeightedTieBreak::LastVariableFirst,
        ];
        for (i, left) in breaks.iter().enumerate() {
            for right in &breaks[i + 1..] {
                let differs = WEIGHTED_REFERENCE_BASES
                    .iter()
                    .filter(|r| r.tie_break == *left)
                    .any(|l| {
                        WEIGHTED_REFERENCE_BASES
                            .iter()
                            .filter(|r| r.tie_break == *right && r.name == l.name)
                            .any(|r| r.basis != l.basis)
                    });
                assert!(
                    differs,
                    "no pinned system tells {left:?} from {right:?}, so a swap between them would \
                     pass the agreement test vacuously"
                );
            }
        }
    }
}
