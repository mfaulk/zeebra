//! The syntactic half of Campa and Roy's shape-position argument (eprint 2025/814, §5), decided
//! on a concrete instance — and a record of why that half is not the whole argument.
//!
//! # What the published theorem says, and what it leaves out
//!
//! Theorem 8 reads: *let `I` be zero-dimensional and `G` a Gröbner basis of it containing, for
//! each variable, an element whose leading monomial is a pure power `x_i^{α_i}`; if `I` has no
//! solutions at infinity, then `I` has shape form in the reduced LEX basis.* Its proof invokes
//! Theorem 7 ([13, Theorem 1.2]), whose standing hypothesis is that **the projection
//! `V(I) → A¹` onto the last coordinate is injective** — and Theorem 8's statement does not carry
//! it.
//!
//! That omission is not cosmetic, because the two hypotheses Theorem 8 *does* state are one
//! hypothesis and it is already implied:
//!
//! - The paper's own Appendix A gives `V(I) finite ⟺ ∀i ∃f ∈ G : LM(f) = x_i^{α_i}`, so the
//!   pure-power condition **is** zero-dimensionality.
//! - Under a *graded* order, `LM(g)` is a monomial of top `deg_≺`, so `LM(top_form(g)) = LM(g)`
//!   and the top-form ideal's leading-term ideal contains every `LM(g)`. A pure power of each
//!   variable is therefore among them, the top-form quotient is finite, and the top forms cut out
//!   only the origin. So **"no solutions at infinity" is automatic** for a Gröbner basis under a
//!   graded order.
//!
//! Taken literally, then, Theorem 8 would say every zero-dimensional ideal is in shape form, and
//! this crate's own corpus refutes that: cyclic's separating set is empty and 44 of 120
//! zero-dimensional differential fixtures fail the detector
//! (`MILESTONE-FGLM-SCALABILITY.md` §8.3). `test_the_published_hypotheses_are_not_sufficient`
//! exhibits one such ideal, discharging every hypothesis below while not being in shape position.
//!
//! # So what is this module for
//!
//! It decides, cheaply and deductively, everything about shape position that *is* syntactic, and
//! names the one hypothesis that is not. The missing hypothesis — that the target coordinate takes
//! distinct values on `V(I)` — is exactly the equality
//! [`ShapeReport::minimal_polynomial_degree`](crate::grobner::fglm::ShapeReport) `== dimension`
//! that `fglm::shape` computes, and it costs a quotient algebra where this costs a Hilbert series.
//!
//! A caller wanting shape position *established* needs both halves, and should say which half gave
//! which: the syntactic conditions are a deduction about the instance, the separating condition is
//! a computation on it, and neither is a proof about a family.

use crate::{
    grobner::{
        f4::{f4_reported, F4Error, F4Options},
        hilbert::{HilbertError, HilbertSeries},
    },
    FiniteField, Monomial, MonomialOrder, MultivariatePolynomial,
};

/// One variable's pure-power leader, and how strong a condition it satisfies.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PurePower {
    /// The variable.
    pub variable: usize,

    /// The smallest `e` with `x_variable^e` leading some basis element.
    pub exponent: u32,

    /// Whether Theorem 4's **strict** condition holds: the element's `deg_≺`-top form is the bare
    /// monomial `x_variable^exponent`, with no other term of the same `deg_≺`.
    ///
    /// This is the hypothesis Theorem 4 is actually stated with, and it is strictly stronger than
    /// "the leading monomial is a pure power". On `ACICO` at `α = 3` over DRL it holds for the `s`
    /// variables and fails for the `y` variables, whose degree-`α` tails include `y_{j−1}^2 s_j` —
    /// which is why Corollary 2 argues by back-substitution rather than by inspection.
    pub strict: bool,
}

/// Theorem 8's printed hypotheses, discharged on one instance.
///
/// **Not sufficient for shape position.** See the module docs: the separating hypothesis Theorem 7
/// carries and Theorem 8 does not is absent from this struct by design, because it is not a
/// syntactic property of the basis.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ShapeHypotheses {
    /// `dim_K K[x]/I`, finite — zero-dimensionality.
    pub quotient_dimension: i128,

    /// One entry per variable, in variable order.
    pub pure_powers: Vec<PurePower>,

    /// `dim_K K[x]/⟨deg_≺-top forms of the basis⟩`, finite — no solutions at infinity but zero.
    ///
    /// Computed rather than assumed, even though the module docs show it is implied under a graded
    /// order: the implication is an argument, and a number that disagreed with it would mean the
    /// argument or the implementation is wrong.
    pub dimension_at_infinity: i128,
}

impl ShapeHypotheses {
    /// The variables for which Theorem 4's strict `deg_≺` condition holds.
    pub fn strict_variables(&self) -> Vec<usize> {
        self.pure_powers
            .iter()
            .filter(|p| p.strict)
            .map(|p| p.variable)
            .collect()
    }
}

/// Which hypothesis could not be discharged.
///
/// A gap is **not** a refutation: the conditions are sufficient-in-part and never necessary, so an
/// ideal can be in shape position with any of them unsatisfied. The variants name the missing
/// hypothesis rather than reporting "not in shape position".
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HypothesisGap {
    /// The leading-term ideal admits no finite quotient dimension.
    PositiveDimensional {
        /// Variables with no pure power among the leading monomials, which is the condition
        /// `socle_degree_bound` returns `None` on and the evidence for *why* it is open.
        without_pure_power: Vec<usize>,
    },

    /// No basis element's leading monomial is a pure power of this variable.
    ///
    /// Unreachable alongside a finite quotient dimension, by the equivalence in the module docs,
    /// and kept as its own variant so that a future order for which the equivalence fails reports
    /// the right thing rather than a dimension error.
    NoPurePower {
        /// The variable with no pure-power leader.
        variable: usize,
    },

    /// The top forms have a nontrivial common zero, so there are solutions at infinity.
    SolutionsAtInfinity {
        /// Variables with no pure power among the top forms' leading monomials.
        without_pure_power: Vec<usize>,
    },

    /// The top-form basis did not complete inside the budget, so the condition is **unknown**.
    ///
    /// Distinct from [`HypothesisGap::SolutionsAtInfinity`] on purpose: a budget being crossed is
    /// not a mathematical property of the ideal, and conflating the two once cost a wrong verdict
    /// on a cipher-derived family (#668 moved that record out; it is at commit `9532a9a2`).
    AtInfinityRefused {
        /// What F4 refused with.
        error: F4Error,
    },

    /// A Hilbert computation failed.
    Hilbert {
        /// What it failed with.
        error: HilbertError,
    },

    /// The order is not graded, so `deg_≺` — which Theorem 4's homogenization is taken with
    /// respect to — is undefined and "the top form" has no meaning.
    ///
    /// Lexicographic and block orders are refused rather than silently answered with the total
    /// degree, because the total-degree top form of a lex basis is a different ideal and a
    /// statement about it would say nothing about the one asked for.
    UngradedOrder {
        /// The order that was offered.
        order: MonomialOrder,
    },
}

impl From<HilbertError> for HypothesisGap {
    fn from(error: HilbertError) -> Self {
        Self::Hilbert { error }
    }
}

/// Decide Theorem 8's printed hypotheses for the ideal `basis` generates.
///
/// `basis` must be a Gröbner basis with respect to `order`; the pure-power condition is a
/// statement about a Gröbner basis and is meaningless on an arbitrary generating set. `options`
/// bounds the auxiliary F4 run on the top forms.
///
/// # Errors
/// [`HypothesisGap`], naming the hypothesis that could not be discharged.
pub fn shape_position_hypotheses<const N: usize, F: FiniteField>(
    basis: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    options: &F4Options,
) -> Result<ShapeHypotheses, HypothesisGap> {
    if matches!(
        order,
        MonomialOrder::Lexicographic | MonomialOrder::Block(_)
    ) {
        return Err(HypothesisGap::UngradedOrder { order });
    }
    let live: Vec<&MultivariatePolynomial<N, F>> = basis.iter().filter(|p| !p.is_zero()).collect();
    let leads: Vec<Monomial<N>> = live.iter().map(|p| p.leading_monomial(order)).collect();

    let series = HilbertSeries::of_basis(basis, order)?;
    let Some(quotient_dimension) = series.quotient_dimension(&leads)? else {
        return Err(HypothesisGap::PositiveDimensional {
            without_pure_power: variables_without_pure_power::<N>(&leads),
        });
    };

    let mut pure_powers = Vec::with_capacity(N);
    for variable in 0..N {
        let witness = live
            .iter()
            .zip(&leads)
            .filter_map(|(p, lead)| pure_power_exponent(lead, variable).map(|e| (e, *p)))
            .min_by_key(|(e, _)| *e)
            .ok_or(HypothesisGap::NoPurePower { variable })?;
        let (exponent, element) = witness;
        pure_powers.push(PurePower {
            variable,
            exponent,
            strict: top_form_is_a_monomial(element, order),
        });
    }

    let forms: Vec<MultivariatePolynomial<N, F>> =
        live.iter().map(|p| graded_top_form(p, order)).collect();
    let (at_infinity, _) = f4_reported(&forms, order, options);
    let at_infinity = at_infinity.map_err(|error| HypothesisGap::AtInfinityRefused { error })?;
    let infinity_leads: Vec<Monomial<N>> = at_infinity
        .iter()
        .filter(|p| !p.is_zero())
        .map(|p| p.leading_monomial(order))
        .collect();
    let infinity_series = HilbertSeries::of_basis(&at_infinity, order)?;
    let Some(dimension_at_infinity) = infinity_series.quotient_dimension(&infinity_leads)? else {
        return Err(HypothesisGap::SolutionsAtInfinity {
            without_pure_power: variables_without_pure_power::<N>(&infinity_leads),
        });
    };

    Ok(ShapeHypotheses {
        quotient_dimension,
        pure_powers,
        dimension_at_infinity,
    })
}

/// `deg_≺` of a monomial: the total degree under a graded order, the weighted degree under a
/// weighted one.
///
/// Theorem 4 homogenizes with respect to `deg_≺`, so the top form has to be taken in the grading
/// the order actually uses. Under a weighted order the total-degree top form is a *different*
/// homogeneous system, and `ACICO` for `α > 3` is stated over a weighted order.
fn order_degree<const N: usize>(order: MonomialOrder, m: &Monomial<N>) -> u64 {
    match order {
        MonomialOrder::Weighted(weighted) => weighted.weighted_degree(m),
        _ => m.degree(),
    }
}

/// The `deg_≺`-homogeneous part of `p` of top `deg_≺`.
fn graded_top_form<const N: usize, F: FiniteField>(
    p: &MultivariatePolynomial<N, F>,
    order: MonomialOrder,
) -> MultivariatePolynomial<N, F> {
    let top = top_degree(p, order);
    let terms: Vec<(Monomial<N>, F)> = p
        .terms()
        .iter()
        .filter(|(m, _)| order_degree(order, m) == top)
        .map(|(m, c)| (*m, *c))
        .collect();
    MultivariatePolynomial::new(&terms)
}

/// Whether `p`'s `deg_≺`-top form is a single monomial, which is Theorem 4's strict condition.
fn top_form_is_a_monomial<const N: usize, F: FiniteField>(
    p: &MultivariatePolynomial<N, F>,
    order: MonomialOrder,
) -> bool {
    let top = top_degree(p, order);
    p.terms()
        .keys()
        .filter(|m| order_degree(order, m) == top)
        .count()
        == 1
}

fn top_degree<const N: usize, F: FiniteField>(
    p: &MultivariatePolynomial<N, F>,
    order: MonomialOrder,
) -> u64 {
    p.terms()
        .keys()
        .map(|m| order_degree(order, m))
        .max()
        .unwrap_or(0)
}

/// `Some(e)` if `m` is `x_variable^e` with `e > 0`, else `None`.
fn pure_power_exponent<const N: usize>(m: &Monomial<N>, variable: usize) -> Option<u32> {
    let exponents = m.exponents();
    let own = *exponents.get(variable)?;
    if own == 0 {
        return None;
    }
    exponents
        .iter()
        .enumerate()
        .all(|(i, e)| i == variable || *e == 0)
        .then_some(own)
}

fn variables_without_pure_power<const N: usize>(leads: &[Monomial<N>]) -> Vec<usize> {
    (0..N)
        .filter(|variable| {
            !leads
                .iter()
                .any(|m| pure_power_exponent(m, *variable).is_some())
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::{shape_position_hypotheses, HypothesisGap};
    use crate::{
        fields::Zp65537,
        grobner::{
            benchmark_systems::planted,
            f4,
            fglm::{shape_report, FglmOptions, QuotientAlgebra},
            F4Options,
        },
        FiniteField, Monomial, MonomialOrder, MultivariatePolynomial,
    };

    type F = Zp65537;

    const ORDER: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

    fn term(exponents: [u32; 2], c: u64) -> (Monomial<2>, F) {
        (Monomial::new(&exponents), F::new(c))
    }

    /// `⟨x² − 1, y² − 1⟩` discharges every hypothesis, strictly, with both dimensions at Bezout.
    #[test]
    fn test_a_binomial_square_system_discharges_every_hypothesis() {
        let system = [
            MultivariatePolynomial::<2, F>::new(&[term([2, 0], 1), term([0, 0], 65536)]),
            MultivariatePolynomial::<2, F>::new(&[term([0, 2], 1), term([0, 0], 65536)]),
        ];
        let basis = f4(&system, ORDER).expect("a basis");
        let hypotheses = shape_position_hypotheses(&basis, ORDER, &F4Options::default())
            .expect("every hypothesis holds");
        assert_eq!(hypotheses.quotient_dimension, 4);
        assert_eq!(hypotheses.dimension_at_infinity, 4);
        assert_eq!(hypotheses.strict_variables(), vec![0, 1]);
    }

    /// A pure-power leader with a same-degree tail is reported as non-strict.
    ///
    /// `x² + xy` leads on `x²` and its top form is not the bare monomial, which is the distinction
    /// between Theorem 4's hypothesis and Theorem 8's.
    #[test]
    fn test_a_same_degree_tail_is_not_the_strict_condition() {
        let system = [
            MultivariatePolynomial::<2, F>::new(&[
                term([2, 0], 1),
                term([1, 1], 1),
                term([0, 0], 65536),
            ]),
            MultivariatePolynomial::<2, F>::new(&[term([0, 2], 1), term([0, 0], 65536)]),
        ];
        let basis = f4(&system, ORDER).expect("a basis");
        let hypotheses = shape_position_hypotheses(&basis, ORDER, &F4Options::default())
            .expect("the printed hypotheses still hold");
        assert!(
            !hypotheses.strict_variables().contains(&0),
            "x's pure-power leader has a degree-two tail, so Theorem 4 does not apply to it"
        );
    }

    /// A positive-dimensional ideal is refused, naming the variables with no pure power.
    #[test]
    fn test_a_positive_dimensional_ideal_is_refused() {
        // `⟨xy − 1⟩` is a hyperbola: one equation, two variables.
        let system = [MultivariatePolynomial::<2, F>::new(&[
            term([1, 1], 1),
            term([0, 0], 65536),
        ])];
        let basis = f4(&system, ORDER).expect("a basis");
        assert_eq!(
            shape_position_hypotheses(&basis, ORDER, &F4Options::default()),
            Err(HypothesisGap::PositiveDimensional {
                without_pure_power: vec![0, 1]
            })
        );
    }

    /// **Theorem 8's printed hypotheses are not sufficient**, and planted-4 is the counterexample.
    ///
    /// Every hypothesis discharges — zero-dimensional, a pure power of each variable leading a
    /// basis element, a finite top-form quotient — and the last variable's minimal polynomial has
    /// degree 4 against a quotient dimension of 16, so the ideal is not in shape position in it.
    /// Each planted pair contributes four points differing only within the pair, so the
    /// projection onto any single coordinate is four-to-one: the hypothesis Theorem 7 carries and
    /// Theorem 8 omits is exactly what fails, and nothing syntactic about the basis can see it.
    #[test]
    fn test_the_published_hypotheses_are_not_sufficient() {
        let point: Vec<F> = [3u64, 5, 7, 11].iter().map(|v| F::new(*v)).collect();
        let system = planted::<4, F>(&point);
        let basis = f4(&system, ORDER).expect("a basis");
        let hypotheses = shape_position_hypotheses(&basis, ORDER, &F4Options::default())
            .expect("planted-4 is zero-dimensional and discharges the printed hypotheses");
        assert_eq!(hypotheses.quotient_dimension, 16);
        let options = FglmOptions::unbounded();
        let algebra = QuotientAlgebra::new(&basis, ORDER, &options).expect("zero-dimensional");
        let report = shape_report(&algebra, 3);
        assert_eq!(report.dimension, 16);
        assert!(
            report.minimal_polynomial_degree < report.dimension,
            "planted-4's last coordinate takes {} distinct values on a 16-point variety",
            report.minimal_polynomial_degree
        );
    }
}
