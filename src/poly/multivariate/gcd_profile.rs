use std::cell::RefCell;

use crate::{util::Json, FiniteField, MultivariatePolynomial};

/// A maximum over observed polynomials, not simultaneous live storage or process memory.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct PolynomialSize {
    pub observations: usize,
    pub max_terms: usize,
    /// Largest monomial total degree after removing the current main variable.
    pub max_coefficient_degree: u64,
}

impl PolynomialSize {
    fn observe<const N: usize, F: FiniteField>(
        &mut self,
        polynomial: &MultivariatePolynomial<N, F>,
        variable: usize,
    ) {
        self.observations += 1;
        self.max_terms = self.max_terms.max(polynomial.terms().len());
        self.max_coefficient_degree = self
            .max_coefficient_degree
            .max(coefficient_degree(polynomial, variable));
    }

    fn json(self) -> Json {
        Json::object([
            ("observations", Json::size(self.observations)),
            ("max_terms", Json::size(self.max_terms)),
            (
                "max_coefficient_degree",
                Json::int(self.max_coefficient_degree),
            ),
        ])
    }
}

/// Passive size observations across one call and all of its recursive GCDs.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct GcdProfile {
    pub prs_entries: PolynomialSize,
    pub raw_remainders: PolynomialSize,
    pub brown_images: PolynomialSize,
    pub brown_interpolants: PolynomialSize,
    pub gcd_calls: usize,
    pub content_calls: usize,
    pub max_recursion_depth: usize,
    pub brown_fallbacks: usize,
    /// Largest local Sylvester coefficient-degree bound, also valid for primitive divisors.
    pub max_subresultant_degree_bound: u64,
    pub subresultant_entries_checked: usize,
    pub subresultant_bound_violations: usize,
    pub subresultant_bounds_unavailable: usize,
}

impl GcdProfile {
    pub fn json(self) -> Json {
        Json::object([
            ("prs_entries", self.prs_entries.json()),
            ("raw_remainders", self.raw_remainders.json()),
            ("brown_images", self.brown_images.json()),
            ("brown_interpolants", self.brown_interpolants.json()),
            ("gcd_calls", Json::size(self.gcd_calls)),
            ("content_calls", Json::size(self.content_calls)),
            ("max_recursion_depth", Json::size(self.max_recursion_depth)),
            ("brown_fallbacks", Json::size(self.brown_fallbacks)),
            (
                "max_subresultant_degree_bound",
                Json::int(self.max_subresultant_degree_bound),
            ),
            (
                "subresultant_entries_checked",
                Json::size(self.subresultant_entries_checked),
            ),
            (
                "subresultant_bound_violations",
                Json::size(self.subresultant_bound_violations),
            ),
            (
                "subresultant_bounds_unavailable",
                Json::size(self.subresultant_bounds_unavailable),
            ),
        ])
    }
}

#[derive(Default)]
struct State {
    profile: GcdProfile,
    depth: usize,
}
thread_local! { static STATE: RefCell<Option<State>> = const { RefCell::new(None) }; }

/// Observe one synchronous computation. Nested scopes panic; unwind resets the scope.
///
/// This scans observed supports and deliberately runs separately from unobserved timing passes.
/// Feature-absent builds compile out every instrumentation call.
pub fn measure<T>(body: impl FnOnce() -> T) -> (T, GcdProfile) {
    STATE.with(|state| {
        let mut state = state.borrow_mut();
        assert!(state.is_none(), "nested GCD size profile");
        *state = Some(State::default());
    });
    struct Reset;
    impl Drop for Reset {
        fn drop(&mut self) {
            STATE.with(|state| {
                state.borrow_mut().take();
            });
        }
    }
    let reset = Reset;
    let value = body();
    let profile = STATE.with(|state| state.borrow_mut().take().unwrap().profile);
    drop(reset);
    (value, profile)
}

pub(super) struct Call;
impl Drop for Call {
    fn drop(&mut self) {
        STATE.with(|state| {
            if let Some(state) = state.borrow_mut().as_mut() {
                state.depth -= 1;
            }
        });
    }
}
pub(super) fn enter() -> Call {
    update(|state| {
        state.depth += 1;
        state.profile.gcd_calls += 1;
        state.profile.max_recursion_depth = state.profile.max_recursion_depth.max(state.depth);
    });
    Call
}
fn update(body: impl FnOnce(&mut State)) {
    STATE.with(|state| {
        if let Some(state) = state.borrow_mut().as_mut() {
            body(state);
        }
    });
}
pub(super) fn content() {
    update(|state| state.profile.content_calls += 1);
}
pub(super) fn fallback() {
    update(|state| state.profile.brown_fallbacks += 1);
}

pub(super) enum Phase {
    Prs,
    Raw,
    Image,
    Interpolant,
}
pub(super) fn observe<const N: usize, F: FiniteField>(
    polynomial: &MultivariatePolynomial<N, F>,
    variable: usize,
    phase: Phase,
) {
    update(|state| {
        match phase {
            Phase::Prs => &mut state.profile.prs_entries,
            Phase::Raw => &mut state.profile.raw_remainders,
            Phase::Image => &mut state.profile.brown_images,
            Phase::Interpolant => &mut state.profile.brown_interpolants,
        }
        .observe(polynomial, variable)
    });
}

fn coefficient_degree<const N: usize, F: FiniteField>(
    polynomial: &MultivariatePolynomial<N, F>,
    variable: usize,
) -> u64 {
    polynomial
        .terms()
        .keys()
        .map(|monomial| {
            monomial
                .exponents()
                .iter()
                .enumerate()
                .filter(|(index, _)| *index != variable)
                .map(|(_, &exponent)| u64::from(exponent))
                .sum()
        })
        .max()
        .unwrap_or(0)
}

pub(super) fn bound<const N: usize, F: FiniteField>(
    a: &MultivariatePolynomial<N, F>,
    b: &MultivariatePolynomial<N, F>,
    variable: usize,
) -> Option<u64> {
    if !STATE.with(|state| state.borrow().is_some()) {
        return None;
    }
    // An order-k minor uses k <= deg(a)+deg(b) coefficient factors per determinant term.
    let bound = (u64::from(a.degree_in(variable)) + u64::from(b.degree_in(variable)))
        .checked_mul(coefficient_degree(a, variable).max(coefficient_degree(b, variable)));
    update(|state| match bound {
        Some(bound) => {
            state.profile.max_subresultant_degree_bound =
                state.profile.max_subresultant_degree_bound.max(bound)
        }
        None => state.profile.subresultant_bounds_unavailable += 1,
    });
    bound
}

pub(super) fn check_bound<const N: usize, F: FiniteField>(
    polynomial: &MultivariatePolynomial<N, F>,
    variable: usize,
    bound: Option<u64>,
) {
    update(|state| {
        if let Some(bound) = bound {
            state.profile.subresultant_entries_checked += 1;
            if coefficient_degree(polynomial, variable) > bound {
                state.profile.subresultant_bound_violations += 1;
            }
        }
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{fields::Zp13, Monomial};

    // Coefficient degree excludes the main variable and sums other exponents without u32 overflow.
    #[test]
    fn coefficient_degree_is_a_wide_sum() {
        let polynomial = MultivariatePolynomial::<3, Zp13>::new(&[
            (Monomial::new(&[u32::MAX, u32::MAX, 1]), Zp13::new(1)),
            (Monomial::new(&[0, 0, 2]), Zp13::new(1)),
        ]);
        let (_, stats) = measure(|| observe(&polynomial, 2, Phase::Prs));
        assert_eq!(stats.prs_entries.max_terms, 2);
        assert_eq!(
            stats.prs_entries.max_coefficient_degree,
            2 * u64::from(u32::MAX)
        );
    }

    // Each scaled subresultant entry is checked against its own call's determinant degree bound.
    #[test]
    fn local_bounds_detect_an_excess() {
        type P = MultivariatePolynomial<2, Zp13>;
        let a = P::parse("y^2+x^3", ["x", "y"]).unwrap();
        let b = P::parse("y+x", ["x", "y"]).unwrap();
        let invalid = P::parse("x^10", ["x", "y"]).unwrap();
        let (_, stats) = measure(|| {
            let limit = bound(&a, &b, 1);
            assert_eq!(limit, Some(9));
            check_bound(&a, 1, limit);
            check_bound(&invalid, 1, limit);
        });
        assert_eq!(stats.max_subresultant_degree_bound, 9);
        assert_eq!(stats.subresultant_bound_violations, 1);
    }
}
