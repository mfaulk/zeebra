//! Using a Hilbert prediction to decide how many pairs a degree is worth, without betting the
//! answer on it.
//!
//! M22-C. The prediction is the one M22-B measured: for a sequence of forms of degrees `d_i` in `n`
//! variables, the positive truncation of `Π(1 − z^{d_i}) / (1 − z)^n` predicts `H(d)`, and
//! `dim I_d = dim R_d − H(d)` bounds how many independent degree-`d` relations exist at all. If the
//! basis in hand already accounts for `dim L_d` of them, then at most
//!
//! ```text
//! N_d = predicted dim I_d − dim L_d
//! ```
//!
//! new leading monomials can appear at degree `d`. That is Sakata–Takagi's `SelectPairLimited`
//! quantity, and on Fukuoka type III `n = 10`'s top forms it is 20, 65, 20 at degrees 2, 3, 4 —
//! exactly the measured minimal-generator counts.
//!
//! # The two halves are not the same kind of claim
//!
//! `dim L_d` is **exact**: it is the Hilbert function of the current leading-term ideal, computed by
//! [`HilbertSeries`]'s closed-form recursion from the
//! monomials in hand. `predicted dim I_d` is a **prediction**, and M22-B measured it exact on
//! random and genuine overdetermined MQ systems and wrong on every structured one — in the
//! dangerous direction on the inhomogeneous ones. So `N_d` inherits the prediction's error, and no
//! completeness claim may rest on it.
//!
//! # How completeness is preserved
//!
//! Neither mode discards a pair:
//!
//! - [`HilbertSelection::CertifiedLimited`] caps the *batch*. The pairs it does not take stay
//!   **pending**, and since the lcm degree is primary under every schedule they are the next thing
//!   selected. A wrong `N_d` therefore costs batches, never correctness, and the algorithm is as
//!   complete as it was with a fixed cap — which is what M22-A's measurements were taken with.
//! - [`HilbertSelection::Deferred`] moves the rest of the degree out of the pending set and
//!   proceeds to the next degree. Those pairs are **promoted back** before the computation can end
//!   ([`PairQueue::promote_deferred`](crate::grobner::PairQueue::promote_deferred)), they stay
//!   visible to Gebauer–Möller while deferred, and they are not recorded as processed, so the chain
//!   criterion cannot use one as a witness. It is a decision about *when*, not *whether*.
//!
//! So this module does not need certification to be correct. Certification is available anyway —
//! see [`super::certify`] — because the plan's §8.3 asks for the result to be established
//! independently of the strategy having run, and because reporting its cost is the only way to
//! answer §8.5's question honestly.

use crate::{
    grobner::hilbert::{monomials_of_degree, HilbertError, HilbertSeries, SemiregularSeries},
    FiniteField, Monomial, MultivariatePolynomial,
};

/// How a Hilbert prediction may influence pair selection.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum HilbertSelection {
    /// No prediction is computed. The baseline.
    #[default]
    Off,

    /// Compute the prediction and record how it compared, changing nothing about the computation.
    ///
    /// The diagnostic mode, and the one that makes "would this have helped?" answerable on an
    /// instance without risking the answer on it. A run under `Observe` is bit-identical to one
    /// under [`HilbertSelection::Off`]; only
    /// [`HilbertCounts`](super::statistics::HilbertCounts) differs.
    Observe,

    /// Cap each batch at `N_d + slack` pairs; the rest stay pending.
    ///
    /// Complete by construction — see the module docs. `slack` is the allowance the literature
    /// writes `e`, for dependencies and unexpected zero reductions; its published values are not
    /// assumed to transfer, which is why it is a parameter and why `examples/hilbert_driven.rs`
    /// sweeps it.
    CertifiedLimited { slack: usize },

    /// As [`HilbertSelection::CertifiedLimited`], but move the rest of the degree aside and proceed.
    ///
    /// The aggressive form, and the only one whose *order of work* differs from a plain cap: once a
    /// degree has yielded its predicted quota, its remaining pairs are deferred and the computation
    /// goes to the next degree. They are promoted back before the end, so this is still complete —
    /// what it buys is that by the time they are processed the basis is larger, so more of them are
    /// eliminated by a criterion and the rest reduce against more reducers.
    Deferred { slack: usize },
}

impl HilbertSelection {
    /// Every mode, for an ablation that should not need editing when one is added.
    pub const ALL: [Self; 4] = [
        Self::Off,
        Self::Observe,
        Self::CertifiedLimited { slack: 0 },
        Self::Deferred { slack: 0 },
    ];

    /// A short name, for a table column.
    pub fn name(&self) -> String {
        match self {
            Self::Off => "off".to_string(),
            Self::Observe => "observe".to_string(),
            Self::CertifiedLimited { slack } => format!("limited+{}", slack),
            Self::Deferred { slack } => format!("deferred+{}", slack),
        }
    }

    /// True if the mode computes a prediction at all.
    pub fn is_active(&self) -> bool {
        !matches!(self, Self::Off)
    }

    /// True if the mode caps the batch.
    pub fn limits(&self) -> bool {
        matches!(self, Self::CertifiedLimited { .. } | Self::Deferred { .. })
    }

    /// True if the mode defers the remainder of a degree.
    pub fn defers(&self) -> bool {
        matches!(self, Self::Deferred { .. })
    }

    /// The allowance, or zero for a mode that does not limit.
    pub fn slack(&self) -> usize {
        match self {
            Self::CertifiedLimited { slack } | Self::Deferred { slack } => *slack,
            _ => 0,
        }
    }
}

/// The degrees to expand the prediction over.
///
/// Generous: the model's degree of regularity for `m` quadratics in `n` variables is well under `n`
/// for the overdetermined case and can approach `n` for a square one, and a range that stops short
/// simply leaves `H` positive, which makes `N_d` large and the cap inert. Erring long costs a few
/// binomial coefficients once.
fn expansion_bound(variables: usize, degrees: &[u64]) -> u64 {
    let widest = degrees.iter().copied().max().unwrap_or(1);
    (variables as u64 + 1) * widest + 2
}

/// A Hilbert prediction for one system, and the exact bookkeeping to turn it into a per-degree cap.
#[derive(Clone, Debug)]
pub struct SelectionLimits {
    /// The predicted Hilbert function of the top-form system.
    predicted: SemiregularSeries,

    /// The number of variables.
    variables: usize,

    /// The allowance added to every cap.
    slack: usize,
}

impl SelectionLimits {
    /// The prediction for the generators of `system`, by their top degrees.
    ///
    /// The model is a statement about a homogeneous sequence, and these generators need not be
    /// homogeneous — so what this predicts is the Hilbert function of the system of **top forms**,
    /// and that is a different ideal. M22-B measured where the substitution is harmless (random and
    /// genuine overdetermined MQ) and where it is not (every structured system, and in the unsafe
    /// direction on the inhomogeneous ones). Nothing here relies on it being right.
    ///
    /// # Errors
    /// [`HilbertError::Overflow`] if a predicted coefficient leaves `i128`.
    pub fn new<const N: usize, F: FiniteField>(
        system: &[MultivariatePolynomial<N, F>],
        slack: usize,
    ) -> Result<Self, HilbertError> {
        let degrees: Vec<u64> = system
            .iter()
            .filter(|p| !p.is_zero())
            .map(|p| p.degree())
            .collect();
        let bound = expansion_bound(N, &degrees);
        Ok(Self {
            predicted: SemiregularSeries::new(N, &degrees, bound)?,
            variables: N,
            slack,
        })
    }

    /// The model's degree of regularity, if the expansion reached it.
    pub fn degree_of_regularity(&self) -> Option<u64> {
        self.predicted.degree_of_regularity()
    }

    /// The predicted `dim I_degree`.
    ///
    /// # Errors
    /// [`HilbertError::Overflow`].
    pub fn predicted_ideal_dimension(&self, degree: u64) -> Result<i128, HilbertError> {
        Ok(monomials_of_degree(self.variables, degree)? - self.predicted.function(degree))
    }

    /// `N_degree + slack`, clamped to at least one, or `None` if the exact half could not be
    /// computed.
    ///
    /// `None` means **no limit**, which is the safe reading of a failed computation: a cap that
    /// cannot be computed must not be guessed at. `leads` are the leading monomials of the basis in
    /// hand, and `dim L_degree` is computed from them exactly.
    ///
    /// Clamped to one because a batch of no pairs makes no progress — see
    /// [`PairQueue::select_batch`](crate::grobner::PairQueue::select_batch) — so a predicted quota
    /// of zero becomes "take one and find out", which is the conservative action and not a
    /// violation of the prediction.
    pub fn cap<const N: usize>(&self, degree: u64, leads: &[Monomial<N>]) -> Option<usize> {
        let predicted = self.predicted_ideal_dimension(degree).ok()?;
        let known = HilbertSeries::of_monomial_ideal(leads)
            .ok()?
            .ideal_dimension(degree)
            .ok()?;
        let available = (predicted - known).max(0) as u128;
        let cap = available.saturating_add(self.slack as u128);
        Some(cap.clamp(1, usize::MAX as u128) as usize)
    }

    /// The predicted new leading monomials at `degree`, without the slack or the clamp.
    ///
    /// What a report compares against the observed count. `None` as [`Self::cap`].
    pub fn predicted_new_elements<const N: usize>(
        &self,
        degree: u64,
        leads: &[Monomial<N>],
    ) -> Option<i128> {
        let predicted = self.predicted_ideal_dimension(degree).ok()?;
        let known = HilbertSeries::of_monomial_ideal(leads)
            .ok()?
            .ideal_dimension(degree)
            .ok()?;
        Some((predicted - known).max(0))
    }
}

#[cfg(test)]
mod tests {
    use super::{HilbertSelection, SelectionLimits};
    use crate::{
        fields::Zp2147483647,
        grobner::{benchmark_systems::katsura, f4},
        poly::MonomialOrder,
        FiniteField, Monomial, MultivariatePolynomial,
    };

    type F = Zp2147483647;
    const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

    /// The modes report what they are, and the default is off.
    #[test]
    fn test_the_modes() {
        assert_eq!(HilbertSelection::default(), HilbertSelection::Off);
        assert!(!HilbertSelection::Off.is_active());
        assert!(HilbertSelection::Observe.is_active());
        assert!(!HilbertSelection::Observe.limits());
        assert!(HilbertSelection::CertifiedLimited { slack: 3 }.limits());
        assert!(!HilbertSelection::CertifiedLimited { slack: 3 }.defers());
        assert!(HilbertSelection::Deferred { slack: 1 }.defers());
        assert!(HilbertSelection::Deferred { slack: 1 }.limits());
        assert_eq!(HilbertSelection::CertifiedLimited { slack: 3 }.slack(), 3);
        assert_eq!(HilbertSelection::Off.slack(), 0);
        assert_eq!(HilbertSelection::ALL.len(), 4);
        assert_eq!(HilbertSelection::Deferred { slack: 2 }.name(), "deferred+2");
    }

    /// With nothing known, the cap at a degree is the whole predicted ideal dimension.
    #[test]
    fn test_the_cap_with_an_empty_basis() {
        // Twenty quadratics in ten variables: the Fukuoka type III shape.
        let system: Vec<MultivariatePolynomial<10, F>> = (0..20)
            .map(|i| {
                let mut exponents = [0u32; 10];
                exponents[i % 10] = 1;
                exponents[(i + 1) % 10] += 1;
                MultivariatePolynomial::new(&[(Monomial::new(&exponents), F::new(1))])
            })
            .collect();
        let limits = SelectionLimits::new(&system, 0).expect("in range");

        // `d_reg` for 20 quadratics in 10 variables, which M22-B measured at 4.
        assert_eq!(limits.degree_of_regularity(), Some(4));

        // dim R_2 = 55 and the model leaves 35, so twenty relations are available at degree two.
        assert_eq!(limits.predicted_ideal_dimension(2).unwrap(), 20);
        let empty: Vec<Monomial<10>> = Vec::new();
        assert_eq!(limits.cap(2, &empty), Some(20));
        assert_eq!(limits.predicted_new_elements(2, &empty), Some(20));
    }

    /// The quota falls as the basis grows, and reaches zero once the degree is accounted for.
    ///
    /// The exact half of `N_d` is the Hilbert function of the leading-term ideal in hand, so the
    /// quota is a *remaining* count rather than a total — which is what makes it usable as a cap
    /// part-way through a degree. Driven here with real leading monomials from a real basis.
    #[test]
    fn test_the_quota_falls_as_the_basis_grows() {
        let system: Vec<MultivariatePolynomial<5, F>> = katsura::<5, F>();
        let limits = SelectionLimits::new(&system, 0).expect("in range");
        let basis = f4(&system, GREVLEX).expect("within limits");
        let leads: Vec<Monomial<5>> = basis.iter().map(|p| p.leading_monomial(GREVLEX)).collect();

        for degree in 1..=6u64 {
            let empty: Vec<Monomial<5>> = Vec::new();
            let before = limits
                .predicted_new_elements(degree, &empty)
                .expect("computable");
            let after = limits
                .predicted_new_elements(degree, &leads)
                .expect("computable");
            assert!(
                after <= before,
                "degree {}: the quota rose from {} to {} as the basis grew",
                degree,
                before,
                after
            );
        }

        // With the finished basis in hand nothing is left to find at any degree.
        for degree in 1..=6u64 {
            assert_eq!(
                limits.predicted_new_elements(degree, &leads),
                Some(0),
                "degree {}",
                degree
            );
        }
    }

    /// The slack is added to the quota.
    #[test]
    fn test_the_slack_is_added() {
        let system: Vec<MultivariatePolynomial<5, F>> = katsura::<5, F>();
        let empty: Vec<Monomial<5>> = Vec::new();
        let none = SelectionLimits::new(&system, 0).expect("in range");
        let some = SelectionLimits::new(&system, 7).expect("in range");
        let (a, b) = (none.cap(3, &empty).unwrap(), some.cap(3, &empty).unwrap());
        assert_eq!(b, a + 7);
    }

    /// Above the degree of regularity the quota is zero, so the cap clamps to one.
    ///
    /// The prediction says nothing is left there. Clamping rather than returning zero is what keeps
    /// a batch of no pairs — which makes no progress — from being requested, and it is the
    /// conservative action: take one pair and find out.
    #[test]
    fn test_above_the_degree_of_regularity() {
        let system: Vec<MultivariatePolynomial<5, F>> = katsura::<5, F>();
        let limits = SelectionLimits::new(&system, 0).expect("in range");
        let dreg = limits.degree_of_regularity().expect("katsura-5 reaches it");

        // The leading-term ideal of the finished basis contains everything at and above d_reg, so
        // nothing is available there.
        let basis = f4(&system, GREVLEX).expect("within limits");
        let leads: Vec<Monomial<5>> = basis.iter().map(|p| p.leading_monomial(GREVLEX)).collect();
        assert_eq!(limits.predicted_new_elements(dreg + 1, &leads), Some(0));
        assert_eq!(limits.cap(dreg + 1, &leads), Some(1));
    }
}
