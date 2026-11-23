//! Hilbert-count certified zero skipping on conventional F4 (#1080, Design D).
//!
//! `C(e)` counts the degree-`e` monomials outside the leading-monomial ideal of the basis in hand,
//! and `S = Π(1 − t^{d_i})/(1 − t)^n`. `docs/research/hilbert-count-acceptance.md` proves that if
//! `C(e) = S(e)` at every degree up to `d`, or the count reaches zero, the leading monomials are
//! exactly right through `d` (Theorem 1, homogeneous input), and exactly those of the top-form
//! ideal under the no-fall witness (Theorem 3, affine input). At a certified degree every
//! remaining pair reduces to zero, so the route drops them instead of reducing them.
//!
//! A drop is final on any input, affine of any shape included (Theorem 4): every dropped pair's
//! S-polynomial has a standard representation over the basis in hand. A zero count is final only
//! on homogeneous or square input (Theorem 3). Affine input that is not square can still fall into
//! a degree the count has closed, so there a zero count turns the route off instead.
//!
//! The route turns off for the rest of the run at the first degree fall, the first degree that
//! closes without matching `S`, or the first series it cannot compute. The run is then plain F4,
//! and the pairs already dropped stay dropped.

use crate::{
    grobner::hilbert::{is_homogeneous, HilbertSeries},
    FiniteField, Monomial, MonomialOrder, MultivariatePolynomial,
};

/// What became of the count route over one run.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum CountRoute {
    /// Not requested: the selection mode is not [`HilbertSelection::CertifiedZeros`].
    ///
    /// [`HilbertSelection::CertifiedZeros`]: super::HilbertSelection::CertifiedZeros
    #[default]
    Unused,

    /// The input failed the applicability predicate, so the run was plain F4 throughout.
    Refused(CountRefusal),

    /// The route stayed on until the queue emptied, without a zero count.
    ///
    /// Every dropped pair was a certified zero when it was dropped, so the output satisfies
    /// Buchberger's criterion.
    Open,

    /// The count reached zero at `degree`, which ended the run with every pair left discarded.
    Completed { degree: u64 },

    /// The route turned off at `degree`, and the rest of the run was plain F4.
    Disabled { degree: u64, reason: CountDisabled },
}

/// Why the input was refused before the run began.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CountRefusal {
    /// The monomial order is not degree compatible (only grlex and grevlex are accepted).
    Order,

    /// A generator is a nonzero constant.
    ConstantGenerator,

    /// `S` overflowed `i128`.
    Series,
}

/// Why a running route turned off.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CountDisabled {
    /// A kept row fell below its batch's degree, or the schedule went down a degree.
    Fell,

    /// A degree closed with `C ≠ S`: the input is not regular there.
    Mismatch,

    /// Affine input that is not square reached a zero count, which does not make its basis final:
    /// an element of `I` can still fall into a degree the count has closed.
    ZeroNotFinal,

    /// The leading-monomial series could not be computed within its budget.
    Series,
}

/// What the main loop must do after consulting the route.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Step {
    /// Carry on as plain F4 would.
    Continue,
    /// The degree is certified: drop its remaining pairs.
    DropDegree(u64),
    /// The count reached zero: drop every pair and end the run.
    Complete,
    /// The route has just turned off.
    Disabled,
}

/// The route's state over one run.
#[derive(Clone, Debug)]
pub(crate) struct ZeroSkip {
    series: HilbertSeries,
    /// Whether a zero count makes the basis final: homogeneous or square input.
    zero_is_final: bool,
    /// Every degree up to and including this one is certified.
    certified_through: Option<u64>,
    /// The degree being processed and its current count `C`.
    open: Option<(u64, i128)>,
    outcome: CountRoute,
    degrees_certified: usize,
}

impl ZeroSkip {
    /// The route for `generators` under `order`, or why it does not apply.
    pub(crate) fn new<const N: usize, F: FiniteField>(
        generators: &[MultivariatePolynomial<N, F>],
        order: MonomialOrder,
    ) -> Result<Self, CountRefusal> {
        if !matches!(
            order,
            MonomialOrder::GradedLexicographic | MonomialOrder::GradedReverseLexicographic
        ) {
            return Err(CountRefusal::Order);
        }
        let degrees: Vec<u64> = generators
            .iter()
            .filter(|p| !p.is_zero())
            .map(|p| p.degree())
            .collect();
        if degrees.contains(&0) {
            return Err(CountRefusal::ConstantGenerator);
        }
        let zero_is_final = degrees.len() == N || is_homogeneous(generators);
        let series =
            HilbertSeries::of_regular_sequence(N, &degrees).map_err(|_| CountRefusal::Series)?;
        Ok(Self {
            series,
            zero_is_final,
            certified_through: None,
            open: None,
            outcome: CountRoute::Open,
            degrees_certified: 0,
        })
    }

    pub(crate) fn is_live(&self) -> bool {
        self.outcome == CountRoute::Open
    }

    pub(crate) fn outcome(&self) -> CountRoute {
        self.outcome
    }

    pub(crate) fn degrees_certified(&self) -> usize {
        self.degrees_certified
    }

    /// The cap on the next sub-batch: the leading monomials the open degree still has to yield,
    /// plus `slack`, and at least one. `None` once the route is off.
    pub(crate) fn cap(&self, slack: usize) -> Option<usize> {
        if !self.is_live() {
            return None;
        }
        let (degree, count) = self.open?;
        let target = self.target(degree)?.max(0);
        let needed = (count - target).max(0) as u128;
        Some(
            needed
                .saturating_add(slack as u128)
                .clamp(1, usize::MAX as u128) as usize,
        )
    }

    /// Called before a batch is selected at `degree`, with the basis's leading monomials.
    pub(crate) fn open<const N: usize>(&mut self, degree: u64, leads: &[Monomial<N>]) -> Step {
        if !self.is_live() {
            return Step::Continue;
        }
        if let Some((open, _)) = self.open {
            if degree == open {
                return Step::Continue;
            }
            if degree < open {
                return self.disable(degree, CountDisabled::Fell);
            }
            if self.certified_through != Some(open) {
                return self.disable(open, CountDisabled::Mismatch);
            }
        }

        let Ok(counts) = HilbertSeries::of_monomial_ideal(leads) else {
            return self.disable(degree, CountDisabled::Series);
        };
        let first = self.certified_through.map_or(0, |d| d + 1);
        for e in first..degree {
            let Ok(count) = counts.function(e) else {
                return self.disable(e, CountDisabled::Series);
            };
            match self.verdict(e, count) {
                Verdict::Certified => self.certify(e),
                Verdict::Zero => return self.complete(e),
                Verdict::Pending | Verdict::Mismatch => {
                    return self.disable(e, CountDisabled::Mismatch)
                }
                Verdict::Unknown => return self.disable(e, CountDisabled::Series),
            }
        }
        let Ok(count) = counts.function(degree) else {
            return self.disable(degree, CountDisabled::Series);
        };
        self.open = Some((degree, count));
        self.check(degree)
    }

    /// Called after a batch at `degree` is reduced, with how many rows it kept and whether any of
    /// them fell below `degree`.
    pub(crate) fn record(&mut self, degree: u64, kept: usize, fell: bool) -> Step {
        if !self.is_live() {
            return Step::Continue;
        }
        if fell {
            return self.disable(degree, CountDisabled::Fell);
        }
        match self.open {
            Some((open, count)) if open == degree => {
                // A kept row's leading monomial is new and of degree `degree`, so it removes
                // exactly one standard monomial there.
                self.open = Some((open, count - kept as i128));
                self.check(degree)
            }
            _ => self.disable(degree, CountDisabled::Fell),
        }
    }

    fn check(&mut self, degree: u64) -> Step {
        let Some((_, count)) = self.open else {
            return Step::Continue;
        };
        match self.verdict(degree, count) {
            Verdict::Certified => {
                self.certify(degree);
                Step::DropDegree(degree)
            }
            Verdict::Zero => self.complete(degree),
            Verdict::Pending => Step::Continue,
            Verdict::Mismatch => self.disable(degree, CountDisabled::Mismatch),
            Verdict::Unknown => self.disable(degree, CountDisabled::Series),
        }
    }

    fn target(&self, degree: u64) -> Option<i128> {
        self.series.function(degree).ok()
    }

    fn verdict(&self, degree: u64, count: i128) -> Verdict {
        let Some(target) = self.target(degree) else {
            return Verdict::Unknown;
        };
        if count == 0 {
            Verdict::Zero
        } else if count == target {
            Verdict::Certified
        } else if count > target {
            Verdict::Pending
        } else {
            // Below S: impossible for homogeneous or no-fall input (Lemma 2), so something the
            // proof assumes does not hold.
            Verdict::Mismatch
        }
    }

    fn certify(&mut self, degree: u64) {
        if self.certified_through != Some(degree) {
            self.certified_through = Some(degree);
            self.degrees_certified += 1;
        }
    }

    fn complete(&mut self, degree: u64) -> Step {
        if !self.zero_is_final {
            return self.disable(degree, CountDisabled::ZeroNotFinal);
        }
        self.outcome = CountRoute::Completed { degree };
        Step::Complete
    }

    fn disable(&mut self, degree: u64, reason: CountDisabled) -> Step {
        self.outcome = CountRoute::Disabled { degree, reason };
        Step::Disabled
    }
}

enum Verdict {
    Certified,
    Zero,
    Pending,
    Mismatch,
    Unknown,
}

#[cfg(test)]
mod tests {
    use super::{CountDisabled, CountRefusal, CountRoute, Step, ZeroSkip};
    use crate::{
        fields::Zp32003, grobner::benchmark_systems::katsura, FiniteField, Monomial, MonomialOrder,
        MultivariatePolynomial,
    };

    type F = Zp32003;
    const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

    fn poly<const N: usize>(terms: &[([u32; N], u64)]) -> MultivariatePolynomial<N, F> {
        let terms: Vec<(Monomial<N>, F)> = terms
            .iter()
            .map(|(e, c)| (Monomial::new(e), F::new(*c)))
            .collect();
        MultivariatePolynomial::new(&terms)
    }

    #[test]
    fn test_the_predicate() {
        let squares = vec![poly::<2>(&[([2, 0], 1)]), poly::<2>(&[([0, 2], 1)])];
        assert!(ZeroSkip::new(&squares, GREVLEX).is_ok());
        assert!(ZeroSkip::new(&squares, MonomialOrder::GradedLexicographic).is_ok());
        assert_eq!(
            ZeroSkip::new(&squares, MonomialOrder::Lexicographic).err(),
            Some(CountRefusal::Order)
        );
        let constant = vec![poly::<2>(&[([2, 0], 1)]), poly::<2>(&[([0, 0], 3)])];
        assert_eq!(
            ZeroSkip::new(&constant, GREVLEX).err(),
            Some(CountRefusal::ConstantGenerator)
        );
        // Affine input of any shape is accepted, and so is homogeneous input.
        let affine = vec![poly::<2>(&[([2, 0], 1), ([0, 1], 1)])];
        assert!(ZeroSkip::new(&affine, GREVLEX).is_ok());
        assert!(ZeroSkip::new(&squares[..1], GREVLEX).is_ok());
        assert!(ZeroSkip::new(&katsura::<5, F>(), GREVLEX).is_ok());
    }

    /// `(x, y, x² + 1)` has `S = 1 − t²`, so finding `x` and `y` makes the count zero at degree 1.
    /// The pair `(x, x² + 1)` still falls to `1` at degree 2, so on affine input that is not square
    /// a zero count turns the route off instead of ending the run (note §4.4.2).
    #[test]
    fn test_a_zero_count_ends_only_a_square_or_homogeneous_run() {
        let (x, y) = (Monomial::<2>::new(&[1, 0]), Monomial::<2>::new(&[0, 1]));
        let overdetermined = vec![
            poly::<2>(&[([1, 0], 1)]),
            poly::<2>(&[([0, 1], 1)]),
            poly::<2>(&[([2, 0], 1), ([0, 0], 1)]),
        ];
        let mut route = ZeroSkip::new(&overdetermined, GREVLEX).unwrap();
        assert_eq!(route.open::<2>(1, &[]), Step::Continue);
        assert_eq!(route.record(1, 2, false), Step::Disabled);
        assert_eq!(
            route.outcome(),
            CountRoute::Disabled {
                degree: 1,
                reason: CountDisabled::ZeroNotFinal
            }
        );
        // The same count found as a later degree opens.
        let mut route = ZeroSkip::new(&overdetermined, GREVLEX).unwrap();
        assert_eq!(route.open(2, &[x, y]), Step::Disabled);

        // Square affine input completes, by Theorem 3.
        let square = vec![
            poly::<2>(&[([1, 0], 1), ([0, 0], 1)]),
            poly::<2>(&[([0, 1], 1)]),
        ];
        let mut route = ZeroSkip::new(&square, GREVLEX).unwrap();
        assert_eq!(route.open(2, &[x, y]), Step::Complete);
    }

    fn squares() -> Vec<MultivariatePolynomial<3, F>> {
        vec![
            poly::<3>(&[([2, 0, 0], 1)]),
            poly::<3>(&[([0, 2, 0], 1)]),
            poly::<3>(&[([0, 0, 2], 1)]),
        ]
    }

    fn m(e: [u32; 3]) -> Monomial<3> {
        Monomial::new(&e)
    }

    /// `(x², y², z²)` has `S = 1, 3, 3, 1, 0`. Driven by hand, with `z²` found by a batch.
    #[test]
    fn test_the_state_machine_certifies_and_completes() {
        let (x2, y2, z2) = (m([2, 0, 0]), m([0, 2, 0]), m([0, 0, 2]));
        let mut route = ZeroSkip::new(&squares(), GREVLEX).unwrap();
        // C(2) = 6 − 2 = 4 > 3: one leading monomial still to find.
        assert_eq!(route.open(2, &[x2, y2]), Step::Continue);
        assert_eq!(route.cap(0), Some(1));
        assert_eq!(route.cap(5), Some(6));
        assert_eq!(route.record(2, 1, false), Step::DropDegree(2));
        assert_eq!(route.degrees_certified(), 3);
        // C(3) = 1 (only xyz is standard) = S(3), so degree 3 is certified as it opens.
        assert_eq!(route.open(3, &[x2, y2, z2]), Step::DropDegree(3));
        assert_eq!(route.open(4, &[x2, y2, z2]), Step::Complete);
        assert_eq!(route.outcome(), CountRoute::Completed { degree: 4 });
        assert_eq!(route.cap(0), None);

        // A zero below the opening degree completes too.
        let linear = [m([1, 0, 0]), m([0, 1, 0]), m([0, 0, 1])];
        let mut route = ZeroSkip::new(&squares(), GREVLEX).unwrap();
        assert_eq!(route.open(2, &linear), Step::Complete);
        assert_eq!(route.outcome(), CountRoute::Completed { degree: 1 });
    }

    #[test]
    fn test_the_route_turns_off() {
        let (x2, y2, z2, xy) = (m([2, 0, 0]), m([0, 2, 0]), m([0, 0, 2]), m([1, 1, 0]));
        let disabled = |degree, reason| CountRoute::Disabled { degree, reason };

        // A fall, after which the route stays off.
        let mut route = ZeroSkip::new(&squares(), GREVLEX).unwrap();
        assert_eq!(route.open(2, &[x2, y2]), Step::Continue);
        assert_eq!(route.record(2, 1, true), Step::Disabled);
        assert_eq!(route.outcome(), disabled(2, CountDisabled::Fell));
        assert_eq!(route.open(3, &[x2, y2, z2]), Step::Continue);
        assert_eq!(route.cap(0), None);

        // A degree that closes short of S.
        let mut route = ZeroSkip::new(&squares(), GREVLEX).unwrap();
        assert_eq!(route.open(2, &[x2, y2]), Step::Continue);
        assert_eq!(route.open(3, &[x2, y2]), Step::Disabled);
        assert_eq!(route.outcome(), disabled(2, CountDisabled::Mismatch));

        // A count below S, which no input the proof covers can produce.
        let mut route = ZeroSkip::new(&squares(), GREVLEX).unwrap();
        assert_eq!(route.open(2, &[x2, y2, z2, xy]), Step::Disabled);
        let mut route = ZeroSkip::new(&squares(), GREVLEX).unwrap();
        assert_eq!(route.open(2, &[x2, y2]), Step::Continue);
        assert_eq!(route.record(2, 2, false), Step::Disabled);
        assert_eq!(route.outcome(), disabled(2, CountDisabled::Mismatch));

        // The schedule going down a degree.
        let mut route = ZeroSkip::new(&squares(), GREVLEX).unwrap();
        assert_eq!(route.open(3, &[x2, y2, z2]), Step::DropDegree(3));
        assert_eq!(route.open(2, &[x2, y2, z2]), Step::Disabled);
        assert_eq!(route.outcome(), disabled(2, CountDisabled::Fell));
    }
}
