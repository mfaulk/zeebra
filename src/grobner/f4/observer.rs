//! Watching an F4 computation go past, so that a stage can be measured on real input.
//!
//! Every optimization in this milestone starts with a measurement, and the input to that
//! measurement is the batches F4 actually builds — not a synthetic approximation of them. An F4
//! batch is determined by two things: the basis at the time, and the pairs selected. Hand both to
//! an observer and a caller can replay any stage in isolation, benchmark it, or count what it did,
//! without reimplementing the main loop.
//!
//! Reimplementing the main loop is the alternative this exists to prevent. Four workstreams each
//! writing their own batch-generating driver would give four slightly different sequences of
//! batches and four incomparable sets of numbers.
//!
//! The observation is free when nobody is observing: [`f4_observed`](super::f4_observed) is
//! generic over the observer, and [`Ignore`]'s empty method inlines away.

use crate::{
    grobner::{
        f4::{
            options::{F4Error, F4Options},
            statistics::F4Statistics,
            symbolic::MonicBasis,
        },
        pairs::CriticalPair,
    },
    poly::MonomialOrder,
    FiniteField, MultivariatePolynomial,
};

/// Notified of each batch an F4 computation reduces.
pub trait BatchObserver<const N: usize, F: FiniteField> {
    /// `basis` is the basis as it stands, and `pairs` the batch about to be reduced — after pair
    /// criteria have discarded what they can, so these are the pairs that reach a matrix.
    fn batch(&mut self, basis: &MonicBasis<N, F>, pairs: &[CriticalPair<N>]);
}

/// An observer that does nothing, for the ordinary path.
#[derive(Clone, Copy, Debug, Default)]
pub struct Ignore;

impl<const N: usize, F: FiniteField> BatchObserver<N, F> for Ignore {
    #[inline]
    fn batch(&mut self, _basis: &MonicBasis<N, F>, _pairs: &[CriticalPair<N>]) {}
}

/// One batch as F4 encountered it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TracedBatch<const N: usize, F: FiniteField> {
    /// The basis the pairs refer to by index, made monic under the order in force.
    pub basis: MonicBasis<N, F>,

    /// The pairs the batch reduced.
    pub pairs: Vec<CriticalPair<N>>,
}

/// Every batch of a computation, kept for replay.
///
/// Memory is the cost: a snapshot holds the whole basis, so a computation with a large basis and
/// many batches holds a lot. That is acceptable for a measurement tool and is why nothing in the
/// shipping path collects one.
#[derive(Clone, Debug, Default)]
pub struct BatchTrace<const N: usize, F: FiniteField> {
    batches: Vec<TracedBatch<N, F>>,
}

impl<const N: usize, F: FiniteField> BatchTrace<N, F> {
    pub fn new() -> Self {
        Self {
            batches: Vec::new(),
        }
    }

    pub fn batches(&self) -> &[TracedBatch<N, F>] {
        &self.batches
    }

    pub fn len(&self) -> usize {
        self.batches.len()
    }

    pub fn is_empty(&self) -> bool {
        self.batches.is_empty()
    }

    /// The largest batch, by the number of pairs it reduced.
    ///
    /// The one measurement that wants a single batch usually wants this one: it is where the
    /// matrix is largest and where a per-batch cost is worth attributing.
    pub fn largest(&self) -> Option<&TracedBatch<N, F>> {
        self.batches.iter().max_by_key(|batch| batch.pairs.len())
    }
}

impl<const N: usize, F: FiniteField> BatchObserver<N, F> for BatchTrace<N, F> {
    fn batch(&mut self, basis: &MonicBasis<N, F>, pairs: &[CriticalPair<N>]) {
        self.batches.push(TracedBatch {
            basis: basis.clone(),
            pairs: pairs.to_vec(),
        });
    }
}

/// Run F4 and collect every batch it reduced, along with the basis and the statistics.
///
/// The basis returned is exactly what [`f4_with_options`](super::f4_with_options) returns for the
/// same input: observing changes nothing, which is asserted rather than assumed.
///
/// # Errors
/// As [`f4_with_options`](super::f4_with_options).
#[allow(clippy::type_complexity)]
pub fn trace_batches<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    options: &F4Options,
) -> Result<
    (
        Vec<MultivariatePolynomial<N, F>>,
        F4Statistics,
        BatchTrace<N, F>,
    ),
    F4Error,
> {
    let mut trace = BatchTrace::new();
    let (basis, statistics) = super::f4_observed(generators, order, options, &mut trace)?;
    Ok((basis, statistics, trace))
}

#[cfg(test)]
mod tests {
    use super::{trace_batches, BatchTrace};
    use crate::{
        fields::Zp2147483647,
        grobner::{
            benchmark_systems::{cyclic, katsura},
            f4::{f4_with_options, options::F4Options, reduce_batch},
        },
        poly::MonomialOrder,
        MultivariatePolynomial,
    };

    type F = Zp2147483647;

    const ALL_ORDERS: [MonomialOrder; 3] = [
        MonomialOrder::Lexicographic,
        MonomialOrder::GradedLexicographic,
        MonomialOrder::GradedReverseLexicographic,
    ];

    /// Observing a computation does not change it: same basis, same statistics.
    #[test]
    fn test_tracing_does_not_change_the_result() {
        for order in ALL_ORDERS {
            let options = F4Options::baseline();
            let system = katsura::<4, F>();

            let (plain, plain_statistics) =
                f4_with_options(&system, order, &options).expect("within limits");
            let (traced, traced_statistics, _) =
                trace_batches(&system, order, &options).expect("within limits");

            assert_eq!(plain, traced, "{}", order.name());
            assert_eq!(plain_statistics, traced_statistics, "{}", order.name());
        }
    }

    /// The trace holds one snapshot per matrix F4 built.
    #[test]
    fn test_the_trace_counts_the_batches() {
        for order in ALL_ORDERS {
            let (_, statistics, trace) =
                trace_batches(&katsura::<5, F>(), order, &F4Options::baseline())
                    .expect("within limits");
            assert_eq!(trace.len(), statistics.batches, "{}", order.name());
            assert!(!trace.is_empty(), "{}", order.name());
            assert_eq!(
                trace.largest().map(|batch| batch.pairs.len()),
                Some(statistics.max_pairs_per_batch),
                "{}",
                order.name()
            );
        }
    }

    /// A traced batch replays to the candidates the live run produced.
    ///
    /// This is the property the whole facility rests on: a snapshot is enough to reconstruct the
    /// batch, so a stage measured on a snapshot is a stage measured on real input.
    #[test]
    fn test_a_traced_batch_replays() {
        for order in ALL_ORDERS {
            let options = F4Options::baseline();
            let (_, _, trace) =
                trace_batches(&cyclic::<4, F>(), order, &options).expect("within limits");

            let mut total_candidates = 0;
            for batch in trace.batches() {
                let outcome = reduce_batch(&batch.basis, &batch.pairs, order, &options)
                    .expect("within limits");
                total_candidates += outcome.candidates.len();

                // Replaying twice gives the same thing, which is what makes a benchmark over a
                // replayed batch meaningful.
                let again = reduce_batch(&batch.basis, &batch.pairs, order, &options)
                    .expect("within limits");
                assert_eq!(outcome.candidates, again.candidates, "{}", order.name());
            }
            assert!(total_candidates > 0, "{}", order.name());
        }
    }

    /// An empty trace is the trace of a computation with nothing to do.
    #[test]
    fn test_an_empty_system_traces_nothing() {
        let empty: Vec<MultivariatePolynomial<3, F>> = Vec::new();
        let (basis, _, trace) =
            trace_batches(&empty, MonomialOrder::Lexicographic, &F4Options::baseline())
                .expect("within limits");
        assert!(basis.is_empty());
        assert!(trace.is_empty());
        assert_eq!(BatchTrace::<3, F>::new().largest(), None);
    }
}
