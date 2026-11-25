//! #1140: end a graded-lex run once its leads look complete, by handing the current elements to
//! conventional F4 rather than running the signature basis to completion.
//!
//! Soundness. Every element is a polynomial combination of the inputs (each row is a monomial
//! multiple of an input or an element), so for any subset `R` of them `<R ∪ F> = I`. Conventional
//! F4 returns the reduced Gröbner basis of the ideal its input generates, which is unique, so
//! `f4(R ∪ F)` is exactly what the full run, or `f4(F)`, returns. No signature invariant is
//! needed, and the result is correct whether or not the leads were complete. When they were, every
//! S-polynomial of `R` reduces to zero and F4 returns the interreduced `R`; the statistics record
//! whether its leads matched.
//!
//! When to hand off. The trigger decides cost only. An incomplete lead set leaves F4 real work, so
//! the handoff waits until a whole signature degree has added no new minimal lead; on eco-9 a
//! trigger of one quiet batch would have fired at every degree from 7. It also waits while fewer
//! entries are pending than there are minimal leads, where finishing the signature run is cheaper
//! than an F4 pass over the leads' pairs (eco-9: 13 pending against 119 leads).

use std::time::{Duration, Instant};

use super::{Engine, SigF4Error};
use crate::{
    grobner::f4::{f4_with_options, F4Options},
    poly::MonomialOrder,
    FiniteField, Monomial, MultivariatePolynomial,
};

pub(super) struct LeadIdealStop {
    enabled: bool,
    /// The signature degree being run, and the new-lead count before its first batch.
    degree: u64,
    degree_start: usize,
}

impl LeadIdealStop {
    pub(super) fn new(order: MonomialOrder, enabled: bool) -> Self {
        Self {
            enabled: enabled && order == MonomialOrder::GradedLexicographic,
            degree: 0,
            degree_start: 0,
        }
    }

    /// Before a batch of signature degree `degree`, with `leads` new minimal leads so far.
    pub(super) fn observe(&mut self, degree: u64, leads: usize) {
        if degree != self.degree {
            self.degree = degree;
            self.degree_start = leads;
        }
    }

    /// After a batch: its degree is finished (`next` is the queue's next degree) without a new
    /// minimal lead, and at least as many entries are pending as there are minimal leads.
    pub(super) fn due(&self, leads: usize, next: Option<u64>, pending: usize) -> bool {
        self.enabled
            && next.is_some_and(|d| d > self.degree)
            && leads == self.degree_start
            && pending >= leads
    }
}

impl<const N: usize, F: FiniteField> Engine<'_, N, F> {
    /// The reduced basis of the input ideal, by conventional F4 over the elements at minimal
    /// leads and the inputs.
    pub(super) fn hand_off(
        &mut self,
        generators: &[MultivariatePolynomial<N, F>],
        wall: Option<(Instant, Duration)>,
    ) -> Result<Vec<MultivariatePolynomial<N, F>>, SigF4Error> {
        let clock = Instant::now();
        let mut seed = self.minimal_elements();
        let mut leads: Vec<Monomial<N>> = seed
            .iter()
            .map(|p| p.leading_monomial(self.order))
            .collect();
        seed.extend(generators.iter().cloned());
        let options = F4Options {
            max_wall_time: wall.map(|(start, budget)| budget.saturating_sub(start.elapsed())),
            ..F4Options::default()
        };
        let result = f4_with_options(&seed, self.order, &options);
        self.stats.lead_ideal_stop = true;
        self.stats.lead_ideal_handoff = clock.elapsed();
        let (reduced, _) = result.map_err(SigF4Error::Budget)?;
        let mut kept: Vec<Monomial<N>> = reduced
            .iter()
            .map(|p| p.leading_monomial(self.order))
            .collect();
        kept.sort();
        leads.sort();
        self.stats.lead_ideal_complete = kept == leads;
        Ok(reduced)
    }

    /// One element per minimal lead, the first inserted on a tie.
    fn minimal_elements(&self) -> Vec<MultivariatePolynomial<N, F>> {
        let order = self.order;
        let mut ids: Vec<usize> = (0..self.basis.len()).collect();
        // A divisor of a lead is never above it, so scanning upwards only checks kept leads.
        ids.sort_by(|&a, &b| {
            order
                .cmp(&self.basis[a].lead, &self.basis[b].lead)
                .then(a.cmp(&b))
        });
        let mut kept: Vec<(u64, Monomial<N>, usize)> = Vec::new();
        for id in ids {
            let lead = self.basis[id].lead;
            let m = self.lead_masks[id];
            if kept
                .iter()
                .any(|&(km, k, _)| km & !m == 0 && super::divides(&k, &lead))
            {
                continue;
            }
            kept.push((m, lead, id));
        }
        kept.iter()
            .map(|&(_, _, id)| MultivariatePolynomial::new(&self.basis[id].terms))
            .collect()
    }
}
