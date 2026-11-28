//! Final interreduction in the engine's own representation (#971, M33 candidate G2-2).
//!
//! The reduced Gröbner basis is unique, so each minimal element's reduced form is its lead plus the
//! normal form of its tail, whichever basis elements serve as reducers. That lets the closure take
//! its reducers from the engine's cached least-ratio search and intern through the run-wide
//! monomial table, and the tails-only sweep (#879) run in the engine's [`Workspace`], so the
//! signature basis is never materialized as polynomials. Only the reduced basis is.

use super::{divides, mask, Engine, View, Workspace, NONE};
use crate::{
    grobner::f4::interreduce::MatrixInterreductionReport, poly::MonomialOrder, FiniteField,
    Monomial, MultivariatePolynomial,
};

/// The F4 interreduction budgets the polynomial route applies, which this route keeps.
#[derive(Clone, Copy)]
pub(super) struct Limits {
    pub rows: usize,
    pub columns: usize,
    pub live_entries: usize,
}

/// Why the column-space route did not produce a basis.
pub(super) enum Declined {
    /// A budget refused the closure or the sweep; the caller falls back to the polynomial route.
    Refused,
    /// The stop predicate fired; `elements` minimal elements were pending.
    Stopped { elements: usize },
}

type Reduced<const N: usize, F> = (
    Vec<MultivariatePolynomial<N, F>>,
    MatrixInterreductionReport,
);

/// The minimal elements: one per minimal generator of the lead ideal, the earliest inserted on a
/// tied lead, in ascending lead order.
pub(super) fn minimal<const N: usize>(leads: &[Monomial<N>], order: MonomialOrder) -> Vec<u32> {
    let mut ids: Vec<u32> = (0..leads.len() as u32).collect();
    ids.sort_by(|&a, &b| {
        order
            .cmp(&leads[a as usize], &leads[b as usize])
            .then(a.cmp(&b))
    });
    let mut kept: Vec<(u64, u32)> = Vec::new();
    for id in ids {
        let lead = &leads[id as usize];
        let m = mask(lead);
        // A graded order puts every divisor first, so the kept set is final when `lead` is read.
        let covered = kept
            .iter()
            .any(|&(k, other)| k & !m == 0 && divides(&leads[other as usize], lead));
        if !covered {
            kept.push((m, id));
        }
    }
    kept.into_iter().map(|(_, id)| id).collect()
}

impl<const N: usize, F: FiniteField> Engine<'_, N, F> {
    /// The reduced basis from the signature basis' own rows, or why not.
    pub(super) fn interreduce_in_columns(
        &mut self,
        limits: Limits,
        mut should_stop: impl FnMut() -> bool,
    ) -> Result<Reduced<N, F>, Declined> {
        let order = self.order;
        let leads: Vec<Monomial<N>> = self.basis.iter().map(|e| e.lead).collect();
        let seeds = minimal(&leads, order);
        let elements = seeds.len();
        if should_stop() {
            return Err(Declined::Stopped { elements });
        }

        // The closure: every seed row, then one reducer multiple per divisible column, interned
        // through the run's table as symbolic preprocessing does.
        self.table.begin_batch();
        let mut work: Vec<u32> = Vec::new();
        let mut handles: Vec<Vec<u32>> = Vec::with_capacity(elements);
        let mut sources: Vec<(u32, Monomial<N>)> = Vec::with_capacity(elements);
        let mut nonzeros = 0usize;
        for &id in &seeds {
            let row: Vec<u32> = match self.basis[id as usize].terms.view() {
                View::Full(terms, hashes) => terms
                    .iter()
                    .zip(hashes)
                    .map(|((m, _), &h)| self.table.intern(*m, h, &mut work))
                    .collect(),
                // Already interned: only the batch-local id is new.
                View::Ids(ids, _) => ids
                    .iter()
                    .map(|&t| self.table.local(t, &mut work))
                    .collect(),
            };
            nonzeros += row.len();
            handles.push(row);
            sources.push((id, Monomial::one()));
        }
        let mut next = 0;
        while next < work.len() {
            let column = work[next];
            let lead = next as u32;
            next += 1;
            let id = self.reducer(column);
            if id == NONE {
                continue;
            }
            let e = &self.basis[id as usize];
            let terms = e.terms.view();
            let mult = self
                .table
                .mono(column)
                .checked_div(&e.lead)
                .expect("the lead divides the column");
            let hm = self
                .table
                .hash_of(column)
                .wrapping_sub(terms.lead_hash(&self.table));
            let mut row = Vec::with_capacity(terms.len());
            row.push(lead);
            terms.intern_times(&mut self.table, 1, &mult, hm, &mut work, &mut row);
            nonzeros += row.len();
            handles.push(row);
            sources.push((id, mult));
            if handles.len() > limits.rows
                || work.len() > limits.columns
                || nonzeros > limits.live_entries
            {
                return Err(Declined::Refused);
            }
        }
        if work.len() > limits.columns || nonzeros > limits.live_entries {
            return Err(Declined::Refused);
        }
        if should_stop() {
            return Err(Declined::Stopped { elements });
        }

        // Columns descending, handles remapped to positions: rows then read left to right.
        let monomials: Vec<Monomial<N>> = work.iter().map(|&id| *self.table.mono(id)).collect();
        let mut by_position: Vec<u32> = (0..monomials.len() as u32).collect();
        by_position
            .sort_unstable_by(|&a, &b| order.cmp(&monomials[b as usize], &monomials[a as usize]));
        let mut position = vec![0u32; monomials.len()];
        for (k, &id) in by_position.iter().enumerate() {
            position[id as usize] = k as u32;
        }
        let columns: Vec<Monomial<N>> = by_position
            .iter()
            .map(|&id| monomials[id as usize])
            .collect();
        let ncols = columns.len();
        let rows: Vec<Vec<(u32, F)>> = handles
            .into_iter()
            .zip(&sources)
            .map(|(row, &(id, _))| {
                self.basis[id as usize]
                    .terms
                    .view()
                    .entries(row, |h| position[h as usize])
            })
            .collect();
        let mut pivot_at = vec![NONE; ncols];
        for (k, row) in rows.iter().enumerate().skip(elements) {
            pivot_at[row[0].0 as usize] = k as u32;
        }
        if should_stop() {
            return Err(Declined::Stopped { elements });
        }

        // Tails only: each seed's tail swept against the fixed rows; its own lead is kept.
        let mut workspace = Workspace::new(ncols);
        let mut reduced = Vec::with_capacity(elements);
        let mut peak = nonzeros;
        for seed in &rows[..elements] {
            let lead = seed[0].0 as usize;
            let (out, _) = workspace.reduce(seed, |c| {
                let k = pivot_at[c];
                (c != lead && k != NONE).then(|| rows[k as usize].as_slice())
            });
            debug_assert_eq!(
                out[0],
                (lead as u32, F::one()),
                "a seed keeps its monic lead"
            );
            // The fixed rows plus the reduced row, as the polynomial route's tails-only sweep counts.
            peak = peak.max(nonzeros + out.len());
            if peak > limits.live_entries {
                return Err(Declined::Refused);
            }
            let terms: Vec<(Monomial<N>, F)> = out
                .into_iter()
                .map(|(c, v)| (columns[c as usize], v))
                .collect();
            reduced.push(MultivariatePolynomial::new(&terms));
        }
        reduced.sort_by(|a: &MultivariatePolynomial<N, F>, b| {
            order.cmp(&b.leading_monomial(order), &a.leading_monomial(order))
        });
        let report = MatrixInterreductionReport {
            rows: rows.len(),
            columns: ncols,
            nonzeros,
            peak_nonzeros: peak,
            peak_entry_capacity: nonzeros + ncols,
            elements,
        };
        Ok((reduced, report))
    }
}

#[cfg(test)]
mod tests {
    use super::minimal;
    use crate::{poly::MonomialOrder, Monomial};

    fn m(e: [u32; 3]) -> Monomial<3> {
        Monomial::new(&e)
    }

    /// The minimal selection keeps one element per minimal lead, the earliest on a tie.
    #[test]
    fn test_minimal_keeps_minimal_generators_of_the_lead_ideal() {
        let order = MonomialOrder::GradedReverseLexicographic;
        // x², y, x²y (divisible by y), y (a tie, later), x³ (divisible by x²), z.
        let leads = [
            m([2, 0, 0]),
            m([0, 1, 0]),
            m([2, 1, 0]),
            m([0, 1, 0]),
            m([3, 0, 0]),
            m([0, 0, 1]),
        ];
        let mut kept = minimal(&leads, order);
        kept.sort_unstable();
        assert_eq!(kept, [0, 1, 5]);
    }
}
