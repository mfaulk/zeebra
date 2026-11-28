//! #1198's count for a tail-reduced store indexed by irreducible monomials (the M4GB layout).
//!
//! Per batch: how many matrix columns no basis lead divides, the cells a dense row over those
//! columns would hold against the sparse entries the batch was built with, and how many stored
//! basis tails each new lead makes reducible. Nothing is reduced here, so the tails are the
//! engine's own. A tail term is counted once, when its monomial first becomes reducible; the
//! fill-in a real re-reduction would add is not followed, which makes the invalidation counts a
//! lower bound.

use std::collections::{HashMap, HashSet};

use super::signature::mask;
use crate::{
    poly::{BuildMonomialHasher, Monomial},
    util::Json,
};

/// One batch of the count.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct TailBatch {
    pub batch: usize,
    pub degree: u64,
    pub columns: usize,
    pub targets: usize,
    pub reducers: usize,
    /// Columns no basis lead divides, before and after the batch's new elements.
    pub irreducible_before: usize,
    pub irreducible_after: usize,
    /// Sparse entries of the rows as built.
    pub target_entries: u64,
    pub reducer_entries: u64,
    /// Cells of one dense vector per row over `irreducible_before`, and over only the irreducible
    /// columns below each row's lead.
    pub dense_cells: u64,
    pub dense_cells_below_lead: u64,
    /// Reducer multiples `(element, multiplier)` no earlier batch built, and the run's total.
    pub new_multiples: usize,
    pub multiples: usize,
    /// The elements the batch added, their terms, and the tail terms some lead already divided.
    pub elements: usize,
    pub element_entries: u64,
    pub element_reducible_entries: u64,
    /// Summed over the batch's new leads: the earlier elements holding a tail term the lead newly
    /// divides, and those terms.
    pub invalidated_elements: u64,
    pub invalidated_terms: u64,
    /// New leads that invalidated at least one stored tail.
    pub invalidating_leads: usize,
    /// The basis after the batch: elements, terms, and the distinct tail monomials no lead
    /// divides (the dense width a basis-only store needs).
    pub basis_elements: usize,
    pub basis_terms: u64,
    pub basis_irreducible_monomials: usize,
    /// The engine's own live-byte peak for the batch's elimination.
    pub live_peak_bytes: u64,
}

impl TailBatch {
    pub fn json(&self) -> Json {
        let n = |v: usize| Json::size(v);
        let u = |v: u64| Json::int(v);
        Json::object([
            ("batch", n(self.batch)),
            ("degree", u(self.degree)),
            ("columns", n(self.columns)),
            ("targets", n(self.targets)),
            ("reducers", n(self.reducers)),
            ("irreducible_before", n(self.irreducible_before)),
            ("irreducible_after", n(self.irreducible_after)),
            ("target_entries", u(self.target_entries)),
            ("reducer_entries", u(self.reducer_entries)),
            ("dense_cells", u(self.dense_cells)),
            ("dense_cells_below_lead", u(self.dense_cells_below_lead)),
            ("new_multiples", n(self.new_multiples)),
            ("multiples", n(self.multiples)),
            ("elements", n(self.elements)),
            ("element_entries", u(self.element_entries)),
            (
                "element_reducible_entries",
                u(self.element_reducible_entries),
            ),
            ("invalidated_elements", u(self.invalidated_elements)),
            ("invalidated_terms", u(self.invalidated_terms)),
            ("invalidating_leads", n(self.invalidating_leads)),
            ("basis_elements", n(self.basis_elements)),
            ("basis_terms", u(self.basis_terms)),
            (
                "basis_irreducible_monomials",
                n(self.basis_irreducible_monomials),
            ),
            ("live_peak_bytes", u(self.live_peak_bytes)),
        ])
    }
}

/// A row of the batch as built: its lead's column and its entry count.
#[derive(Clone, Copy, Debug)]
pub struct BuiltRow<const N: usize> {
    /// `(element, multiplier)` for a reducer multiple, `None` for a target.
    pub multiple: Option<(u32, Monomial<N>)>,
    pub lead_column: u32,
    pub entries: usize,
}

/// The run's ledger: every lead, and each still-irreducible tail monomial with its holders.
#[derive(Clone, Debug, Default)]
pub struct TailStoreCensus<const N: usize> {
    leads: Vec<(u64, Monomial<N>)>,
    tails: HashMap<Monomial<N>, Vec<u32>, BuildMonomialHasher>,
    multiples: HashSet<(u32, Monomial<N>), BuildMonomialHasher>,
    basis_terms: u64,
    open: Option<TailBatch>,
    pub batches: Vec<TailBatch>,
}

impl<const N: usize> TailStoreCensus<N> {
    fn reducible(&self, m: &Monomial<N>) -> bool {
        let bits = mask(m);
        self.leads
            .iter()
            .any(|(lead_bits, lead)| lead_bits & !bits == 0 && m.checked_div(lead).is_some())
    }

    /// Opens a batch: `columns` descending, `rows` as built.
    pub fn begin(
        &mut self,
        degree: u64,
        columns: &[Monomial<N>],
        rows: impl Iterator<Item = BuiltRow<N>>,
    ) {
        let irreducible: Vec<bool> = columns.iter().map(|m| !self.reducible(m)).collect();
        // below[p]: irreducible columns at positions after `p`, the monomials smaller than it.
        let mut below = vec![0u64; columns.len() + 1];
        for p in (0..columns.len()).rev() {
            below[p] = below[p + 1] + u64::from(irreducible[p]);
        }
        let width = below[0];
        let mut record = TailBatch {
            batch: self.batches.len(),
            degree,
            columns: columns.len(),
            irreducible_before: width as usize,
            ..Default::default()
        };
        for row in rows {
            match row.multiple {
                Some(key) => {
                    record.reducers += 1;
                    record.reducer_entries += row.entries as u64;
                    record.new_multiples += usize::from(self.multiples.insert(key));
                }
                None => {
                    record.targets += 1;
                    record.target_entries += row.entries as u64;
                }
            }
            record.dense_cells += width;
            record.dense_cells_below_lead += below[row.lead_column as usize + 1];
        }
        record.multiples = self.multiples.len();
        self.open = Some(record);
    }

    /// Closes the batch with the elements it added, each monic with its lead first.
    pub fn end<S, F>(
        &mut self,
        columns: &[Monomial<N>],
        new: &[(S, Vec<(Monomial<N>, F)>)],
        live_peak_bytes: usize,
    ) {
        let Some(mut record) = self.open.take() else {
            return;
        };
        record.live_peak_bytes = live_peak_bytes as u64;
        let mut stamp: Vec<u32> = vec![u32::MAX; self.leads.len() + new.len()];
        for (k, (_, terms)) in new.iter().enumerate() {
            let id = self.leads.len() as u32;
            let lead = terms[0].0;
            let hit: Vec<Monomial<N>> = self
                .tails
                .keys()
                .filter(|m| m.checked_div(&lead).is_some())
                .copied()
                .collect();
            let mut touched = 0u64;
            for m in &hit {
                let holders = self.tails.remove(m).expect("collected from the map");
                record.invalidated_terms += holders.len() as u64;
                for holder in holders {
                    if stamp[holder as usize] != k as u32 {
                        stamp[holder as usize] = k as u32;
                        touched += 1;
                    }
                }
            }
            record.invalidated_elements += touched;
            record.invalidating_leads += usize::from(touched > 0);
            self.leads.push((mask(&lead), lead));
            record.elements += 1;
            record.element_entries += terms.len() as u64;
            self.basis_terms += terms.len() as u64;
            for (m, _) in &terms[1..] {
                if self.reducible(m) {
                    record.element_reducible_entries += 1;
                } else {
                    self.tails.entry(*m).or_default().push(id);
                }
            }
        }
        record.irreducible_after = columns.iter().filter(|m| !self.reducible(m)).count();
        record.basis_elements = self.leads.len();
        record.basis_terms = self.basis_terms;
        record.basis_irreducible_monomials = self.tails.len();
        self.batches.push(record);
    }

    pub fn batches_json(&self) -> Json {
        Json::Array(self.batches.iter().map(TailBatch::json).collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn m(e: [u32; 2]) -> Monomial<2> {
        Monomial::new(&e)
    }

    fn element(terms: &[[u32; 2]]) -> ((), Vec<(Monomial<2>, u8)>) {
        ((), terms.iter().map(|e| (m(*e), 1u8)).collect())
    }

    // Irreducible columns are those no earlier lead divides, and a dense row is charged the full
    // irreducible width and, separately, only the irreducible columns below its lead.
    #[test]
    fn test_counts_irreducible_columns_and_dense_cells() {
        let mut census = TailStoreCensus::<2>::default();
        census.begin(1, &[m([1, 0])], std::iter::empty());
        census.end(&[m([1, 0])], &[element(&[[1, 0]])], 0);

        // x^2, xy, y^2, y, 1 with lead x known: y^2, y and 1 are irreducible.
        let columns = [m([2, 0]), m([1, 1]), m([0, 2]), m([0, 1]), m([0, 0])];
        let rows = [
            BuiltRow {
                multiple: None,
                lead_column: 2,
                entries: 3,
            },
            BuiltRow {
                multiple: Some((0, m([1, 0]))),
                lead_column: 0,
                entries: 1,
            },
            BuiltRow {
                multiple: Some((0, m([0, 1]))),
                lead_column: 1,
                entries: 1,
            },
        ];
        census.begin(2, &columns, rows.into_iter());
        census.end(&columns, &[element(&[[0, 2], [0, 0]])], 40);
        let b = &census.batches[1];
        assert_eq!((b.columns, b.targets, b.reducers), (5, 1, 2));
        assert_eq!((b.target_entries, b.reducer_entries), (3, 2));
        assert_eq!(b.irreducible_before, 3);
        assert_eq!(b.dense_cells, 9);
        // The target leads at y^2 (y and 1 below); both reducers lead above every irreducible.
        assert_eq!(b.dense_cells_below_lead, 2 + 3 + 3);
        // y^2 is a lead now.
        assert_eq!(b.irreducible_after, 2);
        assert_eq!((b.new_multiples, b.multiples), (2, 2));
        assert_eq!(b.live_peak_bytes, 40);
    }

    // A multiple built again in a later batch is not new.
    #[test]
    fn test_repeated_multiples_are_counted_once() {
        let mut census = TailStoreCensus::<2>::default();
        let row = BuiltRow {
            multiple: Some((0, m([0, 1]))),
            lead_column: 0,
            entries: 2,
        };
        for _ in 0..2 {
            census.begin(2, &[m([1, 1])], std::iter::once(row));
            census.end::<(), u8>(&[m([1, 1])], &[], 0);
        }
        assert_eq!(census.batches[0].new_multiples, 1);
        assert_eq!(census.batches[1].new_multiples, 0);
        assert_eq!(census.batches[1].multiples, 1);
    }

    // A new lead invalidates each stored tail term it divides once, counts each holder once, and
    // a tail term some lead already divides is counted at birth instead.
    #[test]
    fn test_new_leads_invalidate_stored_tails_once() {
        let mut census = TailStoreCensus::<2>::default();
        // x^3 + xy + y^2 and x^2y + xy + y: both hold xy, the first also y^2.
        census.begin(3, &[], std::iter::empty());
        census.end(
            &[],
            &[
                element(&[[3, 0], [1, 1], [0, 2]]),
                element(&[[2, 1], [1, 1], [0, 1]]),
            ],
            0,
        );
        let first = &census.batches[0];
        assert_eq!(first.invalidated_terms, 0);
        assert_eq!(first.basis_irreducible_monomials, 3);
        assert_eq!(first.basis_terms, 6);

        // Lead y divides xy (two holders), y^2 and y: four terms in two elements. The new
        // element's own tail, 1, stays irreducible.
        census.begin(3, &[], std::iter::empty());
        census.end(&[], &[element(&[[0, 1], [0, 0]])], 0);
        let second = &census.batches[1];
        assert_eq!(second.invalidated_terms, 4);
        assert_eq!(second.invalidated_elements, 2);
        assert_eq!(second.invalidating_leads, 1);
        assert_eq!(second.element_reducible_entries, 0);
        assert_eq!(second.basis_irreducible_monomials, 1);

        // A later lead dividing the same monomials finds nothing left to invalidate, and its
        // tail y is reducible at birth.
        census.begin(3, &[], std::iter::empty());
        census.end(&[], &[element(&[[1, 1], [0, 1]])], 0);
        let third = &census.batches[2];
        assert_eq!(third.invalidated_terms, 0);
        assert_eq!(third.invalidating_leads, 0);
        assert_eq!(third.element_reducible_entries, 1);
        assert_eq!(third.basis_elements, 4);
    }
}
