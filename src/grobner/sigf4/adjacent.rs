//! #1075's adjacent-round census: does a row the previous batch built recur, and what does serving
//! it from a buffer save?
//!
//! A row is `mult · source`, keyed by `(source, mult)`. Its terms are the same monomials in every
//! batch that builds it, and the run-wide monomial table (#971) gives each monomial one id for the
//! whole run, so the row's ids can be kept from one batch to the next. Only the previous batch's
//! rows are kept: the buffer holds one batch.
//!
//! - [`AdjacentMode::Count`] keeps the buffer, builds every row as the engine does, and checks each
//!   repeated row's fresh ids against the stored ones. It pays the buffer's upkeep and its misses
//!   and saves nothing.
//! - [`AdjacentMode::Reuse`] serves a repeated row from the stored ids: one table read per term
//!   ([`MonomialTable::local`]) in place of a product, an additive hash and a probe. Both paths
//!   append the same first-occurrence ids in the same order, so the matrix, and with it the basis,
//!   is unchanged; `Count`'s mismatch count is what shows the stored ids are the fresh ones.

use std::{collections::HashMap, mem::size_of};

use crate::{
    poly::{BuildMonomialHasher, Monomial},
    util::Json,
};

use super::table::MonomialTable;

/// What the engine does with the previous batch's rows.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum AdjacentMode {
    /// No buffer: the engine as it ships.
    #[default]
    Off,
    /// Keep the buffer and count its hits; build every row.
    Count,
    /// Keep the buffer and serve its hits from the stored ids.
    Reuse,
}

/// One batch of the census.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct AdjacentBatch {
    pub batch: usize,
    pub targets: usize,
    pub reducers: usize,
    /// Rows whose `(source, mult)` the previous batch built, by kind.
    pub target_hits: usize,
    pub reducer_hits: usize,
    /// Terms of every row, and of the repeated rows.
    pub terms: u64,
    pub hit_terms: u64,
    /// `Count` only: repeated rows whose fresh ids differ from the stored ones. Must be zero.
    pub mismatches: usize,
    /// The buffer handed to the next batch: its ids and its map entries.
    pub retained_bytes: u64,
    /// This batch's symbolic stage, buffer upkeep included.
    pub symbolic_ns: u64,
}

impl AdjacentBatch {
    pub fn json(&self) -> Json {
        let n = |v: usize| Json::size(v);
        let u = |v: u64| Json::int(v);
        Json::object([
            ("batch", n(self.batch)),
            ("targets", n(self.targets)),
            ("reducers", n(self.reducers)),
            ("target_hits", n(self.target_hits)),
            ("reducer_hits", n(self.reducer_hits)),
            ("terms", u(self.terms)),
            ("hit_terms", u(self.hit_terms)),
            ("mismatches", n(self.mismatches)),
            ("retained_bytes", u(self.retained_bytes)),
            ("symbolic_ns", u(self.symbolic_ns)),
        ])
    }
}

/// A row's source as one word: an input index with the top bit set, or a basis element id.
pub(super) type SourceKey = u64;

type Buffer<const N: usize> = HashMap<(SourceKey, Monomial<N>), Vec<u32>, BuildMonomialHasher>;

pub(super) struct Adjacent<const N: usize> {
    mode: AdjacentMode,
    previous: Buffer<N>,
    current: Buffer<N>,
    batch: AdjacentBatch,
    pub(super) batches: Vec<AdjacentBatch>,
}

impl<const N: usize> Adjacent<N> {
    /// `None` when `mode` is [`AdjacentMode::Off`], so the shipping path runs untouched.
    pub(super) fn new(mode: AdjacentMode) -> Option<Self> {
        (mode != AdjacentMode::Off).then(|| Self {
            mode,
            previous: HashMap::default(),
            current: HashMap::default(),
            batch: AdjacentBatch::default(),
            batches: Vec::new(),
        })
    }

    /// One row's handles, appended to `out`. `terms` are the source's monomials with their
    /// additive hashes, lead first; `lead` is `Some((table id, handle))` for a reducer row, whose
    /// lead the closure has already interned and whose handle `out` already holds.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn row(
        &mut self,
        table: &mut MonomialTable<N>,
        key: (SourceKey, Monomial<N>),
        terms: impl ExactSizeIterator<Item = (Monomial<N>, u64)>,
        (mult, mult_hash): (Monomial<N>, u64),
        lead: Option<u32>,
        work: &mut Vec<u32>,
        out: &mut Vec<u32>,
    ) {
        let b = &mut self.batch;
        match lead {
            Some(_) => b.reducers += 1,
            None => b.targets += 1,
        }
        b.terms += terms.len() as u64;
        let stored = self.previous.remove(&key);
        if let Some(ids) = &stored {
            match lead {
                Some(_) => b.reducer_hits += 1,
                None => b.target_hits += 1,
            }
            b.hit_terms += ids.len() as u64;
        }
        if self.mode == AdjacentMode::Reuse {
            if let Some(ids) = stored {
                let rest = if lead.is_some() { &ids[1..] } else { &ids[..] };
                out.extend(rest.iter().map(|&id| table.local(id, work)));
                self.current.insert(key, ids);
                return;
            }
        }
        let mut ids = Vec::with_capacity(terms.len());
        let mut terms = terms;
        if let Some(column) = lead {
            ids.push(column);
            terms.next();
        }
        for (m, h) in terms {
            let id = table.find_or_insert(m * mult, h.wrapping_add(mult_hash));
            ids.push(id);
            out.push(table.local(id, work));
        }
        if stored.as_ref().is_some_and(|s| *s != ids) {
            self.batch.mismatches += 1;
        }
        self.current.insert(key, ids);
    }

    /// Ends a batch: the rows it built become the buffer, and the older buffer is dropped.
    pub(super) fn finish(&mut self) {
        self.previous = std::mem::take(&mut self.current);
        let entry = size_of::<((SourceKey, Monomial<N>), Vec<u32>)>() as u64;
        self.batch.retained_bytes = self
            .previous
            .values()
            .map(|ids| ids.capacity() as u64 * 4 + entry)
            .sum();
    }

    /// Records the batch with its symbolic wall and starts the next one.
    pub(super) fn record(&mut self, symbolic_ns: u64) {
        let mut b = std::mem::take(&mut self.batch);
        b.batch = self.batches.len();
        b.symbolic_ns = symbolic_ns;
        self.batches.push(b);
    }
}

#[cfg(test)]
mod tests {
    use super::{AdjacentBatch, AdjacentMode};
    use crate::{
        fields::Zp32003,
        grobner::{
            benchmark_systems::{cyclic, katsura},
            f4::f4,
            sigf4::{sig_f4_reported, SigF4Options},
        },
        poly::MonomialOrder,
        FiniteField, MultivariatePolynomial,
    };

    const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

    fn census<const N: usize, F: FiniteField>(
        system: &[MultivariatePolynomial<N, F>],
        mode: AdjacentMode,
    ) -> (Vec<MultivariatePolynomial<N, F>>, Vec<AdjacentBatch>) {
        // A wrong buffered row can make the closure diverge; the budget turns that into a failure.
        let options = SigF4Options {
            adjacent: mode,
            max_wall_time: Some(std::time::Duration::from_secs(20)),
            ..SigF4Options::default()
        };
        let (result, stats) = sig_f4_reported(system, GREVLEX, &options);
        (result.expect("finishes"), stats.adjacent)
    }

    /// Serving repeated rows from the buffer changes no basis, every stored row equals the fresh
    /// one, and both buffered modes see the same rows: they differ in time only.
    fn agrees<const N: usize, F: FiniteField>(system: &[MultivariatePolynomial<N, F>]) -> usize {
        let expected = f4(system, GREVLEX).expect("shipping F4 finishes");
        let (off, none) = census(system, AdjacentMode::Off);
        assert_eq!(off, expected);
        assert!(none.is_empty(), "Off records nothing");
        let (counted, count) = census(system, AdjacentMode::Count);
        let (reused, reuse) = census(system, AdjacentMode::Reuse);
        assert_eq!(counted, expected);
        assert_eq!(reused, expected);
        assert_eq!(count.iter().map(|b| b.mismatches).sum::<usize>(), 0);
        let untimed = |batches: &[AdjacentBatch]| -> Vec<AdjacentBatch> {
            batches
                .iter()
                .map(|b| AdjacentBatch {
                    symbolic_ns: 0,
                    ..b.clone()
                })
                .collect()
        };
        assert_eq!(untimed(&count), untimed(&reuse));
        assert_eq!(count[0].target_hits + count[0].reducer_hits, 0, "nothing precedes batch 0");
        count.iter().map(|b| b.target_hits + b.reducer_hits).sum()
    }

    #[test]
    fn test_reuse_is_exact_on_katsura_and_cyclic() {
        let hits = agrees(&katsura::<6, Zp32003>());
        assert!(hits > 0, "Katsura-6 repeats rows across adjacent batches");
        agrees(&cyclic::<5, Zp32003>());
    }
}
