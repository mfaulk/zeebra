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
//!   (`MonomialTable::local`) in place of a product, an additive hash and a probe. Both paths
//!   append the same first-occurrence ids in the same order, so the matrix, and with it the basis,
//!   is unchanged; `Count`'s mismatch count is what shows the stored ids are the fresh ones.
//! - [`AdjacentMode::Flat`] is the same service from a flat buffer: one arena of ids per batch and
//!   one slot per run-wide id, found by the row's lead column rather than a hash of
//!   `(source, mult)`. [`AdjacentMode::FlatCount`] keeps it and builds every row, as `Count` does.

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
    /// Serve hits from the flat buffer ([`Flat`]).
    Flat,
    /// Keep the flat buffer and count its hits; build every row.
    FlatCount,
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
    /// Terms of the repeated rows a serving mode takes from the buffer, each a product and a probe
    /// skipped. A reducer row's lead is the closure's, and a flat target row's lead is probed to find
    /// its slot, so neither counts. `Count` and `FlatCount` report what their serving mode would skip.
    pub saved_probes: u64,
    /// `Count` and `FlatCount`: repeated rows whose fresh ids differ from the stored ones. Must be
    /// zero.
    pub mismatches: usize,
    /// Flat modes: rows left out of the buffer because its arena reached its budget.
    pub unbuffered: usize,
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
            ("saved_probes", u(self.saved_probes)),
            ("mismatches", n(self.mismatches)),
            ("unbuffered", n(self.unbuffered)),
            ("retained_bytes", u(self.retained_bytes)),
            ("symbolic_ns", u(self.symbolic_ns)),
        ])
    }
}

/// A row's source as one word: an input index with the top bit set, or a basis element id.
pub(super) type SourceKey = u64;

type Buffer<const N: usize> = HashMap<(SourceKey, Monomial<N>), Vec<u32>, BuildMonomialHasher>;

/// The flat arena's default budget, in ids: 256 MiB a batch.
pub const FLAT_BUDGET: usize = 1 << 26;

pub(super) struct Adjacent<const N: usize> {
    mode: AdjacentMode,
    previous: Buffer<N>,
    current: Buffer<N>,
    flat: Flat,
    batch: AdjacentBatch,
    pub(super) batches: Vec<AdjacentBatch>,
}

#[derive(Clone, Copy, Debug, Default)]
struct Slot {
    stamp: u32,
    source: u32,
    offset: u32,
}

/// One batch's rows as run-wide ids in one arena, each found by its lead's run-wide id.
///
/// A row `mult · source` is fixed by its lead column and its source, because `mult` is the column
/// over the source's lead. So the row with lead `c` in batch `b` is `slots[c] = (b, source,
/// offset)`, its ids `previous[offset..][..len]` with `len` the source's term count. Nothing is
/// allocated per row and nothing is hashed. Two rows of one batch with the same lead share its
/// slot, and the reducer row keeps it: target rows, built first, write their slots at the end of
/// the batch, where no reducer row took them.
#[derive(Default)]
struct Flat {
    slots: Vec<Slot>,
    previous: Vec<u32>,
    current: Vec<u32>,
    deferred: Vec<(u32, Slot)>,
    /// This batch's; starts at 2, so a slot never written (stamp 0) is never the previous batch's.
    stamp: u32,
    budget: usize,
}

impl Flat {
    fn set(slots: &mut Vec<Slot>, lead: u32, slot: Slot) {
        let at = lead as usize;
        if slots.len() <= at {
            slots.resize((at + 1).next_power_of_two(), Slot::default());
        }
        slots[at] = slot;
    }

    fn finish(&mut self) {
        for (lead, slot) in std::mem::take(&mut self.deferred) {
            let taken = self
                .slots
                .get(lead as usize)
                .is_some_and(|s| s.stamp == self.stamp);
            if !taken {
                Self::set(&mut self.slots, lead, slot);
            }
        }
        std::mem::swap(&mut self.previous, &mut self.current);
        self.current.clear();
        self.stamp += 1;
    }

    fn bytes(&self) -> u64 {
        ((self.previous.capacity() + self.current.capacity()) * size_of::<u32>()
            + self.slots.capacity() * size_of::<Slot>()) as u64
    }
}

/// The flat buffer's source word: an input index with the top bit set, or a basis element id.
fn flat_source(key: SourceKey) -> u32 {
    let low = key as u32;
    debug_assert!(low >> 31 == 0, "fewer than 2³¹ sources");
    if key >> 63 == 1 {
        low | 1 << 31
    } else {
        low
    }
}

impl<const N: usize> Adjacent<N> {
    /// `None` when `mode` is [`AdjacentMode::Off`], so the shipping path runs untouched. `budget`
    /// bounds the flat arena, in ids.
    pub(super) fn new(mode: AdjacentMode, budget: usize) -> Option<Self> {
        (mode != AdjacentMode::Off).then(|| Self {
            mode,
            previous: HashMap::default(),
            current: HashMap::default(),
            flat: Flat {
                stamp: 2,
                budget,
                ..Flat::default()
            },
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
        mult: (Monomial<N>, u64),
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
        match self.mode {
            AdjacentMode::Flat | AdjacentMode::FlatCount => {
                self.flat_row(table, flat_source(key.0), terms, mult, lead, work, out)
            }
            _ => self.map_row(table, key, terms, mult, lead, work, out),
        }
    }

    fn hit(&mut self, reducer: bool, len: usize, saved: usize) {
        let b = &mut self.batch;
        if reducer {
            b.reducer_hits += 1;
        } else {
            b.target_hits += 1;
        }
        b.hit_terms += len as u64;
        b.saved_probes += saved as u64;
    }

    #[allow(clippy::too_many_arguments)]
    fn map_row(
        &mut self,
        table: &mut MonomialTable<N>,
        key: (SourceKey, Monomial<N>),
        terms: impl ExactSizeIterator<Item = (Monomial<N>, u64)>,
        (mult, mult_hash): (Monomial<N>, u64),
        lead: Option<u32>,
        work: &mut Vec<u32>,
        out: &mut Vec<u32>,
    ) {
        let stored = self.previous.remove(&key);
        if let Some(ids) = &stored {
            let len = ids.len();
            self.hit(lead.is_some(), len, len - usize::from(lead.is_some()));
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

    #[allow(clippy::too_many_arguments)]
    fn flat_row(
        &mut self,
        table: &mut MonomialTable<N>,
        source: u32,
        mut terms: impl ExactSizeIterator<Item = (Monomial<N>, u64)>,
        (mult, mult_hash): (Monomial<N>, u64),
        lead: Option<u32>,
        work: &mut Vec<u32>,
        out: &mut Vec<u32>,
    ) {
        let len = terms.len();
        let column = match lead {
            Some(column) => {
                terms.next();
                column
            }
            None => {
                let (m, h) = terms.next().expect("a row has a lead");
                let id = table.find_or_insert(m * mult, h.wrapping_add(mult_hash));
                out.push(table.local(id, work));
                id
            }
        };
        let stamp = self.flat.stamp;
        let stored = self.flat.slots.get(column as usize).and_then(|s| {
            (s.stamp + 1 == stamp && s.source == source).then_some(s.offset as usize)
        });
        if stored.is_some() {
            self.hit(lead.is_some(), len, len - 1);
        }
        let Flat {
            previous, current, ..
        } = &mut self.flat;
        let offset = current.len();
        match stored {
            Some(at) if self.mode == AdjacentMode::Flat => {
                let ids = &previous[at..][..len];
                out.extend(ids[1..].iter().map(|&id| table.local(id, work)));
                current.extend_from_slice(ids);
            }
            _ => {
                current.push(column);
                for (m, h) in terms {
                    let id = table.find_or_insert(m * mult, h.wrapping_add(mult_hash));
                    current.push(id);
                    out.push(table.local(id, work));
                }
                if stored.is_some_and(|at| previous[at..][..len] != current[offset..]) {
                    self.batch.mismatches += 1;
                }
            }
        }
        if offset + len > self.flat.budget {
            self.flat.current.truncate(offset);
            self.batch.unbuffered += 1;
            return;
        }
        let slot = Slot {
            stamp,
            source,
            offset: offset as u32,
        };
        match lead {
            Some(_) => Flat::set(&mut self.flat.slots, column, slot),
            None => self.flat.deferred.push((column, slot)),
        }
    }

    /// Ends a batch: the rows it built become the buffer, and the older buffer is dropped.
    pub(super) fn finish(&mut self) {
        if matches!(self.mode, AdjacentMode::Flat | AdjacentMode::FlatCount) {
            self.flat.finish();
            self.batch.retained_bytes = self.flat.bytes();
            return;
        }
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
    use super::{AdjacentBatch, AdjacentMode, FLAT_BUDGET};
    use crate::{
        fields::Zp32003,
        grobner::{
            benchmark_systems::{cyclic, katsura, noon},
            f4::f4,
            sigf4::{sig_f4_reported, SigF4Options, SigF4Statistics},
        },
        poly::MonomialOrder,
        FiniteField, MultivariatePolynomial,
    };

    const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

    type Basis<const N: usize, F> = Vec<MultivariatePolynomial<N, F>>;

    fn census<const N: usize, F: FiniteField>(
        system: &[MultivariatePolynomial<N, F>],
        mode: AdjacentMode,
        budget: usize,
    ) -> (Basis<N, F>, SigF4Statistics) {
        // A wrong buffered row can make the closure diverge; the budget turns that into a failure.
        let options = SigF4Options {
            adjacent: mode,
            adjacent_budget: budget,
            max_wall_time: Some(std::time::Duration::from_secs(20)),
            ..SigF4Options::default()
        };
        let (result, stats) = sig_f4_reported(system, GREVLEX, &options);
        (result.expect("finishes"), stats)
    }

    /// The engine's work, without its clocks: what a buffered mode must leave unchanged.
    fn work(s: &SigF4Statistics) -> [u64; 12] {
        [
            s.batches as u64,
            s.targets as u64,
            s.reducer_rows as u64,
            s.zero_rows as u64,
            s.singular_rows as u64,
            s.coefficient_products,
            s.products_on_zero_rows,
            s.max_matrix_rows as u64,
            s.max_matrix_columns as u64,
            s.pairs_created as u64,
            s.elements_added as u64,
            s.signature_basis_elements as u64,
        ]
    }

    fn untimed(batches: &[AdjacentBatch]) -> Vec<AdjacentBatch> {
        batches
            .iter()
            .map(|b| AdjacentBatch {
                symbolic_ns: 0,
                retained_bytes: 0,
                ..b.clone()
            })
            .collect()
    }

    /// Serving repeated rows from a buffer changes no basis and no work count, every stored row
    /// equals the fresh one, and each counting mode sees the rows its serving mode serves: they
    /// differ in time only. Returns the hits of the map buffer and of the flat one.
    fn agrees<const N: usize, F: FiniteField>(
        system: &[MultivariatePolynomial<N, F>],
    ) -> (usize, usize) {
        let expected = f4(system, GREVLEX).expect("shipping F4 finishes");
        let (off, shipped) = census(system, AdjacentMode::Off, FLAT_BUDGET);
        assert_eq!(off, expected);
        assert!(shipped.adjacent.is_empty(), "Off records nothing");
        let mut hits = [0; 2];
        let pairs = [
            (AdjacentMode::Count, AdjacentMode::Reuse),
            (AdjacentMode::FlatCount, AdjacentMode::Flat),
        ];
        for (k, (counting, serving)) in pairs.into_iter().enumerate() {
            let (counted, count) = census(system, counting, FLAT_BUDGET);
            let (served, serve) = census(system, serving, FLAT_BUDGET);
            assert_eq!(counted, expected, "{counting:?}");
            assert_eq!(served, expected, "{serving:?}");
            assert_eq!(work(&count), work(&shipped), "{counting:?}");
            assert_eq!(work(&serve), work(&shipped), "{serving:?}");
            let (count, serve) = (count.adjacent, serve.adjacent);
            assert_eq!(count.iter().map(|b| b.mismatches).sum::<usize>(), 0);
            assert_eq!(untimed(&count), untimed(&serve));
            assert_eq!(
                count[0].target_hits + count[0].reducer_hits,
                0,
                "nothing precedes batch 0"
            );
            assert!(serve.iter().all(|b| b.unbuffered == 0));
            hits[k] = serve.iter().map(|b| b.target_hits + b.reducer_hits).sum();
        }
        (hits[0], hits[1])
    }

    #[test]
    fn test_reuse_is_exact_on_katsura_and_cyclic() {
        let (map, flat) = agrees(&katsura::<6, Zp32003>());
        assert!(map > 0, "Katsura-6 repeats rows across adjacent batches");
        assert!(flat > 0, "the flat buffer finds them by lead");
        agrees(&cyclic::<5, Zp32003>());
        agrees(&noon::<5, Zp32003>());
    }

    // An exhausted arena keeps fewer rows, never a wrong one; an empty one keeps none.
    #[test]
    fn test_flat_budget_bounds_the_buffer_and_not_the_basis() {
        let system = katsura::<6, Zp32003>();
        let expected = f4(&system, GREVLEX).expect("shipping F4 finishes");
        let hits = |s: &SigF4Statistics| -> usize {
            s.adjacent
                .iter()
                .map(|b| b.target_hits + b.reducer_hits)
                .sum()
        };
        let (_, full) = census(&system, AdjacentMode::Flat, FLAT_BUDGET);
        let (basis, small) = census(&system, AdjacentMode::Flat, 200);
        assert_eq!(basis, expected);
        assert_eq!(work(&small), work(&full));
        assert!(small.adjacent.iter().map(|b| b.unbuffered).sum::<usize>() > 0);
        assert!(hits(&small) < hits(&full));
        let (basis, none) = census(&system, AdjacentMode::Flat, 0);
        assert_eq!(basis, expected);
        assert_eq!(hits(&none), 0);
    }
}
