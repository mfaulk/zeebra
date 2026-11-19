//! #936's instrument: which signature-basis elements the criteria and the matrices consult, and
//! every syzygy-store operation in order, so the store's share of bookkeeping can be replayed
//! offline (`docs/research/m32-signature-basis-growth.md`). No decision of the engine reads it.

use std::{
    cell::Cell,
    collections::HashSet,
    time::{Duration, Instant},
};

use super::signature::{divides, Signature, SyzygySource, SyzygyStore};
use crate::Monomial;

/// One syzygy-store call, as the engine made it.
#[derive(Clone, Copy, Debug)]
pub enum StoreOp<const N: usize> {
    Insert(Signature<N>, SyzygySource),
    Query(Signature<N>),
}

/// How one basis element was used. "Terms read" means a matrix row was built from its polynomial.
#[derive(Clone, Debug, Default)]
pub struct ElementUse {
    /// Batches completed before it was inserted.
    pub born: usize,
    pub terms: usize,
    pub reducer_rows: u64,
    pub target_rows: u64,
    /// Times it was the smaller half of a kept pair, where only its signature and lead are read.
    pub partner_roles: u64,
    /// Times the rewrite criterion returned it as the canonical rewriter of a signature.
    pub rewriter_wins: Cell<u64>,
    /// The batch at which some other element's lead first divided its lead, if any did.
    pub dominated_from: Option<usize>,
    /// Matrix rows built from its terms in batches after `dominated_from`.
    pub rows_after_dominated: u64,
}

/// One completed batch.
#[derive(Clone, Debug, Default)]
pub struct BatchUse {
    pub degree: u64,
    pub targets: usize,
    pub elements_added: usize,
    /// Elements added in this batch that are not dominated at the end (the minimal basis's leads).
    pub essential_added: usize,
    pub select: Duration,
    pub insert: Duration,
    pub symbolic: Duration,
    pub elimination: Duration,
}

/// Replay of the engine's syzygy-store calls against fresh stores; the timings are best of three.
#[derive(Clone, Debug, Default)]
pub struct StoreReplay {
    pub koszul_inserts: usize,
    pub zero_row_inserts: usize,
    pub queries: usize,
    /// Queries a stored Koszul entry answered first.
    pub koszul_hits: usize,
    /// Of those, queries whose signature equals a Koszul signature generated before it: the only
    /// eliminations Roune–Stillman §3.3's lazy Koszul queue keeps by itself.
    pub koszul_hits_equal: usize,
    /// Koszul hits that neither equal a generated Koszul signature nor are covered by a zero-row
    /// syzygy: pairs a lazy queue would have to reject some other way, or reduce.
    pub koszul_hits_lost: usize,
    pub full: Duration,
    pub without_koszul: Duration,
    /// Koszul inserts skipped because the query right after them was covered and divides them:
    /// the stored signature covering the query covers the Koszul signature too, so the insert was
    /// a no-op (Roune–Stillman §3.3's first observation). The store's contents are unchanged.
    pub koszul_skippable: usize,
    pub skip_covered: Duration,
}

/// What [`super::SigF4Statistics::usage`] carries out of the engine.
#[derive(Clone, Debug, Default)]
pub struct UsageReport {
    pub elements: Vec<ElementUse>,
    pub batches: Vec<BatchUse>,
    pub rewriter_calls: Cell<u64>,
    /// Same-index entries the rewriter scanned, and those whose signature divided the query.
    pub rewriter_scanned: Cell<u64>,
    pub rewriter_divisible: Cell<u64>,
    pub reducer_lookups: u64,
    /// Basis elements the reducer search scanned past its per-monomial cache.
    pub reducer_scanned: u64,
    /// The final minimal-basis selection on the whole signature basis, timed apart.
    pub minimal_selection: Duration,
    pub minimal_elements: usize,
    pub replay: StoreReplay,
}

/// The engine-side log: the report plus what only a generic engine can hold.
#[derive(Debug, Default)]
pub(super) struct UsageLog<const N: usize> {
    pub(super) report: UsageReport,
    leads: Vec<Monomial<N>>,
    pub(super) ops: Vec<StoreOp<N>>,
}

impl UsageReport {
    pub(super) fn rewriter_scan(&self, divisible: bool) {
        bump(&self.rewriter_scanned);
        if divisible {
            bump(&self.rewriter_divisible);
        }
    }

    pub(super) fn rewriter_returned(&self, id: u32) {
        bump(&self.rewriter_calls);
        if let Some(e) = self.elements.get(id as usize) {
            bump(&e.rewriter_wins);
        }
    }

    pub(super) fn reducer(&mut self, id: u32, scanned: u32, batch: usize) {
        self.reducer_lookups += 1;
        self.reducer_scanned += u64::from(scanned);
        if let Some(e) = self.elements.get_mut(id as usize) {
            e.reducer_rows += 1;
            e.rows_after_dominated += u64::from(e.dominated_from.is_some_and(|d| d < batch));
        }
    }

    pub(super) fn target(&mut self, id: u32, batch: usize) {
        let e = &mut self.elements[id as usize];
        e.target_rows += 1;
        e.rows_after_dominated += u64::from(e.dominated_from.is_some_and(|d| d < batch));
    }

    pub(super) fn partner(&mut self, id: u32) {
        self.elements[id as usize].partner_roles += 1;
    }
}

impl<const N: usize> UsageLog<N> {
    /// Records a new element and which leads now dominate which (equal leads: the earlier wins).
    pub(super) fn born(&mut self, lead: Monomial<N>, terms: usize, batch: usize) {
        let mut dominated_from = None;
        for (e, old) in self.report.elements.iter_mut().zip(&self.leads) {
            if divides(old, &lead) {
                dominated_from = Some(batch);
            } else if e.dominated_from.is_none() && divides(&lead, old) {
                e.dominated_from = Some(batch);
            }
        }
        self.leads.push(lead);
        self.report.elements.push(ElementUse {
            born: batch,
            terms,
            dominated_from,
            ..ElementUse::default()
        });
    }

    /// Fills each batch's essential count and replays the store.
    pub(super) fn finish(mut self, indices: usize) -> UsageReport {
        let report = &mut self.report;
        for e in &report.elements {
            if e.dominated_from.is_none() {
                if let Some(b) = report.batches.get_mut(e.born) {
                    b.essential_added += 1;
                }
            }
        }
        report.replay = replay(&self.ops, indices);
        self.report
    }
}

fn bump(c: &Cell<u64>) {
    c.set(c.get() + 1);
}

fn replay<const N: usize>(ops: &[StoreOp<N>], indices: usize) -> StoreReplay {
    let mut out = StoreReplay::default();
    let mut store = SyzygyStore::new(indices);
    let mut zero_rows = SyzygyStore::new(indices);
    let mut generated: HashSet<Signature<N>> = HashSet::new();
    for op in ops {
        match *op {
            StoreOp::Insert(s, source) => {
                if source == SyzygySource::Koszul {
                    out.koszul_inserts += 1;
                    generated.insert(s);
                } else {
                    out.zero_row_inserts += 1;
                    zero_rows.insert(s, source);
                }
                store.insert(s, source);
            }
            StoreOp::Query(t) => {
                out.queries += 1;
                if store.covering(&t) == Some(SyzygySource::Koszul) {
                    out.koszul_hits += 1;
                    if generated.contains(&t) {
                        out.koszul_hits_equal += 1;
                    } else if zero_rows.covering(&t).is_none() {
                        out.koszul_hits_lost += 1;
                    }
                }
            }
        }
    }
    let timed = |keep_koszul: bool| {
        (0..3)
            .map(|_| {
                let clock = Instant::now();
                let mut store = SyzygyStore::new(indices);
                let mut hits = 0usize;
                for op in ops {
                    match *op {
                        StoreOp::Insert(s, source) => {
                            if keep_koszul || source != SyzygySource::Koszul {
                                store.insert(s, source);
                            }
                        }
                        StoreOp::Query(t) => hits += usize::from(store.covering(&t).is_some()),
                    }
                }
                std::hint::black_box(hits);
                clock.elapsed()
            })
            .min()
            .unwrap_or_default()
    };
    out.full = timed(true);
    out.without_koszul = timed(false);
    (out.skip_covered, out.koszul_skippable) = skip_covered(ops, indices);
    out
}

/// The query-first schedule: a Koszul insert followed by a query of a signature dividing it runs
/// the query first and drops the insert if the query is covered. Checks every answer against the
/// recorded order's.
fn skip_covered<const N: usize>(ops: &[StoreOp<N>], indices: usize) -> (Duration, usize) {
    let mut reference = SyzygyStore::new(indices);
    let expected: Vec<bool> = ops
        .iter()
        .filter_map(|op| match *op {
            StoreOp::Insert(s, source) => {
                reference.insert(s, source);
                None
            }
            StoreOp::Query(t) => Some(reference.covering(&t).is_some()),
        })
        .collect();
    let mut best = (Duration::MAX, 0);
    for _ in 0..3 {
        let clock = Instant::now();
        let mut store = SyzygyStore::new(indices);
        let (mut answers, mut skipped, mut k) = (Vec::with_capacity(expected.len()), 0, 0);
        while k < ops.len() {
            match (ops[k], ops.get(k + 1)) {
                (StoreOp::Insert(s, SyzygySource::Koszul), Some(&StoreOp::Query(t)))
                    if s.divides(&t) || t.divides(&s) =>
                {
                    let hit = store.covering(&t).is_some();
                    if hit && t.divides(&s) {
                        skipped += 1;
                    } else {
                        store.insert(s, SyzygySource::Koszul);
                    }
                    answers.push(hit || store.covering(&t).is_some());
                    k += 2;
                }
                (StoreOp::Insert(s, source), _) => {
                    store.insert(s, source);
                    k += 1;
                }
                (StoreOp::Query(t), _) => {
                    answers.push(store.covering(&t).is_some());
                    k += 1;
                }
            }
        }
        let elapsed = clock.elapsed();
        assert_eq!(
            answers, expected,
            "the query-first schedule changed an answer"
        );
        best = best.min((elapsed, skipped));
        best.1 = skipped;
    }
    best
}

#[cfg(test)]
mod tests {
    use crate::{
        fields::Zp32003,
        grobner::{
            benchmark_systems::cyclic,
            sigf4::{sig_f4_reported, SigF4Options},
        },
        MonomialOrder,
    };

    /// The essential elements are exactly the reduced basis, every element is accounted for, and
    /// the query-first replay (which asserts its own answers) skips some Koszul inserts.
    #[test]
    fn test_usage_on_cyclic_5() {
        let (result, stats) = sig_f4_reported(
            &cyclic::<5, Zp32003>(),
            MonomialOrder::GradedReverseLexicographic,
            &SigF4Options::default(),
        );
        let reduced = result.expect("cyclic-5 finishes").len();
        let u = &stats.usage;
        assert_eq!(u.elements.len(), stats.signature_basis_elements);
        let essential = u.elements.iter().filter(|e| e.dominated_from.is_none());
        assert_eq!(essential.count(), reduced);
        assert_eq!(u.minimal_elements, reduced);
        assert_eq!(
            u.batches.iter().map(|b| b.essential_added).sum::<usize>(),
            reduced
        );
        assert_eq!(u.replay.koszul_inserts, stats.pairs_created);
        assert!(u.replay.koszul_skippable > 0);
        assert!(u.replay.koszul_hits_equal + u.replay.koszul_hits_lost <= u.replay.koszul_hits);
    }
}
