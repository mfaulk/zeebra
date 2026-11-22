//! The batched F4-RB main loop (RFC §9 design 1; Lairez Algorithm 8, EF Algorithm 4).

use std::{
    cmp::Ordering,
    collections::BTreeMap,
    mem::size_of,
    sync::{
        atomic::{AtomicUsize, Ordering as AtomicOrdering},
        Mutex,
    },
    time::{Duration, Instant},
};

use super::{
    claim::{Claim, Kind, Stop},
    signature::{divides, mask, Signature, SyzygySource, SyzygyStore},
    table::{hash, MonomialTable},
    SigF4Error, SigF4Options, SigF4Statistics,
};
use crate::{
    fields::ConcurrentJob,
    grobner::{
        buchberger::{minimal_basis_for_interreduction, reduce_grobner_basis_until},
        f4::{
            certify_f4_output_with_workers, certify_f4_output_within,
            interreduce::{
                interreduce_by_matrix_with, MatrixInterreductionAborted,
                MatrixInterreductionMethod, MatrixInterreductionReport,
            },
            F4Error, F4Options,
        },
    },
    poly::MonomialOrder,
    FiniteField, Monomial, MultivariatePolynomial,
};

#[cfg(feature = "research-sigf4-replay")]
#[path = "symbolic_replay.rs"]
pub mod symbolic_replay;

#[path = "interreduce.rs"]
mod columns;

pub(super) const NONE: u32 = u32::MAX;

/// A row after reduction: its remaining entries in column order, and the products spent.
pub(super) type Reduced<F> = (Vec<(u32, F)>, u64);

/// A signed basis element: `(s(α), ᾱ)` with `ᾱ` monic, terms in descending order, and each
/// term's additive hash.
struct Element<const N: usize, F> {
    sig: Signature<N>,
    lead: Monomial<N>,
    terms: Vec<(Monomial<N>, F)>,
    hashes: Vec<u64>,
}

/// What a pending signature reduces: an input, or `mult·element` (the pair's larger half), where
/// `mult = sig / s(element)` and the smaller half is `(lcm / lm(other))·other`. Multipliers are
/// recomputed when the batch reads them, which keeps a pending entry at a third of its size.
#[derive(Clone, Copy)]
enum Source {
    Input(u32),
    Pair { element: u32, other: u32 },
}

#[derive(Clone, Copy)]
struct Pending<const N: usize> {
    sig: Signature<N>,
    source: Source,
}

/// One row of a batch matrix: `mult · source` with signature `sig`.
struct Row<const N: usize> {
    sig: Signature<N>,
    mult: Monomial<N>,
    source: RowSource,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RowSource {
    Input(usize),
    Element(u32),
}

struct Engine<'a, const N: usize, F: FiniteField> {
    order: MonomialOrder,
    options: &'a SigF4Options,
    inputs: Vec<Vec<(Monomial<N>, F)>>,
    input_hashes: Vec<Vec<u64>>,
    basis: Vec<Element<N, F>>,
    /// `mask(lead)` per basis element, apart from the elements so the reducer scan reads eight
    /// bytes per element.
    lead_masks: Vec<u64>,
    /// Per signature index, the elements in insertion order with their signature masks.
    by_index: Vec<Vec<(u64, u32)>>,
    syzygies: SyzygyStore<N>,
    queue: BTreeMap<u64, Vec<Pending<N>>>,
    pending: usize,
    /// Every column monomial of the run, with its least-ratio reducer search cached.
    table: MonomialTable<N>,
    wall: Option<(Instant, Duration)>,
    stats: &'a mut SigF4Statistics,
    #[cfg(feature = "research-sigf4-usage")]
    usage: super::usage::UsageLog<N>,
    #[cfg(feature = "research-reuse")]
    reuse: Option<crate::grobner::reuse_census::ReuseCensus<N, Signature<N>>>,
}

pub(super) fn run<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    options: &SigF4Options,
    stats: &mut SigF4Statistics,
) -> Result<Vec<MultivariatePolynomial<N, F>>, SigF4Error> {
    let started = Instant::now();
    #[cfg(feature = "research-sigf4-split")]
    let inputs_clock = Instant::now();
    graded(order)?;
    if order == MonomialOrder::GradedLexicographic && !options.allow_graded_lex {
        return Err(SigF4Error::Unsupported {
            reason: "graded-lex needs SigF4Options::allow_graded_lex (#961)",
        });
    }

    let mut inputs: Vec<Vec<(Monomial<N>, F)>> = Vec::new();
    for p in generators.iter().filter(|p| !p.is_zero()) {
        let terms = sorted_monic(p, order);
        if !inputs.contains(&terms) {
            inputs.push(terms);
        }
    }
    if inputs.is_empty() {
        return Ok(Vec::new());
    }

    let mut engine = Engine {
        order,
        options,
        by_index: vec![Vec::new(); inputs.len()],
        syzygies: SyzygyStore::new(inputs.len()),
        basis: Vec::new(),
        lead_masks: Vec::new(),
        queue: BTreeMap::new(),
        pending: 0,
        table: MonomialTable::default(),
        wall: options.max_wall_time.map(|budget| (started, budget)),
        input_hashes: inputs
            .iter()
            .map(|terms| terms.iter().map(|(m, _)| hash(m)).collect())
            .collect(),
        inputs,
        stats,
        #[cfg(feature = "research-sigf4-usage")]
        usage: Default::default(),
        // Design 1 only: design 2's parallel pass and the claim cascade count products otherwise.
        #[cfg(feature = "research-reuse")]
        reuse: (options.reuse_census && options.workers <= 1 && !options.parallel_cascade)
            .then(Default::default),
    };
    #[cfg(feature = "research-sigf4-split")]
    {
        engine.stats.split.inputs = inputs_clock.elapsed();
    }
    for i in 0..engine.inputs.len() {
        let sig = Signature::new(engine.inputs[i][0].0, i as u32);
        engine.push(Pending {
            sig,
            source: Source::Input(i as u32),
        });
    }

    let wall = options.max_wall_time.map(|budget| (Instant::now(), budget));
    let mut inconsistent = false;
    while let Some(degree) = engine.queue.keys().next().copied() {
        if let Some((clock, budget)) = wall {
            if engine.stats.batches > 0 && clock.elapsed() >= budget {
                return Err(SigF4Error::Budget(F4Error::TimeBudgetExceeded {
                    degree,
                    elapsed_millis: millis(clock.elapsed()),
                    budget_millis: millis(budget),
                }));
            }
        }
        let entries = engine.queue.remove(&degree).unwrap_or_default();
        engine.pending -= entries.len();
        if engine.batch(entries)? {
            inconsistent = true;
            break;
        }
    }

    // Interreduce from the engine's rows (G2-2); a budget refusal falls back to the polynomial
    // route below, which materializes the whole signature basis first.
    let interreduction = Instant::now();
    let direct = if inconsistent {
        None
    } else {
        let defaults = F4Options::default();
        #[allow(unused_mut)]
        let mut limits = columns::Limits {
            rows: defaults.max_matrix_rows,
            columns: defaults.max_matrix_columns,
            live_entries: defaults.live_entry_allowance::<F>(),
        };
        #[cfg(test)]
        if let Some(live) = options.interreduction_live_entries {
            limits.live_entries = live;
        }
        let should_stop = || wall.is_some_and(|(clock, budget)| clock.elapsed() >= budget);
        match engine.interreduce_in_columns(limits, should_stop) {
            Ok(done) => Some(done),
            Err(columns::Declined::Refused) => None,
            Err(columns::Declined::Stopped { elements }) => {
                let (clock, budget) = wall.unwrap_or((Instant::now(), Duration::ZERO));
                return Err(SigF4Error::Budget(
                    F4Error::InterreductionTimeBudgetExceeded {
                        elements_reduced: 0,
                        elements,
                        elapsed_millis: millis(clock.elapsed()),
                        budget_millis: millis(budget),
                    },
                ));
            }
        }
    };
    let mut interreduction_time = interreduction.elapsed();
    let materialized = direct.is_none()
        || cfg!(any(
            feature = "research-sigf4-split",
            feature = "research-sigf4-usage"
        ));
    #[cfg(feature = "research-sigf4-split")]
    let materialize_clock = Instant::now();
    let basis: Vec<MultivariatePolynomial<N, F>> = if inconsistent {
        vec![MultivariatePolynomial::one()]
    } else if !materialized {
        Vec::new()
    } else {
        engine
            .basis
            .iter()
            .map(|e| MultivariatePolynomial::new(&e.terms))
            .collect()
    };
    #[cfg(feature = "research-sigf4-usage")]
    {
        // Best of three, the clone outside the clock: the selection alone, as interreduction
        // runs it on the whole signature basis.
        let (mut best, mut kept) = (Duration::MAX, 0);
        for _ in 0..3 {
            let copy = basis.clone();
            let clock = Instant::now();
            kept = minimal_basis_for_interreduction(copy, order).len();
            best = best.min(clock.elapsed());
        }
        let usage = std::mem::take(&mut engine.usage);
        engine.stats.usage = usage.finish(engine.inputs.len());
        engine.stats.usage.minimal_selection = best;
        engine.stats.usage.minimal_elements = kept;
    }
    engine.stats.signature_basis_elements = engine.basis.len();
    engine.stats.syzygy_signatures = engine.syzygies.len();
    engine.stats.signature_metadata_bytes = engine.basis.len()
        * (size_of::<Signature<N>>() + 2 * size_of::<u64>())
        + engine.syzygies.len() * (size_of::<Monomial<N>>() + size_of::<u64>() + 1)
        + engine.stats.peak_pending * size_of::<Pending<N>>()
        + engine.table.bytes()
        + engine
            .basis
            .iter()
            .map(|e| e.hashes.len() * size_of::<u64>())
            .sum::<usize>();
    #[cfg(feature = "research-reuse")]
    {
        let bytes_per_term = size_of::<Monomial<N>>() + size_of::<F>();
        engine.stats.reuse = engine
            .reuse
            .take()
            .map(|census| (census.summary_json(bytes_per_term), census.batches_json()));
    }
    #[cfg(feature = "research-sigf4-split")]
    let (leads, drop_clock) = {
        engine.stats.split.materialize = materialize_clock.elapsed();
        let leads: Vec<Monomial<N>> = engine.basis.iter().map(|e| e.lead).collect();
        (leads, Instant::now())
    };
    drop(engine);
    #[cfg(feature = "research-sigf4-split")]
    {
        stats.split.drop = drop_clock.elapsed();
        let copy = basis.clone();
        let clock = Instant::now();
        let _ = minimal_basis_for_interreduction(copy, order);
        stats.split.minimal_selection = clock.elapsed();
    }

    stats.interreduction_in_columns = direct.is_some();
    let (reduced, matrix) = match direct {
        Some(done) => done,
        None => {
            let clock = Instant::now();
            let done = interreduce(basis, order, wall)?;
            interreduction_time += clock.elapsed();
            done
        }
    };
    stats.interreduction = interreduction_time;
    stats.interreduction_columns = matrix.columns;
    stats.interreduction_nonzeros = matrix.nonzeros;
    stats.interreduction_peak_nonzeros = matrix.peak_nonzeros;
    stats.reduced_basis_elements = reduced.len();
    #[cfg(feature = "research-sigf4-split")]
    {
        // The first element at each surviving lead is the one interreduction kept.
        let mut kept: std::collections::HashSet<Monomial<N>> =
            reduced.iter().map(|p| p.leading_monomial(order)).collect();
        let split = &mut stats.split;
        for (lead, &products) in leads.iter().zip(&split.element_products) {
            if kept.remove(lead) {
                split.products_on_kept_elements += products;
            } else {
                split.redundant_elements += 1;
                split.products_on_redundant_elements += products;
            }
        }
    }

    if options.certify {
        // As the shipping F4 certifies (#909, #912): on the engine's workers, under the
        // certificate's own budget when one is set, and a stop is never a rejection.
        let workers = options.workers.max(1);
        let report = match options.max_certify_time {
            None => certify_f4_output_with_workers(generators, &reduced, order, workers),
            Some(budget) => certify_f4_output_within(generators, &reduced, order, workers, budget)
                .map_err(|progress| {
                    SigF4Error::Budget(F4Error::CertificationTimeBudgetExceeded { progress })
                })?,
        };
        if let Some(reason) = report.first_failure() {
            return Err(SigF4Error::Budget(F4Error::CertificationFailed { reason }));
        }
    }
    stats.total = started.elapsed();
    Ok(reduced)
}

/// Lex, `Weighted` and `Block` are refused (plan §9.3): the engine's batches are degrees.
pub(super) fn graded(order: MonomialOrder) -> Result<(), SigF4Error> {
    match order {
        MonomialOrder::GradedReverseLexicographic | MonomialOrder::GradedLexicographic => Ok(()),
        _ => Err(SigF4Error::Unsupported {
            reason: "the signature engine supports graded orders only (RFC §7)",
        }),
    }
}

/// The shipping F4's final stage: minimal basis, then matrix interreduction with the division
/// route as fallback (`f4/mod.rs`), under F4's default limits.
///
/// Tails only (#879): each element's tail is swept against the matrix's unreduced rows, skipping
/// the back-substitution among reducer multiples that the full echelon form performs and then
/// discards. Its precondition — monic rows at distinct leads — holds for every closure of a
/// minimal basis, so the reduced basis is the same. The fallback reports an empty matrix.
fn interreduce<const N: usize, F: FiniteField>(
    basis: Vec<MultivariatePolynomial<N, F>>,
    order: MonomialOrder,
    wall: Option<(Instant, Duration)>,
) -> Result<
    (
        Vec<MultivariatePolynomial<N, F>>,
        MatrixInterreductionReport,
    ),
    SigF4Error,
> {
    let defaults = F4Options::default();
    let should_stop = || wall.is_some_and(|(clock, budget)| clock.elapsed() >= budget);
    let stopped = |elements_reduced, elements| {
        let (clock, budget) = wall.unwrap_or((Instant::now(), Duration::ZERO));
        SigF4Error::Budget(F4Error::InterreductionTimeBudgetExceeded {
            elements_reduced,
            elements,
            elapsed_millis: millis(clock.elapsed()),
            budget_millis: millis(budget),
        })
    };
    let minimal = minimal_basis_for_interreduction(basis, order);
    match interreduce_by_matrix_with(
        minimal,
        order,
        defaults.max_matrix_rows,
        defaults.max_matrix_columns,
        defaults.live_entry_allowance::<F>(),
        MatrixInterreductionMethod::TailsOnly,
        should_stop,
    ) {
        Ok(done) => Ok(done),
        Err(MatrixInterreductionAborted::Refused(_, minimal, _)) => {
            reduce_grobner_basis_until(minimal, order, should_stop)
                .map(|reduced| (reduced, MatrixInterreductionReport::default()))
                .map_err(|s| stopped(s.elements_reduced, s.elements))
        }
        Err(MatrixInterreductionAborted::Stopped(s)) => {
            Err(stopped(s.elements_reduced, s.elements))
        }
    }
}

fn millis(d: Duration) -> u64 {
    d.as_millis().min(u128::from(u64::MAX)) as u64
}

fn sorted_monic<const N: usize, F: FiniteField>(
    p: &MultivariatePolynomial<N, F>,
    order: MonomialOrder,
) -> Vec<(Monomial<N>, F)> {
    let mut terms: Vec<(Monomial<N>, F)> = p.terms().iter().map(|(m, c)| (*m, *c)).collect();
    terms.sort_by(|a, b| order.cmp(&b.0, &a.0));
    let inverse = terms[0].1.inverse();
    for (_, c) in &mut terms {
        *c *= inverse;
    }
    terms
}

fn gcd_is_one<const N: usize>(a: &Monomial<N>, b: &Monomial<N>) -> bool {
    a.exponents()
        .iter()
        .zip(b.exponents())
        .all(|(x, y)| *x == 0 || *y == 0)
}

/// `ratio(a) < ratio(b)` as module terms `s/lt`, compared by cross-multiplication.
fn ratio_cmp<const N: usize, F>(
    basis: &[Element<N, F>],
    order: MonomialOrder,
    a: u32,
    b: u32,
) -> Ordering {
    let (a, b) = (&basis[a as usize], &basis[b as usize]);
    order
        .cmp(&(a.sig.mono * b.lead), &(b.sig.mono * a.lead))
        .then(a.sig.index.cmp(&b.sig.index))
}

/// The least-ratio element whose lead divides `m`, the newest on a tie, resuming a cached
/// `(best, scanned)`; returns it with the basis length scanned to. A function of `m` and the basis
/// alone, whatever the cache held (`docs/research/m32-parallel-symbolic.md` §3, Lemma 1).
fn least_ratio<const N: usize, F>(
    basis: &[Element<N, F>],
    lead_masks: &[u64],
    order: MonomialOrder,
    m: &Monomial<N>,
    cached: Option<(u32, u32)>,
) -> (u32, u32) {
    let (mut best, scanned) = cached.unwrap_or((NONE, 0));
    let total = basis.len() as u32;
    if scanned < total {
        let mm = mask(m);
        for (offset, &lead_mask) in lead_masks[scanned as usize..].iter().enumerate() {
            let id = scanned + offset as u32;
            if lead_mask & !mm != 0 || !divides(&basis[id as usize].lead, m) {
                continue;
            }
            if best == NONE || ratio_cmp(basis, order, id, best) != Ordering::Greater {
                best = id;
            }
        }
    }
    (best, total)
}

impl<const N: usize, F: FiniteField> Engine<'_, N, F> {
    fn push(&mut self, pending: Pending<N>) {
        self.queue
            .entry(pending.sig.degree())
            .or_default()
            .push(pending);
        self.pending += 1;
        self.stats.peak_pending = self.stats.peak_pending.max(self.pending);
    }

    fn ratio_cmp(&self, a: u32, b: u32) -> Ordering {
        ratio_cmp(&self.basis, self.order, a, b)
    }

    /// The canonical rewriter of `t`: the `⊴_rat`-maximal element whose signature divides `t`
    /// (EF Def 7.1, 7.13), i.e. the **greatest** sig-lead ratio, whose multiple at `t` has the
    /// smallest lead; the newest on a tie. Greatest, not least: an element reduced from a multiple
    /// of `α` has a larger ratio than `α` and must supersede it, which the least-ratio choice
    /// does not (it lost pairs on katsura-4).
    fn rewriter(&self, t: &Signature<N>) -> u32 {
        let m = mask(&t.mono);
        let mut best = NONE;
        for &(sig_mask, id) in &self.by_index[t.index as usize] {
            let divisible =
                sig_mask & !m == 0 && divides(&self.basis[id as usize].sig.mono, &t.mono);
            #[cfg(feature = "research-sigf4-usage")]
            self.usage.report.rewriter_scan(divisible);
            if !divisible {
                continue;
            }
            if best == NONE || self.ratio_cmp(id, best) != Ordering::Less {
                best = id;
            }
        }
        #[cfg(feature = "research-sigf4-usage")]
        self.usage.report.rewriter_returned(best);
        best
    }

    /// The least-signature reducer multiple for column `id`, i.e. the least-ratio element whose
    /// lead divides its monomial. Cached per monomial; only elements added since are rescanned.
    fn reducer(&mut self, id: u32) -> u32 {
        let cached = self.table.reducer(id);
        let m = self.table.mono(id);
        let (best, total) = least_ratio(&self.basis, &self.lead_masks, self.order, m, Some(cached));
        let scanned = cached.1;
        if scanned < total {
            self.table.set_reducer(id, (best, total));
        }
        #[cfg(feature = "research-sigf4-usage")]
        self.usage
            .report
            .reducer(best, total.saturating_sub(scanned), self.stats.batches - 1);
        best
    }

    fn reject_by_syzygy(&mut self, t: &Signature<N>) -> bool {
        #[cfg(feature = "research-sigf4-usage")]
        self.usage.ops.push(super::usage::StoreOp::Query(*t));
        match self.syzygies.covering(t) {
            Some(SyzygySource::Koszul) => self.stats.rejected_koszul += 1,
            Some(SyzygySource::ZeroRow) => self.stats.rejected_zero_row += 1,
            None => return false,
        }
        true
    }

    /// Selects this degree's targets, builds and eliminates the matrix, and adds new elements.
    /// True if the ideal turned out to be the whole ring.
    fn batch(&mut self, mut entries: Vec<Pending<N>>) -> Result<bool, SigF4Error> {
        let clock = Instant::now();
        #[cfg(feature = "research-sigf4-usage")]
        let before = (self.stats.symbolic, self.stats.elimination);
        let order = self.order;
        entries.sort_by(|a, b| a.sig.cmp_in(&b.sig, order));
        let mut targets: Vec<Row<N>> = Vec::new();
        let mut start = 0;
        while start < entries.len() {
            let mut end = start + 1;
            while end < entries.len() && entries[end].sig == entries[start].sig {
                end += 1;
            }
            let group = &entries[start..end];
            let t = group[0].sig;
            start = end;
            if self.reject_by_syzygy(&t) {
                self.stats.rejected_duplicate += group.len() - 1;
                continue;
            }
            if let Some(i) = group.iter().find_map(|p| match p.source {
                Source::Input(i) => Some(i as usize),
                Source::Pair { .. } => None,
            }) {
                self.stats.rejected_duplicate += group.len() - 1;
                targets.push(Row {
                    sig: t,
                    mult: Monomial::one(),
                    source: RowSource::Input(i),
                });
                continue;
            }
            let rewriter = self.rewriter(&t);
            let mut kept = None;
            for p in group {
                let Source::Pair { element, other } = p.source else {
                    continue;
                };
                let passes = element == rewriter && {
                    let (e, o) = (&self.basis[element as usize], &self.basis[other as usize]);
                    let other_mult = Monomial::lcm(&e.lead, &o.lead)
                        .checked_div(&o.lead)
                        .expect("lcm");
                    let other_sig = o.sig.times(&other_mult);
                    self.rewriter(&other_sig) == other
                };
                if !passes {
                    self.stats.rejected_rewrite += 1;
                } else if kept.is_some() {
                    self.stats.rejected_duplicate += 1;
                } else {
                    kept = Some(element);
                    #[cfg(feature = "research-sigf4-usage")]
                    self.usage.report.partner(other);
                }
            }
            if let Some(element) = kept {
                let mult = t
                    .mono
                    .checked_div(&self.basis[element as usize].sig.mono)
                    .expect("the element's signature divides the pair's");
                targets.push(Row {
                    sig: t,
                    mult,
                    source: RowSource::Element(element),
                });
            }
        }
        self.stats.bookkeeping += clock.elapsed();
        #[cfg(feature = "research-sigf4-usage")]
        let select = clock.elapsed();
        if targets.is_empty() {
            return Ok(false);
        }
        #[cfg(feature = "research-sigf4-usage")]
        for t in &targets {
            if let RowSource::Element(id) = t.source {
                self.usage.report.target(id, self.stats.batches);
            }
        }
        self.stats.batches += 1;
        self.stats.targets += targets.len();

        let (columns, rows, handles, reducer_count) = self.symbolic(&targets)?;
        let new = self.eliminate(&columns, &rows, handles, reducer_count, targets.len())?;

        let clock = Instant::now();
        if self.options.check_signatures {
            for (sig, terms) in &new {
                self.check_new_element(sig, &terms[0].0);
            }
        }
        #[cfg(feature = "research-sigf4-usage")]
        let mut batch_use = super::usage::BatchUse {
            degree: targets[0].sig.degree(),
            targets: targets.len(),
            elements_added: new.len(),
            select,
            symbolic: self.stats.symbolic - before.0,
            elimination: self.stats.elimination - before.1,
            ..Default::default()
        };
        for (sig, terms) in new {
            if terms[0].0.is_one() {
                self.stats.bookkeeping += clock.elapsed();
                return Ok(true);
            }
            #[cfg(feature = "research-sigf4-usage")]
            let (inserted, lead, len) = (Instant::now(), terms[0].0, terms.len());
            self.insert(sig, terms)?;
            #[cfg(feature = "research-sigf4-usage")]
            {
                batch_use.insert += inserted.elapsed();
                self.usage.born(lead, len, self.stats.batches - 1);
            }
        }
        self.stats.bookkeeping += clock.elapsed();
        #[cfg(feature = "research-sigf4-usage")]
        self.usage.report.batches.push(batch_use);
        Ok(false)
    }

    /// Columns (descending); rows, targets first in signature order, then reducers; and each
    /// row's column per term, in term order.
    ///
    /// Every term is looked up once, here, and keeps the handle the lookup gave it, so elimination
    /// builds its sparse rows by array lookup rather than hashing every term a second time.
    /// Handles are first-occurrence ids until the columns are sorted, then column positions.
    #[allow(clippy::type_complexity)]
    fn symbolic(
        &mut self,
        targets: &[Row<N>],
    ) -> Result<(Vec<Monomial<N>>, Vec<Row<N>>, Vec<Vec<u32>>, usize), SigF4Error> {
        #[cfg(feature = "research-sigf4-replay")]
        let before = symbolic_replay::active().then(|| self.table.reducer_map());
        #[cfg(feature = "research-sigf4-split")]
        let (mut split, mut scratch) = {
            let (cpu, khz_before) = super::SymbolicSplit::cpu_khz();
            let split = super::SymbolicSplit {
                cpu,
                khz_before,
                ..Default::default()
            };
            (split, Vec::new())
        };
        let clock = Instant::now();
        self.table.begin_batch();
        // Table ids in first-occurrence order: a term's handle indexes this until the sort.
        let mut work: Vec<u32> = Vec::new();
        let mut rows: Vec<Row<N>> = Vec::with_capacity(targets.len());
        let mut handles: Vec<Vec<u32>> = Vec::with_capacity(targets.len());
        for t in targets {
            rows.push(Row {
                sig: t.sig,
                mult: t.mult,
                source: t.source,
            });
            let (terms, hashes) = match t.source {
                RowSource::Input(i) => (&self.inputs[i], &self.input_hashes[i]),
                RowSource::Element(id) => {
                    let e = &self.basis[id as usize];
                    (&e.terms, &e.hashes)
                }
            };
            let hm = hash(&t.mult);
            #[cfg(not(feature = "research-sigf4-split"))]
            handles.push(
                terms
                    .iter()
                    .zip(hashes)
                    .map(|((m, _), &h)| {
                        self.table
                            .intern(*m * t.mult, h.wrapping_add(hm), &mut work)
                    })
                    .collect(),
            );
            #[cfg(feature = "research-sigf4-split")]
            {
                let mut row = Vec::with_capacity(terms.len());
                let products = terms.iter().map(|(m, _)| *m).zip(hashes.iter().copied());
                let table = &mut self.table;
                split.row(
                    &mut scratch,
                    products,
                    (t.mult, hm),
                    |m, h| table.intern(m, h, &mut work),
                    &mut row,
                );
                handles.push(row);
            }
        }
        let mut reducers = 0;
        let mut next = 0;
        while next < work.len() {
            let column = work[next];
            let lead = next as u32;
            next += 1;
            #[cfg(feature = "research-sigf4-split")]
            let search = Instant::now();
            let id = self.reducer(column);
            #[cfg(feature = "research-sigf4-split")]
            {
                split.reducer_search += search.elapsed();
                split.searches += 1;
            }
            if id == NONE {
                continue;
            }
            let e = &self.basis[id as usize];
            let mult = self
                .table
                .mono(column)
                .checked_div(&e.lead)
                .expect("the lead divides the column");
            // Additive: h(mult) = h(column) - h(lead).
            let hm = self.table.hash_of(column).wrapping_sub(e.hashes[0]);
            let sig = e.sig.times(&mult);
            let mut row = Vec::with_capacity(e.terms.len());
            row.push(lead);
            #[cfg(not(feature = "research-sigf4-split"))]
            for ((tm, _), &th) in e.terms[1..].iter().zip(&e.hashes[1..]) {
                row.push(
                    self.table
                        .intern(*tm * mult, th.wrapping_add(hm), &mut work),
                );
            }
            #[cfg(feature = "research-sigf4-split")]
            {
                let products = e.terms[1..]
                    .iter()
                    .map(|(m, _)| *m)
                    .zip(e.hashes[1..].iter().copied());
                let table = &mut self.table;
                split.row(
                    &mut scratch,
                    products,
                    (mult, hm),
                    |m, h| table.intern(m, h, &mut work),
                    &mut row,
                );
            }
            handles.push(row);
            rows.push(Row {
                sig,
                mult,
                source: RowSource::Element(id),
            });
            reducers += 1;
        }
        #[cfg(feature = "research-sigf4-split")]
        let sort = Instant::now();
        let order = self.order;
        let work: Vec<Monomial<N>> = work.iter().map(|&id| *self.table.mono(id)).collect();
        let mut by_position: Vec<u32> = (0..work.len() as u32).collect();
        by_position.sort_unstable_by(|&a, &b| order.cmp(&work[b as usize], &work[a as usize]));
        let mut position = vec![0u32; work.len()];
        for (k, &id) in by_position.iter().enumerate() {
            position[id as usize] = k as u32;
        }
        for row in &mut handles {
            for h in row.iter_mut() {
                *h = position[*h as usize];
            }
        }
        let columns: Vec<Monomial<N>> = by_position.iter().map(|&id| work[id as usize]).collect();
        #[cfg(feature = "research-sigf4-split")]
        {
            split.column_sort = sort.elapsed();
        }
        self.stats.reducer_rows += reducers;
        self.stats.max_matrix_rows = self.stats.max_matrix_rows.max(rows.len());
        self.stats.max_matrix_columns = self.stats.max_matrix_columns.max(columns.len());
        self.stats.symbolic += clock.elapsed();
        #[cfg(feature = "research-sigf4-split")]
        {
            split.total = clock.elapsed();
            split.khz_after = super::SymbolicSplit::cpu_khz().1;
            self.stats.split.symbolic.push(split);
        }
        #[cfg(feature = "research-sigf4-replay")]
        if let Some(before) = before {
            let view = symbolic_replay::View {
                order: self.order,
                basis: &self.basis,
                lead_masks: &self.lead_masks,
                inputs: &self.inputs,
            };
            let cache = self.table.reducer_map();
            let serial = (&columns[..], &rows[..], &handles[..], &cache);
            symbolic_replay::replay(view, targets, &before, serial, clock.elapsed());
        }
        if rows.len() > self.options.max_matrix_rows {
            return Err(SigF4Error::Budget(F4Error::TooManyRows {
                limit: self.options.max_matrix_rows,
            }));
        }
        if columns.len() > self.options.max_matrix_columns {
            return Err(SigF4Error::Budget(F4Error::TooManyColumns {
                limit: self.options.max_matrix_columns,
            }));
        }
        Ok((columns, rows, handles, reducers))
    }

    fn terms_of(&self, source: RowSource) -> &[(Monomial<N>, F)] {
        match source {
            RowSource::Input(i) => &self.inputs[i],
            RowSource::Element(id) => &self.basis[id as usize].terms,
        }
    }

    /// Regular elimination: each target, in increasing signature order, is fully reduced by
    /// pivots of strictly smaller signature — reducer multiples, or earlier targets of this batch
    /// (Lairez Algorithm 8 line 98). Returns the new elements in signature order.
    ///
    /// With `workers > 1` (design 2, RFC §6.1 item 1) every target is first reduced against the
    /// reducer block alone, in parallel: targets are independent there, and each pivot use is
    /// still checked against the target's signature. The serial pass then finishes each target in
    /// signature order against earlier targets' results, in place of §6.1 item 2's displacement
    /// claim. Both passes perform only permitted operations, so leads are those of the serial
    /// order (EF Lemma 4.10) and the engine stays deterministic.
    #[allow(clippy::type_complexity)]
    fn eliminate(
        &mut self,
        columns: &[Monomial<N>],
        rows: &[Row<N>],
        handles: Vec<Vec<u32>>,
        reducer_count: usize,
        target_count: usize,
    ) -> Result<Vec<(Signature<N>, Vec<(Monomial<N>, F)>)>, SigF4Error> {
        let clock = Instant::now();
        let order = self.order;
        if self.options.check_signatures {
            for (row, handles) in rows.iter().zip(&handles) {
                let terms = self.terms_of(row.source);
                assert_eq!(terms.len(), handles.len(), "one handle per term");
                for ((m, _), &h) in terms.iter().zip(handles) {
                    assert_eq!(
                        columns[h as usize],
                        *m * row.mult,
                        "a handle names its column"
                    );
                }
            }
        }
        let mut sparse_rows: Vec<Vec<(u32, F)>> = rows
            .iter()
            .zip(handles)
            .map(|(row, handles)| {
                handles
                    .into_iter()
                    .zip(self.terms_of(row.source))
                    .map(|(h, (_, c))| (h, *c))
                    .collect()
            })
            .collect();
        let ncols = columns.len();
        let mut reducer_at: Vec<u32> = vec![NONE; ncols];
        let reducer_rows: Vec<Vec<(u32, F)>> = sparse_rows.split_off(target_count);
        let reducer_sigs: Vec<Signature<N>> = rows[target_count..].iter().map(|r| r.sig).collect();
        let targets: Vec<(Signature<N>, Vec<(u32, F)>)> = rows[..target_count]
            .iter()
            .map(|r| r.sig)
            .zip(sparse_rows)
            .collect();
        debug_assert_eq!(reducer_rows.len(), reducer_count);
        for (k, entries) in reducer_rows.iter().enumerate() {
            reducer_at[entries[0].0 as usize] = k as u32;
        }

        let block = ReducerBlock {
            order,
            rows: &reducer_rows,
            sigs: &reducer_sigs,
            at: &reducer_at,
            ncols,
        };
        if self.options.parallel_cascade {
            return self.claim(&block, &targets, columns, clock);
        }
        #[cfg(feature = "research-sigf4-split")]
        let mut split = super::BatchSplit {
            targets: target_count,
            reducers: reducer_count,
            columns: ncols,
            entries: targets
                .iter()
                .map(|t| t.1.len() as u64)
                .chain(reducer_rows.iter().map(|r| r.len() as u64))
                .sum(),
            setup: clock.elapsed(),
            ..Default::default()
        };
        // Charged as the parallel cascade charges (#962): the rows, the pivot maps and every
        // workspace up front, then each reduced row as it is made. A crossing abandons the batch
        // before any of it is settled.
        let mut live = LiveBudget::new(self.options.max_live_bytes);
        let phase_a_workers = if self.options.workers > 1 {
            self.options.workers
        } else {
            0
        };
        let fixed = batch_rows_bytes(&block, &targets)
            + 2 * ncols * size_of::<u32>()
            + (1 + phase_a_workers) * Workspace::<F>::bytes(ncols);
        if let Err(stop) = live.charge(fixed) {
            return Err(self.abandon(&live, clock, stop));
        }
        #[cfg(feature = "research-sigf4-split")]
        let pass_clock = Instant::now();
        let prereduced: Vec<Reduced<F>> = if self.options.workers > 1 {
            let job = PhaseA {
                block: &block,
                targets: &targets,
                workers: self.options.workers,
            };
            match F::run_concurrent(job) {
                Ok(done) => done,
                Err(job) => job.serial(),
            }
        } else {
            Vec::new()
        };
        #[cfg(feature = "research-sigf4-split")]
        {
            split.parallel_pass = pass_clock.elapsed();
            split.parallel_products = prereduced.iter().map(|r| r.1).sum();
        }
        #[cfg(feature = "research-sigf4-split")]
        let pass_clock = Instant::now();
        let prereduced_bytes = prereduced
            .iter()
            .map(|(row, _)| std::mem::size_of_val(row.as_slice()))
            .sum::<usize>();
        if let Err(stop) = live.charge(prereduced_bytes) {
            return Err(self.abandon(&live, clock, stop));
        }
        let mut prereduced = prereduced.into_iter();

        let mut target_at: Vec<u32> = vec![NONE; ncols];
        // Every target's outcome in signature order; `target_at` indexes the elements among them.
        let mut finals: Vec<(Signature<N>, Kind, Vec<(u32, F)>, u64)> = Vec::new();
        let mut workspace = Workspace::new(ncols);
        let check = self.options.check_signatures;
        #[cfg(feature = "research-sigf4-replay")]
        let mut replay = super::replay::Recorder::new(ncols);
        for (t, raw) in &targets {
            let t = *t;
            let (entries, earlier) = prereduced.next().unwrap_or_else(|| (raw.clone(), 0));
            #[cfg(feature = "research-sigf4-split")]
            let mut cascade = 0u64;
            let (mut out, later) = workspace.reduce(&entries, |c| {
                let pivot = if let Some(pivot) = block.admissible(c, &t) {
                    Some(pivot)
                } else if target_at[c] != NONE {
                    let (s, _, entries, _) = &finals[target_at[c] as usize];
                    assert!(
                        !check || s.cmp_in(&t, order) == Ordering::Less,
                        "an earlier target must have a smaller signature"
                    );
                    #[cfg(feature = "research-sigf4-split")]
                    {
                        cascade += (entries.len() - 1) as u64;
                    }
                    Some(entries.as_slice())
                } else {
                    None
                };
                #[cfg(feature = "research-sigf4-replay")]
                replay.step(
                    c,
                    pivot.map(<[_]>::len),
                    pivot.is_some() && block.admissible(c, &t).is_none(),
                );
                pivot
            });
            #[cfg(feature = "research-sigf4-replay")]
            replay.end(earlier, out.first().map(|e| e.0));
            #[cfg(feature = "research-sigf4-split")]
            {
                split.cascade_products += cascade;
                split.serial_reducer_products += later - cascade;
                split.cascading_targets += usize::from(cascade > 0);
            }
            let kind = block.classify(&t, &out);
            if kind == Kind::Element {
                let inverse = out[0].1.inverse();
                for (_, v) in &mut out {
                    *v *= inverse;
                }
            }
            if let Err(stop) = live.charge(std::mem::size_of_val(out.as_slice())) {
                return Err(self.abandon(&live, clock, stop));
            }
            if kind == Kind::Element {
                target_at[out[0].0 as usize] = finals.len() as u32;
            }
            finals.push((t, kind, out, earlier + later));
        }
        #[cfg(feature = "research-sigf4-replay")]
        replay.finish();
        #[cfg(feature = "research-reuse")]
        self.census_reuse(&block, rows, &targets, &finals);
        #[cfg(feature = "research-sigf4-split")]
        {
            split.serial_pass = pass_clock.elapsed();
            self.stats.split.batches.push(split);
        }
        self.stats.claim_peak_live_bytes = self.stats.claim_peak_live_bytes.max(live.peak);
        let mut results = Vec::new();
        for (t, kind, row, products) in finals {
            self.settle(t, kind, &row, products, columns);
            if kind == Kind::Element {
                results.push((t, row));
            }
        }
        self.stats.elimination += clock.elapsed();
        Ok(finish_batch(results, columns))
    }

    /// #1031: census this batch's reducer reuse, with the engine's own product count beside it.
    #[cfg(feature = "research-reuse")]
    #[allow(clippy::type_complexity)]
    fn census_reuse(
        &mut self,
        block: &ReducerBlock<'_, N, F>,
        rows: &[Row<N>],
        targets: &[(Signature<N>, Vec<(u32, F)>)],
        finals: &[(Signature<N>, Kind, Vec<(u32, F)>, u64)],
    ) {
        use crate::grobner::reuse_census::{Reducer, Target};
        let Some(census) = self.reuse.as_mut() else {
            return;
        };
        let reducers: Vec<Reducer<'_, N, Signature<N>, F>> = rows[targets.len()..]
            .iter()
            .zip(block.rows)
            .map(|(row, entries)| {
                let RowSource::Element(element) = row.source else {
                    unreachable!("a reducer is a basis-element multiple")
                };
                Reducer {
                    element,
                    multiplier: row.mult,
                    lead: row.mult * self.basis[element as usize].lead,
                    signature: row.sig,
                    row: entries,
                }
            })
            .collect();
        let targets: Vec<Target<'_, Signature<N>, F>> = targets
            .iter()
            .map(|(signature, row)| Target {
                signature: *signature,
                row,
            })
            .collect();
        let order = self.order;
        let cmp = move |a: &Signature<N>, b: &Signature<N>| a.cmp_in(b, order);
        let live = finals.iter().map(|f| f.3).sum();
        census.observe(block.ncols, &reducers, &targets, Some(&cmp), Some(live));
    }

    /// Records a serial batch abandoned on its live budget, whole and before any settlement.
    fn abandon(&mut self, live: &LiveBudget, clock: Instant, stop: SigF4Error) -> SigF4Error {
        self.stats.claim_peak_live_bytes = self.stats.claim_peak_live_bytes.max(live.peak);
        self.stats.elimination += clock.elapsed();
        stop
    }

    /// The parallel cascade (M31-S2): #902's prereduce + claim schedule, then design 1's
    /// accounting in signature order. A stopped batch is abandoned whole, before any insertion.
    #[allow(clippy::type_complexity)]
    fn claim(
        &mut self,
        block: &ReducerBlock<'_, N, F>,
        targets: &[(Signature<N>, Vec<(u32, F)>)],
        columns: &[Monomial<N>],
        clock: Instant,
    ) -> Result<Vec<(Signature<N>, Vec<(Monomial<N>, F)>)>, SigF4Error> {
        let rows_bytes = batch_rows_bytes(block, targets);
        let job = Claim {
            block,
            targets,
            workers: self.options.workers.max(1),
            check: self.options.check_signatures,
            deadline: self.wall.map(|(start, budget)| start + budget),
            live_limit: self.options.max_live_bytes,
            fixed_bytes: rows_bytes,
            #[cfg(test)]
            adversary: self.options.adversary,
        };
        let done = match F::run_concurrent(job) {
            Ok(done) => done,
            Err(job) => job.serial(),
        };
        let report = match done {
            Ok(report) => report,
            Err(stop) => {
                self.stats.elimination += clock.elapsed();
                return Err(SigF4Error::Budget(match stop {
                    Stop::Wall => {
                        // Without a budget only the tests' adversary stops a batch on the wall.
                        let (start, budget) = self.wall.unwrap_or((clock, Duration::ZERO));
                        F4Error::TimeBudgetExceeded {
                            degree: targets[0].0.degree(),
                            elapsed_millis: millis(start.elapsed()),
                            budget_millis: millis(budget),
                        }
                    }
                    Stop::LiveBytes { bytes, limit } => F4Error::TooManyLiveBytes { bytes, limit },
                }));
            }
        };
        self.stats.claim_announcement_waits += report.announcement_waits;
        self.stats.claim_final_waits += report.final_waits;
        self.stats.claim_phase_a += report.phase_a;
        self.stats.claim_cascade += report.cascade;
        self.stats.claim_peak_live_bytes =
            self.stats.claim_peak_live_bytes.max(report.peak_live_bytes);
        let mut results = Vec::new();
        for ((t, _), outcome) in targets.iter().zip(report.outcomes) {
            self.settle(*t, outcome.kind, &outcome.row, outcome.products, columns);
            if outcome.kind == Kind::Element {
                results.push((*t, outcome.row));
            }
        }
        self.stats.elimination += clock.elapsed();
        Ok(finish_batch(results, columns))
    }

    /// Design 1's per-target accounting: a zero row records its syzygy signature (RFC T6), a
    /// singular row is discarded (EF Lemma 5.1), an element joins the batch's results.
    fn settle(
        &mut self,
        t: Signature<N>,
        kind: Kind,
        row: &[(u32, F)],
        products: u64,
        columns: &[Monomial<N>],
    ) {
        self.stats.coefficient_products += products;
        match kind {
            Kind::Zero => {
                self.stats.reductions_to_zero += 1;
                self.stats.zero_rows += 1;
                self.stats.rows_adding_no_rank += 1;
                self.stats.products_on_zero_rows += products;
                #[cfg(feature = "research-sigf4-usage")]
                self.usage
                    .ops
                    .push(super::usage::StoreOp::Insert(t, SyzygySource::ZeroRow));
                self.syzygies.insert(t, SyzygySource::ZeroRow);
            }
            Kind::Singular => {
                self.stats.singular_rows += 1;
                self.stats.rows_adding_no_rank += 1;
                self.stats.products_on_singular_rows += products;
            }
            Kind::Element => {
                #[cfg(feature = "research-sigf4-split")]
                self.stats.split.element_products.push(products);
            }
        }
        #[cfg(test)]
        {
            let terms: Vec<String> = row
                .iter()
                .map(|(c, v)| format!("{v}*{:?}", columns[*c as usize]))
                .collect();
            if self.stats.batch_trace.len() < self.stats.batches {
                self.stats.batch_trace.push(Vec::new());
            }
            self.stats
                .batch_trace
                .last_mut()
                .expect("pushed above")
                .push(format!("{t:?} {kind:?} [{}]", terms.join(", ")));
        }
        #[cfg(not(test))]
        let _ = (row, columns);
    }

    /// Adds `(sig, terms)` to the basis, recording Koszul syzygies and the new pairs.
    fn insert(
        &mut self,
        sig: Signature<N>,
        terms: Vec<(Monomial<N>, F)>,
    ) -> Result<(), SigF4Error> {
        let lead = terms[0].0;
        let id = self.basis.len() as u32;
        let order = self.order;
        for g in 0..self.basis.len() {
            let (g_sig, g_lead) = (self.basis[g].sig, self.basis[g].lead);
            let k_new = sig.times(&g_lead);
            let k_old = g_sig.times(&lead);
            match k_new.cmp_in(&k_old, order) {
                Ordering::Greater => self.syzygies.insert(k_new, SyzygySource::Koszul),
                Ordering::Less => self.syzygies.insert(k_old, SyzygySource::Koszul),
                Ordering::Equal => false,
            };
            #[cfg(feature = "research-sigf4-usage")]
            if k_new != k_old {
                let k = if k_new.cmp_in(&k_old, order) == Ordering::Greater {
                    k_new
                } else {
                    k_old
                };
                self.usage
                    .ops
                    .push(super::usage::StoreOp::Insert(k, SyzygySource::Koszul));
            }

            let lcm = Monomial::lcm(&lead, &g_lead);
            let u = lcm.checked_div(&lead).expect("lcm");
            let v = lcm.checked_div(&g_lead).expect("lcm");
            let (su, sv) = (sig.times(&u), g_sig.times(&v));
            let source = match su.cmp_in(&sv, order) {
                Ordering::Equal => {
                    self.stats.pairs_singular += 1;
                    continue;
                }
                Ordering::Greater => (su, id, g as u32),
                Ordering::Less => (sv, g as u32, id),
            };
            self.stats.pairs_created += 1;
            if gcd_is_one(&lead, &g_lead) {
                self.stats.rejected_product += 1;
                continue;
            }
            let (t, element, other) = source;
            if self.reject_by_syzygy(&t) {
                continue;
            }
            self.push(Pending {
                sig: t,
                source: Source::Pair { element, other },
            });
        }
        self.by_index[sig.index as usize].push((mask(&sig.mono), id));
        self.lead_masks.push(mask(&lead));
        let hashing = Instant::now();
        let hashes = terms.iter().map(|(m, _)| hash(m)).collect();
        self.stats.element_hashing += hashing.elapsed();
        self.basis.push(Element {
            sig,
            lead,
            terms,
            hashes,
        });
        self.stats.elements_added += 1;
        if let Some(limit) = self.options.max_basis_elements {
            if self.basis.len() > limit {
                return Err(SigF4Error::Budget(F4Error::TooManyBasisElements {
                    elements: self.basis.len(),
                    limit,
                }));
            }
        }
        Ok(())
    }

    /// RFC §4's invariants for a new element, checked against the basis before its batch (Lairez
    /// reduces by this batch's results unmultiplied only): its lead is at most its shifted
    /// signature monomial (Schreyer), and no element top-reduces it with a smaller or equal
    /// signature.
    fn check_new_element(&self, sig: &Signature<N>, lead: &Monomial<N>) {
        assert_ne!(
            self.order.cmp(lead, &sig.mono),
            Ordering::Greater,
            "a lead above its shifted signature means a reduction raised the signature"
        );
        for e in &self.basis {
            if let Some(mult) = lead.checked_div(&e.lead) {
                assert_eq!(
                    e.sig.times(&mult).cmp_in(sig, self.order),
                    Ordering::Greater,
                    "a new element must be regular top-irreducible and not singular"
                );
            }
        }
    }
}

/// The batch's sparse rows, targets and reducers, already allocated when elimination starts.
fn batch_rows_bytes<const N: usize, F>(
    block: &ReducerBlock<'_, N, F>,
    targets: &[(Signature<N>, Vec<(u32, F)>)],
) -> usize {
    (targets.iter().map(|(_, r)| r.len()).sum::<usize>()
        + block.rows.iter().map(Vec::len).sum::<usize>())
        * size_of::<(u32, F)>()
}

/// The serial cascade's live-byte account, in the parallel cascade's units (#962): crossing the
/// limit is [`F4Error::TooManyLiveBytes`], which the dispatch falls back from.
struct LiveBudget {
    live: usize,
    peak: usize,
    limit: Option<usize>,
}

impl LiveBudget {
    fn new(limit: Option<usize>) -> Self {
        Self {
            live: 0,
            peak: 0,
            limit,
        }
    }

    fn charge(&mut self, bytes: usize) -> Result<(), SigF4Error> {
        self.live = self.live.saturating_add(bytes);
        self.peak = self.peak.max(self.live);
        match self.limit {
            Some(limit) if self.live > limit => {
                Err(SigF4Error::Budget(F4Error::TooManyLiveBytes {
                    bytes: self.live,
                    limit,
                }))
            }
            _ => Ok(()),
        }
    }
}

#[allow(clippy::type_complexity)]
fn finish_batch<const N: usize, F: FiniteField>(
    results: Vec<(Signature<N>, Vec<(u32, F)>)>,
    columns: &[Monomial<N>],
) -> Vec<(Signature<N>, Vec<(Monomial<N>, F)>)> {
    results
        .into_iter()
        .map(|(sig, entries)| {
            let terms = entries
                .into_iter()
                .map(|(c, v)| (columns[c as usize], v))
                .collect();
            (sig, terms)
        })
        .collect()
}

/// The batch's reducer multiples, one per lead column, with their signatures.
pub(super) struct ReducerBlock<'a, const N: usize, F> {
    pub(super) order: MonomialOrder,
    pub(super) rows: &'a [Vec<(u32, F)>],
    pub(super) sigs: &'a [Signature<N>],
    pub(super) at: &'a [u32],
    pub(super) ncols: usize,
}

impl<const N: usize, F> ReducerBlock<'_, N, F> {
    /// How target `t` ended with `row`: zero, singular (its lead's reducer has signature exactly
    /// `t`, EF Lemma 5.1) or a new element.
    pub(super) fn classify(&self, t: &Signature<N>, row: &[(u32, F)]) -> Kind {
        let Some(&(lead, _)) = row.first() else {
            return Kind::Zero;
        };
        let r = self.at[lead as usize];
        if r != NONE && self.sigs[r as usize] == *t {
            Kind::Singular
        } else {
            Kind::Element
        }
    }

    /// The reducer at column `c` if its signature is strictly below `t`.
    pub(super) fn admissible(&self, c: usize, t: &Signature<N>) -> Option<&[(u32, F)]> {
        let r = self.at[c];
        (r != NONE && self.sigs[r as usize].cmp_in(t, self.order) == Ordering::Less)
            .then(|| self.rows[r as usize].as_slice())
    }
}

/// A dense accumulator with a bitset of possibly-nonzero columns, reused across rows.
pub(super) struct Workspace<F> {
    acc: Vec<F>,
    touched: Vec<u64>,
}

impl<F> Workspace<F> {
    /// What one workspace over `ncols` columns holds, as the live budget charges it.
    pub(super) fn bytes(ncols: usize) -> usize {
        ncols * size_of::<F>() + ncols.div_ceil(64) * size_of::<u64>()
    }
}

impl<F: FiniteField> Workspace<F> {
    pub(super) fn new(ncols: usize) -> Self {
        Self {
            acc: vec![F::zero(); ncols],
            touched: vec![0; ncols.div_ceil(64)],
        }
    }

    /// Reduces `entries` column by column with whatever `pivot` offers (monic rows, lead first);
    /// returns the remaining entries in column order and the multiply-accumulates spent. Pivot
    /// tails only reach columns to the right, so a column is final once passed.
    pub(super) fn reduce<'p>(
        &mut self,
        entries: &[(u32, F)],
        mut pivot: impl FnMut(usize) -> Option<&'p [(u32, F)]>,
    ) -> Reduced<F>
    where
        F: 'p,
    {
        let Some(&(first, _)) = entries.first() else {
            return (Vec::new(), 0);
        };
        for &(c, v) in entries {
            let c = c as usize;
            self.acc[c] = v;
            self.touched[c >> 6] |= 1 << (c & 63);
        }
        let words = self.touched.len();
        let mut products = 0u64;
        let mut out = Vec::new();
        let mut w = first as usize >> 6;
        // #1033's density trace: exact nonzeros at or right of the current column.
        #[cfg(feature = "research-work")]
        let (ncols, mut nonzeros, mut applied) = (self.acc.len(), entries.len(), 0usize);
        #[cfg(feature = "research-work")]
        crate::linalg::work::density_intake(nonzeros, first as usize, ncols);
        while w < words {
            let bits = self.touched[w];
            if bits == 0 {
                w += 1;
                continue;
            }
            let c = (w << 6) | bits.trailing_zeros() as usize;
            self.touched[w] &= bits - 1;
            let coefficient = std::mem::replace(&mut self.acc[c], F::zero());
            if coefficient.is_zero() {
                continue;
            }
            match pivot(c) {
                Some(row) => {
                    #[cfg(feature = "research-work")]
                    {
                        crate::linalg::work::density_application(
                            nonzeros,
                            c,
                            ncols,
                            applied,
                            row.len() - 1,
                        );
                        applied += 1;
                        nonzeros -= 1;
                    }
                    let factor = coefficient.prepare_factor();
                    for (cc, v) in &row[1..] {
                        let cc = *cc as usize;
                        #[cfg(feature = "research-work")]
                        let before = self.acc[cc].is_zero();
                        self.acc[cc] -= v.mul_prepared(&factor);
                        #[cfg(feature = "research-work")]
                        {
                            nonzeros += usize::from(before);
                            nonzeros -= usize::from(self.acc[cc].is_zero());
                        }
                        self.touched[cc >> 6] |= 1 << (cc & 63);
                    }
                    products += (row.len() - 1) as u64;
                }
                None => {
                    #[cfg(feature = "research-work")]
                    {
                        nonzeros -= 1;
                    }
                    out.push((c as u32, coefficient))
                }
            }
        }
        #[cfg(feature = "research-work")]
        {
            debug_assert_eq!(nonzeros, 0);
            crate::linalg::work::density_end(
                out.len(),
                out.first().map_or(0, |e| e.0 as usize),
                ncols,
            );
        }
        (out, products)
    }
}

/// Design 2's parallel pass: every target reduced against the reducer block only.
struct PhaseA<'a, const N: usize, F> {
    block: &'a ReducerBlock<'a, N, F>,
    targets: &'a [(Signature<N>, Vec<(u32, F)>)],
    workers: usize,
}

impl<const N: usize, F: FiniteField> PhaseA<'_, N, F> {
    fn reduce_one(&self, workspace: &mut Workspace<F>, k: usize) -> Reduced<F> {
        let (t, entries) = &self.targets[k];
        workspace.reduce(entries, |c| self.block.admissible(c, t))
    }

    /// The same pass on one thread, for a field that cannot cross threads.
    fn serial(self) -> Vec<Reduced<F>> {
        let mut workspace = Workspace::new(self.block.ncols);
        (0..self.targets.len())
            .map(|k| self.reduce_one(&mut workspace, k))
            .collect()
    }
}

impl<const N: usize, F: FiniteField> ConcurrentJob<F> for PhaseA<'_, N, F> {
    type Output = Vec<Reduced<F>>;

    fn run(self) -> Self::Output
    where
        F: Send + Sync,
    {
        let n = self.targets.len();
        let workers = self.workers.min(n).max(1);
        let next = AtomicUsize::new(0);
        let slots: Vec<Mutex<Option<Reduced<F>>>> = (0..n).map(|_| Mutex::new(None)).collect();
        std::thread::scope(|scope| {
            let mut members = Vec::new();
            for _ in 0..workers {
                members.push(crate::util::team::spawn(scope, || {
                    let mut workspace = Workspace::new(self.block.ncols);
                    loop {
                        let k = next.fetch_add(1, AtomicOrdering::Relaxed);
                        if k >= n {
                            break;
                        }
                        let done = self.reduce_one(&mut workspace, k);
                        *slots[k].lock().expect("a slot is never poisoned") = Some(done);
                    }
                }));
            }
            crate::util::team::join_all(members);
        });
        slots
            .into_iter()
            .map(|slot| {
                slot.into_inner()
                    .expect("a slot is never poisoned")
                    .expect("every target was reduced")
            })
            .collect()
    }
}

#[cfg(all(test, feature = "research-work"))]
mod density_tests {
    use super::Workspace;
    use crate::{fields::Zp13, linalg::work::measure, FiniteField};

    type F = Zp13;

    /// #1033: the signature workspace files each application's products under the remaining
    /// span's density before it, counting the products it reports, and records intake and end.
    #[test]
    fn test_density_trace_buckets_signature_reduction_products() {
        let pivot: Vec<(u32, F)> = (0..10).map(|c| (c, F::new(1))).collect();
        let ((out, products), report) = measure(|| {
            let mut workspace = Workspace::<F>::new(10);
            // Two nonzeros over ten columns from column 0: 20%, bucket 4 of 20.
            workspace.reduce(&[(0, F::new(1)), (1, F::new(1))], |c| {
                (c == 0).then_some(pivot.as_slice())
            })
        });
        assert_eq!(products, 9, "the pivot's tail");
        // Column 1 cancels; columns 2..9 hold -1 and are unpivoted.
        assert_eq!(out.len(), 8);
        let trace = &report.outside_batch.forward_density;
        assert_eq!(trace.products_by_span[4], 9);
        assert_eq!(trace.products_by_span.iter().sum::<usize>(), 9);
        assert_eq!(trace.rows_at_checkpoint[0][4], 1, "intake at 20%");
        // The row leaves with 8 nonzeros from column 2: 8 of 8, the top bucket.
        assert_eq!(trace.rows_at_end[19], 1);
    }
}
