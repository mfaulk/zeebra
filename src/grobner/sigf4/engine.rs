//! The batched F4-RB main loop (RFC §9 design 1; Lairez Algorithm 8, EF Algorithm 4).

use std::{
    cmp::Ordering,
    collections::{BTreeMap, HashSet},
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
    fields::{ConcurrentJob, PreparedFactor},
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
    linalg::lane::{Lane, LaneKernel, LaneRow, LaneWorkspace},
    poly::MonomialOrder,
    FiniteField, Monomial, MultivariatePolynomial,
};

#[cfg(feature = "research-sigf4-replay")]
#[path = "symbolic_replay.rs"]
pub mod symbolic_replay;

#[path = "interreduce.rs"]
mod columns;

#[path = "lead_ideal.rs"]
mod lead_ideal;

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
#[derive(Clone, Copy, Debug)]
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

/// #1075's buffer key for a row source: inputs with the top bit set, elements by id.
#[cfg(feature = "research-adjacent")]
fn source_key(source: RowSource) -> super::adjacent::SourceKey {
    match source {
        RowSource::Input(i) => i as u64 | 1 << 63,
        RowSource::Element(id) => u64::from(id),
    }
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
    /// Per element, its place in the sig-lead ratio order (`ratio_cmp`), equal ratios sharing
    /// one: comparing two ratios is one integer comparison (Roune–Stillman 2012 §3.4).
    ratio_rank: Vec<u32>,
    /// The elements in ascending ratio order, to place the next one.
    by_ratio: Vec<u32>,
    syzygies: SyzygyStore<N>,
    queue: BTreeMap<u64, Vec<Pending<N>>>,
    pending: usize,
    /// Elements inserted with a lead no earlier lead divides (#1140).
    new_leads: usize,
    /// Every column monomial of the run, with its least-ratio reducer search cached.
    table: MonomialTable<N>,
    wall: Option<(Instant, Duration)>,
    stats: &'a mut SigF4Statistics,
    #[cfg(feature = "research-sigf4-usage")]
    usage: super::usage::UsageLog<N>,
    #[cfg(feature = "research-reuse")]
    reuse: Option<crate::grobner::reuse_census::ReuseCensus<N, Signature<N>>>,
    #[cfg(feature = "research-adjacent")]
    adjacent: Option<super::adjacent::Adjacent<N>>,
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
        ratio_rank: Vec::new(),
        by_ratio: Vec::new(),
        syzygies: SyzygyStore::new(inputs.len()),
        basis: Vec::new(),
        lead_masks: Vec::new(),
        queue: BTreeMap::new(),
        pending: 0,
        new_leads: 0,
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
        #[cfg(feature = "research-adjacent")]
        adjacent: super::adjacent::Adjacent::new(options.adjacent, options.adjacent_budget),
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
    let mut stop = lead_ideal::LeadIdealStop::new(order, options.lead_ideal_stop);
    let mut early = None;
    #[cfg(feature = "research-sigf4")]
    let mut carried: Option<(u64, Vec<MultivariatePolynomial<N, F>>)> = None;
    #[cfg(feature = "research-sigf4")]
    let mut carry_stop = options.carry.map(super::carry::CarryStop::new);
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
        stop.observe(degree, engine.new_leads);
        if engine.batch(entries)? {
            inconsistent = true;
            break;
        }
        let next = engine.queue.keys().next().copied();
        if stop.due(engine.new_leads, next, engine.pending) {
            early = Some(engine.hand_off(generators, wall)?);
            break;
        }
        #[cfg(feature = "research-sigf4")]
        if let Some(carry) = carry_stop.as_mut().and_then(|stop| {
            stop.due(degree, next, || engine.minimal_lead_count())
                .then_some(stop.carry)
        }) {
            let mut seed = match carry.mode {
                super::carry::CarryMode::Restart => Vec::new(),
                super::carry::CarryMode::Continue => engine.minimal_elements(),
            };
            seed.extend(generators.iter().cloned());
            carried = Some((degree, seed));
            break;
        }
    }
    #[cfg(feature = "research-sigf4")]
    if let Some((degree, seed)) = carried.take() {
        let signature_elements = engine.basis.len();
        drop(engine);
        let prefix = started.elapsed();
        let clock = std::time::Instant::now();
        let remaining = wall.map(|(start, budget)| budget.saturating_sub(start.elapsed()));
        let f4_options = super::carry::conventional_options(options, remaining);
        let (result, f4_stats) = crate::grobner::f4::f4_reported(&seed, order, &f4_options);
        stats.carry = Some(super::carry::CarryReport {
            degree,
            seed: seed.len(),
            signature_elements,
            prefix,
            conventional: clock.elapsed(),
            conventional_batches: f4_stats.batches,
        });
        let reduced = result.map_err(SigF4Error::Budget)?;
        stats.reduced_basis_elements = reduced.len();
        return certified(generators, reduced, order, options, stats, started);
    }

    // Interreduce from the engine's rows (G2-2); a budget refusal falls back to the polynomial
    // route below, which materializes the whole signature basis first.
    let interreduction = Instant::now();
    let direct = if inconsistent || early.is_some() {
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
    let materialized = (direct.is_none() && early.is_none())
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
    #[cfg(feature = "research-adjacent")]
    if let Some(census) = engine.adjacent.take() {
        engine.stats.adjacent = census.batches;
    }
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
    let (reduced, matrix) = match (early, direct) {
        (Some(reduced), _) => (reduced, MatrixInterreductionReport::default()),
        (None, Some(done)) => done,
        (None, None) => {
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

    certified(generators, reduced, order, options, stats, started)
}

/// Certifies `reduced` when `options.certify` asks, then records the run's total wall.
fn certified<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    reduced: Vec<MultivariatePolynomial<N, F>>,
    order: MonomialOrder,
    options: &SigF4Options,
    stats: &mut SigF4Statistics,
    started: Instant,
) -> Result<Vec<MultivariatePolynomial<N, F>>, SigF4Error> {
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

/// `a / gcd(a, b)`, which is `lcm(a, b) / b`.
fn quotient_by_gcd<const N: usize>(a: &Monomial<N>, b: &Monomial<N>) -> Monomial<N> {
    let mut q = *a;
    for (x, y) in q.exponents.iter_mut().zip(b.exponents()) {
        *x = x.saturating_sub(*y);
    }
    q
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
        #[cfg(test)]
        self.stats
            .pair_trace
            .push(format!("{:?} {:?}", pending.sig, pending.source));
        self.queue
            .entry(pending.sig.degree())
            .or_default()
            .push(pending);
        self.pending += 1;
        self.stats.peak_pending = self.stats.peak_pending.max(self.pending);
    }

    /// `ratio_cmp(a, b)` from the ranks; by cross-multiplication under the test-only reference.
    fn newer_ratio_cmp(&self, a: u32, b: u32) -> Ordering {
        #[cfg(test)]
        if self.options.reference_pairs {
            return ratio_cmp(&self.basis, self.order, a, b);
        }
        self.ratio_rank[a as usize].cmp(&self.ratio_rank[b as usize])
    }

    /// Places a new element, `(sig, lead)`, in the ratio order and ranks it, before it joins the
    /// basis. Ranks at or above a new distinct ratio's move up by one.
    fn rank(&mut self, sig: &Signature<N>, lead: &Monomial<N>) {
        let order = self.order;
        let basis = &self.basis;
        let cmp = |id: u32| {
            let e = &basis[id as usize];
            order
                .cmp(&(e.sig.mono * *lead), &(sig.mono * e.lead))
                .then(e.sig.index.cmp(&sig.index))
        };
        let at = self
            .by_ratio
            .partition_point(|&id| cmp(id) == Ordering::Less);
        let rank = match self.by_ratio.get(at) {
            Some(&next) if cmp(next) == Ordering::Equal => self.ratio_rank[next as usize],
            Some(&next) => {
                let rank = self.ratio_rank[next as usize];
                for r in &mut self.ratio_rank {
                    *r += u32::from(*r >= rank);
                }
                rank
            }
            None => self
                .by_ratio
                .last()
                .map_or(0, |&id| self.ratio_rank[id as usize] + 1),
        };
        if self.options.check_signatures {
            for id in 0..self.basis.len() as u32 {
                assert_eq!(
                    self.ratio_rank[id as usize].cmp(&rank),
                    cmp(id),
                    "a ratio rank disagrees with the ratios"
                );
            }
        }
        self.by_ratio.insert(at, self.basis.len() as u32);
        self.ratio_rank.push(rank);
    }

    /// The canonical rewriter of `t`: the `⊴_rat`-maximal element whose signature divides `t`
    /// (EF Def 7.1, 7.13), i.e. the **greatest** sig-lead ratio, whose multiple at `t` has the
    /// smallest lead; the newest on a tie. Greatest, not least: an element reduced from a multiple
    /// of `α` has a larger ratio than `α` and must supersede it, which the least-ratio choice
    /// does not (it lost pairs on katsura-4).
    fn rewriter(&mut self, t: &Signature<N>) -> u32 {
        let m = mask(&t.mono);
        let mut best = NONE;
        let candidates = &self.by_index[t.index as usize];
        let mut tests = 0;
        for &(sig_mask, id) in candidates {
            let passes = sig_mask & !m == 0;
            tests += u64::from(passes);
            let divisible = passes && divides(&self.basis[id as usize].sig.mono, &t.mono);
            #[cfg(feature = "research-sigf4-usage")]
            self.usage.report.rewriter_scan(divisible);
            if !divisible {
                continue;
            }
            if best == NONE || self.newer_ratio_cmp(id, best) != Ordering::Less {
                best = id;
            }
        }
        let work = &mut self.stats.pair_work;
        work.rewriter_calls += 1;
        work.rewriter_scanned += candidates.len() as u64;
        work.rewriter_divisibility += tests;
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

    /// The syzygy criterion, counted with the pair-creation queries or the selection ones.
    fn reject_by_syzygy(&mut self, t: &Signature<N>, at_creation: bool) -> bool {
        #[cfg(feature = "research-sigf4-usage")]
        self.usage.ops.push(super::usage::StoreOp::Query(*t));
        let work = &mut self.stats.pair_work;
        let work = if at_creation {
            &mut work.creation_queries
        } else {
            &mut work.selection_queries
        };
        match self.syzygies.covering_counted(t, work) {
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
            if self.reject_by_syzygy(&t, false) {
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
        let select = clock.elapsed();
        self.stats.bookkeeping += select;
        self.stats.bookkeeping_select += select;
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
        #[cfg(test)]
        self.stats.batch_degrees.push(targets[0].sig.degree());
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
            #[cfg(feature = "research-adjacent")]
            if let Some(adjacent) = self.adjacent.as_mut() {
                let mut row = Vec::with_capacity(terms.len());
                let products = terms.iter().map(|(m, _)| *m).zip(hashes.iter().copied());
                let key = (source_key(t.source), t.mult);
                adjacent.row(
                    &mut self.table,
                    key,
                    products,
                    (t.mult, hm),
                    None,
                    &mut work,
                    &mut row,
                );
                handles.push(row);
                continue;
            }
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
            #[cfg(feature = "research-adjacent")]
            if let Some(adjacent) = self.adjacent.as_mut() {
                let products = e
                    .terms
                    .iter()
                    .map(|(m, _)| *m)
                    .zip(e.hashes.iter().copied());
                let key = (source_key(RowSource::Element(id)), mult);
                let lead = Some(column);
                adjacent.row(
                    &mut self.table,
                    key,
                    products,
                    (mult, hm),
                    lead,
                    &mut work,
                    &mut row,
                );
                handles.push(row);
                rows.push(Row {
                    sig,
                    mult,
                    source: RowSource::Element(id),
                });
                reducers += 1;
                continue;
            }
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
        #[cfg(feature = "research-adjacent")]
        if let Some(adjacent) = self.adjacent.as_mut() {
            adjacent.finish();
            adjacent.record(clock.elapsed().as_nanos() as u64);
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

    /// #1078: the configured row layout where the serial cascade at one worker reduces without a
    /// lane, or a research census reads the field rows; the baseline everywhere else.
    fn row_layout(&self, lane_free: bool) -> super::layout::RowLayout {
        #[cfg(feature = "research-reuse")]
        let census = self.reuse.is_some();
        #[cfg(not(feature = "research-reuse"))]
        let census = false;
        let serial = self.options.workers <= 1 && !self.options.parallel_cascade;
        if lane_free && serial && !census {
            self.options.row_layout
        } else {
            super::layout::RowLayout::Baseline
        }
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
        let ncols = columns.len();
        // #945, #1183: the reducer block in lane form, when the options and the field allow it.
        // A field has at most one of the two lanes.
        let lane = if self.options.small_prime_lane {
            F::small_prime_lane()
        } else {
            None
        }
        .or_else(|| {
            if self.options.prime31_lane {
                F::prime31_lane()
            } else {
                None
            }
        });
        // #1078: the batch's own rows in the chosen layout.
        let arm = self.row_layout(lane.is_none());
        let narrow = arm.narrow() && ncols <= super::layout::U16_COLUMNS;
        let mut handles = handles;
        let reducer_handles = handles.split_off(target_count);
        #[cfg(any(feature = "research-sigf4", feature = "research-sigf4-split"))]
        let (target_entry_count, reducer_entry_count): (usize, usize) = (
            handles.iter().map(Vec::len).sum(),
            reducer_handles.iter().map(Vec::len).sum(),
        );
        let owned = |row: &Row<N>, handles: Vec<u32>| -> Vec<(u32, F)> {
            handles
                .into_iter()
                .zip(self.terms_of(row.source))
                .map(|(h, (_, c))| (h, *c))
                .collect()
        };
        let split = |row: &Row<N>, handles: Vec<u32>| -> (Vec<u16>, Vec<F>) {
            let columns = handles.into_iter().map(|h| h as u16).collect();
            let coefficients = self.terms_of(row.source).iter().map(|(_, c)| *c).collect();
            (columns, coefficients)
        };
        let mut reducer_at: Vec<u32> = vec![NONE; ncols];
        for (k, handles) in reducer_handles.iter().enumerate() {
            reducer_at[handles[0] as usize] = k as u32;
        }
        let reducer_elements: Vec<u32> = rows[target_count..]
            .iter()
            .map(|r| match r.source {
                RowSource::Element(id) => id,
                RowSource::Input(_) => unreachable!("a reducer is a basis-element multiple"),
            })
            .collect();
        let reducer_rows_of = || {
            rows[target_count..]
                .iter()
                .zip(reducer_handles.iter().cloned())
        };
        let mut reducer_rows: Vec<Vec<(u32, F)>> = Vec::new();
        let reducer_layout = match (arm.source(), narrow) {
            (false, false) => {
                reducer_rows = reducer_rows_of().map(|(r, h)| owned(r, h)).collect();
                None
            }
            (true, false) => Some(ReducerLayout::Source(reducer_handles.clone())),
            (false, true) => Some(ReducerLayout::Split(
                reducer_rows_of().map(|(r, h)| split(r, h)).collect(),
            )),
            (true, true) => Some(ReducerLayout::Source16(
                reducer_handles
                    .iter()
                    .map(|h| h.iter().map(|&c| c as u16).collect())
                    .collect(),
            )),
        };
        drop(reducer_handles);
        let reducer_sigs: Vec<Signature<N>> = rows[target_count..].iter().map(|r| r.sig).collect();
        let mut target_split: Vec<(Vec<u16>, Vec<F>)> = Vec::new();
        let targets: Vec<(Signature<N>, Vec<(u32, F)>)> = rows[..target_count]
            .iter()
            .zip(handles)
            .map(|(row, handles)| {
                if narrow {
                    target_split.push(split(row, handles));
                    (row.sig, Vec::new())
                } else {
                    (row.sig, owned(row, handles))
                }
            })
            .collect();
        debug_assert_eq!(
            reducer_at.iter().filter(|&&k| k != NONE).count(),
            reducer_count
        );
        // Each pivot is held once (#945's corrective iteration): in lane form only, unless a
        // research census reads the field rows.
        #[cfg(feature = "research-reuse")]
        let field_copies = lane.is_none() || self.reuse.is_some();
        #[cfg(not(feature = "research-reuse"))]
        let field_copies = lane.is_none();
        #[cfg(feature = "research-sigf4-split")]
        let reducer_entries = reducer_entry_count as u64;
        let lane_rows: Vec<LaneRow> = match &lane {
            None => Vec::new(),
            Some(lane) if field_copies => reducer_rows
                .iter()
                .map(|row| LaneRow::from_monic(lane, LaneKernel::default(), row))
                .collect(),
            Some(lane) => std::mem::take(&mut reducer_rows)
                .into_iter()
                .map(|row| LaneRow::from_monic(lane, LaneKernel::default(), &row))
                .collect(),
        };
        let lane_bytes: usize = lane_rows.iter().map(LaneRow::bytes).sum();
        let block = ReducerBlock {
            order,
            rows: &reducer_rows,
            sigs: &reducer_sigs,
            at: &reducer_at,
            ncols,
            lane: lane.map(|lane| (lane, lane_rows.as_slice())),
            field_copies,
            layout: reducer_layout.as_ref(),
            elements: &reducer_elements,
        };
        if self.options.parallel_cascade {
            if let Some(done) = self.claim(&block, &targets, columns, clock, lane_bytes)? {
                return Ok(done);
            }
        }
        #[cfg(feature = "research-sigf4-split")]
        let mut split = super::BatchSplit {
            targets: target_count,
            reducers: reducer_count,
            columns: ncols,
            entries: target_entry_count as u64 + reducer_entries,
            setup: clock.elapsed(),
            ..Default::default()
        };
        // Charged as the parallel cascade charges (#962): the rows, the pivot maps and every
        // workspace up front, then each reduced row as it is made. A crossing abandons the batch
        // before any of it is settled.
        let mut live = LiveBudget::new(self.options.max_live_bytes);
        // A claim batch redone here (#961) keeps the cascade's phase A, even at one worker, so
        // its products stay the cascade's.
        let phase_a = self.options.workers > 1 || self.options.parallel_cascade;
        let phase_a_workers = if phase_a {
            self.options.workers.max(1)
        } else {
            0
        };
        let row_bytes = batch_rows_bytes(&block, &targets, &target_split);
        let fixed = row_bytes
            + lane_bytes
            + 2 * ncols * size_of::<u32>()
            + (1 + phase_a_workers) * block.workspace_bytes();
        if let Err(stop) = live.charge(fixed) {
            return Err(self.abandon(&live, clock, stop));
        }
        #[cfg(feature = "research-sigf4")]
        let layout_rows = {
            let rows = super::layout::row_bytes(
                target_entry_count,
                reducer_entry_count,
                ncols,
                size_of::<F>(),
                size_of::<(u32, F)>(),
            );
            if lane.is_none() {
                debug_assert_eq!(rows[arm.index()], row_bytes, "{arm:?}");
            }
            rows
        };
        #[cfg(feature = "research-sigf4-split")]
        let pass_clock = Instant::now();
        let prereduced: Vec<Reduced<F>> = if phase_a {
            let job = PhaseA {
                block: &block,
                targets: &targets,
                workers: phase_a_workers,
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
        let mut workspace = block.workspace();
        // #945: each element's row in lane form, beside `finals`, when the batch uses lanes.
        let mut final_lanes: Vec<Option<LaneRow>> = Vec::new();
        let check = self.options.check_signatures;
        #[cfg(feature = "research-sigf4-replay")]
        let mut replay = super::replay::Recorder::new(ncols);
        // #961: a reducer multiple of this degree whose lead an element of smaller signature now
        // holds is itself a row to reduce, at its own signature: promoted to a target here, as a
        // whole-matrix echelon in signature order would reduce it, rather than left to a pair a
        // later batch of this degree takes. Its row and every column it reaches are already in
        // the matrix. Largest signature first, so the least pops from the end.
        let mut taken: HashSet<Signature<N>> = targets.iter().map(|(t, _)| *t).collect();
        let mut promoted: Vec<(Signature<N>, u32)> = Vec::new();
        // The census replays the rows this pass reduced, promoted ones included, in its order.
        #[cfg(feature = "research-reuse")]
        let mut reduced_rows: Vec<(Signature<N>, Vec<(u32, F)>)> = Vec::new();
        let mut next = 0;
        loop {
            let from_targets = match (targets.get(next), promoted.last()) {
                (None, None) => break,
                (Some((t, _)), Some((p, _))) => t.cmp_in(p, order) == Ordering::Less,
                (target, _) => target.is_some(),
            };
            let (t, entries, earlier) = if from_targets {
                let (t, raw) = &targets[next];
                let k = next;
                next += 1;
                let (entries, earlier) = prereduced.next().unwrap_or_else(|| {
                    let raw = match target_split.get(k) {
                        Some((columns, coefficients)) => columns
                            .iter()
                            .map(|&c| u32::from(c))
                            .zip(coefficients.iter().copied())
                            .collect(),
                        None => raw.clone(),
                    };
                    (raw, 0)
                });
                (*t, entries, earlier)
            } else {
                let (t, r) = promoted.pop().expect("matched above");
                let entries = block
                    .reducer_entries_in(r as usize, |id| self.basis[id as usize].terms.as_slice());
                (t, entries, 0)
            };
            #[cfg(feature = "research-reuse")]
            if self.reuse.is_some() {
                reduced_rows.push((t, entries.clone()));
            }
            #[cfg(feature = "research-sigf4-split")]
            let mut cascade = 0u64;
            let basis = &self.basis;
            let (mut out, later) = workspace.reduce_pivots(&entries, |c| {
                let pivot = if let Some(pivot) =
                    block.admissible_pivot_in(c, &t, |id| basis[id as usize].terms.as_slice())
                {
                    Some(pivot)
                } else if target_at[c] != NONE {
                    let (s, _, entries, _) = &finals[target_at[c] as usize];
                    assert!(
                        !check || s.cmp_in(&t, order) == Ordering::Less,
                        "an earlier target must have a smaller signature"
                    );
                    let pivot = match &final_lanes[target_at[c] as usize] {
                        Some(row) => PivotRow::Lane(row),
                        None => PivotRow::Field(entries.as_slice()),
                    };
                    #[cfg(feature = "research-sigf4-split")]
                    {
                        cascade += pivot.products();
                    }
                    Some(pivot)
                } else {
                    None
                };
                #[cfg(feature = "research-sigf4-replay")]
                replay.step(
                    c,
                    pivot.as_ref().map(|p| p.products() as usize + 1),
                    pivot.is_some() && !block.admits(c, &t),
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
            if kind == Kind::Element {
                let lead = out[0].0;
                target_at[lead as usize] = finals.len() as u32;
                if let Some((s, r)) = self.promotion(&block, &t, lead, &taken) {
                    taken.insert(s);
                    let at =
                        promoted.partition_point(|(p, _)| p.cmp_in(&s, order) == Ordering::Greater);
                    promoted.insert(at, (s, r));
                    self.stats.targets += 1;
                    self.stats.promoted_reducers += 1;
                }
            }
            let out_lane = if kind == Kind::Element {
                block.lane_row(&out)
            } else {
                None
            };
            if out_lane.is_some() && !block.field_copies {
                out = Vec::new();
            }
            let bytes =
                std::mem::size_of_val(out.as_slice()) + out_lane.as_ref().map_or(0, LaneRow::bytes);
            if let Err(stop) = live.charge(bytes) {
                return Err(self.abandon(&live, clock, stop));
            }
            final_lanes.push(out_lane);
            finals.push((t, kind, out, earlier + later));
        }
        #[cfg(feature = "research-sigf4-replay")]
        replay.finish();
        #[cfg(feature = "research-reuse")]
        self.census_reuse(&block, &rows[target_count..], &reduced_rows, &finals);
        #[cfg(feature = "research-sigf4-split")]
        {
            split.targets = finals.len();
            split.serial_pass = pass_clock.elapsed();
            self.stats.split.batches.push(split);
        }
        self.stats.claim_peak_live_bytes = self.stats.claim_peak_live_bytes.max(live.peak);
        #[cfg(feature = "research-sigf4")]
        self.stats.layout.record(
            layout_rows,
            fixed - row_bytes,
            live.peak - fixed,
            ncols,
            reducer_entry_count * size_of::<F>(),
            arm != super::layout::RowLayout::Baseline,
        );
        let mut results = Vec::new();
        for ((t, kind, row, products), lane_row) in finals.into_iter().zip(final_lanes) {
            let row = block.field_row(row, lane_row);
            self.settle(t, kind, &row, products, columns);
            if kind == Kind::Element {
                results.push((t, row));
            }
        }
        self.stats.elimination += clock.elapsed();
        Ok(finish_batch(results, columns))
    }

    /// #1031: census this batch's reducer reuse, with the engine's own product count beside it.
    /// `targets` are the rows the serial pass reduced, in its order, promoted rows (#961) included.
    #[cfg(feature = "research-reuse")]
    #[allow(clippy::type_complexity)]
    fn census_reuse(
        &mut self,
        block: &ReducerBlock<'_, N, F>,
        reducer_rows: &[Row<N>],
        targets: &[(Signature<N>, Vec<(u32, F)>)],
        finals: &[(Signature<N>, Kind, Vec<(u32, F)>, u64)],
    ) {
        use crate::grobner::reuse_census::{Reducer, Target};
        let Some(census) = self.reuse.as_mut() else {
            return;
        };
        let reducers: Vec<Reducer<'_, N, Signature<N>, F>> = reducer_rows
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

    /// #961's promotion test for an element of signature `t` with lead column `lead`: the
    /// reducer row there, when it has `t`'s degree, a larger signature, is not yet a target of the
    /// batch, and no known syzygy covers it.
    fn promotion(
        &self,
        block: &ReducerBlock<'_, N, F>,
        t: &Signature<N>,
        lead: u32,
        taken: &HashSet<Signature<N>>,
    ) -> Option<(Signature<N>, u32)> {
        let r = block.at[lead as usize];
        if r == NONE {
            return None;
        }
        let s = block.sigs[r as usize];
        (s.degree() == t.degree()
            && s.cmp_in(t, self.order) == Ordering::Greater
            && !taken.contains(&s)
            && self.syzygies.covering(&s).is_none())
        .then_some((s, r))
    }

    /// The parallel cascade (M31-S2): #902's prereduce + claim schedule, then design 1's
    /// accounting in signature order. A stopped batch is abandoned whole, before any insertion.
    ///
    /// `None` when design 1 would promote a reducer row (#961): the cascade's target set is fixed,
    /// so the batch is redone by design 1 and its rows stay design 1's. The first promotion is
    /// found from these outcomes, which equal design 1's up to it.
    #[allow(clippy::type_complexity)]
    fn claim(
        &mut self,
        block: &ReducerBlock<'_, N, F>,
        targets: &[(Signature<N>, Vec<(u32, F)>)],
        columns: &[Monomial<N>],
        clock: Instant,
        lane_bytes: usize,
    ) -> Result<Option<Vec<(Signature<N>, Vec<(Monomial<N>, F)>)>>, SigF4Error> {
        let rows_bytes = batch_rows_bytes(block, targets, &[]) + lane_bytes;
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
        let taken: HashSet<Signature<N>> = targets.iter().map(|(t, _)| *t).collect();
        let promotes = targets.iter().zip(&report.outcomes).any(|((t, _), o)| {
            let lead = o
                .row
                .first()
                .map(|e| e.0)
                .or(o.lane.as_ref().map(LaneRow::lead));
            o.kind == Kind::Element
                && lead.is_some_and(|lead| self.promotion(block, t, lead, &taken).is_some())
        });
        if promotes {
            self.stats.claim_promotion_fallbacks += 1;
            return Ok(None);
        }
        let mut results = Vec::new();
        for ((t, _), outcome) in targets.iter().zip(report.outcomes) {
            let row = block.field_row(outcome.row, outcome.lane);
            self.settle(*t, outcome.kind, &row, outcome.products, columns);
            if outcome.kind == Kind::Element {
                results.push((*t, row));
            }
        }
        self.stats.elimination += clock.elapsed();
        Ok(Some(finish_batch(results, columns)))
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
                self.syzygies.insert_counted(
                    t,
                    SyzygySource::ZeroRow,
                    &mut self.stats.pair_work.zero_row,
                );
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
        let lead_mask = mask(&lead);
        let id = self.basis.len() as u32;
        self.rank(&sig, &lead);
        #[cfg(test)]
        let covered = if self.options.reference_pairs {
            self.pairs_reference(sig, lead, lead_mask)
        } else {
            self.pairs(sig, lead, lead_mask)
        };
        #[cfg(not(test))]
        let covered = self.pairs(sig, lead, lead_mask);
        self.new_leads += usize::from(!covered);
        self.by_index[sig.index as usize].push((mask(&sig.mono), id));
        self.lead_masks.push(lead_mask);
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

    /// Creates the new element's pairs with every older element, recording Koszul syzygies, and
    /// returns whether an older lead divides its lead. Exact against `pairs_reference`: the same
    /// pairs are queued, rejected by the same criteria with the same attribution, and the syzygy
    /// store ends each call identical.
    ///
    /// - The ratio ranks decide which half is larger, so only that half's signature `T` and its
    ///   Koszul signature `K` are built. `K = gcd(leads)·T` and both compare the same two ratios,
    ///   so the rank comparison is the comparison of both pairs of candidates.
    /// - The syzygy criterion runs on `T` before `K` is inserted, and a covered `T` skips the
    ///   insert: whatever covers `T` covers `K`, so the insert is a no-op (Roune–Stillman 2012
    ///   §3.3). The order does not change the query's answer: past the product criterion `gcd ≠
    ///   1`, so `K` does not divide `T`, and the entries a kept `K` drops are its multiples, which
    ///   do not divide `T` either. The order of the remaining entries is kept.
    fn pairs(&mut self, sig: Signature<N>, lead: Monomial<N>, lead_mask: u64) -> bool {
        let id = self.basis.len() as u32;
        let rank = self.ratio_rank[id as usize];
        let mut covered = false;
        for g in 0..self.basis.len() {
            self.stats.pair_work.visited += 1;
            let other = &self.basis[g];
            let (g_sig, g_lead) = (other.sig, other.lead);
            covered = covered || (self.lead_masks[g] & !lead_mask == 0 && divides(&g_lead, &lead));
            let (element, partner, winner, w_lead, o_lead) = match rank.cmp(&self.ratio_rank[g]) {
                Ordering::Equal => {
                    self.stats.pairs_singular += 1;
                    continue;
                }
                Ordering::Greater => (id, g as u32, sig, lead, g_lead),
                Ordering::Less => (g as u32, id, g_sig, g_lead, lead),
            };
            self.stats.pairs_created += 1;
            let koszul = Signature::new(winner.mono * o_lead, winner.index);
            if gcd_is_one(&lead, &g_lead) {
                self.stats.rejected_product += 1;
                self.insert_koszul(koszul);
                continue;
            }
            let t = Signature::new(
                winner.mono * quotient_by_gcd(&o_lead, &w_lead),
                winner.index,
            );
            if self.reject_by_syzygy(&t, true) {
                self.stats.pair_work.koszul_skipped += 1;
                continue;
            }
            self.insert_koszul(koszul);
            self.stats.pair_work.pushed += 1;
            self.push(Pending {
                sig: t,
                source: Source::Pair {
                    element,
                    other: partner,
                },
            });
        }
        covered
    }

    fn insert_koszul(&mut self, k: Signature<N>) {
        #[cfg(feature = "research-sigf4-usage")]
        self.usage
            .ops
            .push(super::usage::StoreOp::Insert(k, SyzygySource::Koszul));
        self.syzygies
            .insert_counted(k, SyzygySource::Koszul, &mut self.stats.pair_work.koszul);
    }

    /// The pair loop as it stood before #1185, kept as the oracle `pairs` is tested against: both
    /// Koszul signatures and both halves computed per pair, the Koszul insert before the query.
    #[cfg(test)]
    fn pairs_reference(&mut self, sig: Signature<N>, lead: Monomial<N>, lead_mask: u64) -> bool {
        let id = self.basis.len() as u32;
        let order = self.order;
        let mut covered = false;
        for g in 0..self.basis.len() {
            let (g_sig, g_lead) = (self.basis[g].sig, self.basis[g].lead);
            covered = covered || (self.lead_masks[g] & !lead_mask == 0 && divides(&g_lead, &lead));
            self.stats.pair_work.visited += 1;
            let k_new = sig.times(&g_lead);
            let k_old = g_sig.times(&lead);
            let koszul = &mut self.stats.pair_work.koszul;
            match k_new.cmp_in(&k_old, order) {
                Ordering::Greater => {
                    self.syzygies
                        .insert_counted(k_new, SyzygySource::Koszul, koszul)
                }
                Ordering::Less => self
                    .syzygies
                    .insert_counted(k_old, SyzygySource::Koszul, koszul),
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
            if self.reject_by_syzygy(&t, true) {
                continue;
            }
            self.stats.pair_work.pushed += 1;
            self.push(Pending {
                sig: t,
                source: Source::Pair { element, other },
            });
        }
        covered
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
    target_split: &[(Vec<u16>, Vec<F>)],
) -> usize {
    let split = |(c, v): &(Vec<u16>, Vec<F>)| size_of_val(c.as_slice()) + size_of_val(v.as_slice());
    let layout = match block.layout {
        None => 0,
        Some(ReducerLayout::Source(rows)) => rows.iter().map(|r| size_of_val(r.as_slice())).sum(),
        Some(ReducerLayout::Split(rows)) => rows.iter().map(split).sum(),
        Some(ReducerLayout::Source16(rows)) => rows.iter().map(|r| size_of_val(r.as_slice())).sum(),
    };
    (targets.iter().map(|(_, r)| r.len()).sum::<usize>()
        + block.rows.iter().map(Vec::len).sum::<usize>())
        * size_of::<(u32, F)>()
        + target_split.iter().map(split).sum::<usize>()
        + layout
}

/// #1078: a batch's reducer multiples in a non-baseline layout; [`ReducerBlock::rows`] is empty.
pub(super) enum ReducerLayout<F> {
    Source(Vec<Vec<u32>>),
    Split(Vec<(Vec<u16>, Vec<F>)>),
    Source16(Vec<Vec<u16>>),
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
    /// #1078: the reducers' layout when not the baseline, and each reducer's basis element.
    pub(super) layout: Option<&'a ReducerLayout<F>>,
    pub(super) elements: &'a [u32],
    pub(super) ncols: usize,
    /// #945: the field's lane and `rows` in lane form, when the batch reduces in `u32` lanes.
    pub(super) lane: Option<(Lane<F>, &'a [LaneRow])>,
    /// Whether `rows` and each element's field row are kept beside their lane forms. Without
    /// lanes, always; with them, only for a research census, so each pivot is held once.
    pub(super) field_copies: bool,
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

    /// The reducer at column `c` if its signature is strictly below `t`, as a field row.
    #[cfg(test)]
    pub(super) fn admissible(&self, c: usize, t: &Signature<N>) -> Option<&[(u32, F)]> {
        self.admits(c, t)
            .then(|| self.rows[self.at[c] as usize].as_slice())
    }

    /// Whether the reducer at column `c` has a signature strictly below `t`.
    pub(super) fn admits(&self, c: usize, t: &Signature<N>) -> bool {
        let r = self.at[c];
        r != NONE && self.sigs[r as usize].cmp_in(t, self.order) == Ordering::Less
    }

    /// [`Self::admissible`], in the representation the batch reduces in.
    pub(super) fn admissible_pivot(
        &self,
        c: usize,
        t: &Signature<N>,
    ) -> Option<PivotRow<'_, N, F>> {
        self.admissible_pivot_in(c, t, |_| unreachable!("a layout batch has its basis"))
    }

    /// [`Self::admissible_pivot`] for any layout: `terms` gives a basis element's terms, which a
    /// source-backed reducer reads its coefficients from.
    pub(super) fn admissible_pivot_in<'p>(
        &'p self,
        c: usize,
        t: &Signature<N>,
        terms: impl FnOnce(u32) -> &'p [(Monomial<N>, F)],
    ) -> Option<PivotRow<'p, N, F>> {
        if !self.admits(c, t) {
            return None;
        }
        let r = self.at[c] as usize;
        Some(match (&self.lane, self.layout) {
            (Some((_, rows)), _) => PivotRow::Lane(&rows[r]),
            (None, None) => PivotRow::Field(self.rows[r].as_slice()),
            (None, Some(ReducerLayout::Source(rows))) => {
                PivotRow::Source(&rows[r], terms(self.elements[r]))
            }
            (None, Some(ReducerLayout::Split(rows))) => PivotRow::Split(&rows[r].0, &rows[r].1),
            (None, Some(ReducerLayout::Source16(rows))) => {
                PivotRow::Source16(&rows[r], terms(self.elements[r]))
            }
        })
    }

    /// A target's field row for settlement: `row` itself, or its lane form converted back when
    /// only that was kept.
    pub(super) fn field_row(&self, row: Vec<(u32, F)>, lane_row: Option<LaneRow>) -> Vec<(u32, F)>
    where
        F: FiniteField,
    {
        match (&self.lane, lane_row) {
            (Some((lane, _)), Some(lane_row)) if row.is_empty() => lane_row.to_field(lane),
            _ => row,
        }
    }

    /// Reducer `k`'s row in field form, from its lane form when no field copy was kept.
    /// `terms` gives a basis element's terms, as for [`Self::admissible_pivot_in`].
    pub(super) fn reducer_entries_in<'p>(
        &'p self,
        k: usize,
        terms: impl FnOnce(u32) -> &'p [(Monomial<N>, F)],
    ) -> Vec<(u32, F)>
    where
        F: FiniteField,
    {
        let borrowed = |columns: &mut dyn Iterator<Item = u32>, terms: &[(Monomial<N>, F)]| {
            columns.zip(terms.iter().map(|(_, c)| *c)).collect()
        };
        match (&self.lane, self.layout) {
            (Some((lane, rows)), _) if !self.field_copies => rows[k].to_field(lane),
            (_, None) => self.rows[k].clone(),
            (_, Some(ReducerLayout::Source(rows))) => {
                borrowed(&mut rows[k].iter().copied(), terms(self.elements[k]))
            }
            (_, Some(ReducerLayout::Split(rows))) => rows[k]
                .0
                .iter()
                .map(|&c| u32::from(c))
                .zip(rows[k].1.iter().copied())
                .collect(),
            (_, Some(ReducerLayout::Source16(rows))) => borrowed(
                &mut rows[k].iter().map(|&c| u32::from(c)),
                terms(self.elements[k]),
            ),
        }
    }

    /// A workspace in the batch's representation.
    pub(super) fn workspace(&self) -> Workspace<F>
    where
        F: FiniteField,
    {
        Workspace::with_lane(self.ncols, self.lane.as_ref().map(|(lane, _)| *lane))
    }

    /// What [`Self::workspace`] holds, as the live budget charges it: a lane's cells where they
    /// are wider than `F` (#1183's are `u64`).
    pub(super) fn workspace_bytes(&self) -> usize {
        let cell = self.lane.as_ref().map_or(0, |(lane, _)| lane.cell_bytes());
        Workspace::<F>::bytes_with_cells(self.ncols, cell)
    }

    /// A monic `row` in lane form, when the batch reduces in lanes.
    pub(super) fn lane_row(&self, row: &[(u32, F)]) -> Option<LaneRow>
    where
        F: FiniteField,
    {
        self.lane
            .as_ref()
            .map(|(lane, _)| LaneRow::from_monic(lane, LaneKernel::default(), row))
    }
}

/// A pivot in whichever representation its batch reduces in.
pub(super) enum PivotRow<'p, const N: usize, F> {
    Field(&'p [(u32, F)]),
    Lane(&'p LaneRow),
    /// #1078: a reducer multiple's columns, with its coefficients read from the element's terms.
    Source(&'p [u32], &'p [(Monomial<N>, F)]),
    /// #1078: `u16` columns beside their coefficients.
    Split(&'p [u16], &'p [F]),
    /// #1078: `u16` columns, coefficients from the element's terms.
    Source16(&'p [u16], &'p [(Monomial<N>, F)]),
}

impl<const N: usize, F> PivotRow<'_, N, F> {
    /// Entries right of the lead, in a field-form pivot.
    #[cfg_attr(not(feature = "research-work"), allow(dead_code))]
    fn tail_len(&self) -> usize {
        match self {
            PivotRow::Field(row) => row.len() - 1,
            PivotRow::Lane(_) => unreachable!("a lane pivot reduces in a lane workspace"),
            PivotRow::Source(columns, _) => columns.len() - 1,
            PivotRow::Split(columns, _) | PivotRow::Source16(columns, _) => columns.len() - 1,
        }
    }

    /// Products one application costs: the entries right of the lead.
    #[cfg(any(feature = "research-sigf4-split", feature = "research-sigf4-replay"))]
    pub(super) fn products(&self) -> u64 {
        match self {
            PivotRow::Lane(row) => row.nonzeros(),
            other => other.tail_len() as u64,
        }
    }
}

/// Subtracts `factor` times a pivot's tail from the accumulator, marking each column touched.
#[inline(always)]
fn subtract_tail<'v, F: FiniteField + 'v>(
    acc: &mut [F],
    touched: &mut [u64],
    factor: &PreparedFactor<F>,
    tail: impl Iterator<Item = (usize, &'v F)>,
    #[cfg(feature = "research-work")] nonzeros: &mut usize,
) {
    for (cc, v) in tail {
        #[cfg(feature = "research-work")]
        let before = acc[cc].is_zero();
        acc[cc] -= v.mul_prepared(factor);
        #[cfg(feature = "research-work")]
        {
            *nonzeros += usize::from(before);
            *nonzeros -= usize::from(acc[cc].is_zero());
        }
        touched[cc >> 6] |= 1 << (cc & 63);
    }
}

/// A dense accumulator with a bitset of possibly-nonzero columns, reused across rows.
pub(super) struct Workspace<F> {
    acc: Vec<F>,
    touched: Vec<u64>,
    /// #945: when present, every row is reduced here and `acc` is empty.
    lane: Option<LaneWorkspace<F>>,
}

impl<F> Workspace<F> {
    /// What one workspace over `ncols` columns holds, as the live budget charges it.
    /// Each column takes at least `cell` bytes: a lane's cells may be wider than `F`.
    pub(super) fn bytes_with_cells(ncols: usize, cell: usize) -> usize {
        ncols * size_of::<F>().max(cell) + ncols.div_ceil(64) * size_of::<u64>()
    }
}

impl<F: FiniteField> Workspace<F> {
    pub(super) fn new(ncols: usize) -> Self {
        Self::with_lane(ncols, None)
    }

    /// A workspace that reduces in `lane` when one is given.
    pub(super) fn with_lane(ncols: usize, lane: Option<Lane<F>>) -> Self {
        match lane {
            Some(lane) => Self {
                acc: Vec::new(),
                touched: Vec::new(),
                lane: Some(LaneWorkspace::new(lane, ncols)),
            },
            None => Self {
                acc: vec![F::zero(); ncols],
                touched: vec![0; ncols.div_ceil(64)],
                lane: None,
            },
        }
    }

    /// [`Self::reduce`] against pivots in the workspace's own representation.
    ///
    /// # Panics
    /// If a pivot's representation is not the workspace's.
    pub(super) fn reduce_pivots<'p, const N: usize>(
        &mut self,
        entries: &[(u32, F)],
        mut pivot: impl FnMut(usize) -> Option<PivotRow<'p, N, F>>,
    ) -> Reduced<F>
    where
        F: 'p,
    {
        if let Some(lane) = &mut self.lane {
            return lane.reduce(entries, |c| {
                pivot(c).map(|p| match p {
                    PivotRow::Lane(row) => row,
                    _ => unreachable!("a field pivot in a lane workspace"),
                })
            });
        }
        self.reduce_rows(entries, pivot)
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
        self.reduce_rows::<0>(entries, |c| pivot(c).map(PivotRow::Field))
    }

    /// [`Self::reduce`] over field-form pivots in any of #1078's layouts.
    fn reduce_rows<'p, const N: usize>(
        &mut self,
        entries: &[(u32, F)],
        mut pivot: impl FnMut(usize) -> Option<PivotRow<'p, N, F>>,
    ) -> Reduced<F>
    where
        F: 'p,
    {
        assert!(
            self.lane.is_none(),
            "a lane workspace reduces through reduce_pivots"
        );
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
                            row.tail_len(),
                        );
                        applied += 1;
                        nonzeros -= 1;
                    }
                    let factor = coefficient.prepare_factor();
                    let (acc, touched) = (&mut self.acc[..], &mut self.touched[..]);
                    let tail = match row {
                        PivotRow::Field(row) => {
                            let tail = row[1..].iter().map(|(cc, v)| (*cc as usize, v));
                            subtract_tail(
                                acc,
                                touched,
                                &factor,
                                tail,
                                #[cfg(feature = "research-work")]
                                &mut nonzeros,
                            );
                            row.len() - 1
                        }
                        PivotRow::Source(columns, terms) => {
                            let coefficients = terms[1..].iter().map(|(_, v)| v);
                            let tail = columns[1..].iter().map(|&cc| cc as usize);
                            subtract_tail(
                                acc,
                                touched,
                                &factor,
                                tail.zip(coefficients),
                                #[cfg(feature = "research-work")]
                                &mut nonzeros,
                            );
                            columns.len() - 1
                        }
                        PivotRow::Split(columns, coefficients) => {
                            let tail = columns[1..].iter().map(|&cc| cc as usize);
                            subtract_tail(
                                acc,
                                touched,
                                &factor,
                                tail.zip(&coefficients[1..]),
                                #[cfg(feature = "research-work")]
                                &mut nonzeros,
                            );
                            columns.len() - 1
                        }
                        PivotRow::Source16(columns, terms) => {
                            let coefficients = terms[1..].iter().map(|(_, v)| v);
                            let tail = columns[1..].iter().map(|&cc| cc as usize);
                            subtract_tail(
                                acc,
                                touched,
                                &factor,
                                tail.zip(coefficients),
                                #[cfg(feature = "research-work")]
                                &mut nonzeros,
                            );
                            columns.len() - 1
                        }
                        PivotRow::Lane(_) => unreachable!("a lane pivot in a field workspace"),
                    };
                    products += tail as u64;
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
        workspace.reduce_pivots(entries, |c| self.block.admissible_pivot(c, t))
    }

    /// The same pass on one thread, for a field that cannot cross threads.
    fn serial(self) -> Vec<Reduced<F>> {
        let mut workspace = self.block.workspace();
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
                    let mut workspace = self.block.workspace();
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

#[cfg(test)]
mod layout_tests {
    use super::{PivotRow, Workspace};
    use crate::{
        fields::{PrimeFieldElement64, Zp32003},
        FiniteField, Monomial,
    };

    type Goldilocks = PrimeFieldElement64<18446744069414584321>;

    /// Reduces a two-entry row by one monic pivot over `ncols` columns that reaches the last
    /// column, in the field form and each #1078 layout.
    fn reduce_in_every_layout<F: FiniteField>(ncols: usize) -> Vec<Vec<(u32, F)>> {
        let last = ncols as u32 - 1;
        let pivot: Vec<(u32, F)> = vec![(0, F::one()), (last - 1, F::new(3)), (last, F::new(5))];
        let terms: Vec<(Monomial<1>, F)> =
            pivot.iter().map(|&(_, v)| (Monomial::one(), v)).collect();
        let columns: Vec<u32> = pivot.iter().map(|e| e.0).collect();
        let narrow: Vec<u16> = columns.iter().map(|&c| c as u16).collect();
        let coefficients: Vec<F> = pivot.iter().map(|e| e.1).collect();
        let row = [(0, F::new(2)), (last, F::new(7))];
        let mut workspace = Workspace::<F>::new(ncols);
        let mut run = |p: PivotRow<'_, 1, F>| {
            let mut p = Some(p);
            workspace
                .reduce_rows(&row, |c| if c == 0 { p.take() } else { None })
                .0
        };
        let mut out = vec![
            run(PivotRow::Field(&pivot)),
            run(PivotRow::Source(&columns, &terms)),
        ];
        if ncols <= crate::grobner::sigf4::layout::U16_COLUMNS {
            out.push(run(PivotRow::Split(&narrow, &coefficients)));
            out.push(run(PivotRow::Source16(&narrow, &terms)));
        }
        out
    }

    /// #1078: at 65,535 and 65,536 columns every layout, `u16` ones included, reduces into the
    /// last column exactly as the field form does; at 65,537 the `u32` layouts still agree.
    #[test]
    fn test_layouts_agree_at_the_u16_width_boundary() {
        for (ncols, layouts) in [(65_535, 4), (65_536, 4), (65_537, 2)] {
            let out = reduce_in_every_layout::<Zp32003>(ncols);
            assert_eq!(out.len(), layouts, "{ncols}");
            let last = ncols as u32 - 1;
            let expected = vec![
                (last - 1, -(Zp32003::new(2) * Zp32003::new(3))),
                (last, Zp32003::new(7) - Zp32003::new(2) * Zp32003::new(5)),
            ];
            for row in &out {
                assert_eq!(row, &expected, "{ncols}");
            }
            assert!(reduce_in_every_layout::<Goldilocks>(ncols)
                .windows(2)
                .all(|w| w[0] == w[1]));
        }
    }
}
