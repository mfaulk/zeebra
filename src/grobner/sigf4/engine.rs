//! The batched F4-RB main loop (RFC §9 design 1; Lairez Algorithm 8, EF Algorithm 4).

use std::{
    cmp::Ordering,
    collections::BTreeMap,
    mem::size_of,
    time::{Duration, Instant},
};

use super::{
    signature::{divides, mask, Signature, SyzygySource, SyzygyStore},
    SigF4Error, SigF4Options, SigF4Statistics,
};
use crate::{
    grobner::{
        buchberger::{minimal_basis_for_interreduction, reduce_grobner_basis_until},
        f4::{
            certify_f4_output,
            interreduce::{interreduce_by_matrix, MatrixInterreductionAborted},
            F4Error, F4Options,
        },
    },
    poly::{MonomialMap, MonomialOrder},
    FiniteField, Monomial, MultivariatePolynomial,
};

const NONE: u32 = u32::MAX;

/// A signed basis element: `(s(α), ᾱ)` with `ᾱ` monic, terms in descending order.
struct Element<const N: usize, F> {
    sig: Signature<N>,
    sig_mask: u64,
    lead: Monomial<N>,
    lead_mask: u64,
    terms: Vec<(Monomial<N>, F)>,
}

/// What a pending signature reduces: an input, or `mult·element` (the pair's larger half).
#[derive(Clone, Copy)]
enum Source<const N: usize> {
    Input(usize),
    Pair {
        mult: Monomial<N>,
        element: u32,
        other_mult: Monomial<N>,
        other: u32,
    },
}

#[derive(Clone, Copy)]
struct Pending<const N: usize> {
    sig: Signature<N>,
    source: Source<N>,
}

/// One row of a batch matrix: `mult · source` with signature `sig`.
struct Row<const N: usize> {
    sig: Signature<N>,
    mult: Monomial<N>,
    source: RowSource,
}

#[derive(Clone, Copy)]
enum RowSource {
    Input(usize),
    Element(u32),
}

struct Engine<'a, const N: usize, F: FiniteField> {
    order: MonomialOrder,
    options: &'a SigF4Options,
    inputs: Vec<Vec<(Monomial<N>, F)>>,
    basis: Vec<Element<N, F>>,
    by_index: Vec<Vec<u32>>,
    syzygies: SyzygyStore<N>,
    queue: BTreeMap<u64, Vec<Pending<N>>>,
    pending: usize,
    /// Least-ratio basis element whose lead divides the key, and how much of the basis was scanned.
    reducers: MonomialMap<N, (u32, u32)>,
    stats: &'a mut SigF4Statistics,
}

pub(super) fn run<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    options: &SigF4Options,
    stats: &mut SigF4Statistics,
) -> Result<Vec<MultivariatePolynomial<N, F>>, SigF4Error> {
    let started = Instant::now();
    if !matches!(
        order,
        MonomialOrder::GradedReverseLexicographic | MonomialOrder::GradedLexicographic
    ) {
        return Err(SigF4Error::Unsupported {
            reason: "the signature engine supports graded orders only (RFC §7)",
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
        queue: BTreeMap::new(),
        pending: 0,
        reducers: MonomialMap::default(),
        inputs,
        stats,
    };
    for i in 0..engine.inputs.len() {
        let sig = Signature::new(engine.inputs[i][0].0, i as u32);
        engine.push(Pending {
            sig,
            source: Source::Input(i),
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

    let basis: Vec<MultivariatePolynomial<N, F>> = if inconsistent {
        vec![MultivariatePolynomial::one()]
    } else {
        engine
            .basis
            .iter()
            .map(|e| MultivariatePolynomial::new(&e.terms))
            .collect()
    };
    engine.stats.signature_basis_elements = engine.basis.len();
    engine.stats.syzygy_signatures = engine.syzygies.len();
    engine.stats.signature_metadata_bytes = engine.basis.len()
        * (size_of::<Signature<N>>() + 2 * size_of::<u64>())
        + engine.syzygies.len() * (size_of::<Monomial<N>>() + size_of::<u64>() + 1)
        + engine.stats.peak_pending * size_of::<Pending<N>>()
        + engine.reducers.len() * (size_of::<Monomial<N>>() + 8);
    drop(engine);

    let interreduction = Instant::now();
    let reduced = interreduce(basis, order, wall)?;
    stats.interreduction = interreduction.elapsed();
    stats.reduced_basis_elements = reduced.len();

    if options.certify {
        let report = certify_f4_output(generators, &reduced, order);
        if let Some(reason) = report.first_failure() {
            return Err(SigF4Error::Budget(F4Error::CertificationFailed { reason }));
        }
    }
    stats.total = started.elapsed();
    Ok(reduced)
}

/// The shipping F4's final stage: minimal basis, then matrix interreduction with the division
/// route as fallback (`f4/mod.rs`), under F4's default limits.
fn interreduce<const N: usize, F: FiniteField>(
    basis: Vec<MultivariatePolynomial<N, F>>,
    order: MonomialOrder,
    wall: Option<(Instant, Duration)>,
) -> Result<Vec<MultivariatePolynomial<N, F>>, SigF4Error> {
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
    match interreduce_by_matrix(
        minimal,
        order,
        defaults.max_matrix_rows,
        defaults.max_matrix_columns,
        defaults.live_entry_allowance::<F>(),
        should_stop,
    ) {
        Ok((reduced, _)) => Ok(reduced),
        Err(MatrixInterreductionAborted::Refused(_, minimal, _)) => {
            reduce_grobner_basis_until(minimal, order, should_stop)
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

impl<const N: usize, F: FiniteField> Engine<'_, N, F> {
    fn push(&mut self, pending: Pending<N>) {
        self.queue
            .entry(pending.sig.degree())
            .or_default()
            .push(pending);
        self.pending += 1;
        self.stats.peak_pending = self.stats.peak_pending.max(self.pending);
    }

    /// `ratio(a) < ratio(b)` as module terms `s/lt`, compared by cross-multiplication.
    fn ratio_cmp(&self, a: u32, b: u32) -> Ordering {
        let (a, b) = (&self.basis[a as usize], &self.basis[b as usize]);
        self.order
            .cmp(&(a.sig.mono * b.lead), &(b.sig.mono * a.lead))
            .then(a.sig.index.cmp(&b.sig.index))
    }

    /// The canonical rewriter of `t`: the `⊴_rat`-maximal element whose signature divides `t`
    /// (EF Def 7.1, 7.13), i.e. the **greatest** sig-lead ratio, whose multiple at `t` has the
    /// smallest lead; the newest on a tie. Greatest, not least: an element reduced from a multiple
    /// of `α` has a larger ratio than `α` and must supersede it, which the least-ratio choice
    /// does not (it lost pairs on katsura-4).
    fn rewriter(&self, t: &Signature<N>) -> u32 {
        let m = mask(&t.mono);
        let mut best = NONE;
        for &id in &self.by_index[t.index as usize] {
            let e = &self.basis[id as usize];
            if e.sig_mask & !m != 0 || !divides(&e.sig.mono, &t.mono) {
                continue;
            }
            if best == NONE || self.ratio_cmp(id, best) != Ordering::Less {
                best = id;
            }
        }
        best
    }

    /// The least-signature reducer multiple for column monomial `m`, i.e. the least-ratio element
    /// whose lead divides `m`. Cached per monomial; only elements added since are rescanned.
    fn reducer(&mut self, m: &Monomial<N>) -> u32 {
        let (mut best, scanned) = self.reducers.get(m).copied().unwrap_or((NONE, 0));
        let total = self.basis.len() as u32;
        if scanned < total {
            let mm = mask(m);
            for id in scanned..total {
                let e = &self.basis[id as usize];
                if e.lead_mask & !mm != 0 || !divides(&e.lead, m) {
                    continue;
                }
                if best == NONE || self.ratio_cmp(id, best) != Ordering::Greater {
                    best = id;
                }
            }
            self.reducers.insert(*m, (best, total));
        }
        best
    }

    fn reject_by_syzygy(&mut self, t: &Signature<N>) -> bool {
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
                Source::Input(i) => Some(i),
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
                let Source::Pair {
                    mult,
                    element,
                    other_mult,
                    other,
                } = p.source
                else {
                    continue;
                };
                let passes = element == rewriter && {
                    let other_sig = self.basis[other as usize].sig.times(&other_mult);
                    self.rewriter(&other_sig) == other
                };
                if !passes {
                    self.stats.rejected_rewrite += 1;
                } else if kept.is_some() {
                    self.stats.rejected_duplicate += 1;
                } else {
                    kept = Some((mult, element));
                }
            }
            if let Some((mult, element)) = kept {
                targets.push(Row {
                    sig: t,
                    mult,
                    source: RowSource::Element(element),
                });
            }
        }
        self.stats.bookkeeping += clock.elapsed();
        if targets.is_empty() {
            return Ok(false);
        }
        self.stats.batches += 1;
        self.stats.targets += targets.len();

        let (columns, rows, reducer_count) = self.symbolic(&targets)?;
        let new = self.eliminate(&columns, &rows, reducer_count, targets.len());

        let clock = Instant::now();
        if self.options.check_signatures {
            for (sig, terms) in &new {
                self.check_new_element(sig, &terms[0].0);
            }
        }
        for (sig, terms) in new {
            if terms[0].0.is_one() {
                self.stats.bookkeeping += clock.elapsed();
                return Ok(true);
            }
            self.insert(sig, terms)?;
        }
        self.stats.bookkeeping += clock.elapsed();
        Ok(false)
    }

    /// Columns (descending), and rows: targets first in signature order, then reducers.
    #[allow(clippy::type_complexity)]
    fn symbolic(
        &mut self,
        targets: &[Row<N>],
    ) -> Result<(Vec<Monomial<N>>, Vec<Row<N>>, usize), SigF4Error> {
        let clock = Instant::now();
        let mut seen: MonomialMap<N, ()> = MonomialMap::default();
        let mut work: Vec<Monomial<N>> = Vec::new();
        let mut rows: Vec<Row<N>> = Vec::with_capacity(targets.len());
        for t in targets {
            rows.push(Row {
                sig: t.sig,
                mult: t.mult,
                source: t.source,
            });
            for (m, _) in self.terms_of(t.source) {
                let m = *m * t.mult;
                if seen.insert(m, ()).is_none() {
                    work.push(m);
                }
            }
        }
        let mut reducers = 0;
        let mut next = 0;
        while next < work.len() {
            let m = work[next];
            next += 1;
            let id = self.reducer(&m);
            if id == NONE {
                continue;
            }
            let e = &self.basis[id as usize];
            let mult = m.checked_div(&e.lead).expect("the lead divides the column");
            let sig = e.sig.times(&mult);
            for (tm, _) in &e.terms[1..] {
                let tm = *tm * mult;
                if seen.insert(tm, ()).is_none() {
                    work.push(tm);
                }
            }
            rows.push(Row {
                sig,
                mult,
                source: RowSource::Element(id),
            });
            reducers += 1;
        }
        let order = self.order;
        work.sort_unstable_by(|a, b| order.cmp(b, a));
        self.stats.reducer_rows += reducers;
        self.stats.max_matrix_rows = self.stats.max_matrix_rows.max(rows.len());
        self.stats.max_matrix_columns = self.stats.max_matrix_columns.max(work.len());
        self.stats.symbolic += clock.elapsed();
        if rows.len() > self.options.max_matrix_rows {
            return Err(SigF4Error::Budget(F4Error::TooManyRows {
                limit: self.options.max_matrix_rows,
            }));
        }
        if work.len() > self.options.max_matrix_columns {
            return Err(SigF4Error::Budget(F4Error::TooManyColumns {
                limit: self.options.max_matrix_columns,
            }));
        }
        Ok((work, rows, reducers))
    }

    fn terms_of(&self, source: RowSource) -> &[(Monomial<N>, F)] {
        match source {
            RowSource::Input(i) => &self.inputs[i],
            RowSource::Element(id) => &self.basis[id as usize].terms,
        }
    }

    /// Serial regular elimination: each target, in increasing signature order, is fully reduced
    /// by pivots of strictly smaller signature — reducer multiples, or earlier targets of this
    /// batch (Lairez Algorithm 8 line 98). Returns the new elements in signature order.
    #[allow(clippy::type_complexity)]
    fn eliminate(
        &mut self,
        columns: &[Monomial<N>],
        rows: &[Row<N>],
        reducer_count: usize,
        target_count: usize,
    ) -> Vec<(Signature<N>, Vec<(Monomial<N>, F)>)> {
        let clock = Instant::now();
        let index: MonomialMap<N, u32> = columns
            .iter()
            .enumerate()
            .map(|(i, m)| (*m, i as u32))
            .collect();
        let sparse = |row: &Row<N>| -> Vec<(u32, F)> {
            self.terms_of(row.source)
                .iter()
                .map(|(m, c)| (index[&(*m * row.mult)], *c))
                .collect()
        };
        let ncols = columns.len();
        let mut reducer_at: Vec<u32> = vec![NONE; ncols];
        let reducer_rows: Vec<Vec<(u32, F)>> = rows[target_count..].iter().map(sparse).collect();
        let target_rows: Vec<Vec<(u32, F)>> = rows[..target_count].iter().map(sparse).collect();
        debug_assert_eq!(reducer_rows.len(), reducer_count);
        for (k, entries) in reducer_rows.iter().enumerate() {
            reducer_at[entries[0].0 as usize] = k as u32;
        }
        let mut target_at: Vec<u32> = vec![NONE; ncols];
        let mut results: Vec<(Signature<N>, Vec<(u32, F)>)> = Vec::new();
        let mut acc: Vec<F> = vec![F::zero(); ncols];
        let words = ncols.div_ceil(64);
        let mut touched: Vec<u64> = vec![0; words];

        for (target, entries) in rows[..target_count].iter().zip(target_rows) {
            let t = target.sig;
            let mut first = usize::MAX;
            for (c, v) in entries {
                let c = c as usize;
                acc[c] = v;
                touched[c >> 6] |= 1 << (c & 63);
                first = first.min(c);
            }
            let mut products: u64 = 0;
            let mut out: Vec<(u32, F)> = Vec::new();
            let mut w = first >> 6;
            while w < words {
                let bits = touched[w];
                if bits == 0 {
                    w += 1;
                    continue;
                }
                let c = (w << 6) | bits.trailing_zeros() as usize;
                touched[w] &= touched[w] - 1;
                let coefficient = std::mem::replace(&mut acc[c], F::zero());
                if coefficient.is_zero() {
                    continue;
                }
                let r = reducer_at[c];
                let pivot: Option<&[(u32, F)]> = if r != NONE
                    && rows[target_count + r as usize].sig.cmp_in(&t, self.order) == Ordering::Less
                {
                    Some(&reducer_rows[r as usize])
                } else if target_at[c] != NONE {
                    let (s, entries) = &results[target_at[c] as usize];
                    assert!(
                        !self.options.check_signatures
                            || s.cmp_in(&t, self.order) == Ordering::Less,
                        "an earlier target must have a smaller signature"
                    );
                    Some(entries)
                } else {
                    None
                };
                match pivot {
                    Some(entries) => {
                        let factor = coefficient.prepare_factor();
                        for (cc, v) in &entries[1..] {
                            let cc = *cc as usize;
                            acc[cc] -= v.mul_prepared(&factor);
                            touched[cc >> 6] |= 1 << (cc & 63);
                        }
                        products += (entries.len() - 1) as u64;
                    }
                    None => out.push((c as u32, coefficient)),
                }
            }
            self.stats.coefficient_products += products;
            if out.is_empty() {
                self.stats.reductions_to_zero += 1;
                self.stats.zero_rows += 1;
                self.stats.rows_adding_no_rank += 1;
                self.stats.products_on_zero_rows += products;
                self.syzygies.insert(t, SyzygySource::ZeroRow);
                continue;
            }
            let lead = out[0].0 as usize;
            let r = reducer_at[lead];
            if r != NONE && rows[target_count + r as usize].sig == t {
                self.stats.singular_rows += 1;
                self.stats.rows_adding_no_rank += 1;
                self.stats.products_on_singular_rows += products;
                continue;
            }
            let inverse = out[0].1.inverse();
            for (_, v) in &mut out {
                *v *= inverse;
            }
            target_at[lead] = results.len() as u32;
            results.push((t, out));
        }
        self.stats.elimination += clock.elapsed();
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

            let lcm = Monomial::lcm(&lead, &g_lead);
            let u = lcm.checked_div(&lead).expect("lcm");
            let v = lcm.checked_div(&g_lead).expect("lcm");
            let (su, sv) = (sig.times(&u), g_sig.times(&v));
            let source = match su.cmp_in(&sv, order) {
                Ordering::Equal => {
                    self.stats.pairs_singular += 1;
                    continue;
                }
                Ordering::Greater => (su, u, id, v, g as u32),
                Ordering::Less => (sv, v, g as u32, u, id),
            };
            self.stats.pairs_created += 1;
            if gcd_is_one(&lead, &g_lead) {
                self.stats.rejected_product += 1;
                continue;
            }
            let (t, mult, element, other_mult, other) = source;
            if self.reject_by_syzygy(&t) {
                continue;
            }
            self.push(Pending {
                sig: t,
                source: Source::Pair {
                    mult,
                    element,
                    other_mult,
                    other,
                },
            });
        }
        self.by_index[sig.index as usize].push(id);
        self.basis.push(Element {
            sig,
            sig_mask: mask(&sig.mono),
            lead,
            lead_mask: mask(&lead),
            terms,
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
