//! #1031's reduced-multiple reuse census, shared by the conventional and signature engines.
//!
//! Each batch's elimination is replayed three ways over the same pivots: as built, with every
//! reducer multiple tail-reduced against the batch's other reducers first, and with only the
//! multiples built in an earlier batch tail-reduced. The three replays must leave every target with
//! the same residual (it is the unique vector in the row plus the span of the admissible pivots
//! with no entry in a pivot column), and any difference is counted. Under a signature bound a
//! reducer is tail-reduced only by reducers of smaller signature, which keeps its signature, so
//! the admissible pivots of every target are unchanged.
//!
//! The tail-reduced arm is an upper bound on what a store of tail-reduced multiples could avoid:
//! a stored row from an earlier batch is reduced against that batch's pivots, not this one's.

use std::{cmp::Ordering, collections::HashMap};

use crate::{
    grobner::{
        f4::{BatchObserver, MacaulayMatrix, MonicBasis, RowKind},
        pairs::CriticalPair,
    },
    poly::{BuildMonomialHasher, Monomial},
    util::Json,
    FiniteField,
};

const NONE: u32 = u32::MAX;

/// `a` against `b` in the signature order.
pub type SignatureOrder<'a, S> = &'a dyn Fn(&S, &S) -> Ordering;

/// A reducer multiple: `multiplier · basis[element]`, monic, lead first, columns ascending.
pub struct Reducer<'a, const N: usize, S, F> {
    pub element: u32,
    pub multiplier: Monomial<N>,
    pub lead: Monomial<N>,
    pub signature: S,
    pub row: &'a [(u32, F)],
}

/// A row the batch reduces, in the order the engine reduces them.
pub struct Target<'a, S, F> {
    pub signature: S,
    pub row: &'a [(u32, F)],
}

/// Products of one replay, by the kind of pivot applied.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ArmProducts {
    /// Applications of a reducer at a column the target had when built, and their products.
    pub primary_applications: u64,
    pub primary_products: u64,
    /// Applications of a reducer at a column an earlier application filled in.
    pub secondary_applications: u64,
    pub secondary_products: u64,
    /// Applications of, and products against, pivots this batch discovered (earlier targets'
    /// results).
    pub discovered_applications: u64,
    pub discovered_products: u64,
    /// Every product spent on targets that ended zero.
    pub zero_row_products: u64,
}

impl ArmProducts {
    pub fn reducer_products(&self) -> u64 {
        self.primary_products + self.secondary_products
    }

    /// Multiply-accumulates: a pivot's entries after its lead, per application.
    pub fn total(&self) -> u64 {
        self.reducer_products() + self.discovered_products
    }

    pub fn applications(&self) -> u64 {
        self.primary_applications + self.secondary_applications + self.discovered_applications
    }

    fn add(&mut self, o: &Self) {
        self.primary_applications += o.primary_applications;
        self.primary_products += o.primary_products;
        self.secondary_applications += o.secondary_applications;
        self.secondary_products += o.secondary_products;
        self.discovered_applications += o.discovered_applications;
        self.discovered_products += o.discovered_products;
        self.zero_row_products += o.zero_row_products;
    }

    fn json(&self) -> Json {
        let n = |v: u64| Json::int(v);
        Json::object([
            ("primary_applications", n(self.primary_applications)),
            ("primary_products", n(self.primary_products)),
            ("secondary_applications", n(self.secondary_applications)),
            ("secondary_products", n(self.secondary_products)),
            ("discovered_applications", n(self.discovered_applications)),
            ("discovered_products", n(self.discovered_products)),
            ("zero_row_products", n(self.zero_row_products)),
        ])
    }
}

/// One batch of the census.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct BatchCensus {
    pub batch: usize,
    pub targets: usize,
    pub zero_targets: usize,
    pub reducers: usize,
    pub columns: usize,
    /// Reducers whose `(element, multiplier)` was built in an earlier batch: `CacheMode::Count`'s
    /// repeat.
    pub exact_hits: usize,
    /// Not an exact hit, but `(element, multiplier / x_j)` was built in an earlier batch for some
    /// `x_j`: a one-variable `Simplify` chain step (Faugère 1999, Remark 2.6).
    pub ancestor_hits: usize,
    /// Not an exact hit, but an earlier batch had a reducer with the same leading monomial.
    pub lead_only: usize,
    /// Of `lead_only`, those whose earlier reducer's signature is at most this one's, so it is
    /// admissible wherever this one is. Equal to `lead_only` without a signature bound.
    pub lead_only_admissible: usize,
    /// Entries of the reducer block as built, of the hit reducers as built, and of the block
    /// tail-reduced (`None` when the tail reduction was abandoned).
    pub block_entries: u64,
    pub hit_entries: u64,
    pub reduced_block_entries: Option<u64>,
    /// Products spent tail-reducing the whole block, and the hit reducers' own share of them.
    pub tail_products: u64,
    pub tail_products_hits: u64,
    /// True when tail reduction exceeded its product budget and the reduced arms were not run.
    pub tail_abandoned: bool,
    pub plain: ArmProducts,
    pub reduced: Option<ArmProducts>,
    pub hits_reduced: Option<ArmProducts>,
    /// Targets whose residual differed between arms. Must be zero.
    pub residual_mismatches: usize,
    /// The engine's own product count for the batch, which `plain.total()` must equal.
    pub live_products: Option<u64>,
}

impl BatchCensus {
    pub fn json(&self) -> Json {
        let n = |v: usize| Json::size(v);
        let u = |v: u64| Json::int(v);
        Json::object([
            ("batch", n(self.batch)),
            ("targets", n(self.targets)),
            ("zero_targets", n(self.zero_targets)),
            ("reducers", n(self.reducers)),
            ("columns", n(self.columns)),
            ("exact_hits", n(self.exact_hits)),
            ("ancestor_hits", n(self.ancestor_hits)),
            ("lead_only", n(self.lead_only)),
            ("lead_only_admissible", n(self.lead_only_admissible)),
            ("block_entries", u(self.block_entries)),
            ("hit_entries", u(self.hit_entries)),
            (
                "reduced_block_entries",
                self.reduced_block_entries.map_or(Json::Null, u),
            ),
            ("tail_products", u(self.tail_products)),
            ("tail_products_hits", u(self.tail_products_hits)),
            ("tail_abandoned", Json::Bool(self.tail_abandoned)),
            ("plain", self.plain.json()),
            (
                "reduced",
                self.reduced.as_ref().map_or(Json::Null, ArmProducts::json),
            ),
            (
                "hits_reduced",
                self.hits_reduced
                    .as_ref()
                    .map_or(Json::Null, ArmProducts::json),
            ),
            ("residual_mismatches", n(self.residual_mismatches)),
            ("live_products", self.live_products.map_or(Json::Null, u)),
        ])
    }
}

/// An LRU store of tail-reduced multiples, evicted at batch ends to `factor` times the largest
/// tail-reduced reducer block seen so far.
#[derive(Clone, Debug)]
struct Lru<const N: usize> {
    factor: u64,
    entries: HashMap<(u32, Monomial<N>), (u64, usize), BuildMonomialHasher>,
    total: u64,
    peak: u64,
    hits: u64,
}

/// The run's cross-batch ledger and its per-batch records.
#[derive(Clone, Debug)]
pub struct ReuseCensus<const N: usize, S> {
    /// Per key: the batch it was last built in, its built length and its last tail-reduced length.
    keys: HashMap<(u32, Monomial<N>), (usize, u64, u64), BuildMonomialHasher>,
    /// Per leading monomial: the last reducer that led with it, and its signature.
    leads: HashMap<Monomial<N>, ((u32, Monomial<N>), S), BuildMonomialHasher>,
    store_entries: u64,
    store_built_entries: u64,
    peak_store_entries: u64,
    peak_store_built_entries: u64,
    largest_block: u64,
    lru: Vec<Lru<N>>,
    /// Reuse distances in batches: 1, 2, 3–4, 5–8, 9 and more.
    distances: [u64; 5],
    /// Tail reduction is abandoned past this many times the batch's plain reducer products.
    tail_budget_factor: u64,
    /// Targets stop at their first unpivoted column, as the conventional engine's forward
    /// elimination does; otherwise every pivot column is cleared, as the signature engine does.
    echelon: bool,
    pub batches: Vec<BatchCensus>,
}

impl<const N: usize, S> Default for ReuseCensus<N, S> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize, S> ReuseCensus<N, S> {
    /// Targets reduced through every pivot column, as the signature engine reduces them.
    pub fn new() -> Self {
        Self {
            keys: HashMap::default(),
            leads: HashMap::default(),
            store_entries: 0,
            store_built_entries: 0,
            peak_store_entries: 0,
            peak_store_built_entries: 0,
            largest_block: 0,
            lru: [2, 4]
                .into_iter()
                .map(|factor| Lru {
                    factor,
                    entries: HashMap::default(),
                    total: 0,
                    peak: 0,
                    hits: 0,
                })
                .collect(),
            distances: [0; 5],
            tail_budget_factor: 16,
            echelon: false,
            batches: Vec::new(),
        }
    }

    /// Targets reduced until their leading column has no pivot, as the conventional engine's
    /// forward elimination reduces them. Arms are then compared by leading term only: the tails
    /// left behind depend on the pivots' tails, the leading term does not.
    pub fn echelon() -> Self {
        Self {
            echelon: true,
            ..Self::new()
        }
    }
}

impl<const N: usize, S: Clone> ReuseCensus<N, S> {
    /// Census one batch. `cmp` is the signature order, or `None` when there is no signature bound;
    /// `live_products` is the engine's own count for the batch, when it has one.
    pub fn observe<F: FiniteField>(
        &mut self,
        columns: usize,
        reducers: &[Reducer<'_, N, S, F>],
        targets: &[Target<'_, S, F>],
        cmp: Option<SignatureOrder<'_, S>>,
        live_products: Option<u64>,
    ) {
        let batch = self.batches.len();
        let mut record = BatchCensus {
            batch,
            targets: targets.len(),
            reducers: reducers.len(),
            columns,
            live_products,
            ..Default::default()
        };

        // Signature ranks over the batch, equal signatures sharing one.
        let (reducer_rank, target_rank) = match cmp {
            None => (None, None),
            Some(cmp) => {
                let mut all: Vec<(&S, usize)> = reducers
                    .iter()
                    .map(|r| &r.signature)
                    .chain(targets.iter().map(|t| &t.signature))
                    .zip(0..)
                    .collect();
                all.sort_by(|a, b| cmp(a.0, b.0));
                let mut rank = vec![0u32; all.len()];
                let mut current = 0u32;
                for i in 0..all.len() {
                    if i > 0 && cmp(all[i - 1].0, all[i].0) != Ordering::Equal {
                        current += 1;
                    }
                    rank[all[i].1] = current;
                }
                let targets_rank = rank.split_off(reducers.len());
                (Some(rank), Some(targets_rank))
            }
        };
        let mut at = vec![NONE; columns];
        for (k, r) in reducers.iter().enumerate() {
            at[r.row[0].0 as usize] = k as u32;
        }

        // The cross-batch ledger, read before this batch writes it.
        let mut hit = vec![false; reducers.len()];
        for (k, r) in reducers.iter().enumerate() {
            let key = (r.element, r.multiplier);
            record.block_entries += r.row.len() as u64;
            if let Some(&(last, _, _)) = self.keys.get(&key) {
                hit[k] = true;
                record.exact_hits += 1;
                record.hit_entries += r.row.len() as u64;
                let bucket = match batch - last {
                    1 => 0,
                    2 => 1,
                    3..=4 => 2,
                    5..=8 => 3,
                    _ => 4,
                };
                self.distances[bucket] += 1;
                for lru in &mut self.lru {
                    if lru.entries.contains_key(&key) {
                        lru.hits += 1;
                    }
                }
                continue;
            }
            let ancestor = (0..N).any(|j| {
                r.multiplier
                    .checked_div(&Monomial::univariate(j, 1))
                    .is_some_and(|m| self.keys.contains_key(&(r.element, m)))
            });
            if ancestor {
                record.ancestor_hits += 1;
            }
            if let Some((_, sig)) = self.leads.get(&r.lead) {
                record.lead_only += 1;
                if cmp.is_none_or(|cmp| cmp(sig, &r.signature) != Ordering::Greater) {
                    record.lead_only_admissible += 1;
                }
            }
        }

        let admissible = |k: u32, t: usize| match (&reducer_rank, &target_rank) {
            (Some(rr), Some(tr)) => rr[k as usize] < tr[t],
            _ => true,
        };
        let singular = |lead: u32, t: usize| match (&reducer_rank, &target_rank) {
            (Some(rr), Some(tr)) => {
                at[lead as usize] != NONE && rr[at[lead as usize] as usize] == tr[t]
            }
            _ => false,
        };
        let mut workspace = Workspace::new(columns);

        let plain_rows: Vec<&[(u32, F)]> = reducers.iter().map(|r| r.row).collect();
        let (plain, residuals) = replay(
            &mut workspace,
            &plain_rows,
            &at,
            targets,
            &admissible,
            &singular,
            columns,
            self.echelon,
        );
        record.plain = plain;
        record.zero_targets = residuals.iter().filter(|r| r.is_empty()).count();

        // Tail-reduce the block, rightmost lead first, so every pivot a tail meets is final.
        let budget = self
            .tail_budget_factor
            .saturating_mul(plain.reducer_products().max(1 << 16));
        let mut order: Vec<usize> = (0..reducers.len()).collect();
        order.sort_by_key(|&k| std::cmp::Reverse(reducers[k].row[0].0));
        let mut reduced: Vec<Vec<(u32, F)>> = vec![Vec::new(); reducers.len()];
        for &k in &order {
            let row = reducers[k].row;
            let (tail, products) = workspace.reduce(&row[1..], false, |c| {
                let j = at[c];
                let allowed = j != NONE
                    && match &reducer_rank {
                        Some(rr) => rr[j as usize] < rr[k],
                        None => true,
                    };
                allowed.then(|| (reduced[j as usize].as_slice(), Pivot::Reducer))
            });
            record.tail_products += products.total();
            if hit[k] {
                record.tail_products_hits += products.total();
            }
            let mut out = Vec::with_capacity(tail.len() + 1);
            out.push(row[0]);
            out.extend(tail);
            reduced[k] = out;
            if record.tail_products > budget {
                record.tail_abandoned = true;
                break;
            }
        }

        if !record.tail_abandoned {
            record.reduced_block_entries = Some(reduced.iter().map(|r| r.len() as u64).sum());
            let all: Vec<&[(u32, F)]> = reduced.iter().map(Vec::as_slice).collect();
            let (arm, rows) = replay(
                &mut workspace,
                &all,
                &at,
                targets,
                &admissible,
                &singular,
                columns,
                self.echelon,
            );
            record.reduced = Some(arm);
            record.residual_mismatches += mismatches(&residuals, &rows, self.echelon);
            let mixed: Vec<&[(u32, F)]> = (0..reducers.len())
                .map(|k| if hit[k] { all[k] } else { plain_rows[k] })
                .collect();
            let (arm, rows) = replay(
                &mut workspace,
                &mixed,
                &at,
                targets,
                &admissible,
                &singular,
                columns,
                self.echelon,
            );
            record.hits_reduced = Some(arm);
            record.residual_mismatches += mismatches(&residuals, &rows, self.echelon);
        }

        // Write the ledger and the stores.
        let block = record.reduced_block_entries.unwrap_or(record.block_entries);
        self.largest_block = self.largest_block.max(block);
        for (k, r) in reducers.iter().enumerate() {
            let key = (r.element, r.multiplier);
            let built = r.row.len() as u64;
            let len = if record.tail_abandoned {
                built
            } else {
                reduced[k].len() as u64
            };
            let previous = self.keys.insert(key, (batch, built, len));
            if let Some((_, old_built, old_len)) = previous {
                self.store_entries -= old_len;
                self.store_built_entries -= old_built;
            }
            self.store_entries += len;
            self.store_built_entries += built;
            self.leads.insert(r.lead, (key, r.signature.clone()));
            for lru in &mut self.lru {
                if let Some((old, _)) = lru.entries.insert(key, (len, batch)) {
                    lru.total -= old;
                }
                lru.total += len;
            }
        }
        self.peak_store_entries = self.peak_store_entries.max(self.store_entries);
        self.peak_store_built_entries = self.peak_store_built_entries.max(self.store_built_entries);
        for lru in &mut self.lru {
            let cap = lru.factor * self.largest_block;
            lru.peak = lru.peak.max(lru.total.min(cap));
            if lru.total > cap {
                let mut by_age: Vec<((u32, Monomial<N>), (u64, usize))> =
                    lru.entries.iter().map(|(k, v)| (*k, *v)).collect();
                by_age.sort_by_key(|(_, (_, last))| *last);
                for (key, (len, _)) in by_age {
                    if lru.total <= cap {
                        break;
                    }
                    lru.entries.remove(&key);
                    lru.total -= len;
                }
            }
        }
        self.batches.push(record);
    }

    /// The run's totals, with store sizes in bytes at `bytes_per_term` per stored term.
    pub fn summary_json(&self, bytes_per_term: usize) -> Json {
        let u = |v: u64| Json::int(v);
        let b = bytes_per_term as u64;
        let mut plain = ArmProducts::default();
        let mut reduced = ArmProducts::default();
        let mut hits_reduced = ArmProducts::default();
        let mut plain_where_reduced = ArmProducts::default();
        let sum = |f: fn(&BatchCensus) -> usize| self.batches.iter().map(f).sum::<usize>();
        let sum64 = |f: fn(&BatchCensus) -> u64| self.batches.iter().map(f).sum::<u64>();
        for record in &self.batches {
            plain.add(&record.plain);
            if let (Some(r), Some(h)) = (&record.reduced, &record.hits_reduced) {
                reduced.add(r);
                hits_reduced.add(h);
                plain_where_reduced.add(&record.plain);
            }
        }
        Json::object([
            ("batches", Json::size(self.batches.len())),
            ("targets", Json::size(sum(|r| r.targets))),
            ("zero_targets", Json::size(sum(|r| r.zero_targets))),
            ("reducers", Json::size(sum(|r| r.reducers))),
            ("distinct_keys", Json::size(self.keys.len())),
            ("exact_hits", Json::size(sum(|r| r.exact_hits))),
            ("ancestor_hits", Json::size(sum(|r| r.ancestor_hits))),
            ("lead_only", Json::size(sum(|r| r.lead_only))),
            (
                "lead_only_admissible",
                Json::size(sum(|r| r.lead_only_admissible)),
            ),
            (
                "abandoned_batches",
                Json::size(self.batches.iter().filter(|r| r.tail_abandoned).count()),
            ),
            (
                "residual_mismatches",
                Json::size(sum(|r| r.residual_mismatches)),
            ),
            (
                "live_mismatches",
                Json::size(
                    self.batches
                        .iter()
                        .filter(|r| r.live_products.is_some_and(|p| p != r.plain.total()))
                        .count(),
                ),
            ),
            ("block_entries", u(sum64(|r| r.block_entries))),
            ("hit_entries", u(sum64(|r| r.hit_entries))),
            ("tail_products", u(sum64(|r| r.tail_products))),
            ("tail_products_hits", u(sum64(|r| r.tail_products_hits))),
            ("plain", plain.json()),
            ("plain_where_reduced", plain_where_reduced.json()),
            ("reduced", reduced.json()),
            ("hits_reduced", hits_reduced.json()),
            (
                "reuse_distance",
                Json::Array(self.distances.iter().map(|&d| u(d)).collect()),
            ),
            ("bytes_per_term", Json::size(bytes_per_term)),
            ("store_peak_bytes_reduced", u(self.peak_store_entries * b)),
            (
                "store_peak_bytes_built",
                u(self.peak_store_built_entries * b),
            ),
            ("largest_block_entries", u(self.largest_block)),
            (
                "lru",
                Json::Array(
                    self.lru
                        .iter()
                        .map(|lru| {
                            Json::object([
                                ("factor", u(lru.factor)),
                                ("peak_bytes", u(lru.peak * b)),
                                ("hits_retained", u(lru.hits)),
                            ])
                        })
                        .collect(),
                ),
            ),
        ])
    }

    pub fn batches_json(&self) -> Json {
        Json::Array(self.batches.iter().map(BatchCensus::json).collect())
    }
}

/// The conventional engine's census, as a batch observer: every matrix F4 is about to eliminate,
/// reducer multiples as the block and pair rows as targets in arrival order.
#[derive(Clone, Debug)]
pub struct F4Census<const N: usize> {
    pub census: ReuseCensus<N, ()>,
}

impl<const N: usize> Default for F4Census<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> F4Census<N> {
    pub fn new() -> Self {
        Self {
            census: ReuseCensus::echelon(),
        }
    }
}

impl<const N: usize, F: FiniteField> BatchObserver<N, F> for F4Census<N> {
    fn batch(&mut self, _: &MonicBasis<N, F>, _: &[CriticalPair<N>]) {}

    fn matrix(&mut self, matrix: &MacaulayMatrix<N, F>) {
        let narrow = |index: usize| -> Vec<(u32, F)> {
            matrix
                .matrix()
                .row(index)
                .entries()
                .iter()
                .map(|&(c, v)| (c as u32, v))
                .collect()
        };
        let mut reducer_rows = Vec::new();
        let mut target_rows = Vec::new();
        for (index, origin) in matrix.row_origins().iter().enumerate() {
            match origin.kind {
                RowKind::Reducer => reducer_rows.push((index, narrow(index))),
                RowKind::PairComponent { .. } => target_rows.push(narrow(index)),
            }
        }
        let columns = matrix.columns();
        let reducers: Vec<Reducer<'_, N, (), F>> = reducer_rows
            .iter()
            .map(|(index, row)| {
                let origin = &matrix.row_origins()[*index];
                Reducer {
                    element: origin.basis_index as u32,
                    multiplier: origin.multiplier,
                    lead: columns[row[0].0 as usize],
                    signature: (),
                    row,
                }
            })
            .collect();
        let targets: Vec<Target<'_, (), F>> = target_rows
            .iter()
            .map(|row| Target { signature: (), row })
            .collect();
        self.census
            .observe(matrix.num_columns(), &reducers, &targets, None, None);
    }
}

#[derive(Clone, Copy)]
enum Pivot {
    Reducer,
    Discovered,
}

fn mismatches<F: PartialEq>(a: &[Vec<(u32, F)>], b: &[Vec<(u32, F)>], echelon: bool) -> usize {
    let differ = |x: &Vec<(u32, F)>, y: &Vec<(u32, F)>| {
        if echelon {
            x.first() != y.first()
        } else {
            x != y
        }
    };
    a.iter().zip(b).filter(|(x, y)| differ(x, y)).count() + a.len().abs_diff(b.len())
}

/// Reduce every target, in order, against the reducers in `rows` (where admissible) and the
/// pivots earlier targets discovered. Returns the products and each target's residual.
#[allow(clippy::too_many_arguments)]
fn replay<F: FiniteField, S>(
    workspace: &mut Workspace<F>,
    rows: &[&[(u32, F)]],
    at: &[u32],
    targets: &[Target<'_, S, F>],
    admissible: &dyn Fn(u32, usize) -> bool,
    singular: &dyn Fn(u32, usize) -> bool,
    columns: usize,
    echelon: bool,
) -> (ArmProducts, Vec<Vec<(u32, F)>>) {
    let mut total = ArmProducts::default();
    let mut discovered: Vec<u32> = vec![NONE; columns];
    let mut residuals: Vec<Vec<(u32, F)>> = Vec::with_capacity(targets.len());
    for (t, target) in targets.iter().enumerate() {
        workspace.mark(target.row);
        let (out, products) = workspace.reduce(target.row, echelon, |c| {
            let k = at[c];
            if k != NONE && admissible(k, t) {
                Some((rows[k as usize], Pivot::Reducer))
            } else if discovered[c] != NONE {
                Some((
                    residuals[discovered[c] as usize].as_slice(),
                    Pivot::Discovered,
                ))
            } else {
                None
            }
        });
        total.add(&products);
        let mut out = out;
        match out.first() {
            None => total.zero_row_products += products.total(),
            Some(&(lead, _)) if !singular(lead, t) => {
                let inverse = out[0].1.inverse();
                for (_, v) in &mut out {
                    *v *= inverse;
                }
                discovered[lead as usize] = t as u32;
            }
            Some(_) => {}
        }
        residuals.push(out);
    }
    (total, residuals)
}

/// A dense accumulator with a bitset of possibly-nonzero columns, and a per-column stamp of the
/// row's original columns.
struct Workspace<F> {
    acc: Vec<F>,
    touched: Vec<u64>,
    original: Vec<u32>,
    stamp: u32,
}

impl<F: FiniteField> Workspace<F> {
    fn new(columns: usize) -> Self {
        Self {
            acc: vec![F::zero(); columns],
            touched: vec![0; columns.div_ceil(64)],
            original: vec![0; columns],
            stamp: 0,
        }
    }

    /// Stamp `entries`' columns as the next row's originals.
    fn mark(&mut self, entries: &[(u32, F)]) {
        self.stamp = self.stamp.wrapping_add(1);
        for &(c, _) in entries {
            self.original[c as usize] = self.stamp;
        }
    }

    /// Reduce `entries` column by column with whatever `pivot` offers (monic rows, lead first);
    /// with `echelon`, stop at the first column `pivot` has nothing for and keep the rest as is.
    fn reduce<'p>(
        &mut self,
        entries: &[(u32, F)],
        echelon: bool,
        mut pivot: impl FnMut(usize) -> Option<(&'p [(u32, F)], Pivot)>,
    ) -> (Vec<(u32, F)>, ArmProducts)
    where
        F: 'p,
    {
        let mut products = ArmProducts::default();
        let Some(&(first, _)) = entries.first() else {
            return (Vec::new(), products);
        };
        for &(c, v) in entries {
            let c = c as usize;
            self.acc[c] = v;
            self.touched[c >> 6] |= 1 << (c & 63);
        }
        let mut out = Vec::new();
        let mut stopped = false;
        let mut w = first as usize >> 6;
        while w < self.touched.len() {
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
            if stopped {
                out.push((c as u32, coefficient));
                continue;
            }
            match pivot(c) {
                Some((row, kind)) => {
                    let factor = coefficient.prepare_factor();
                    for (cc, v) in &row[1..] {
                        let cc = *cc as usize;
                        self.acc[cc] -= v.mul_prepared(&factor);
                        self.touched[cc >> 6] |= 1 << (cc & 63);
                    }
                    let n = (row.len() - 1) as u64;
                    match kind {
                        Pivot::Discovered => {
                            products.discovered_applications += 1;
                            products.discovered_products += n;
                        }
                        Pivot::Reducer if self.original[c] == self.stamp => {
                            products.primary_applications += 1;
                            products.primary_products += n;
                        }
                        Pivot::Reducer => {
                            products.secondary_applications += 1;
                            products.secondary_products += n;
                        }
                    }
                }
                None => {
                    out.push((c as u32, coefficient));
                    stopped = echelon;
                }
            }
        }
        (out, products)
    }
}

#[cfg(test)]
mod tests {
    use super::{Reducer, ReuseCensus, Target};
    use crate::{fields::Zp32003, poly::Monomial, FiniteField};

    type F = Zp32003;

    fn m(e: &[u32]) -> Monomial<2> {
        Monomial::new(e)
    }

    fn row(entries: &[(u32, u64)]) -> Vec<(u32, F)> {
        entries.iter().map(|&(c, v)| (c, F::new(v))).collect()
    }

    // Reducer rows over columns 0..4: r0 = c0 + c1, r1 = c1 + c2, r2 = c2 + c3.
    fn chain() -> Vec<Vec<(u32, F)>> {
        vec![
            row(&[(0, 1), (1, 1)]),
            row(&[(1, 1), (2, 1)]),
            row(&[(2, 1), (3, 1)]),
        ]
    }

    fn reducers<'a>(
        rows: &'a [Vec<(u32, F)>],
        keys: &[(u32, [u32; 2])],
    ) -> Vec<Reducer<'a, 2, (), F>> {
        rows.iter()
            .zip(keys)
            .map(|(row, &(element, mult))| Reducer {
                element,
                multiplier: m(&mult),
                lead: m(&[9 - row[0].0, 0]),
                signature: (),
                row,
            })
            .collect()
    }

    // A chain of fill-ins is paid as secondary products as built and vanishes once the block is tail-reduced.
    #[test]
    fn tail_reduction_removes_the_fill_in_chain() {
        let block = chain();
        let target = row(&[(0, 1), (4, 1)]);
        let mut census = ReuseCensus::<2, ()>::new();
        let reducers = reducers(&block, &[(0, [1, 0]), (1, [0, 1]), (2, [0, 0])]);
        let targets = [Target {
            signature: (),
            row: &target,
        }];
        census.observe(5, &reducers, &targets, None, None);
        let record = &census.batches[0];
        assert_eq!(record.plain.primary_applications, 1);
        assert_eq!(record.plain.secondary_applications, 2);
        assert_eq!(record.plain.reducer_products(), 3);
        let reduced = record.reduced.unwrap();
        assert_eq!(reduced.primary_applications, 1);
        assert_eq!(reduced.secondary_applications, 0);
        assert_eq!(reduced.reducer_products(), 1);
        assert_eq!(record.tail_products, 2);
        assert_eq!(record.residual_mismatches, 0);
        assert_eq!(record.exact_hits, 0);
    }

    // A key built in an earlier batch is an exact hit; its one-variable parent is an ancestor hit.
    #[test]
    fn keys_from_earlier_batches_are_hits_and_ancestors() {
        let block = chain();
        let target = row(&[(0, 1)]);
        let targets = [Target {
            signature: (),
            row: &target,
        }];
        let mut census = ReuseCensus::<2, ()>::new();
        census.observe(
            5,
            &reducers(&block, &[(0, [1, 0]), (1, [0, 1]), (2, [0, 0])]),
            &targets,
            None,
            None,
        );
        census.observe(
            5,
            &reducers(&block, &[(0, [1, 0]), (1, [1, 1]), (3, [0, 0])]),
            &targets,
            None,
            None,
        );
        let second = &census.batches[1];
        assert_eq!(second.exact_hits, 1);
        assert_eq!(second.ancestor_hits, 1);
        // Reducer 2 is new, but its leading monomial was led by a different key before.
        assert_eq!(second.lead_only, 2);
        assert_eq!(second.plain.secondary_applications, 2);
        assert_eq!(second.hits_reduced.unwrap().secondary_applications, 0);
        assert_eq!(second.residual_mismatches, 0);
    }

    // Under a signature bound a reducer of larger signature neither reduces the target nor another reducer.
    #[test]
    fn a_signature_bound_limits_both_pivots_and_tail_reduction() {
        let block = chain();
        let target = row(&[(0, 1), (4, 1)]);
        let mut census = ReuseCensus::<2, u32>::new();
        let keys = [(0, [1, 0]), (1, [0, 1]), (2, [0, 0])];
        let sigs = [1u32, 5, 2];
        let reducers: Vec<Reducer<'_, 2, u32, F>> = block
            .iter()
            .zip(keys.iter().zip(sigs))
            .map(|(row, (&(element, mult), signature))| Reducer {
                element,
                multiplier: m(&mult),
                lead: m(&[9 - row[0].0, 0]),
                signature,
                row,
            })
            .collect();
        let targets = [Target {
            signature: 3u32,
            row: &target,
        }];
        let cmp = |a: &u32, b: &u32| a.cmp(b);
        census.observe(5, &reducers, &targets, Some(&cmp), None);
        let record = &census.batches[0];
        // r0 applies; r1 (signature 5) is inadmissible, so column 1 stays.
        assert_eq!(record.plain.reducer_products(), 1);
        // r0 may not be tail-reduced by r1, and r1 by r2 is allowed but r1 never applies.
        assert_eq!(record.reduced.unwrap().reducer_products(), 1);
        assert_eq!(record.tail_products, 1);
        assert_eq!(record.residual_mismatches, 0);
    }

    // A target that a discovered pivot zeroes is charged to the zero-row products.
    #[test]
    fn a_repeated_target_is_a_zero_row_against_the_discovered_pivot() {
        let block = chain();
        let a = row(&[(0, 1), (4, 2)]);
        let b = row(&[(0, 3), (4, 6)]);
        let mut census = ReuseCensus::<2, ()>::new();
        let targets = [
            Target {
                signature: (),
                row: &a,
            },
            Target {
                signature: (),
                row: &b,
            },
        ];
        census.observe(
            5,
            &reducers(&block, &[(0, [1, 0]), (1, [0, 1]), (2, [0, 0])]),
            &targets,
            None,
            None,
        );
        let record = &census.batches[0];
        assert_eq!(record.zero_targets, 1);
        // Each target pays the three-step chain; the second then meets the first's residual.
        assert_eq!(record.plain.discovered_products, 1);
        assert_eq!(record.plain.zero_row_products, 4);
        assert_eq!(record.residual_mismatches, 0);
    }

    // On the signature engine the census changes no basis, its as-built replay reproduces the
    // engine's own products in every batch, and no arm changes any target's residual.
    #[test]
    fn the_signature_engine_census_is_faithful_and_inert() {
        use crate::{
            fields::Zp2147483647,
            grobner::{
                benchmark_systems::{cyclic, katsura},
                sigf4::{sig_f4_reported, SigF4Options},
            },
            MonomialOrder,
        };
        type G = Zp2147483647;
        let order = MonomialOrder::GradedReverseLexicographic;
        let census = SigF4Options {
            reuse_census: true,
            ..SigF4Options::default()
        };
        let systems: [Vec<crate::MultivariatePolynomial<6, G>>; 2] = [katsura(), cyclic()];
        for system in systems {
            let (plain, _) = sig_f4_reported(&system, order, &SigF4Options::default());
            let (counted, stats) = sig_f4_reported(&system, order, &census);
            assert_eq!(plain.unwrap(), counted.unwrap());
            let (summary, batches) = stats.reuse.expect("census requested");
            let int = |key: &str| summary.get(key).and_then(|v| v.as_int()).unwrap();
            assert_eq!(int("batches") as usize, stats.batches);
            assert_eq!(int("batches") as usize, batches.items().len());
            assert_eq!(int("residual_mismatches"), 0);
            assert_eq!(int("live_mismatches"), 0);
            assert_eq!(int("reducers") as usize, stats.reducer_rows);
            assert!(int("exact_hits") > 0);
        }
    }

    // Design 2 and the claim cascade count products differently, so the census declines them.
    #[test]
    fn the_signature_engine_census_is_serial_only() {
        use crate::{
            fields::Zp2147483647,
            grobner::{
                benchmark_systems::katsura,
                sigf4::{sig_f4_reported, SigF4Options},
            },
            MonomialOrder,
        };
        let options = SigF4Options {
            reuse_census: true,
            workers: 2,
            ..SigF4Options::default()
        };
        let system = katsura::<5, Zp2147483647>();
        let (_, stats) =
            sig_f4_reported(&system, MonomialOrder::GradedReverseLexicographic, &options);
        assert!(stats.reuse.is_none());
    }

    // On the conventional engine the census changes no basis, counts exactly CacheMode::Count's
    // repeats, and its as-built replay reproduces the forward ledger's products batch by batch.
    #[test]
    fn the_conventional_census_matches_cache_count_and_the_ledger() {
        use super::F4Census;
        use crate::{
            fields::Zp2147483647,
            grobner::{
                benchmark_systems::{cyclic, katsura},
                f4_observed, f4_with_options, CacheMode, F4Options, ParallelForward,
                ParallelSymbolic,
            },
            MonomialOrder,
        };
        type G = Zp2147483647;
        let order = MonomialOrder::GradedReverseLexicographic;
        let options = F4Options {
            reducer_cache: CacheMode::Count,
            parallel_forward: ParallelForward::Serial,
            parallel_symbolic: ParallelSymbolic::Serial,
            ..F4Options::default()
        };
        let systems: [Vec<crate::MultivariatePolynomial<6, G>>; 2] = [katsura(), cyclic()];
        for system in systems {
            let plain = f4_with_options(&system, order, &F4Options::default())
                .unwrap()
                .0;
            let mut observer = F4Census::<6>::new();
            let ((basis, stats), ledger) = crate::linalg::work::measure(|| {
                f4_observed(&system, order, &options, &mut observer).unwrap()
            });
            assert_eq!(plain, basis);
            let census = &observer.census;
            assert_eq!(census.batches.len(), stats.batches);
            let hits: usize = census.batches.iter().map(|b| b.exact_hits).sum();
            assert_eq!(hits, stats.reducer_rows_reused);
            assert!(census.batches.iter().all(|b| b.residual_mismatches == 0));
            assert_eq!(ledger.batches.len(), census.batches.len());
            // The ledger charges a pivot's lead too: one product more per application.
            for (record, batch) in census.batches.iter().zip(&ledger.batches) {
                assert_eq!(
                    record.plain.total() + record.plain.applications(),
                    batch.forward.coefficient_products as u64
                );
                assert_eq!(batch.forward.reducer_target_operations, 0);
            }
        }
    }
}
