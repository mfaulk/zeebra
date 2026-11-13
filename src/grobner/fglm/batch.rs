//! Border targets reduce independently against an immutable triangular symbolic closure; targets must never become pivots for one another.

use std::{
    hash::{DefaultHasher, Hash, Hasher},
    time::Duration,
};

use crate::poly::MonomialMap;

use crate::{
    grobner::{
        f4::{MonicBasis, StageClock},
        fglm::{BorderIndex, FglmError, QuotientBasis},
    },
    FiniteField, Monomial, MonomialOrder, MultivariatePolynomial,
};

/// How many border monomials to reduce in one batch.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BorderBatchSize {
    /// Every distinct border monomial in one batch.
    ///
    /// The largest closure and the most sharing, and **not the right choice everywhere**. It is the
    /// fastest size on katsura and cyclic and the slowest on the planted family, where a reduction
    /// is one step and the closure is most of the work — planted-10 takes about 41 ms unbounded
    /// against 27 ms at a size of one, measured in §6.7 of
    /// `docs/MILESTONE-FGLM-SCALABILITY.md`. Kept for measurement and for a caller who knows their
    /// staircase.
    Unbounded,

    /// At most this many targets per batch, in the border's own descending order.
    ///
    /// Several batches then each build their own closure, so the sharing is within a batch and not
    /// across them — which is the whole trade, and it runs in opposite directions on the two
    /// families. Measured, 64 is the size that is **faster than the scalar path on every system in
    /// the corpus**, which is why [`BorderBatch::recommended`] uses it. §6.4 of
    /// `docs/MILESTONE-FGLM-SCALABILITY.md` has the figures.
    Fixed(usize),
}

impl Default for BorderBatchSize {
    /// `Fixed(64)`, the size measured faster than the scalar path on every system in the corpus.
    ///
    /// Not `Unbounded`, which is faster on katsura and slower than scalar on the planted family —
    /// a default has to be right on both.
    fn default() -> Self {
        Self::Fixed(64)
    }
}

impl BorderBatchSize {
    /// Targets per batch, with [`Self::Unbounded`] reported as the total.
    pub(super) fn chunk(&self, total: usize) -> usize {
        match self {
            Self::Unbounded => total.max(1),
            Self::Fixed(size) => (*size).max(1),
        }
    }
}

/// What to do when a batch crosses one of its limits.
///
/// **Neither option drops a target.** The milestone's §6.5 is explicit about that, and the two
/// policies differ only in whether the caller is told to try something else or does it themselves.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum BatchOverflow {
    /// Return a structured error. The caller decides what to do.
    #[default]
    Fail,

    /// Reduce that batch's targets one at a time with the scalar path instead.
    ///
    /// The scalar path builds no closure and no matrix, so it cannot cross these limits — it is the
    /// fallback that always exists. Counted in [`BorderBatchStatistics::fallbacks`], so a run that
    /// quietly took it is visible.
    Scalar,
}

/// Limits on what one batch may build, and what to do if it would exceed them.
///
/// Every limit is on the **representation**: rows enumerated, columns mapped, entries stored. A
/// batch's closure is discovered a row at a time with no way to know its size in advance, so these
/// are checked as it grows rather than computed up front — a batch that would need a million
/// reducer multiples must not allocate them all before anyone notices.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BorderBatch {
    /// Targets per batch.
    pub size: BorderBatchSize,

    /// Reducer multiples one batch's closure may hold.
    pub max_reducer_rows: usize,

    /// Distinct monomials one batch's closure may reach, i.e. matrix columns.
    pub max_columns: usize,

    /// Entries the reducer rows may hold between them.
    pub max_nonzeros: usize,

    /// What to do when one of the above is crossed.
    pub on_overflow: BatchOverflow,

    /// How to run a batch's target loop. See [`BorderReduction`].
    pub reduction: BorderReduction,
}

/// How a batch's target loop is decomposed.
///
/// The targets of a batch are independent — the pivots are fixed before any of them is touched, so
/// `NF(u_1)` cannot involve `u_2` — and the loop may therefore be split anywhere without changing
/// an answer. Both variants are the *same arithmetic* in two decompositions, and both return the
/// remainders in target order.
///
/// What a split costs is the `dirty_from` carry. `reduce_targets` keeps the previous target's
/// leading column and zeroes only `[previous start, width)` before the next, and the border
/// descends so that region shrinks across a batch. A group's first target has no predecessor and
/// starts from a freshly zeroed buffer of the closure's full width, so `G` groups pay about `G`
/// widths where one pays one — counted exactly in
/// [`BorderBatchStatistics::buffer_cells_zeroed`].
///
/// **Neither variant is concurrent.** The decomposition is the half of parallelism that can be
/// taken without putting `Send + Sync` on the conversion's whole public surface, and §6.8 of
/// `docs/MILESTONE-FGLM-SCALABILITY.md` is why it was not worth paying for the other half:
/// [`measure_border_reduction`] runs the groups on threads and the batches are too small for it to
/// pay.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum BorderReduction {
    /// One group: the carry runs the length of the batch.
    ///
    /// The default, and the fastest, because the carry is a saving and a split gives it up.
    #[default]
    Sequential,

    /// Contiguous groups, run one after another.
    ///
    /// Buys **nothing on its own** — it is the decomposition a parallel reduction would use with
    /// the threads left out, so the carry's cost can be measured apart from the dispatch cost
    /// instead of tangled with it. Zero and one both mean one group.
    Grouped(usize),
}

impl BorderReduction {
    /// Contiguous groups the targets are split into, which is one for the sequential path.
    pub(super) fn groups(&self) -> usize {
        match self {
            Self::Sequential => 1,
            Self::Grouped(groups) => (*groups).max(1),
        }
    }
}

impl Default for BorderBatch {
    fn default() -> Self {
        Self::recommended()
    }
}

impl BorderBatch {
    /// A batch size that is never the wrong choice, and limits high enough not to interfere.
    ///
    /// **64 targets**, because that is the size measured faster than the scalar path on every
    /// system in the corpus. Larger is better on katsura and cyclic and worse on the planted
    /// family, and 64 is within 13% of the best size on the first and 11% on the second — so it
    /// gives up a little of katsura's 15.7x rather than turning planted's win into a loss.
    ///
    /// 200,000 reducer rows and columns is about 30x the largest closure in the benchmark corpus,
    /// and 20 million entries is F4's live-nonzero figure. The point of them is to stop a batch
    /// whose closure is exploding, not to tune one that is not.
    pub fn recommended() -> Self {
        Self {
            size: BorderBatchSize::Fixed(64),
            max_reducer_rows: 200_000,
            max_columns: 200_000,
            max_nonzeros: 20_000_000,
            on_overflow: BatchOverflow::Fail,
            reduction: BorderReduction::Sequential,
        }
    }

    /// No limit worth reaching, for measurement.
    pub fn unbounded() -> Self {
        Self {
            size: BorderBatchSize::Unbounded,
            max_reducer_rows: usize::MAX,
            max_columns: usize::MAX,
            max_nonzeros: usize::MAX,
            on_overflow: BatchOverflow::Fail,
            reduction: BorderReduction::Sequential,
        }
    }

    /// These limits with a different batch size.
    pub fn with_size(self, size: BorderBatchSize) -> Self {
        Self { size, ..self }
    }

    /// These limits with a different overflow policy.
    pub fn with_overflow(self, on_overflow: BatchOverflow) -> Self {
        Self {
            on_overflow,
            ..self
        }
    }

    /// These limits with a different target-loop decomposition. See [`BorderReduction`].
    pub fn with_reduction(self, reduction: BorderReduction) -> Self {
        Self { reduction, ..self }
    }
}

/// What the batched border reduction did.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct BorderBatchStatistics {
    /// Batches attempted.
    pub batches: usize,

    /// Batches that crossed a limit and were reduced scalar-wise instead.
    ///
    /// Nonzero only under [`BatchOverflow::Scalar`]. A run where this is nonzero did not do what
    /// the caller asked, and saying so is the point of counting it.
    pub fallbacks: usize,

    /// Reducer multiples across every batch's closure.
    pub reducer_rows: usize,

    /// Columns across every batch, i.e. distinct monomials the closures reached.
    ///
    /// Summed, not deduplicated between batches: it is the work done, not the monomials involved.
    pub columns: usize,

    /// Entries the reducer rows held, summed over batches.
    pub reducer_entries: usize,

    /// The largest single batch's reducer entries, which is what bounds the live storage.
    pub peak_reducer_entries: usize,

    /// Field-element cells the reduction buffers had zeroed, by allocation or by a clear.
    ///
    /// The `dirty_from` carry stated in the one unit the decompositions can be compared in. A
    /// freshly allocated buffer is already zero, so a group of targets pays the closure's full
    /// width once at its start and then only `[previous start, width)` per target — and
    /// `BorderBatch::reduction_groups` groups pay about `G` widths where one pays one. Counted
    /// always, like the other counters here, because one `usize` add per target is nothing beside
    /// the column scan it accompanies.
    pub buffer_cells_zeroed: usize,

    /// Wall clock building the batches' symbolic closures.
    ///
    /// Zero unless [`FglmOptions::measure_stages`](super::FglmOptions::measure_stages) is set, and
    /// a strict refinement of [`FglmStageTimings::border_symbolic`](super::FglmStageTimings) —
    /// that field charges both halves of a batch together, these two split it.
    pub closure_time: Duration,

    /// Wall clock reducing the batches' targets against those closures.
    ///
    /// The other half of [`Self::closure_time`], and the half whose inner loop is independent per
    /// target.
    pub reduction_time: Duration,

    /// The largest single batch's reduction time.
    ///
    /// **The figure that decides whether parallelising the target loop can pay**, which is why it
    /// is peaked rather than summed: a parallel reduction dispatches once per batch, so what it has
    /// to beat is one batch's work and not the stage's. §6.4 of
    /// `docs/MILESTONE-SIMD-PARALLELISM.md` asks for exactly this measurement and §6.8 of
    /// `docs/MILESTONE-FGLM-SCALABILITY.md` reports it.
    pub peak_reduction_time: Duration,
}

impl BorderBatchStatistics {
    /// Fold another batch's figures into these.
    pub(super) fn add(&mut self, other: &Self) {
        self.batches += other.batches;
        self.fallbacks += other.fallbacks;
        self.reducer_rows += other.reducer_rows;
        self.columns += other.columns;
        self.reducer_entries += other.reducer_entries;
        self.peak_reducer_entries = self.peak_reducer_entries.max(other.peak_reducer_entries);
        self.buffer_cells_zeroed += other.buffer_cells_zeroed;
        self.closure_time += other.closure_time;
        self.reduction_time += other.reduction_time;
        self.peak_reduction_time = self.peak_reduction_time.max(other.peak_reduction_time);
    }
}

/// One target's normal form, as `(monomial, coefficient)` pairs over standard monomials.
pub(super) type Remainder<const N: usize, F> = Vec<(Monomial<N>, F)>;

/// One batch's symbolic closure: a reducer row per reducible monomial, over a shared column map.
///
/// Built once per batch and then read-only, which is what "fixed reducer pivots" means in code.
#[derive(Clone, Debug)]
pub(super) struct Closure<const N: usize, F: FiniteField> {
    /// Every monomial the closure reached, descending by the order. Column `c` is `columns[c]`.
    columns: Vec<Monomial<N>>,

    /// `column_of[m]` is `m`'s column index.
    column_of: MonomialMap<N, usize>,

    /// For a reducible column, the reducer row leading at it, as `(column, coefficient)` pairs
    /// ascending by column. Monic at its leading column, which is the first entry.
    ///
    /// `None` for a standard column, which is what makes the descending pass stop reducing there.
    reducer_of_column: Vec<Option<Vec<(usize, F)>>>,
}

impl<const N: usize, F: FiniteField> Closure<N, F> {
    /// Columns in the closure.
    pub(super) fn columns(&self) -> usize {
        self.columns.len()
    }

    /// Reducer rows in the closure.
    pub(super) fn reducer_rows(&self) -> usize {
        self.reducer_of_column
            .iter()
            .filter(|row| row.is_some())
            .count()
    }

    /// Entries the reducer rows hold between them.
    pub(super) fn reducer_entries(&self) -> usize {
        self.reducer_of_column
            .iter()
            .filter_map(|row| row.as_ref().map(Vec::len))
            .sum()
    }

    /// Whether the column for `monomial` has a reducer row, i.e. whether `monomial` is reducible.
    ///
    /// `None` if the monomial is not in the closure at all. Test-only: the closure's consumers read
    /// the remainders, and this exists so the invariant of §6.4 can be checked *directly* rather
    /// than inferred from the answers being right.
    #[cfg(test)]
    pub(super) fn is_reducible(&self, monomial: &Monomial<N>) -> Option<bool> {
        self.column_of
            .get(monomial)
            .map(|column| self.reducer_of_column[*column].is_some())
    }

    /// Every monomial the closure reached. Test-only, for the same reason as
    /// [`Self::is_reducible`].
    #[cfg(test)]
    pub(super) fn monomials(&self) -> &[Monomial<N>] {
        &self.columns
    }
}

/// The symbolic closure of `targets` under reduction by `basis`.
///
/// # Errors
/// [`FglmError::BorderBatchExceeded`] if the closure crosses one of `limits`, checked as it grows.
pub(super) fn closure<const N: usize, F: FiniteField>(
    targets: &[Monomial<N>],
    basis: &MonicBasis<N, F>,
    order: MonomialOrder,
    limits: &BorderBatch,
) -> Result<Closure<N, F>, FglmError> {
    // Monomial -> the reducer multiple leading at it, before columns are numbered. A monomial with
    // no entry here is standard; a monomial absent from the map entirely has not been seen.
    let mut reducer_of: MonomialMap<N, Option<Vec<(Monomial<N>, F)>>> = MonomialMap::default();
    let mut pending: Vec<Monomial<N>> = targets.to_vec();
    let mut rows = 0usize;
    let mut entries = 0usize;

    while let Some(monomial) = pending.pop() {
        if reducer_of.contains_key(&monomial) {
            continue;
        }
        if reducer_of.len() >= limits.max_columns {
            return Err(FglmError::BorderBatchExceeded {
                reason: "columns",
                limit: limits.max_columns,
            });
        }

        match basis.find_divisor(&monomial) {
            None => {
                reducer_of.insert(monomial, None);
            }
            Some((index, multiplier)) => {
                let terms: Vec<(Monomial<N>, F)> =
                    basis.shifted_terms(index, &multiplier).collect();
                debug_assert_eq!(
                    terms.first().map(|(m, _)| *m),
                    Some(monomial),
                    "a shifted reducer must lead with the monomial it reduces"
                );

                rows += 1;
                if rows > limits.max_reducer_rows {
                    return Err(FglmError::BorderBatchExceeded {
                        reason: "reducer rows",
                        limit: limits.max_reducer_rows,
                    });
                }
                entries =
                    entries
                        .checked_add(terms.len())
                        .ok_or(FglmError::BorderBatchExceeded {
                            reason: "reducer entries",
                            limit: limits.max_nonzeros,
                        })?;
                if entries > limits.max_nonzeros {
                    return Err(FglmError::BorderBatchExceeded {
                        reason: "reducer entries",
                        limit: limits.max_nonzeros,
                    });
                }

                // Every monomial of the multiple joins the closure, which is what makes the
                // invariant in §6.4 hold: nothing reducible is left without a row.
                for (support, _) in &terms {
                    if !reducer_of.contains_key(support) {
                        pending.push(*support);
                    }
                }
                reducer_of.insert(monomial, Some(terms));
            }
        }
    }

    // Columns descending by the order, so a column index below another means a larger monomial and
    // a single forward pass suffices.
    let mut columns: Vec<Monomial<N>> = reducer_of.keys().copied().collect();
    columns.sort_by(|a, b| order.cmp(b, a));
    let column_of: MonomialMap<N, usize> = columns
        .iter()
        .enumerate()
        .map(|(index, monomial)| (*monomial, index))
        .collect();

    let reducer_of_column: Vec<Option<Vec<(usize, F)>>> = columns
        .iter()
        .map(|monomial| {
            reducer_of[monomial].as_ref().map(|terms| {
                let mut row: Vec<(usize, F)> = terms
                    .iter()
                    .map(|(support, coefficient)| (column_of[support], *coefficient))
                    .collect();
                row.sort_unstable_by_key(|(column, _)| *column);
                row
            })
        })
        .collect();

    Ok(Closure {
        columns,
        column_of,
        reducer_of_column,
    })
}

/// Each target's normal form, as coefficients over the closure's standard columns.
///
/// One descending pass per target against the **fixed** reducer rows. A target is never a pivot, so
/// `reduce(u_1)` cannot involve `u_2`, and the `k` answers are the same `k` answers the scalar path
/// would give.
///
/// The buffer is cleared and read over the region a target can dirty rather than the closure's full
/// width. `buffer[start] = one` is the only seed and a reducer row leading at `c` has its other
/// entries at columns after `c`, so every write for a target lands at or after its leading column
/// and `[0, start)` stays zero. Targets arrive in the border's descending order, so `start` grows
/// across a batch and the saving approaches the full width by its last target.
///
/// # The split
/// `groups` contiguous groups of targets, each with its own buffer and its own carry, and the
/// remainders returned **in target order** regardless of it. Splitting is sound for the reason
/// above: a target's answer is a function of the target and the closure alone. What it costs is the
/// `dirty_from` carry — the groups are contiguous and the border descends, so monotonicity holds
/// *inside* a group and only a group's first target pays the full width. Zero and one both mean one
/// group, and more groups than targets means one target each.
///
/// The groups run one after another. That is deliberate: it is the decomposition a parallel
/// reduction would use, with the thread-dispatch cost left out, so the carry's cost can be measured
/// apart from it. §6.8 of `docs/MILESTONE-FGLM-SCALABILITY.md` reports both.
///
/// # Returns
/// The remainders, and the field-element cells the groups' buffers had zeroed between them.
///
/// # Panics
/// If a target is not in the closure, which means it was not among the monomials the closure was
/// built from.
pub(super) fn reduce_targets<const N: usize, F: FiniteField>(
    targets: &[Monomial<N>],
    closure: &Closure<N, F>,
    reduction: BorderReduction,
) -> (Vec<Remainder<N, F>>, usize) {
    let (mut results, block) = split(targets, reduction.groups());
    let mut zeroed = 0usize;
    for (slots, group) in results.chunks_mut(block).zip(targets.chunks(block)) {
        zeroed += reduce_group(group, closure, slots);
    }
    (results, zeroed)
}

/// [`reduce_targets`] with one contiguous group per worker, each on its own scoped thread.
///
/// **Measurement only, and not reachable from a conversion.** Making the conversion able to call
/// this means `F: Send + Sync` on `fglm_to_lex`, `QuotientAlgebra::new`,
/// `solve_zero_dimensional_with_options` and the differential harness — the whole public surface
/// that reaches a border batch — and §6.8 of `docs/MILESTONE-FGLM-SCALABILITY.md` measured that
/// there is nothing to buy with it. The code is here because the refutation is a measurement rather
/// than an argument, and it cannot be remeasured later from a path that does not exist.
///
/// Zero and one worker both run on this thread with no thread spawned at all.
fn reduce_targets_on_workers<const N: usize, F: FiniteField + Send + Sync>(
    targets: &[Monomial<N>],
    closure: &Closure<N, F>,
    workers: usize,
) -> (Vec<Remainder<N, F>>, usize) {
    if workers <= 1 {
        return reduce_targets(targets, closure, BorderReduction::Sequential);
    }

    let (mut results, block) = split(targets, workers);

    // Static blocks, like `sample_determinants`: every target is one descending scan of the same
    // closure, so the blocks are comparable work by construction and a shared counter would only
    // add contention. The per-group cell counts come back through a pre-sized vector for the same
    // reason the remainders do — a running total behind a lock would be a figure that depended on
    // the interleaving.
    let mut cells: Vec<usize> = vec![0; results.chunks(block).len()];
    std::thread::scope(|scope| {
        for ((slots, group), count) in results
            .chunks_mut(block)
            .zip(targets.chunks(block))
            .zip(cells.iter_mut())
        {
            scope.spawn(move || {
                *count = reduce_group(group, closure, slots);
            });
        }
    });
    (results, cells.iter().sum())
}

/// Somewhere for every target's answer, and the block size `groups` implies.
///
/// **Pre-sized and written through contiguous blocks**, so each slot is written by exactly one group
/// from exactly one target and the sequence is a function of `targets` alone — not of which group
/// finished first. That is what makes a concurrent decomposition's answers the sequential one's,
/// rather than something to be checked afterwards.
///
/// `div_ceil` so the blocks cover every target: a short tail means fewer groups than asked for,
/// never more, and never a target left unreduced.
fn split<const N: usize, F: FiniteField>(
    targets: &[Monomial<N>],
    groups: usize,
) -> (Vec<Remainder<N, F>>, usize) {
    let results: Vec<Remainder<N, F>> = vec![Vec::new(); targets.len()];
    let block = targets.len().div_ceil(groups.max(1)).max(1);
    (results, block)
}

/// One group of targets reduced into `slots`, returning the cells its buffer had zeroed.
///
/// The whole of the reduction's arithmetic, and the only place it lives: the sequential path is this
/// called once and a split path is this called per group, so the two cannot compute differently.
fn reduce_group<const N: usize, F: FiniteField>(
    targets: &[Monomial<N>],
    closure: &Closure<N, F>,
    slots: &mut [Remainder<N, F>],
) -> usize {
    let mut buffer = vec![F::zero(); closure.columns.len()];
    reduce_group_with_buffer(targets, closure, slots, &mut buffer)
}

fn reduce_group_with_buffer<const N: usize, F: FiniteField>(
    targets: &[Monomial<N>],
    closure: &Closure<N, F>,
    slots: &mut [Remainder<N, F>],
    buffer: &mut [F],
) -> usize {
    // The previous target's leading column, below which the buffer is known to be zero. Starts at
    // the width because a freshly allocated buffer is zero everywhere.
    let mut dirty_from = closure.columns.len();

    // The allocation above zeroed a full width, which is the group's share of the carry's cost.
    let mut zeroed = closure.columns.len();

    for (target, slot) in targets.iter().zip(slots) {
        let start = *closure
            .column_of
            .get(target)
            .expect("a target outside the closure it was built from");
        debug_assert!(
            buffer[..dirty_from].iter().all(|slot| slot.is_zero()),
            "the buffer below the previous target's column must still be zero"
        );
        zeroed += closure.columns.len() - dirty_from;
        buffer[dirty_from..]
            .iter_mut()
            .for_each(|slot| *slot = F::zero());
        dirty_from = start;
        buffer[start] = F::one();

        // Descending the columns once. A reducer row leading at `c` has every other entry strictly
        // below `c` in the order, hence at a larger index, so nothing already passed is disturbed.
        // The scan runs to the end rather than stopping at the first standard column: a standard
        // monomial can be larger than a reducible one.
        for column in start..closure.columns.len() {
            let factor = buffer[column];
            if factor.is_zero() {
                continue;
            }
            let Some(row) = &closure.reducer_of_column[column] else {
                continue;
            };
            for (target_column, coefficient) in row {
                buffer[*target_column] -= factor * *coefficient;
            }
            debug_assert!(
                buffer[column].is_zero(),
                "a monic reducer must clear its own column"
            );
        }

        // From `start`, not from zero: `buffer[start] = one` is the only seed and every write below
        // lands at a column at or after it, so nothing before `start` can be nonzero.
        *slot = buffer[start..]
            .iter()
            .enumerate()
            .filter(|(_, value)| !value.is_zero())
            .map(|(offset, value)| {
                let column = start + offset;
                debug_assert!(
                    closure.reducer_of_column[column].is_none(),
                    "a reducible monomial survived the reduction"
                );
                (closure.columns[column], *value)
            })
            .collect();
    }

    zeroed
}

/// One batch of border monomials reduced, and what it cost.
///
/// `measure` splits the batch's wall clock between the closure and the reduction. Two clock reads
/// per batch, which is why it is a flag: the batch count is small, but a caller who is not
/// measuring should not pay even that. The split is what §6.4 of
/// `docs/MILESTONE-SIMD-PARALLELISM.md` asks anyone revisiting parallelism to start from — the size
/// of a *batch's* parallelizable phase rather than a stage's share of the total.
///
/// # Errors
/// As [`closure`].
pub(super) fn reduce_batch<const N: usize, F: FiniteField>(
    targets: &[Monomial<N>],
    basis: &MonicBasis<N, F>,
    order: MonomialOrder,
    limits: &BorderBatch,
    measure: bool,
) -> Result<(Vec<Remainder<N, F>>, BorderBatchStatistics), FglmError> {
    let mut clock = StageClock::new(measure);
    let closure = closure(targets, basis, order, limits)?;
    let closure_time = clock.lap();

    let (remainders, buffer_cells_zeroed) = reduce_targets(targets, &closure, limits.reduction);
    let reduction_time = clock.lap();

    let statistics = BorderBatchStatistics {
        batches: 1,
        fallbacks: 0,
        reducer_rows: closure.reducer_rows(),
        columns: closure.columns(),
        reducer_entries: closure.reducer_entries(),
        peak_reducer_entries: closure.reducer_entries(),
        buffer_cells_zeroed,
        closure_time,
        reduction_time,
        peak_reduction_time: reduction_time,
    };
    Ok((remainders, statistics))
}

/// Fold one batch's statistics into a running total.
pub(super) fn accumulate(total: &mut BorderBatchStatistics, batch: &BorderBatchStatistics) {
    total.add(batch);
}

/// What the whole border's batched reduction costs at a given worker count, and what it computed.
///
/// **A measurement entry point, not a route into the conversion.** It exists because the parallel
/// decomposition's refutation in §6.8 of `docs/MILESTONE-FGLM-SCALABILITY.md` is a measurement, and
/// a measurement that cannot be repeated is an assertion. `workers` above one runs the contiguous
/// groups on scoped threads — which is why this and not
/// [`fglm_to_lex_with_options`](super::fglm_to_lex_with_options) carries `F: Send + Sync`.
///
/// `digest` hashes every remainder in target order, so a caller compares worker counts for
/// **bit-identical** answers with one equality rather than by holding `|∂B|` remainders. It is a
/// within-process digest and not a stable wire format.
///
/// # Errors
/// As `closure`, and [`FglmError`] from enumerating the standard monomials.
pub fn measure_border_reduction<const N: usize, F: FiniteField + Send + Sync>(
    source_basis: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    limits: &BorderBatch,
    workers: usize,
) -> Result<(BorderBatchStatistics, u64), FglmError> {
    let quotient = QuotientBasis::new(source_basis, order, usize::MAX)?;
    let targets = BorderIndex::new(&quotient).monomials().to_vec();

    let nonzero: Vec<MultivariatePolynomial<N, F>> = source_basis
        .iter()
        .filter(|p| !p.is_zero())
        .cloned()
        .collect();
    let monic = MonicBasis::new(&nonzero, order);

    let mut total = BorderBatchStatistics::default();
    let mut hasher = DefaultHasher::new();
    for group in targets.chunks(limits.size.chunk(targets.len())) {
        let mut clock = StageClock::new(true);
        let closed = closure(group, &monic, order, limits)?;
        let closure_time = clock.lap();

        let (remainders, buffer_cells_zeroed) = reduce_targets_on_workers(group, &closed, workers);
        let reduction_time = clock.lap();

        for remainder in &remainders {
            remainder.hash(&mut hasher);
        }
        total.add(&BorderBatchStatistics {
            batches: 1,
            fallbacks: 0,
            reducer_rows: closed.reducer_rows(),
            columns: closed.columns(),
            reducer_entries: closed.reducer_entries(),
            peak_reducer_entries: closed.reducer_entries(),
            buffer_cells_zeroed,
            closure_time,
            reduction_time,
            peak_reduction_time: reduction_time,
        });
    }
    Ok((total, hasher.finish()))
}

/// An owned group for research executors, sharing one immutable closure per batch.
#[cfg(feature = "research-work")]
pub struct BorderReductionTask<const N: usize, F: FiniteField> {
    data: std::sync::Arc<(Vec<Monomial<N>>, Closure<N, F>)>,
    range: std::ops::Range<usize>,
    index: usize,
}

/// An ordered group's complete remainders; fields are private to prevent fabricated results.
#[cfg(feature = "research-work")]
pub struct BorderReductionResult<const N: usize, F: FiniteField> {
    remainders: Vec<Remainder<N, F>>,
    zeroed: usize,
    index: usize,
}

#[cfg(feature = "research-work")]
impl<const N: usize, F: FiniteField> BorderReductionTask<N, F> {
    /// Reduce this group with reusable scratch; every active cell is cleared before reuse.
    pub fn run(self, scratch: &mut Vec<F>) -> BorderReductionResult<N, F> {
        let width = self.data.1.columns.len();
        let reused = scratch.len().min(width);
        scratch[..reused].fill(F::zero());
        scratch.resize(width, F::zero());
        let mut remainders = vec![Vec::new(); self.range.len()];
        let zeroed = reduce_group_with_buffer(
            &self.data.0[self.range],
            &self.data.1,
            &mut remainders,
            scratch,
        );
        BorderReductionResult {
            remainders,
            zeroed,
            index: self.index,
        }
    }
}

/// Measure owned task dispatch without changing the conversion or its public field bounds.
///
/// Only available with `research-work`. The callback must finish every submitted group before
/// returning. Closure construction, task ownership/collection and clearing are timed; executor
/// construction is the caller's responsibility. Scratch capacities and RSS are separate from
/// `max_scratch_cells`, which bounds active field cells for one batch, not retained allocations.
///
/// # Errors
/// Returns the existing closure/quotient errors, or `BorderBatchExceeded` with reason
/// `"worker scratch cells"` before dispatch if this explicit research allowance is insufficient.
///
/// # Panics
/// Panics if the dispatcher drops, duplicates or corrupts the ordered groups.
#[cfg(feature = "research-work")]
pub fn measure_border_reduction_with<const N: usize, F: FiniteField + Send + Sync>(
    source_basis: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    limits: &BorderBatch,
    workers: usize,
    max_scratch_cells: usize,
    mut dispatch: impl FnMut(Vec<BorderReductionTask<N, F>>) -> Vec<BorderReductionResult<N, F>>,
) -> Result<(BorderBatchStatistics, u64), FglmError> {
    let quotient = QuotientBasis::new(source_basis, order, usize::MAX)?;
    let targets = BorderIndex::new(&quotient).monomials().to_vec();
    let nonzero: Vec<_> = source_basis
        .iter()
        .filter(|p| !p.is_zero())
        .cloned()
        .collect();
    let monic = MonicBasis::new(&nonzero, order);
    let mut total = BorderBatchStatistics::default();
    let mut hasher = DefaultHasher::new();
    for group in targets.chunks(limits.size.chunk(targets.len())) {
        let mut clock = StageClock::new(true);
        let closed = closure(group, &monic, order, limits)?;
        let closure_time = clock.lap();
        let block = group.len().div_ceil(workers.max(1)).max(1);
        let count = group.len().div_ceil(block);
        if closed
            .columns()
            .checked_mul(count)
            .is_none_or(|cells| cells > max_scratch_cells)
        {
            return Err(FglmError::BorderBatchExceeded {
                reason: "worker scratch cells",
                limit: max_scratch_cells,
            });
        }
        let columns = closed.columns();
        let reducer_rows = closed.reducer_rows();
        let reducer_entries = closed.reducer_entries();
        let data = std::sync::Arc::new((group.to_vec(), closed));
        let tasks = (0..count)
            .map(|index| BorderReductionTask {
                data: data.clone(),
                range: index * block..((index + 1) * block).min(group.len()),
                index,
            })
            .collect();
        let mut results = dispatch(tasks);
        assert_eq!(results.len(), count, "dispatcher dropped a group");
        results.sort_unstable_by_key(|r| r.index);
        let mut zeroed = 0;
        for (index, result) in results.iter().enumerate() {
            assert_eq!(result.index, index, "dispatcher duplicated a group");
            assert_eq!(
                result.remainders.len(),
                (group.len() - index * block).min(block)
            );
            zeroed += result.zeroed;
        }
        let reduction_time = clock.lap();
        for result in results {
            for remainder in result.remainders {
                remainder.hash(&mut hasher);
            }
        }
        total.add(&BorderBatchStatistics {
            batches: 1,
            fallbacks: 0,
            columns,
            reducer_rows,
            reducer_entries,
            peak_reducer_entries: reducer_entries,
            buffer_cells_zeroed: zeroed,
            closure_time,
            reduction_time,
            peak_reduction_time: reduction_time,
        });
    }
    Ok((total, hasher.finish()))
}

#[cfg(test)]
mod tests {
    use super::{
        closure, measure_border_reduction, reduce_batch, reduce_targets, BatchOverflow,
        BorderBatch, BorderBatchSize, BorderReduction,
    };
    use crate::{
        fields::Zp2147483647,
        grobner::{
            benchmark_systems::{cyclic, katsura, planted},
            f4,
            f4::MonicBasis,
            fglm::{BorderIndex, FglmError, FglmOptions, QuotientBasis},
        },
        FiniteField, MonomialOrder, MultivariatePolynomial, One, Zero,
    };

    type F = Zp2147483647;

    const ORDERS: [MonomialOrder; 3] = [
        MonomialOrder::Lexicographic,
        MonomialOrder::GradedLexicographic,
        MonomialOrder::GradedReverseLexicographic,
    ];

    const SYSTEMS: [&[&str]; 6] = [
        &["x^2", "y^2"],
        &["x^2 - y", "y^3 - 1"],
        &["x + y", "x*y - 1"],
        &["x^3 - 1", "y - x^2"],
        &["x^2 - 2*x + 1", "y - x"],
        &["x^4 - x", "y^2 - x"],
    ];

    fn parse<const N: usize>(
        system: &[&str],
        variables: [&str; N],
    ) -> Vec<MultivariatePolynomial<N, F>> {
        system
            .iter()
            .map(|s| MultivariatePolynomial::parse(s, variables).unwrap())
            .collect()
    }

    /// The source basis, its standard monomials, its border, and the basis made monic.
    fn setup<const N: usize>(
        system: &[MultivariatePolynomial<N, F>],
        order: MonomialOrder,
    ) -> (
        Vec<MultivariatePolynomial<N, F>>,
        QuotientBasis<N>,
        Vec<crate::Monomial<N>>,
        MonicBasis<N, F>,
    ) {
        let basis = f4(system, order).expect("within limits");
        let quotient = QuotientBasis::new(&basis, order, usize::MAX).expect("finite");
        let border = BorderIndex::new(&quotient).monomials().to_vec();
        let monic = MonicBasis::new(&basis, order);
        (basis, quotient, border, monic)
    }

    /// Every monomial a closure reaches that is reducible has a reducer row leading at it.
    ///
    /// §6.4's symbolic closure invariant, tested directly rather than inferred from the answers
    /// being right. A monomial reachable from a target or from a reducer multiple, reducible by the
    /// basis and *without* a row, is a monomial the reduction would leave in the remainder — which
    /// is how an incomplete closure fails.
    #[test]
    fn test_the_closure_invariant_holds() {
        fn check<const N: usize>(
            name: &str,
            system: &[MultivariatePolynomial<N, F>],
            order: MonomialOrder,
        ) {
            let (_, _, border, monic) = setup(system, order);
            if border.is_empty() {
                return;
            }
            let closed =
                closure(&border, &monic, order, &BorderBatch::unbounded()).expect("within limits");

            for monomial in closed.monomials() {
                let reducible = monic.find_divisor(monomial).is_some();
                assert_eq!(
                    closed.is_reducible(monomial),
                    Some(reducible),
                    "{} under {:?}: {} is {} reducible and the closure says otherwise",
                    name,
                    order,
                    monomial,
                    if reducible { "" } else { "not" }
                );
            }

            // And every target is in it, which is the other half of being closed *from* them.
            for target in &border {
                assert!(
                    closed.is_reducible(target).is_some(),
                    "{} under {:?}: target {} is not in its own closure",
                    name,
                    order,
                    target
                );
            }
        }

        for order in ORDERS {
            for system in SYSTEMS {
                check(system[0], &parse(system, ["x", "y"]), order);
            }
            check("katsura-3", &katsura::<3, F>(), order);
        }
        let grevlex = MonomialOrder::GradedReverseLexicographic;
        check("katsura-5", &katsura::<5, F>(), grevlex);
        check("cyclic-5", &cyclic::<5, F>(), grevlex);
    }

    /// A batch's remainders are the scalar normal forms, target for target.
    ///
    /// The whole correctness requirement, and stated against `normal_form` rather than against
    /// another batch: the scalar reduction is the reference the milestone names.
    #[test]
    fn test_a_batch_agrees_with_the_scalar_normal_forms() {
        fn check<const N: usize>(
            name: &str,
            system: &[MultivariatePolynomial<N, F>],
            order: MonomialOrder,
        ) {
            let (basis, _, border, monic) = setup(system, order);
            if border.is_empty() {
                return;
            }

            // Every batch size the milestone names, so the answer is checked to be independent of
            // how the targets were grouped.
            for size in [
                BorderBatchSize::Fixed(1),
                BorderBatchSize::Fixed(4),
                BorderBatchSize::Fixed(16),
                BorderBatchSize::Fixed(64),
                BorderBatchSize::Unbounded,
            ] {
                let chunk = size.chunk(border.len());
                let mut remainders = Vec::new();
                for group in border.chunks(chunk) {
                    let (batch, _) =
                        reduce_batch(group, &monic, order, &BorderBatch::unbounded(), false)
                            .expect("within limits");
                    remainders.extend(batch);
                }

                assert_eq!(remainders.len(), border.len(), "a target was dropped");
                for (target, remainder) in border.iter().zip(&remainders) {
                    let expected = MultivariatePolynomial::new(&[(*target, F::one())])
                        .normal_form(&basis, order);
                    let got: MultivariatePolynomial<N, F> = MultivariatePolynomial::new(remainder);
                    assert_eq!(
                        got, expected,
                        "{} under {:?} at {:?}: NF({}) disagrees with the scalar reduction",
                        name, order, size, target
                    );
                }
            }
        }

        for order in ORDERS {
            for system in SYSTEMS {
                check(system[0], &parse(system, ["x", "y"]), order);
            }
            check("katsura-3", &katsura::<3, F>(), order);
        }
        let grevlex = MonomialOrder::GradedReverseLexicographic;
        check("katsura-5", &katsura::<5, F>(), grevlex);
        check("katsura-6", &katsura::<6, F>(), grevlex);
        check("cyclic-5", &cyclic::<5, F>(), grevlex);
        let point: Vec<F> = [3u64, 5, 7, 11, 13, 17]
            .iter()
            .map(|v| F::new(*v))
            .collect();
        check("planted-6", &planted::<6, F>(&point), grevlex);
    }

    /// A target's answer does not depend on which other targets shared its batch.
    ///
    /// §6.2's requirement that targets must not eliminate one another, stated as an observable
    /// property: reducing `u` alone and reducing it beside every other border monomial must give
    /// the same remainder. An implementation that let targets become pivots would fail this.
    #[test]
    fn test_a_target_does_not_depend_on_its_batch() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let (_, _, border, monic) = setup(&katsura::<5, F>(), order);
        assert!(border.len() > 4);

        let (together, _) = reduce_batch(&border, &monic, order, &BorderBatch::unbounded(), false)
            .expect("within limits");

        for (position, target) in border.iter().enumerate() {
            let (alone, _) = reduce_batch(
                std::slice::from_ref(target),
                &monic,
                order,
                &BorderBatch::unbounded(),
                false,
            )
            .expect("within limits");
            assert_eq!(
                alone[0], together[position],
                "NF({}) depends on what shared its batch",
                target
            );
        }

        // And the reverse grouping: the same targets in the opposite order must give the same
        // answers, matched up by target rather than by position.
        let mut reversed = border.clone();
        reversed.reverse();
        let (backwards, _) =
            reduce_batch(&reversed, &monic, order, &BorderBatch::unbounded(), false)
                .expect("within limits");
        for (position, target) in reversed.iter().enumerate() {
            let forwards = border.iter().position(|m| m == target).expect("a target");
            assert_eq!(
                backwards[position], together[forwards],
                "NF({}) depends on the order of its batch",
                target
            );
        }
    }

    /// Every remainder's monomials are standard, which is what makes it a coordinate vector.
    #[test]
    fn test_every_remainder_is_standard() {
        let order = MonomialOrder::GradedReverseLexicographic;
        for system in [katsura::<5, F>(), cyclic::<5, F>()] {
            let (_, quotient, border, monic) = setup(&system, order);
            let closed =
                closure(&border, &monic, order, &BorderBatch::unbounded()).expect("within limits");
            for remainder in reduce_targets(&border, &closed, BorderReduction::Sequential).0 {
                for (monomial, coefficient) in &remainder {
                    assert!(
                        !coefficient.is_zero(),
                        "a zero coefficient survived into a remainder"
                    );
                    assert!(
                        quotient.index_of(monomial).is_some(),
                        "{} is in a remainder and is not standard",
                        monomial
                    );
                }
            }
        }
    }

    /// A target whose column is below the previous target's gets the same remainder regardless.
    ///
    /// The reduction buffer is only cleared over the region the previous target could have dirtied,
    /// `[previous start, len)`. Targets arrive in the border's descending order, so `start`
    /// normally grows and that region covers everything written; this feeds them *ascending*
    /// instead, so each `start` is below the last and the cleared region is a strict subset of the
    /// buffer. A buffer cleared from the wrong index leaves a stale coefficient at a column the
    /// next target never reaches, which this catches.
    #[test]
    fn test_a_target_below_the_previous_one_is_unaffected_by_it() {
        let order = MonomialOrder::GradedReverseLexicographic;
        for system in [katsura::<5, F>(), cyclic::<5, F>()] {
            let (_, _, border, monic) = setup(&system, order);
            assert!(border.len() > 4);
            let closed =
                closure(&border, &monic, order, &BorderBatch::unbounded()).expect("within limits");

            // The border descends, so reversing it makes every `start` smaller than the last.
            let mut ascending = border.clone();
            ascending.reverse();
            let together = reduce_targets(&ascending, &closed, BorderReduction::Sequential).0;
            for (position, target) in ascending.iter().enumerate() {
                let alone = reduce_targets(
                    std::slice::from_ref(target),
                    &closed,
                    BorderReduction::Sequential,
                )
                .0;
                assert_eq!(
                    together[position], alone[0],
                    "NF({}) depends on the target reduced before it",
                    target
                );
            }
        }
    }

    /// Splitting the target loop into groups changes no remainder and no target's position.
    ///
    /// The requirement a parallel reduction would stand or fall on, stated against the one-group
    /// path: the targets are independent, so any contiguous split must give **bit-identical**
    /// answers in **target order**. Field arithmetic is exact, so there is no reassociation to
    /// excuse a difference. Checked at more groups than there are targets, which is the degenerate
    /// split of one target each.
    #[test]
    fn test_splitting_the_target_loop_changes_no_answer() {
        fn check<const N: usize>(
            name: &str,
            system: &[MultivariatePolynomial<N, F>],
            order: MonomialOrder,
        ) {
            let (_, _, border, monic) = setup(system, order);
            if border.is_empty() {
                return;
            }

            for size in [
                BorderBatchSize::Fixed(1),
                BorderBatchSize::Fixed(7),
                BorderBatchSize::Fixed(64),
                BorderBatchSize::Unbounded,
            ] {
                let chunk = size.chunk(border.len());
                for group in border.chunks(chunk) {
                    let closed = closure(group, &monic, order, &BorderBatch::unbounded())
                        .expect("within limits");
                    let (reference, _) =
                        reduce_targets(group, &closed, BorderReduction::Sequential);
                    for groups in [1usize, 2, 3, 4, 8, 16, 32, 128, 1_000] {
                        let (got, _) =
                            reduce_targets(group, &closed, BorderReduction::Grouped(groups));
                        assert_eq!(
                            got, reference,
                            "{} under {:?} at {:?}: {} groups disagree with one",
                            name, order, size, groups
                        );
                    }
                    // Zero groups is one group rather than a division by zero.
                    assert_eq!(
                        reduce_targets(group, &closed, BorderReduction::Grouped(0)).0,
                        reference
                    );
                }
            }
        }

        for order in ORDERS {
            for system in SYSTEMS {
                check(system[0], &parse(system, ["x", "y"]), order);
            }
            check("katsura-3", &katsura::<3, F>(), order);
        }
        let grevlex = MonomialOrder::GradedReverseLexicographic;
        check("katsura-5", &katsura::<5, F>(), grevlex);
        check("katsura-6", &katsura::<6, F>(), grevlex);
        check("cyclic-5", &cyclic::<5, F>(), grevlex);
        let point: Vec<F> = [3u64, 5, 7, 11, 13, 17]
            .iter()
            .map(|v| F::new(*v))
            .collect();
        check("planted-6", &planted::<6, F>(&point), grevlex);
    }

    /// The cells a split zeroes are one full width per group plus each target's own dirty tail.
    ///
    /// The `dirty_from` accounting, pinned against a model built from the targets' leading columns
    /// rather than from the implementation. This is the quantity the parallel decomposition gives
    /// up: the model says `groups * width` for the buffers plus `width - previous start` per target
    /// after a group's first, so a split pays about one extra width per extra group.
    #[test]
    fn test_a_split_costs_one_full_width_of_zeroing_per_group() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let (_, _, border, monic) = setup(&katsura::<6, F>(), order);
        let closed =
            closure(&border, &monic, order, &BorderBatch::unbounded()).expect("within limits");
        let width = closed.columns();
        assert!(border.len() > 16 && width > 16);

        // What the two paths zero, from the targets' columns alone.
        let model = |groups: usize| {
            let block = border.len().div_ceil(groups.max(1)).max(1);
            let mut cells = 0usize;
            for group in border.chunks(block) {
                cells += width;
                let mut dirty_from = width;
                for target in group {
                    cells += width - dirty_from;
                    dirty_from = closed.column_of[target];
                }
            }
            cells
        };

        let one = reduce_targets(&border, &closed, BorderReduction::Sequential).1;
        assert_eq!(one, model(1), "the one-group accounting");
        for groups in [1usize, 2, 4, 8, 16, 32] {
            let got = reduce_targets(&border, &closed, BorderReduction::Grouped(groups)).1;
            assert_eq!(got, model(groups), "the accounting at {} groups", groups);
        }

        // And the direction: more groups zero more cells, by under a width each.
        let two = reduce_targets(&border, &closed, BorderReduction::Grouped(2)).1;
        assert!(two > one, "a second group must cost a buffer");
        assert!(
            two - one <= width,
            "a second group costs at most one full width"
        );
    }

    /// The parallel reduction's answers are the sequential ones, at every worker count.
    ///
    /// Determinism across thread counts, asserted directly rather than through a downstream basis:
    /// the digest hashes every remainder in target order, so an answer that differed in one
    /// coefficient or arrived in a different position changes it. Field arithmetic is exact, so
    /// there is no reassociation to excuse a difference — and the counters must agree too, except
    /// `buffer_cells_zeroed`, which **is** the carry and is expected to grow with the workers.
    #[test]
    fn test_the_parallel_reduction_is_bit_identical_at_every_worker_count() {
        fn check<const N: usize>(
            name: &str,
            system: &[MultivariatePolynomial<N, F>],
            order: MonomialOrder,
        ) {
            let basis = f4(system, order).expect("within limits");
            for size in [
                BorderBatchSize::Fixed(1),
                BorderBatchSize::Fixed(7),
                BorderBatchSize::Fixed(64),
                BorderBatchSize::Unbounded,
            ] {
                let limits = BorderBatch::unbounded().with_size(size);
                let (sequential, digest) =
                    measure_border_reduction(&basis, order, &limits, 1).expect("within limits");

                for workers in [1usize, 2, 3, 4, 8, 16, 32, 64, 128] {
                    let (statistics, got) =
                        measure_border_reduction(&basis, order, &limits, workers)
                            .expect("within limits");
                    assert_eq!(
                        got, digest,
                        "{} at {:?}: {} workers computed different remainders",
                        name, size, workers
                    );
                    assert_eq!(
                        statistics.reducer_entries, sequential.reducer_entries,
                        "{} at {:?}: {} workers changed the closure",
                        name, size, workers
                    );
                    assert!(
                        statistics.buffer_cells_zeroed >= sequential.buffer_cells_zeroed,
                        "{} at {:?}: {} workers zeroed fewer cells than one",
                        name,
                        size,
                        workers
                    );
                }
            }
        }

        let grevlex = MonomialOrder::GradedReverseLexicographic;
        for order in ORDERS {
            check("katsura-3", &katsura::<3, F>(), order);
        }
        check("katsura-5", &katsura::<5, F>(), grevlex);
        check("katsura-6", &katsura::<6, F>(), grevlex);
        check("cyclic-5", &cyclic::<5, F>(), grevlex);
        let point: Vec<F> = [3u64, 5, 7, 11, 13, 17]
            .iter()
            .map(|v| F::new(*v))
            .collect();
        check("planted-6", &planted::<6, F>(&point), grevlex);
    }

    /// A limit that the closure crosses is a structured error naming which limit.
    #[test]
    fn test_a_crossed_limit_is_a_structured_error() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let (_, _, border, monic) = setup(&katsura::<5, F>(), order);

        for (limits, reason) in [
            (
                BorderBatch::unbounded().with_size(BorderBatchSize::Unbounded),
                "columns",
            ),
            (BorderBatch::unbounded(), "reducer rows"),
            (BorderBatch::unbounded(), "reducer entries"),
        ] {
            let mut limits = limits;
            match reason {
                "columns" => limits.max_columns = 1,
                "reducer rows" => limits.max_reducer_rows = 1,
                _ => limits.max_nonzeros = 1,
            }
            match closure(&border, &monic, order, &limits) {
                Err(FglmError::BorderBatchExceeded { reason: got, .. }) => {
                    assert_eq!(got, reason)
                }
                other => panic!("expected a {} error, got ok = {}", reason, other.is_ok()),
            }
        }
    }

    /// The fallback policy reduces a batch it cannot do scalar-wise, and says that it did.
    #[test]
    fn test_the_fallback_reduces_rather_than_dropping() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let basis = f4(&katsura::<5, F>(), order).expect("within limits");

        // A column limit of one makes every batch overflow, so every target takes the fallback.
        let limits = BorderBatch::unbounded().with_overflow(BatchOverflow::Scalar);
        let mut limits = limits;
        limits.max_columns = 1;

        let options = FglmOptions::unbounded()
            .with_operator_construction(crate::grobner::fglm::OperatorConstruction::BatchedBorder)
            .with_border_batch(limits);

        let (algebra, statistics) =
            crate::grobner::fglm::QuotientAlgebra::new_with_statistics(&basis, order, &options)
                .expect("the fallback should finish");

        assert!(statistics.batches.fallbacks > 0, "no batch fell back");
        assert_eq!(
            statistics.batches.fallbacks, statistics.batches.batches,
            "every batch should have fallen back at a column limit of one"
        );
        // And the answer is still the reference answer.
        let reference =
            crate::grobner::fglm::QuotientAlgebra::new(&basis, order, &FglmOptions::unbounded())
                .expect("finite");
        assert_eq!(algebra, reference, "the fallback changed the operators");
    }

    /// A measured conversion splits each batch's clock between the closure and the reduction.
    ///
    /// The finer split §6.4 of `docs/MILESTONE-SIMD-PARALLELISM.md` asks for: the two halves are
    /// both nonzero, they do not exceed the `border_symbolic` figure that charges them together,
    /// and the peak is one batch's reduction rather than the stage's. Unmeasured, the durations are
    /// zero and the cell counter is not.
    #[test]
    fn test_a_measured_batch_splits_the_closure_from_the_reduction() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let basis = f4(&katsura::<6, F>(), order).expect("within limits");
        let batched = FglmOptions::unbounded()
            .with_operator_construction(crate::grobner::fglm::OperatorConstruction::BatchedBorder)
            .with_border_batch(BorderBatch::unbounded().with_size(BorderBatchSize::Fixed(16)));

        let mut measured = batched;
        measured.measure_stages = true;
        let (_, statistics) =
            crate::grobner::fglm::QuotientAlgebra::new_with_statistics(&basis, order, &measured)
                .expect("finite");
        let batches = statistics.batches;

        assert!(batches.batches > 1, "the split needs several batches");
        assert!(!batches.closure_time.is_zero(), "the closure was not timed");
        assert!(
            !batches.reduction_time.is_zero(),
            "the reduction was not timed"
        );
        assert!(
            batches.closure_time + batches.reduction_time <= statistics.timings.border_symbolic,
            "the halves exceed the figure that charges them together"
        );
        assert!(
            batches.peak_reduction_time <= batches.reduction_time,
            "a peak above the sum"
        );
        assert!(
            !batches.peak_reduction_time.is_zero(),
            "no batch's reduction was timed"
        );
        assert!(batches.buffer_cells_zeroed > 0, "no buffer was zeroed");

        let (_, unmeasured) =
            crate::grobner::fglm::QuotientAlgebra::new_with_statistics(&basis, order, &batched)
                .expect("finite");
        assert!(
            unmeasured.batches.closure_time.is_zero()
                && unmeasured.batches.reduction_time.is_zero()
                && unmeasured.batches.peak_reduction_time.is_zero(),
            "an unmeasured conversion read the clock"
        );
        assert_eq!(
            unmeasured.batches.buffer_cells_zeroed, batches.buffer_cells_zeroed,
            "the cell counter depends on whether the clock was read"
        );
    }

    /// Splitting the reduction into groups leaves the operators and every other counter alone.
    ///
    /// The whole-conversion half of the equivalence: a split path must agree with the sequential
    /// one on the operators *and* on the statistics that are not the carry's own accounting, so a
    /// caller cannot tell which decomposition ran except by the cells it zeroed.
    #[test]
    fn test_a_split_reduction_changes_nothing_but_the_cells_it_zeroed() {
        fn check<const N: usize>(name: &str, system: &[MultivariatePolynomial<N, F>]) {
            let order = MonomialOrder::GradedReverseLexicographic;
            let basis = f4(system, order).expect("within limits");
            let batched = FglmOptions::unbounded().with_operator_construction(
                crate::grobner::fglm::OperatorConstruction::BatchedBorder,
            );
            let (reference, reference_statistics) =
                crate::grobner::fglm::QuotientAlgebra::new_with_statistics(&basis, order, &batched)
                    .expect("finite");

            for groups in [2usize, 4, 16, 128] {
                let split = batched.with_border_batch(
                    BorderBatch::unbounded().with_reduction(BorderReduction::Grouped(groups)),
                );
                let (algebra, statistics) =
                    crate::grobner::fglm::QuotientAlgebra::new_with_statistics(
                        &basis, order, &split,
                    )
                    .expect("finite");
                assert_eq!(
                    algebra, reference,
                    "{}: {} groups changed the operators",
                    name, groups
                );
                assert_eq!(
                    statistics.batches.reducer_entries,
                    reference_statistics.batches.reducer_entries,
                    "{}: {} groups changed the closure",
                    name,
                    groups
                );
                assert!(
                    statistics.batches.buffer_cells_zeroed
                        > reference_statistics.batches.buffer_cells_zeroed,
                    "{}: {} groups zeroed no more cells than one",
                    name,
                    groups
                );
            }
        }

        check("katsura-6", &katsura::<6, F>());
        check("cyclic-5", &cyclic::<5, F>());
    }

    /// The failing policy returns the error rather than falling back.
    #[test]
    fn test_the_failing_policy_fails() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let basis = f4(&katsura::<5, F>(), order).expect("within limits");

        let mut limits = BorderBatch::unbounded().with_overflow(BatchOverflow::Fail);
        limits.max_columns = 1;
        let options = FglmOptions::unbounded()
            .with_operator_construction(crate::grobner::fglm::OperatorConstruction::BatchedBorder)
            .with_border_batch(limits);

        assert!(matches!(
            crate::grobner::fglm::QuotientAlgebra::new(&basis, order, &options),
            Err(FglmError::BorderBatchExceeded { .. })
        ));
    }
}

#[cfg(all(test, feature = "research-work"))]
mod dispatch_tests {
    use super::*;
    use crate::{fields::Zp2147483647 as F, One};

    fn basis() -> Vec<MultivariatePolynomial<2, F>> {
        ["x^2 - y", "y^3 - 1"]
            .iter()
            .map(|p| MultivariatePolynomial::parse(p, ["x", "y"]).unwrap())
            .collect()
    }

    // Owned dispatched batches reproduce scalar remainders with dirty reused scratch and reversed completion.
    #[test]
    fn dispatched_remainders_agree_with_scalar() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let basis = basis();
        for workers in [1, 2, 7] {
            let limits = BorderBatch::recommended().with_size(BorderBatchSize::Fixed(2));
            let reference = measure_border_reduction(&basis, order, &limits, 1).unwrap();
            let got =
                measure_border_reduction_with(&basis, order, &limits, workers, 100_000, |tasks| {
                    let mut scratch = vec![F::ONE; 200];
                    tasks
                        .into_iter()
                        .rev()
                        .map(|task| task.run(&mut scratch))
                        .collect()
                })
                .unwrap();
            assert_eq!(got.1, reference.1);
            assert_eq!(got.0.reducer_entries, reference.0.reducer_entries);
        }
    }

    // Reused scratch yields every exact scalar coefficient across prime widths and characteristic two.
    #[test]
    fn exact_remainders_across_fields() {
        fn check<G: FiniteField>() {
            let order = MonomialOrder::GradedReverseLexicographic;
            let basis: Vec<MultivariatePolynomial<2, G>> = ["x^2 - y", "y^3 - 1"]
                .iter()
                .map(|p| MultivariatePolynomial::parse(p, ["x", "y"]).unwrap())
                .collect();
            let quotient = QuotientBasis::new(&basis, order, 100).unwrap();
            let targets = BorderIndex::new(&quotient).monomials().to_vec();
            let monic = MonicBasis::new(&basis, order);
            let closed = closure(&targets, &monic, order, &BorderBatch::recommended()).unwrap();
            let reference = reduce_targets(&targets, &closed, BorderReduction::Sequential).0;
            let task = BorderReductionTask {
                data: std::sync::Arc::new((targets.clone(), closed)),
                range: 0..targets.len(),
                index: 0,
            };
            let mut scratch = vec![G::ONE; 300];
            assert_eq!(task.run(&mut scratch).remainders, reference);
        }
        check::<crate::fields::Zp2>();
        check::<crate::fields::Zp32003>();
        check::<F>();
        check::<crate::fields::Gf256Mq>();
    }

    // Scratch and closure refusals occur before handing any batch to workers.
    #[test]
    fn dispatch_budgets_refuse_before_execution() {
        let basis = basis();
        let mut calls = 0;
        let result = measure_border_reduction_with(
            &basis,
            MonomialOrder::GradedReverseLexicographic,
            &BorderBatch::recommended(),
            2,
            0,
            |_| {
                calls += 1;
                Vec::new()
            },
        );
        assert!(matches!(
            result,
            Err(FglmError::BorderBatchExceeded {
                reason: "worker scratch cells",
                limit: 0
            })
        ));
        assert_eq!(calls, 0);
        let mut limits = BorderBatch::recommended();
        limits.max_columns = 1;
        let result = measure_border_reduction_with(
            &basis,
            MonomialOrder::GradedReverseLexicographic,
            &limits,
            2,
            100_000,
            |_| {
                calls += 1;
                Vec::new()
            },
        );
        assert!(matches!(
            result,
            Err(FglmError::BorderBatchExceeded {
                reason: "columns",
                limit: 1
            })
        ));
        assert_eq!(calls, 0);
    }

    // A dispatcher that drops results cannot report a complete mathematical answer.
    #[test]
    #[should_panic(expected = "dispatcher dropped a group")]
    fn dispatch_requires_all_results() {
        let _ = measure_border_reduction_with(
            &basis(),
            MonomialOrder::GradedReverseLexicographic,
            &BorderBatch::recommended(),
            2,
            100_000,
            |_| Vec::new(),
        );
    }
}
