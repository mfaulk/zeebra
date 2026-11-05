//! Many border monomials reduced at once, sharing the symbolic work and the reducer multiples.
//!
//! M18-1 removed the duplicated reductions. What is left is `|∂B|` independent normal forms, each
//! of which searches the basis for a divisor, builds a multiple, and subtracts it — through
//! `MultivariatePolynomial`'s `HashMap`, once per step. F4's answer to the same shape of problem is
//! to do the symbolic work for a whole batch once and the arithmetic over integer column indices,
//! and that is what this does for border monomials.
//!
//! # The targets must not reduce one another
//! This is the one way a batch here differs from an F4 batch, and it is not a detail. An F4 matrix
//! is echelonized: any row may become a pivot, and rows reduce each other. Here **each target has
//! its own answer** — `NF(u_1)` must not involve `u_2` — so the pivots are *fixed* before any
//! target is touched, every pivot is a reducer multiple, and no target ever becomes one.
//!
//! That is also why `linalg::reduce_rows_against_pivots_with` is not what runs below. Its contract
//! is to echelonize the lower block against an upper one, which for these targets would be the
//! wrong computation rather than a slower one.
//!
//! # The closure
//! Start from the targets. For every monomial `m` seen, if some `LM(g)` divides `m`, add the
//! reducer multiple `(m / LM(g)) * g` and look at its monomials too. Stop when nothing new appears.
//!
//! Each reducible monomial then has **exactly one** reducer row, whose leading monomial it is, and
//! whose other monomials are strictly below it. So the reducer rows are a triangular system in the
//! order's own column indexing, and reducing a target is one descending pass: at each column with a
//! nonzero, subtract that column's reducer row if it has one. Nothing can reintroduce a nonzero in
//! a column already passed.
//!
//! **The pass cannot stop at the first standard column.** A standard monomial can be *larger* than
//! a nonstandard one — with `G = {x^2, y^2}` under grevlex, `xy` is standard and `y^2 < xy` is not —
//! so the scan runs to the end of the columns.
//!
//! §6 of `docs/MILESTONE-FGLM-SCALABILITY.md` has the measurements, including why the batch size is
//! bounded rather than left unbounded.
//!
//! # References
//! * Faugère, J.-C. (1999), *A new efficient algorithm for computing Gröbner bases (F4)*, for the
//!   symbolic-preprocessing-then-linear-algebra shape.
//! * *An Algorithm for Splitting Polynomial Systems Based on F4*, PASCO 2017, for F4-style
//!   preprocessing in support of quotient-algebra normal forms.

use std::collections::HashMap;

use crate::{
    grobner::{f4::MonicBasis, fglm::FglmError},
    FiniteField, Monomial, MonomialOrder,
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
    column_of: HashMap<Monomial<N>, usize>,

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
    let mut reducer_of: HashMap<Monomial<N>, Option<Vec<(Monomial<N>, F)>>> = HashMap::new();
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
    let column_of: HashMap<Monomial<N>, usize> = columns
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
/// # Panics
/// If a target is not in the closure, which means it was not among the monomials the closure was
/// built from.
pub(super) fn reduce_targets<const N: usize, F: FiniteField>(
    targets: &[Monomial<N>],
    closure: &Closure<N, F>,
) -> Vec<Remainder<N, F>> {
    let mut buffer: Vec<F> = vec![F::zero(); closure.columns.len()];
    let mut results = Vec::with_capacity(targets.len());

    // The previous target's leading column, below which the buffer is known to be zero. Starts at
    // the width because a freshly allocated buffer is zero everywhere.
    let mut dirty_from = closure.columns.len();

    for target in targets {
        let start = *closure
            .column_of
            .get(target)
            .expect("a target outside the closure it was built from");
        debug_assert!(
            buffer[..dirty_from].iter().all(|slot| slot.is_zero()),
            "the buffer below the previous target's column must still be zero"
        );
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
        let remainder: Remainder<N, F> = buffer[start..]
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
        results.push(remainder);
    }

    results
}

/// One batch of border monomials reduced, and what it cost.
///
/// # Errors
/// As [`closure`].
pub(super) fn reduce_batch<const N: usize, F: FiniteField>(
    targets: &[Monomial<N>],
    basis: &MonicBasis<N, F>,
    order: MonomialOrder,
    limits: &BorderBatch,
) -> Result<(Vec<Remainder<N, F>>, BorderBatchStatistics), FglmError> {
    let closure = closure(targets, basis, order, limits)?;
    let statistics = BorderBatchStatistics {
        batches: 1,
        fallbacks: 0,
        reducer_rows: closure.reducer_rows(),
        columns: closure.columns(),
        reducer_entries: closure.reducer_entries(),
        peak_reducer_entries: closure.reducer_entries(),
    };
    Ok((reduce_targets(targets, &closure), statistics))
}

/// Fold one batch's statistics into a running total.
pub(super) fn accumulate(total: &mut BorderBatchStatistics, batch: &BorderBatchStatistics) {
    total.add(batch);
}

#[cfg(test)]
mod tests {
    use super::{
        closure, reduce_batch, reduce_targets, BatchOverflow, BorderBatch, BorderBatchSize,
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
                    let (batch, _) = reduce_batch(group, &monic, order, &BorderBatch::unbounded())
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

        let (together, _) =
            reduce_batch(&border, &monic, order, &BorderBatch::unbounded()).expect("within limits");

        for (position, target) in border.iter().enumerate() {
            let (alone, _) = reduce_batch(
                std::slice::from_ref(target),
                &monic,
                order,
                &BorderBatch::unbounded(),
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
        let (backwards, _) = reduce_batch(&reversed, &monic, order, &BorderBatch::unbounded())
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
            for remainder in reduce_targets(&border, &closed) {
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
            let together = reduce_targets(&ascending, &closed);
            for (position, target) in ascending.iter().enumerate() {
                let alone = reduce_targets(std::slice::from_ref(target), &closed);
                assert_eq!(
                    together[position], alone[0],
                    "NF({}) depends on the target reduced before it",
                    target
                );
            }
        }
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
