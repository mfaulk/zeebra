//! A structured batch in Faugère–Lachartre order (#816): every pair row swept against the whole
//! reducer block, then `D'` eliminated alone on the columns no reducer leads.
//!
//! `D'` is renumbered onto its own columns before its elimination so that dense scans, and the
//! `Dense` backend's buffer, span only those columns; the rows are mapped back afterwards, so the
//! matrix the caller extracts candidates from is indexed as it was built. Reducer rows are never
//! written.

use super::{
    candidate,
    macaulay::MacaulayMatrix,
    statistics::{StageClock, StageTimings},
    structured::BlockOutcome,
};
use crate::{
    linalg::{
        echelon::{row_echelon_with, sweep_rows_against_pivots, Backend},
        sparse::{SparseMatrix, SparseRow},
    },
    FiniteField,
};

/// Eliminate a batch in Faugère–Lachartre order.
///
/// `candidate_columns[c]` says whether a pivot in original column `c` is a candidate; under
/// `reduce`, exactly the candidate rows are then cleared of every other pivot column, the contract
/// [`candidate::finish`] keeps for the forward order. The sweep and the echelon of `D'` are charged
/// to `stages.forward`, the candidate pass to `stages.backward`.
///
/// # Errors
/// The live entry count, reducer rows included, that crossed `allowance`.
pub(crate) fn eliminate<const N: usize, F: FiniteField>(
    backend: Backend,
    matrix: &mut MacaulayMatrix<N, F>,
    candidate_columns: &[bool],
    reduce: bool,
    allowance: usize,
    clock: &mut StageClock,
    stages: &mut StageTimings,
) -> Result<(BlockOutcome, candidate::Report), usize> {
    let split = matrix.partition_reducers_first();
    debug_assert_eq!(
        super::structured::check_reducer_block(matrix.matrix(), split),
        Ok(())
    );
    let mut statistics = sweep_rows_against_pivots(matrix.matrix_mut(), split, allowance)?;

    let columns = matrix.num_columns();
    let mut reducer_led = vec![false; columns];
    let mut upper = 0usize;
    for row in &matrix.matrix().rows()[..split] {
        if let Some(lead) = row.leading_column() {
            reducer_led[lead] = true;
        }
        upper += row.nonzeros();
    }
    let mut compact = vec![usize::MAX; columns];
    let mut original = Vec::new();
    for (column, led) in reducer_led.iter().enumerate() {
        if !led {
            compact[column] = original.len();
            original.push(column);
        }
    }
    // The renumbering is monotone, so sorted rows stay sorted.
    let lower: Vec<SparseRow<F>> = matrix.matrix_mut().rows_mut()[split..]
        .iter_mut()
        .map(|row| {
            let row = std::mem::take(row);
            let entries = row
                .entries()
                .iter()
                .map(|&(column, value)| {
                    debug_assert_ne!(compact[column], usize::MAX, "a reducer column survived");
                    (compact[column], value)
                })
                .collect();
            SparseRow::from_sorted_unchecked(entries)
        })
        .collect();
    let mut residual = SparseMatrix::new(original.len(), lower);

    // `D'` is budgeted with the reducer block still resident beside it.
    let within = allowance.saturating_sub(upper);
    let lift = |live: usize| live.saturating_add(upper);
    let mut inner = row_echelon_with(backend, &mut residual, within).map_err(lift)?;
    stages.forward = clock.lap();

    let mut report = candidate::Report::default();
    let mut back_substituted_rows = None;
    if reduce {
        let selected: Vec<bool> = original
            .iter()
            .map(|&column| candidate_columns[column])
            .collect();
        let has_candidates = residual
            .rows()
            .iter()
            .any(|row| row.leading_column().is_some_and(|c| selected[c]));
        let (visits, finished) = if !has_candidates {
            (0, candidate::Report::default())
        } else if candidate::workspace_bytes::<F>(residual.num_columns())
            .is_some_and(|bytes| bytes <= candidate::WORKSPACE_LIMIT)
        {
            candidate::finish(
                &mut residual,
                &selected,
                within,
                candidate::WORKSPACE_LIMIT,
                &mut inner,
            )
            .map_err(lift)?
        } else {
            candidate::full(&mut residual, within, 0, &mut inner).map_err(lift)?
        };
        back_substituted_rows = Some(visits);
        report = finished;
    }

    for (slot, row) in matrix.matrix_mut().rows_mut()[split..]
        .iter_mut()
        .zip(residual.rows())
    {
        let entries = row
            .entries()
            .iter()
            .map(|&(column, value)| (original[column], value))
            .collect();
        *slot = SparseRow::from_sorted_unchecked(entries);
    }

    statistics.rank += inner.rank;
    statistics.zero_rows = matrix.num_rows() - statistics.rank;
    statistics.row_operations += inner.row_operations;
    statistics.pivot_inversions += inner.pivot_inversions;
    statistics.peak_nonzeros = statistics.peak_nonzeros.max(lift(inner.peak_nonzeros));
    statistics.final_nonzeros = lift(inner.final_nonzeros);
    debug_assert_eq!(statistics.final_nonzeros, matrix.nonzeros());
    Ok((
        BlockOutcome {
            statistics,
            free_pivots: split,
            back_substituted_rows,
        },
        report,
    ))
}

#[cfg(test)]
mod tests {
    use crate::{
        fields::{Bn254Fr, Gf256, Zp13, Zp2, Zp2147483647, Zp32003},
        grobner::{
            benchmark_systems::{cyclic, katsura},
            f4::{f4_reported, BatchOrder, F4Error, F4Options},
        },
        linalg::Backend,
        FiniteField, MonomialOrder, MultivariatePolynomial,
    };

    fn agree<const N: usize, F: FiniteField>(
        system: &[MultivariatePolynomial<N, F>],
        order: MonomialOrder,
        options: &F4Options,
    ) {
        let forward = F4Options {
            batch_order: BatchOrder::Forward,
            ..options.clone()
        };
        let fl = F4Options {
            batch_order: BatchOrder::FaugereLachartre,
            ..options.clone()
        };
        let (expected, _) = f4_reported(system, order, &forward);
        let (actual, _) = f4_reported(system, order, &fl);
        assert_eq!(actual.unwrap(), expected.unwrap(), "{order:?} {options:?}");
    }

    // Whole F4 runs in either batch order reach the same reduced basis, over every field width,
    // order, backend, row form and forward-worker setting.
    #[test]
    fn both_orders_reach_the_same_basis() {
        fn check<F: FiniteField>() {
            for order in [
                MonomialOrder::GradedReverseLexicographic,
                MonomialOrder::Lexicographic,
            ] {
                for elimination in [Backend::Sparse, Backend::Dense, Backend::Adaptive] {
                    for reduce_batch_rows in [true, false] {
                        let options = F4Options {
                            elimination,
                            reduce_batch_rows,
                            ..F4Options::default()
                        };
                        agree(&katsura::<5, F>(), order, &options);
                        agree(&cyclic::<5, F>(), order, &options);
                    }
                }
            }
        }
        check::<Zp13>();
        check::<Zp2>();
        check::<Zp32003>();
        check::<Zp2147483647>();
        check::<Bn254Fr>();
        check::<Gf256>();
    }

    // A larger computation, whose batches have many reducer and pair rows.
    #[test]
    fn both_orders_reach_the_same_katsura_7() {
        agree(
            &katsura::<7, Zp32003>(),
            MonomialOrder::GradedReverseLexicographic,
            &F4Options::default(),
        );
    }

    // The route's reported peak is its budget boundary: admitted at the peak, refused one below.
    #[test]
    fn the_reported_peak_is_the_budget_boundary() {
        let system = katsura::<6, Zp32003>();
        let order = MonomialOrder::GradedReverseLexicographic;
        let at = |entries: usize| F4Options {
            batch_order: BatchOrder::FaugereLachartre,
            parallel_forward: crate::grobner::f4::ParallelForward::Serial,
            ..F4Options::default().with_live_entries::<Zp32003>(entries)
        };
        let (basis, statistics) = f4_reported(&system, order, &at(usize::MAX / 64));
        basis.unwrap();
        let peak = statistics.max_live_nonzeros;
        assert!(peak > 0);
        let (admitted, _) = f4_reported(&system, order, &at(peak));
        admitted.unwrap();
        let (refused, _) = f4_reported(&system, order, &at(peak - 1));
        assert!(
            matches!(refused, Err(F4Error::TooManyNonzeros { .. })),
            "{refused:?}"
        );
    }
}
