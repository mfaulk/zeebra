//! F4's structured elimination over `GF(2)`, bit-packed (#777).
//!
//! Same contract as the generic route: the reducer block is taken as given and never written, the
//! pair rows are reduced against it and then among themselves, and only the rows whose leading
//! column `selected` names — the candidates — are back-substituted in full. Those rows are the
//! unique reduced rows of the batch's row space at their columns, so they equal the generic
//! route's candidates exactly; the unselected rows differ, and F4 never reads them.

use std::mem::size_of;

use crate::{
    grobner::f4::{
        macaulay::MacaulayMatrix, statistics::PackedGf2Statistics, structured::BlockOutcome,
    },
    linalg::{
        gf2::{
            four_russians_workspace, reduce_against_pivots, reduce_against_pivots_workspace,
            reduced_row_echelon_four_russians_selected, BitMatrix,
        },
        sparse::{EliminationStatistics, SparseRow},
    },
    FiniteField,
};

/// A budget the packed route crossed while writing its result back.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Refusal {
    /// Live sparse entries crossed the entry allowance.
    Entries(usize),
    /// Live sparse bytes plus the packed matrix crossed `max_live_bytes`.
    Bytes(usize),
}

/// What the packed route did to one batch.
#[derive(Debug)]
pub(crate) struct Packed {
    pub block: BlockOutcome,
    pub statistics: PackedGf2Statistics,
}

/// Table width for clearing the reducer block; [`reduce_against_pivots`] falls back to single
/// `xor`s per group whenever a table would not pay, so a wide default costs nothing on sparse groups.
const FORWARD_TABLE_BITS: usize = 8;

/// Four Russians table width for the pair block, from #272's crossover table (§4): 6 up to about a
/// thousand rows, 8 beyond.
fn pair_table_bits(rows: usize) -> usize {
    match rows {
        0..128 => 4,
        128..1024 => 6,
        _ => 8,
    }
}

/// Whether `F` has characteristic two, the precondition for reading a one-coefficient matrix as `GF(2)`.
pub(crate) fn characteristic_two<F: FiniteField>() -> bool {
    (F::ONE + F::ONE).is_zero()
}

/// Bytes the packed route holds for `pair_rows` rows over `columns` columns, at its peak.
pub(crate) fn workspace_bytes(pair_rows: usize, columns: usize) -> usize {
    let matrix = pair_rows
        .saturating_mul(columns.div_ceil(64))
        .saturating_mul(size_of::<u64>());
    let passes = reduce_against_pivots_workspace(pair_rows, columns, FORWARD_TABLE_BITS).max(
        four_russians_workspace(pair_rows, columns, pair_table_bits(pair_rows)),
    );
    matrix.saturating_add(passes).saturating_add(columns)
}

/// Eliminate `matrix` bit-packed, or decline and leave its coefficients untouched.
///
/// `Ok(None)` is a decline: a coefficient other than one, or a packed working set that would not
/// fit in `max_bytes` beside the sparse matrix. The rows may have been rearranged reducers-first,
/// which every structured route does anyway.
///
/// # Errors
/// A [`Refusal`] if writing the result back crosses `max_entries` or `max_bytes`.
pub(crate) fn eliminate<const N: usize, F: FiniteField>(
    matrix: &mut MacaulayMatrix<N, F>,
    selected: &[bool],
    max_entries: usize,
    max_bytes: usize,
) -> Result<Option<Packed>, Refusal> {
    debug_assert!(characteristic_two::<F>());
    let split = matrix.partition_reducers_first();
    debug_assert_eq!(
        super::structured::check_reducer_block(matrix.matrix(), split),
        Ok(()),
        "the reducer block is not the triangular prefix symbolic preprocessing makes it"
    );
    let columns = matrix.num_columns();
    let (reducers, pairs) = matrix.matrix().rows().split_at(split);
    let pair_rows = pairs.len();

    let entry_bytes = size_of::<(usize, F)>();
    let initial_nonzeros = matrix.nonzeros();
    let workspace = workspace_bytes(pair_rows, columns);
    if initial_nonzeros
        .saturating_mul(entry_bytes)
        .saturating_add(workspace)
        > max_bytes
    {
        return Ok(None);
    }
    if !reducers
        .iter()
        .all(|row| row.entries().iter().all(|(_, c)| *c == F::ONE))
    {
        return Ok(None);
    }
    let Some(mut packed) = BitMatrix::pack_binary(pairs, columns) else {
        return Ok(None);
    };

    let forward = reduce_against_pivots(&mut packed, reducers, FORWARD_TABLE_BITS);
    let echelon = reduced_row_echelon_four_russians_selected(
        &mut packed,
        pair_table_bits(pair_rows),
        selected,
    );

    // Written back row by row, each original dropped as its replacement lands, so the live count
    // is exact at every step and a crossing is caught at the row that causes it.
    let packed_bytes = packed.bytes();
    let mut resident = initial_nonzeros;
    let mut peak = initial_nonzeros;
    let mut targets = 0;
    let rows = matrix.matrix_mut().rows_mut();
    for index in 0..pair_rows {
        let row = if index < echelon.rank {
            let row: SparseRow<F> = packed.row_to_sparse(index);
            if row.leading_column().is_some_and(|column| selected[column]) {
                targets += 1;
            }
            row
        } else {
            SparseRow::zero()
        };
        let slot = &mut rows[split + index];
        resident = resident - slot.nonzeros() + row.nonzeros();
        *slot = row;
        peak = peak.max(resident);
        if resident > max_entries {
            return Err(Refusal::Entries(resident));
        }
        let bytes = resident
            .saturating_mul(entry_bytes)
            .saturating_add(packed_bytes);
        if bytes > max_bytes {
            return Err(Refusal::Bytes(bytes));
        }
    }

    let row_xors = forward.row_xors + echelon.row_xors;
    Ok(Some(Packed {
        block: BlockOutcome {
            statistics: EliminationStatistics {
                rank: split + echelon.rank,
                zero_rows: pair_rows - echelon.rank,
                initial_nonzeros,
                final_nonzeros: resident,
                peak_nonzeros: peak,
                row_operations: row_xors,
                pivot_inversions: 0,
            },
            free_pivots: split,
            back_substituted_rows: Some(targets),
        },
        statistics: PackedGf2Statistics {
            batches: 1,
            declined_batches: 0,
            row_xors,
            tables: forward.tables + echelon.tables,
            workspace_bytes: workspace,
        },
    }))
}

#[cfg(test)]
mod tests {
    use crate::{
        fields::{Gf256, Zp13, Zp2},
        grobner::{
            benchmark_systems::{cyclic, katsura},
            f4::{
                f4_with_options, options::Gf2Elimination, reduce_batch, trace_batches,
                BatchOutcome, F4Error, F4Options, TracedBatch,
            },
            field_equations::with_field_equations,
        },
        poly::{Monomial, MonomialOrder},
        FiniteField, MultivariatePolynomial, One, Zero,
    };
    use rand::{rngs::StdRng, Rng, SeedableRng};

    const ORDERS: [MonomialOrder; 3] = [
        MonomialOrder::Lexicographic,
        MonomialOrder::GradedLexicographic,
        MonomialOrder::GradedReverseLexicographic,
    ];

    fn options(gf2_elimination: Gf2Elimination) -> F4Options {
        F4Options {
            gf2_elimination,
            ..F4Options::default()
        }
    }

    /// Random quadratics with a planted root, plus the field equations: dense Boolean MQ.
    fn random_mq<const N: usize>(
        seed: u64,
        equations: usize,
        density: f64,
    ) -> Vec<MultivariatePolynomial<N, Zp2>> {
        let mut rng = StdRng::seed_from_u64(seed);
        let plant: [Zp2; N] = std::array::from_fn(|_| {
            if rng.gen_bool(0.5) {
                Zp2::one()
            } else {
                Zp2::zero()
            }
        });
        let system: Vec<_> = (0..equations)
            .map(|_| {
                let mut terms = Vec::new();
                for i in 0..N {
                    for j in i..N {
                        if rng.gen_bool(density) {
                            let mut exponents = [0u32; N];
                            exponents[i] += 1;
                            exponents[j] += 1;
                            terms.push((Monomial::new(&exponents), Zp2::one()));
                        }
                    }
                }
                let mut polynomial = MultivariatePolynomial::new(&terms);
                let value = polynomial.eval(&plant);
                polynomial +=
                    MultivariatePolynomial::new(&[(Monomial::one(), Zp2::zero() - value)]);
                polynomial
            })
            .collect();
        with_field_equations(&system).expect("GF(2) has an order")
    }

    fn solve<const N: usize, F: FiniteField>(
        system: &[MultivariatePolynomial<N, F>],
        order: MonomialOrder,
        mode: Gf2Elimination,
    ) -> (
        Vec<MultivariatePolynomial<N, F>>,
        crate::grobner::f4::F4Statistics,
    ) {
        f4_with_options(system, order, &options(mode)).expect("solves")
    }

    /// The largest batch of a generic run, for replay under either route.
    fn largest_batch<const N: usize>(
        system: &[MultivariatePolynomial<N, Zp2>],
    ) -> TracedBatch<N, Zp2> {
        let order = MonomialOrder::GradedReverseLexicographic;
        let (_, _, trace) =
            trace_batches(system, order, &options(Gf2Elimination::Generic)).unwrap();
        trace.largest().expect("at least one batch").clone()
    }

    fn replay<const N: usize>(
        batch: &TracedBatch<N, Zp2>,
        options: &F4Options,
    ) -> Result<BatchOutcome<N, Zp2>, F4Error> {
        reduce_batch(
            &batch.basis,
            &batch.pairs,
            MonomialOrder::GradedReverseLexicographic,
            options,
        )
    }

    /// The packed route returns the generic route's basis, under every order, on dense and sparse Boolean systems.
    #[test]
    fn test_packed_route_returns_the_generic_basis() {
        for order in ORDERS {
            let systems: Vec<Vec<MultivariatePolynomial<6, Zp2>>> = vec![
                random_mq::<6>(1, 6, 0.5),
                random_mq::<6>(2, 12, 0.3),
                random_mq::<6>(3, 6, 0.05),
                with_field_equations(&cyclic::<6, Zp2>()).unwrap(),
                with_field_equations(&katsura::<6, Zp2>()).unwrap(),
            ];
            for system in &systems {
                let (generic, generic_stats) = solve(system, order, Gf2Elimination::Generic);
                let (packed, packed_stats) = solve(system, order, Gf2Elimination::Packed);
                assert_eq!(packed, generic, "{}", order.name());
                assert_eq!(generic_stats.packed_gf2.batches, 0);
                assert_eq!(
                    packed_stats.packed_gf2.batches, packed_stats.batches,
                    "every batch packs"
                );
                assert_eq!(packed_stats.packed_gf2.declined_batches, 0);
                assert_eq!(packed_stats.candidate_reduction.batches, 0);
                assert_eq!(packed, solve(system, order, Gf2Elimination::Auto).0);
            }
        }
    }

    /// Replayed batch by batch, the packed route's candidates equal the generic route's, including rank-deficient and candidate-free batches.
    #[test]
    fn test_packed_candidates_equal_generic_candidates_per_batch() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let system = random_mq::<10>(7, 12, 0.3);
        let (_, _, trace) =
            trace_batches(&system, order, &options(Gf2Elimination::Generic)).unwrap();
        let (mut deficient, mut candidate_free) = (0, 0);
        for batch in trace.batches() {
            let generic = replay(batch, &options(Gf2Elimination::Generic)).unwrap();
            let packed = replay(batch, &options(Gf2Elimination::Packed)).unwrap();
            assert_eq!(packed.candidates, generic.candidates);
            assert_eq!(packed.statistics.packed_gf2.batches, 1);
            assert_eq!(
                packed.statistics.elimination.rank,
                generic.statistics.elimination.rank
            );
            assert_eq!(
                packed.statistics.back_substituted_rows,
                Some(generic.candidates.len())
            );
            deficient += usize::from(packed.statistics.elimination.zero_rows > 0);
            candidate_free += usize::from(packed.candidates.is_empty());
        }
        assert!(deficient > 0, "some batch must have dependent rows");
        assert!(
            candidate_free > 0,
            "some batch must reduce entirely to known leads"
        );
    }

    /// An empty batch and a batch whose rows are all pivots both pass through the packed route unchanged.
    #[test]
    fn test_degenerate_batches() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let system = random_mq::<4>(4, 4, 0.5);
        let basis = crate::grobner::f4::MonicBasis::new(&system, order);
        let empty = reduce_batch(&basis, &[], order, &options(Gf2Elimination::Packed)).unwrap();
        assert!(empty.candidates.is_empty());
        assert_eq!(empty.statistics.elimination.rank, 0);

        // A single linear polynomial against x^2 + x: one pair whose S-polynomial reduces to zero.
        let x = MultivariatePolynomial::<2, Zp2>::parse("x^2 + x", ["x", "y"]).unwrap();
        let y = MultivariatePolynomial::<2, Zp2>::parse("y^2 + y", ["x", "y"]).unwrap();
        let system = [x, y];
        let basis = crate::grobner::f4::MonicBasis::new(&system, order);
        let pairs = [crate::grobner::pairs::CriticalPair::new(
            &system, 0, 1, order,
        )];
        let generic =
            reduce_batch(&basis, &pairs, order, &options(Gf2Elimination::Generic)).unwrap();
        let packed = reduce_batch(&basis, &pairs, order, &options(Gf2Elimination::Packed)).unwrap();
        assert_eq!(packed.candidates, generic.candidates);
        assert!(packed.candidates.is_empty());
        assert_eq!(packed.statistics.packed_gf2.batches, 1);
        assert_eq!(
            packed.statistics.elimination.rank + packed.statistics.elimination.zero_rows,
            packed.statistics.rows
        );
    }

    /// Outside its contract — odd characteristic, a non-binary coefficient, echelon output — the packed setting runs the generic route.
    #[test]
    fn test_packed_setting_falls_back_outside_its_contract() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let odd = katsura::<4, Zp13>();
        let (basis, stats) =
            f4_with_options(&odd, order, &options(Gf2Elimination::Packed)).unwrap();
        assert_eq!(
            basis,
            f4_with_options(&odd, order, &options(Gf2Elimination::Generic))
                .unwrap()
                .0
        );
        assert_eq!(stats.packed_gf2, Default::default());

        let system = [
            MultivariatePolynomial::<2, Gf256>::parse("x^2 + 2*x*y + 1", ["x", "y"]).unwrap(),
            MultivariatePolynomial::<2, Gf256>::parse("x*y + y^2 + x", ["x", "y"]).unwrap(),
        ];
        let (basis, stats) =
            f4_with_options(&system, order, &options(Gf2Elimination::Packed)).unwrap();
        assert_eq!(
            basis,
            f4_with_options(&system, order, &options(Gf2Elimination::Generic))
                .unwrap()
                .0
        );
        assert_eq!(
            stats.packed_gf2.batches + stats.packed_gf2.declined_batches,
            stats.batches
        );

        let system = random_mq::<5>(5, 5, 0.5);
        let echelon = F4Options {
            reduce_batch_rows: false,
            ..options(Gf2Elimination::Packed)
        };
        let (_, stats) = f4_with_options(&system, order, &echelon).unwrap();
        assert_eq!(stats.packed_gf2, Default::default());
    }

    /// A packed working set that does not fit beside the sparse matrix is declined, and the generic route answers within the same budget.
    #[test]
    fn test_packed_bytes_are_charged_to_max_live_bytes() {
        let batch = largest_batch(&random_mq::<7>(77, 7, 0.5));
        let unlimited = options(Gf2Elimination::Packed);
        let packed = replay(&batch, &unlimited).unwrap();
        let generic = replay(&batch, &options(Gf2Elimination::Generic)).unwrap();
        let entry_bytes = F4Options::bytes_per_entry::<Zp2>();
        let workspace = packed.statistics.packed_gf2.workspace_bytes;
        assert!(workspace > 0);

        // Admits the generic route's peak but not the sparse matrix plus the packed working set.
        let admitted = packed.statistics.elimination.initial_nonzeros * entry_bytes + workspace;
        let generic_needs = generic.statistics.elimination.peak_nonzeros * entry_bytes;
        let budget = generic_needs.max(admitted - 1);
        if budget < admitted {
            let tight = F4Options {
                max_live_bytes: budget,
                max_live_nonzeros: usize::MAX,
                ..unlimited.clone()
            };
            let declined = replay(&batch, &tight).unwrap();
            assert_eq!(declined.candidates, generic.candidates);
            assert_eq!(declined.statistics.packed_gf2.batches, 0);
            assert_eq!(declined.statistics.packed_gf2.declined_batches, 1);
        }

        // The packed route's own peak — sparse entries beside its working set, then beside the
        // bit matrix during write-back — is admitted exactly; one byte fewer is never packed past.
        let statistics = &packed.statistics;
        let bit_matrix =
            (statistics.rows - statistics.reducer_rows) * statistics.columns.div_ceil(64) * 8;
        let exact = admitted.max(statistics.elimination.peak_nonzeros * entry_bytes + bit_matrix);
        let at = |bytes: usize| F4Options {
            max_live_bytes: bytes,
            max_live_nonzeros: usize::MAX,
            ..unlimited.clone()
        };
        let fits = replay(&batch, &at(exact)).unwrap();
        assert_eq!(fits.statistics.packed_gf2.batches, 1);
        assert_eq!(fits.candidates, generic.candidates);
        match replay(&batch, &at(exact - 1)) {
            Ok(outcome) => {
                assert_eq!(outcome.statistics.packed_gf2.batches, 0);
                assert_eq!(outcome.candidates, generic.candidates);
            }
            Err(error) => assert!(matches!(error, F4Error::TooManyLiveBytes { .. })),
        }
    }

    /// The entry allowance binds on the packed route's write-back exactly at its reported peak.
    #[test]
    fn test_packed_write_back_honours_the_entry_allowance() {
        let batch = largest_batch(&random_mq::<7>(78, 7, 0.5));
        let packed = replay(&batch, &options(Gf2Elimination::Packed)).unwrap();
        let peak = packed.statistics.elimination.peak_nonzeros;
        let at = |entries: usize| F4Options {
            max_live_nonzeros: entries,
            max_live_bytes: usize::MAX,
            ..options(Gf2Elimination::Packed)
        };
        assert_eq!(
            replay(&batch, &at(peak)).unwrap().candidates,
            packed.candidates
        );
        if peak > packed.statistics.elimination.initial_nonzeros {
            assert_eq!(
                replay(&batch, &at(peak - 1)).unwrap_err(),
                F4Error::TooManyNonzeros {
                    nonzeros: peak,
                    limit: peak - 1
                }
            );
        }
    }

    /// A budget the generic route refuses is refused under the packed setting too.
    #[test]
    fn test_a_budget_the_generic_route_refuses_stays_refused() {
        let system = random_mq::<7>(79, 7, 0.5);
        let order = MonomialOrder::GradedReverseLexicographic;
        let tight = |mode| F4Options {
            gf2_elimination: mode,
            ..F4Options::default().with_live_entries::<Zp2>(200)
        };
        let generic = f4_with_options(&system, order, &tight(Gf2Elimination::Generic)).unwrap_err();
        let packed = f4_with_options(&system, order, &tight(Gf2Elimination::Packed)).unwrap_err();
        assert_eq!(generic.stop_kind(), packed.stop_kind());
    }

    /// Auto packs dense, wide matrices and leaves sparse or narrow ones on the generic route.
    #[test]
    fn test_dispatch_rule() {
        let (columns, pairs) = (Gf2Elimination::MIN_COLUMNS, Gf2Elimination::MIN_PAIR_ROWS);
        // 1000 rows of `columns` cells: the density threshold in entries.
        let dense = (Gf2Elimination::MIN_DENSITY_PPM as usize * columns).div_ceil(1000);
        assert!(Gf2Elimination::prefers_packed(1000, pairs, columns, dense));
        assert!(!Gf2Elimination::prefers_packed(
            1000,
            pairs,
            columns,
            dense - 1
        ));
        assert!(!Gf2Elimination::prefers_packed(
            1000,
            pairs,
            columns - 1,
            1_000_000
        ));
        assert!(!Gf2Elimination::prefers_packed(
            1000,
            pairs - 1,
            columns,
            1_000_000
        ));
        assert!(!Gf2Elimination::prefers_packed(0, 0, 0, 0));
        assert!(!Gf2Elimination::Generic.selects_packed(1000, 1000, 1000, 1_000_000));
        assert!(Gf2Elimination::Packed.selects_packed(1, 0, 1, 0));
        assert_eq!(F4Options::default().gf2_elimination, Gf2Elimination::Auto);
        assert_eq!(
            F4Options::baseline().gf2_elimination,
            Gf2Elimination::Generic
        );
    }
}
