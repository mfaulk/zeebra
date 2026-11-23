//! F4's packed `GF(2)` reducer sweep on the residual columns only (#1077, the default since #1092).
//!
//! A structured batch is `[A B; C D]`: reducer rows `[A B]` with `A` unit upper triangular on the
//! columns the reducers lead, and pair rows `[C D]`. Over `GF(2)` the pair block after the reducer
//! sweep is exactly `D + C·A⁻¹B`, which lives on the residual columns alone. A reducer's *tail*, its
//! row of `A⁻¹B`, is the residual part of its row plus the tails of the reducers it names, so the
//! tails are built back to front; a pair row is then its own `D` bits plus the tails its `C` entries
//! name. Nothing is packed at the full width. The matrix that results is the one
//! `packed::eliminate` reduces, so the echelon, selective back substitution and write-back
//! that follow are its.

use std::{
    mem::size_of,
    time::{Duration, Instant},
};

use crate::{
    grobner::f4::{
        macaulay::MacaulayMatrix,
        packed::{pair_table_bits, Packed, Refusal},
        statistics::PackedGf2Statistics,
        structured::BlockOutcome,
    },
    linalg::{
        gf2::{four_russians_workspace, reduced_row_echelon_four_russians_selected, BitMatrix},
        sparse::{EliminationStatistics, SparseRow},
    },
    FiniteField,
};

/// Tails applied per table to pair rows; a group falls back to one `xor` per reference when its
/// table would not pay, as in `reduce_against_pivots`.
const MULTIPLY_TABLE_BITS: usize = 8;

const NONE: usize = usize::MAX;

#[inline]
fn xor_into(destination: &mut [u64], source: &[u64]) {
    for (d, s) in destination.iter_mut().zip(source) {
        *d ^= *s;
    }
}

fn flip_bit(words: &mut [u64], column: usize) {
    words[column / 64] ^= 1 << (column % 64);
}

fn ones(words: &[u64]) -> usize {
    words.iter().map(|w| w.count_ones() as usize).sum()
}

/// What the residual route did, summed over batches; byte counts are the largest of any batch.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ResidualGf2Statistics {
    /// Batches the route eliminated.
    pub batches: usize,
    /// Columns of the batch.
    pub columns: usize,
    /// Columns no reducer leads: the packed width.
    pub residual_columns: usize,
    /// Reducer rows, one per known-pivot column.
    pub reducers: usize,
    /// Pair-row entries in known-pivot columns: `C`'s nonzeros.
    pub known_entries: usize,
    /// Pair-row entries in residual columns: `D`'s nonzeros.
    pub residual_entries: usize,
    /// Reducer entries in residual columns: `B`'s nonzeros.
    pub reducer_residual_entries: usize,
    /// Reducers some pair row names directly.
    pub referenced_tails: usize,
    /// Tails built.
    pub tails_built: usize,
    /// Set bits across the built tails, `B`'s entries after fill-in.
    pub tail_entries: usize,
    /// Tail references served: `C`'s entries plus the references between tails.
    pub tail_uses: usize,
    /// Set bits of `D + C·A⁻¹B` before its echelon.
    pub reduced_entries: usize,
    /// Row `xor`s building tails, and the words they wrote.
    pub tail_xors: usize,
    pub tail_words: usize,
    /// Row `xor`s applying tails to pair rows, tables included, and their words.
    pub multiply_xors: usize,
    pub multiply_words: usize,
    /// Row `xor`s of the echelon of `D + C·A⁻¹B`, and their words.
    pub echelon_xors: usize,
    pub echelon_words: usize,
    /// Tables built to apply tails.
    pub tables: usize,
    /// The largest of them, in bytes.
    pub table_bytes: usize,
    /// Bytes of built tails.
    pub tail_bytes: usize,
    /// The peak working set charged against `max_live_bytes`.
    pub workspace_bytes: usize,
    /// Scanning and packing `C` and `D`.
    pub pack: Duration,
    /// Building tails.
    pub tails: Duration,
    /// Applying them.
    pub multiply: Duration,
    /// The echelon of `D + C·A⁻¹B`.
    pub echelon: Duration,
    /// Writing the rows back as sparse rows.
    pub write_back: Duration,
}

impl ResidualGf2Statistics {
    pub(crate) fn record(&mut self, other: &Self) {
        for (sum, add) in [
            (&mut self.batches, other.batches),
            (&mut self.columns, other.columns),
            (&mut self.residual_columns, other.residual_columns),
            (&mut self.reducers, other.reducers),
            (&mut self.known_entries, other.known_entries),
            (&mut self.residual_entries, other.residual_entries),
            (
                &mut self.reducer_residual_entries,
                other.reducer_residual_entries,
            ),
            (&mut self.referenced_tails, other.referenced_tails),
            (&mut self.tails_built, other.tails_built),
            (&mut self.tail_entries, other.tail_entries),
            (&mut self.tail_uses, other.tail_uses),
            (&mut self.reduced_entries, other.reduced_entries),
            (&mut self.tail_xors, other.tail_xors),
            (&mut self.tail_words, other.tail_words),
            (&mut self.multiply_xors, other.multiply_xors),
            (&mut self.multiply_words, other.multiply_words),
            (&mut self.echelon_xors, other.echelon_xors),
            (&mut self.echelon_words, other.echelon_words),
            (&mut self.tables, other.tables),
        ] {
            *sum = sum.saturating_add(add);
        }
        self.table_bytes = self.table_bytes.max(other.table_bytes);
        self.tail_bytes = self.tail_bytes.max(other.tail_bytes);
        self.workspace_bytes = self.workspace_bytes.max(other.workspace_bytes);
        self.pack += other.pack;
        self.tails += other.tails;
        self.multiply += other.multiply;
        self.echelon += other.echelon;
        self.write_back += other.write_back;
    }
}

/// Why [`residual_form`] did not run.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Decline {
    /// A coefficient other than one.
    Coefficient,
    /// The working set, in bytes, would exceed the room given.
    Bytes(usize),
}

/// `D + C·A⁻¹B`, packed on the residual columns.
#[derive(Debug)]
pub(crate) struct ResidualForm {
    pub matrix: BitMatrix,
    /// `original[c]` is the batch column of residual column `c`.
    pub original: Vec<usize>,
    pub statistics: ResidualGf2Statistics,
}

/// The pair block after the reducer sweep, on the residual columns only.
///
/// `reducers` is F4's reducer block: nonzero rows, leads strictly ascending. Declines before
/// allocating anything at width if the working set would exceed `room` bytes.
pub(crate) fn residual_form<F: FiniteField>(
    reducers: &[SparseRow<F>],
    pairs: &[SparseRow<F>],
    columns: usize,
    room: usize,
) -> Result<ResidualForm, Decline> {
    let clock = Instant::now();
    let mut statistics = ResidualGf2Statistics {
        batches: 1,
        columns,
        reducers: reducers.len(),
        ..Default::default()
    };
    // `known[c]` is the reducer leading column `c`; `compact[c]` is the residual index of the rest.
    let mut known = vec![NONE; columns];
    for (index, row) in reducers.iter().enumerate() {
        if row.entries().iter().any(|(_, c)| *c != F::ONE) {
            return Err(Decline::Coefficient);
        }
        known[row.leading_column().expect("a reducer row is nonzero")] = index;
    }
    let mut compact = vec![NONE; columns];
    let mut original = Vec::with_capacity(columns - reducers.len());
    for (column, &reducer) in known.iter().enumerate() {
        if reducer == NONE {
            compact[column] = original.len();
            original.push(column);
        }
    }
    let width = original.len();
    let stride = width.div_ceil(64);
    statistics.residual_columns = width;
    statistics.reducer_residual_entries = reducers
        .iter()
        .map(|row| {
            row.entries()
                .iter()
                .filter(|(c, _)| known[*c] == NONE)
                .count()
        })
        .sum();

    let mut referenced = vec![false; reducers.len()];
    for row in pairs {
        for &(column, coefficient) in row.entries() {
            if coefficient != F::ONE {
                return Err(Decline::Coefficient);
            }
            match known[column] {
                NONE => statistics.residual_entries += 1,
                reducer => {
                    referenced[reducer] = true;
                    statistics.known_entries += 1;
                }
            }
        }
    }
    statistics.referenced_tails = referenced.iter().filter(|&&r| r).count();
    // Every tail is built: every F4 batch reaches every tail, so building only the reachable ones
    // saved nothing measurable (#1077, §5).
    let built = reducers.len();

    let row_bytes = stride * size_of::<u64>();
    let maps = columns * 2 * size_of::<usize>()
        + width * size_of::<usize>()
        + reducers.len() * (1 + 2 * size_of::<usize>());
    let tail_bytes = built * row_bytes;
    // Per pair row a cursor, a queue link and a scratch use; per referenced tail a member and a head.
    let queue_bytes = pairs.len() * (2 * size_of::<usize>() + size_of::<(usize, usize)>())
        + statistics.referenced_tails * 2 * size_of::<usize>();
    let table_bytes = (1usize << MULTIPLY_TABLE_BITS) * row_bytes;
    let echelon = four_russians_workspace(pairs.len(), width, pair_table_bits(pairs.len())) + width;
    let workspace =
        maps + pairs.len() * row_bytes + (tail_bytes + queue_bytes + table_bytes).max(echelon);
    statistics.workspace_bytes = workspace;
    statistics.tail_bytes = tail_bytes;
    if workspace > room {
        return Err(Decline::Bytes(workspace));
    }

    // Referenced tails in groups of up to `MULTIPLY_TABLE_BITS`, ascending, so a pair row's `C`
    // entries visit its groups in order.
    let mut group_of = vec![(NONE, 0usize); reducers.len()];
    let mut members: Vec<Vec<usize>> = Vec::new();
    for (index, _) in referenced.iter().enumerate().filter(|(_, &r)| r) {
        if members
            .last()
            .is_none_or(|group| group.len() == MULTIPLY_TABLE_BITS)
        {
            members.push(Vec::with_capacity(MULTIPLY_TABLE_BITS));
        }
        let group = members.len() - 1;
        group_of[index] = (group, members[group].len());
        members[group].push(index);
    }
    let mut matrix = BitMatrix::zero(pairs.len(), width);
    for (target, row) in pairs.iter().enumerate() {
        let words = matrix.row_mut(target);
        for &(column, _) in row.entries() {
            if known[column] == NONE {
                flip_bit(words, compact[column]);
            }
        }
    }
    // `C` stays in the sparse rows: each pair row waits in the queue of the next group it names,
    // with a cursor into its entries, so a group visits exactly the rows that use it.
    let upcoming = |target: usize, cursor: &mut usize| -> Option<usize> {
        let entries = pairs[target].entries();
        while *cursor < entries.len() {
            let reducer = known[entries[*cursor].0];
            if reducer != NONE {
                return Some(group_of[reducer].0);
            }
            *cursor += 1;
        }
        None
    };
    let mut cursor = vec![0usize; pairs.len()];
    let mut link = vec![NONE; pairs.len()];
    let mut head = vec![NONE; members.len()];
    for target in (0..pairs.len()).rev() {
        if let Some(group) = upcoming(target, &mut cursor[target]) {
            link[target] = head[group];
            head[group] = target;
        }
    }
    statistics.pack = clock.elapsed();

    // Back to front: every reducer a tail names comes later, so its tail is already built.
    let clock = Instant::now();
    let mut tail_words = vec![0u64; built * stride];
    for at in (0..built).rev() {
        let (head, rest) = tail_words.split_at_mut((at + 1) * stride);
        let tail = &mut head[at * stride..];
        for &(column, _) in &reducers[at].entries()[1..] {
            match known[column] {
                NONE => flip_bit(tail, compact[column]),
                later => {
                    let from = (later - at - 1) * stride;
                    xor_into(tail, &rest[from..from + stride]);
                    statistics.tail_xors += 1;
                }
            }
        }
    }
    statistics.tail_words = statistics.tail_xors * stride;
    statistics.tail_uses = statistics.tail_xors + statistics.known_entries;
    statistics.tails_built = built;
    statistics.tail_entries = ones(&tail_words);
    statistics.tails = clock.elapsed();

    let clock = Instant::now();
    let tail = |reducer: usize| &tail_words[reducer * stride..(reducer + 1) * stride];
    let mut table: Vec<u64> = Vec::new();
    let mut targets: Vec<(usize, usize)> = Vec::new();
    for (index, group) in members.iter().enumerate() {
        targets.clear();
        let mut target = head[index];
        while target != NONE {
            let after = link[target];
            let entries = pairs[target].entries();
            let mut bits = 0usize;
            while let Some(&(column, _)) = entries.get(cursor[target]) {
                match known[column] {
                    NONE => {}
                    reducer if group_of[reducer].0 == index => bits |= 1 << group_of[reducer].1,
                    _ => break,
                }
                cursor[target] += 1;
            }
            targets.push((target, bits));
            if let Some(later) = upcoming(target, &mut cursor[target]) {
                link[target] = head[later];
                head[later] = target;
            }
            target = after;
        }
        let singles: usize = targets
            .iter()
            .map(|(_, bits)| bits.count_ones() as usize)
            .sum();
        let entries = 1usize << group.len();
        if entries + targets.len() < singles {
            table.clear();
            table.resize(entries * stride, 0);
            for index in 1..entries {
                let (previous, pivot) = (index & (index - 1), index.trailing_zeros() as usize);
                let (before, current) = table.split_at_mut(index * stride);
                let current = &mut current[..stride];
                current.copy_from_slice(&before[previous * stride..(previous + 1) * stride]);
                xor_into(current, tail(group[pivot]));
                statistics.multiply_xors += 1;
            }
            statistics.tables += 1;
            statistics.table_bytes = statistics.table_bytes.max(entries * row_bytes);
            for &(target, bits) in &targets {
                xor_into(
                    matrix.row_mut(target),
                    &table[bits * stride..(bits + 1) * stride],
                );
                statistics.multiply_xors += 1;
            }
        } else {
            for &(target, mut bits) in &targets {
                while bits != 0 {
                    xor_into(
                        matrix.row_mut(target),
                        tail(group[bits.trailing_zeros() as usize]),
                    );
                    statistics.multiply_xors += 1;
                    bits &= bits - 1;
                }
            }
        }
    }
    statistics.multiply_words = statistics.multiply_xors * stride;
    statistics.reduced_entries = (0..pairs.len()).map(|r| ones(matrix.row(r))).sum();
    statistics.multiply = clock.elapsed();
    Ok(ResidualForm {
        matrix,
        original,
        statistics,
    })
}

/// [`super::packed::eliminate`]'s contract, with the reducer sweep done on the residual columns.
///
/// # Errors
/// As [`super::packed::eliminate`].
pub(crate) fn eliminate<const N: usize, F: FiniteField>(
    matrix: &mut MacaulayMatrix<N, F>,
    selected: &[bool],
    max_entries: usize,
    max_bytes: usize,
) -> Result<Option<Packed>, Refusal> {
    debug_assert!(super::packed::characteristic_two::<F>());
    let split = matrix.partition_reducers_first();
    debug_assert_eq!(
        super::structured::check_reducer_block(matrix.matrix(), split),
        Ok(())
    );
    let columns = matrix.num_columns();
    let (reducers, pairs) = matrix.matrix().rows().split_at(split);
    let pair_rows = pairs.len();
    let entry_bytes = size_of::<(usize, F)>();
    let initial_nonzeros = matrix.nonzeros();
    let Some(room) = max_bytes.checked_sub(initial_nonzeros.saturating_mul(entry_bytes)) else {
        return Ok(None);
    };
    let Ok(mut form) = residual_form(reducers, pairs, columns, room) else {
        return Ok(None);
    };

    let clock = Instant::now();
    let local: Vec<bool> = form.original.iter().map(|&c| selected[c]).collect();
    let echelon = reduced_row_echelon_four_russians_selected(
        &mut form.matrix,
        pair_table_bits(pair_rows),
        &local,
    );
    let mut statistics = form.statistics;
    statistics.echelon_xors = echelon.row_xors;
    statistics.echelon_words = echelon.xor_words;
    statistics.echelon = clock.elapsed();

    // As the full-width route: row by row, each original dropped as its replacement lands.
    let clock = Instant::now();
    let packed_bytes = form.matrix.bytes();
    let mut resident = initial_nonzeros;
    let mut peak = initial_nonzeros;
    let mut targets = 0;
    let rows = matrix.matrix_mut().rows_mut();
    for index in 0..pair_rows {
        let row = if index < echelon.rank {
            let entries = form
                .matrix
                .row_to_sparse::<F>(index)
                .entries()
                .iter()
                .map(|&(column, value)| (form.original[column], value))
                .collect();
            let row = SparseRow::from_sorted_unchecked(entries);
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
    statistics.write_back = clock.elapsed();

    let row_xors = statistics.tail_xors + statistics.multiply_xors + echelon.row_xors;
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
            xor_words: statistics.tail_words + statistics.multiply_words + echelon.xor_words,
            tables: statistics.tables + echelon.tables,
            workspace_bytes: statistics.workspace_bytes,
            residual: statistics,
        },
    }))
}

#[cfg(test)]
mod tests {
    use super::{residual_form, Decline};
    use crate::{
        fields::{Gf256, Zp13, Zp2},
        grobner::{
            benchmark_systems::{cyclic, katsura},
            f4::{
                f4_with_options, reduce_batch, trace_batches, BatchOrder, F4Error, F4Options,
                Gf2Elimination, MonicBasis, TracedBatch,
            },
            field_equations::with_field_equations,
            pairs::CriticalPair,
        },
        linalg::{
            gf2::{reduce_against_pivots, reduced_row_echelon_four_russians_selected, BitMatrix},
            sparse::SparseRow,
        },
        poly::{Monomial, MonomialOrder},
        MultivariatePolynomial, One, Zero,
    };
    use rand::{rngs::StdRng, seq::SliceRandom, Rng, SeedableRng};

    const ORDER: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

    fn row(mut columns: Vec<usize>) -> SparseRow<Zp2> {
        columns.sort_unstable();
        columns.dedup();
        SparseRow::from_sorted(columns.into_iter().map(|c| (c, Zp2::one())).collect()).unwrap()
    }

    fn symmetric_difference(a: &[usize], b: &[usize]) -> Vec<usize> {
        let mut out: Vec<usize> = a.iter().filter(|c| !b.contains(c)).copied().collect();
        out.extend(b.iter().filter(|c| !a.contains(c)));
        out
    }

    /// A reducer block of `reducers` unit-triangular rows and `pairs` pair rows over
    /// `reducers + residual` columns, the known-pivot columns scattered among the residual ones.
    /// With `deficient`, a third of the pair rows are sums of others.
    struct Synthetic {
        reducers: Vec<SparseRow<Zp2>>,
        pairs: Vec<SparseRow<Zp2>>,
        columns: usize,
        known: Vec<bool>,
    }

    fn synthetic(
        rng: &mut StdRng,
        reducers: usize,
        residual: usize,
        pairs: usize,
        reducer_density: f64,
        pair_density: f64,
        deficient: bool,
    ) -> Synthetic {
        let columns = reducers + residual;
        let mut order: Vec<usize> = (0..columns).collect();
        order.shuffle(rng);
        let mut leads = order[..reducers].to_vec();
        leads.sort_unstable();
        let mut known = vec![false; columns];
        for &lead in &leads {
            known[lead] = true;
        }
        let reducer_rows = leads
            .iter()
            .map(|&lead| {
                let mut entries = vec![lead];
                entries.extend((lead + 1..columns).filter(|_| rng.gen_bool(reducer_density)));
                row(entries)
            })
            .collect();
        let mut supports: Vec<Vec<usize>> = Vec::new();
        for index in 0..pairs {
            let support = if deficient && index >= 2 && index % 3 == 0 {
                let a = rng.gen_range(0..supports.len());
                let b = rng.gen_range(0..supports.len());
                if a == b {
                    supports[a].clone()
                } else {
                    symmetric_difference(&supports[a], &supports[b])
                }
            } else {
                (0..columns)
                    .filter(|_| rng.gen_bool(pair_density))
                    .collect()
            };
            supports.push(support);
        }
        Synthetic {
            reducers: reducer_rows,
            pairs: supports.into_iter().map(row).collect(),
            columns,
            known,
        }
    }

    fn columns_of(matrix: &BitMatrix, index: usize, original: Option<&[usize]>) -> Vec<usize> {
        matrix
            .row_to_sparse::<Zp2>(index)
            .entries()
            .iter()
            .map(|&(c, _)| original.map_or(c, |o| o[c]))
            .collect()
    }

    /// The shipped route's reducer sweep at full width, as batch columns per pair row.
    fn full_width(batch: &Synthetic) -> BitMatrix {
        let mut packed = BitMatrix::pack_binary(&batch.pairs, batch.columns).unwrap();
        reduce_against_pivots(&mut packed, &batch.reducers, 8);
        for (index, row) in batch.pairs.iter().enumerate() {
            assert_eq!(
                columns_of(&packed, index, None),
                naive_sweep(batch, row),
                "the reference sweeps disagree"
            );
        }
        packed
    }

    /// The sweep by definition: add the reducer leading a pair row's first known column until none
    /// is left.
    fn naive_sweep(batch: &Synthetic, row: &SparseRow<Zp2>) -> Vec<usize> {
        let by_lead: std::collections::HashMap<usize, &SparseRow<Zp2>> = batch
            .reducers
            .iter()
            .map(|r| (r.leading_column().unwrap(), r))
            .collect();
        let mut set: std::collections::BTreeSet<usize> =
            row.entries().iter().map(|&(c, _)| c).collect();
        while let Some(&column) = set.iter().find(|&&c| batch.known[c]) {
            for &(c, _) in by_lead[&column].entries() {
                if !set.remove(&c) {
                    set.insert(c);
                }
            }
        }
        set.into_iter().collect()
    }

    /// Residual width on either side of one and two machine words, empty, and with and without
    /// reducers: every pair row equals the full-width sweep's, column for column.
    #[test]
    fn test_residual_form_equals_the_full_width_sweep_across_word_edges() {
        let mut rng = StdRng::seed_from_u64(1077);
        for residual in [0, 1, 63, 64, 65, 127, 128, 129] {
            for reducers in [0, 1, 7, 70, 130] {
                for (reducer_density, pair_density) in [(0.05, 0.05), (0.3, 0.2), (0.7, 0.5)] {
                    let batch = synthetic(
                        &mut rng,
                        reducers,
                        residual,
                        40,
                        reducer_density,
                        pair_density,
                        true,
                    );
                    let expected = full_width(&batch);
                    let form =
                        residual_form(&batch.reducers, &batch.pairs, batch.columns, usize::MAX)
                            .unwrap();
                    assert_eq!(form.matrix.num_columns(), residual);
                    assert_eq!(form.statistics.residual_columns, residual);
                    for index in 0..batch.pairs.len() {
                        let full = columns_of(&expected, index, None);
                        assert!(full.iter().all(|&c| !batch.known[c]));
                        assert_eq!(
                            columns_of(&form.matrix, index, Some(&form.original)),
                            full,
                            "residual {residual}, reducers {reducers}, row {index}"
                        );
                    }
                }
            }
        }
    }

    /// After the selective echelon, the selected rows — the only ones F4 reads — and the rank equal
    /// the full-width route's, on rank-deficient batches.
    #[test]
    fn test_selected_rows_after_the_echelon_equal_the_full_width_routes() {
        let mut rng = StdRng::seed_from_u64(1078);
        for residual in [63, 64, 65, 127, 128, 129, 300] {
            let batch = synthetic(&mut rng, 90, residual, 120, 0.2, 0.1, true);
            let selected: Vec<bool> = (0..batch.columns).map(|_| rng.gen_bool(0.5)).collect();
            let mut full = full_width(&batch);
            let full_echelon = reduced_row_echelon_four_russians_selected(&mut full, 6, &selected);
            let mut form =
                residual_form(&batch.reducers, &batch.pairs, batch.columns, usize::MAX).unwrap();
            let local: Vec<bool> = form.original.iter().map(|&c| selected[c]).collect();
            let echelon = reduced_row_echelon_four_russians_selected(&mut form.matrix, 6, &local);
            assert_eq!(echelon.rank, full_echelon.rank);
            assert!(
                echelon.rank < batch.pairs.len(),
                "the batch is rank deficient"
            );
            for index in 0..echelon.rank {
                let ours = columns_of(&form.matrix, index, Some(&form.original));
                let theirs = columns_of(&full, index, None);
                assert_eq!(ours[0], theirs[0], "pivot columns agree");
                if selected[ours[0]] {
                    assert_eq!(ours, theirs, "residual {residual}, row {index}");
                }
            }
        }
    }

    /// Randomized shapes: residual and full-width sweeps agree on every row, and every reducer's
    /// tail is built.
    #[test]
    fn test_random_batches_agree_and_every_tail_is_built() {
        let mut rng = StdRng::seed_from_u64(1079);
        for _ in 0..200 {
            let reducers = rng.gen_range(0..200);
            let residual = rng.gen_range(0..200);
            let pairs = rng.gen_range(0..80);
            let (reducer_density, pair_density) =
                (rng.gen_range(0.0..0.6), rng.gen_range(0.0..0.4));
            let deficient = rng.gen_bool(0.5);
            let batch = synthetic(
                &mut rng,
                reducers,
                residual,
                pairs,
                reducer_density,
                pair_density,
                deficient,
            );
            let expected = full_width(&batch);
            let form =
                residual_form(&batch.reducers, &batch.pairs, batch.columns, usize::MAX).unwrap();
            assert_eq!(form.statistics.tails_built, reducers);
            assert!(form.statistics.referenced_tails <= reducers);
            assert_eq!(
                form.statistics.known_entries + form.statistics.residual_entries,
                batch.pairs.iter().map(SparseRow::nonzeros).sum::<usize>()
            );
            for index in 0..pairs {
                assert_eq!(
                    columns_of(&form.matrix, index, Some(&form.original)),
                    columns_of(&expected, index, None)
                );
            }
        }
    }

    /// A non-unit coefficient declines, as does a working set larger than the room given; the
    /// declined room is the reported working set less one byte.
    #[test]
    fn test_residual_form_declines_coefficients_and_bytes() {
        let mut rng = StdRng::seed_from_u64(1080);
        let batch = synthetic(&mut rng, 30, 70, 20, 0.2, 0.2, false);
        let fits = residual_form(&batch.reducers, &batch.pairs, batch.columns, usize::MAX).unwrap();
        let bytes = fits.statistics.workspace_bytes;
        assert!(bytes > 0);
        assert!(residual_form(&batch.reducers, &batch.pairs, batch.columns, bytes).is_ok());
        assert_eq!(
            residual_form(&batch.reducers, &batch.pairs, batch.columns, bytes - 1).unwrap_err(),
            Decline::Bytes(bytes)
        );

        let lift = |rows: &[SparseRow<Zp2>]| -> Vec<SparseRow<Gf256>> {
            rows.iter()
                .map(|r| {
                    SparseRow::from_sorted(
                        r.entries()
                            .iter()
                            .map(|&(c, _)| (c, Gf256::one()))
                            .collect(),
                    )
                    .unwrap()
                })
                .collect()
        };
        let (reducers, mut pairs) = (lift(&batch.reducers), lift(&batch.pairs));
        assert!(residual_form(&reducers, &pairs, batch.columns, usize::MAX).is_ok());
        let (column, _) = pairs[3].entries()[0];
        let two = Gf256::new(2);
        pairs[3] = SparseRow::from_sorted(vec![(column, two)]).unwrap();
        assert_eq!(
            residual_form(&reducers, &pairs, batch.columns, usize::MAX).unwrap_err(),
            Decline::Coefficient
        );
    }

    /// Random quadratics with a planted root, plus the field equations.
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

    fn options(gf2_elimination: Gf2Elimination) -> F4Options {
        F4Options {
            gf2_elimination,
            ..F4Options::default()
        }
    }

    fn fl_generic() -> F4Options {
        F4Options {
            batch_order: BatchOrder::FaugereLachartre,
            ..options(Gf2Elimination::Generic)
        }
    }

    fn replay<const N: usize>(
        batch: &TracedBatch<N, Zp2>,
        options: &F4Options,
    ) -> Result<crate::grobner::f4::BatchOutcome<N, Zp2>, F4Error> {
        reduce_batch(&batch.basis, &batch.pairs, ORDER, options)
    }

    /// Replayed batch by batch, the residual route's candidates equal the full-width packed
    /// route's and the Faugère–Lachartre route's coefficient for coefficient, rank-deficient and
    /// candidate-free batches included.
    #[test]
    fn test_residual_candidates_equal_full_width_and_fl_candidates_per_batch() {
        let system = random_mq::<10>(7, 12, 0.3);
        let (_, _, trace) =
            trace_batches(&system, ORDER, &options(Gf2Elimination::Generic)).unwrap();
        let (mut deficient, mut candidate_free, mut narrow) = (0, 0, 0);
        for batch in trace.batches() {
            let full = replay(batch, &options(Gf2Elimination::FullWidth)).unwrap();
            let fl = replay(batch, &fl_generic()).unwrap();
            assert_eq!(full.candidates, fl.candidates);
            assert_eq!(full.statistics.packed_gf2.batches, 1);
            assert_eq!(full.statistics.packed_gf2.residual, Default::default());
            let residual = replay(batch, &options(Gf2Elimination::Packed)).unwrap();
            assert_eq!(residual.candidates, full.candidates);
            let (r, p) = (&residual.statistics, &full.statistics);
            assert_eq!(r.packed_gf2.batches, 1);
            assert_eq!(r.packed_gf2.residual.batches, 1);
            assert_eq!(r.elimination.rank, p.elimination.rank);
            assert_eq!(r.elimination.zero_rows, p.elimination.zero_rows);
            assert_eq!(r.back_substituted_rows, p.back_substituted_rows);
            assert_eq!(
                r.packed_gf2.residual.residual_columns + r.packed_gf2.residual.reducers,
                r.columns
            );
            narrow += usize::from(r.packed_gf2.residual.residual_columns < r.columns);
            deficient += usize::from(full.statistics.elimination.zero_rows > 0);
            candidate_free += usize::from(full.candidates.is_empty());
        }
        assert!(deficient > 0 && candidate_free > 0 && narrow > 0);
    }

    /// Whole solves: the residual route returns the generic basis under every order, over `GF(2)`
    /// and over `GF(2^8)` with binary coefficients, and packs every batch.
    #[test]
    fn test_residual_route_returns_the_generic_basis() {
        for order in [
            MonomialOrder::Lexicographic,
            MonomialOrder::GradedLexicographic,
            MonomialOrder::GradedReverseLexicographic,
        ] {
            let systems: Vec<Vec<MultivariatePolynomial<6, Zp2>>> = vec![
                random_mq::<6>(1, 6, 0.5),
                random_mq::<6>(2, 12, 0.3),
                random_mq::<6>(3, 6, 0.05),
                with_field_equations(&cyclic::<6, Zp2>()).unwrap(),
                with_field_equations(&katsura::<6, Zp2>()).unwrap(),
            ];
            for system in &systems {
                let (generic, _) =
                    f4_with_options(system, order, &options(Gf2Elimination::Generic)).unwrap();
                let (basis, statistics) =
                    f4_with_options(system, order, &options(Gf2Elimination::Packed)).unwrap();
                assert_eq!(basis, generic, "{}", order.name());
                assert_eq!(statistics.packed_gf2.batches, statistics.batches);
                assert_eq!(statistics.packed_gf2.residual.batches, statistics.batches);
                assert_eq!(statistics.packed_gf2.declined_batches, 0);
            }
            let binary = cyclic::<5, Gf256>();
            let (generic, _) =
                f4_with_options(&binary, order, &options(Gf2Elimination::Generic)).unwrap();
            let (basis, statistics) =
                f4_with_options(&binary, order, &options(Gf2Elimination::Packed)).unwrap();
            assert_eq!(basis, generic);
            assert_eq!(
                statistics.packed_gf2.batches + statistics.packed_gf2.declined_batches,
                statistics.batches
            );
            assert!(statistics.packed_gf2.residual.batches > 0);
        }
    }

    /// Outside the contract — odd characteristic, a coefficient other than one over `GF(2^8)`,
    /// echelon output — the residual route runs generic, and declines exactly the batches the
    /// full-width route declines.
    #[test]
    fn test_residual_route_keeps_the_packed_eligibility_check() {
        let residual = options(Gf2Elimination::Packed);
        let odd = katsura::<4, Zp13>();
        let (basis, statistics) = f4_with_options(&odd, ORDER, &residual).unwrap();
        assert_eq!(
            basis,
            f4_with_options(&odd, ORDER, &options(Gf2Elimination::Generic))
                .unwrap()
                .0
        );
        assert_eq!(statistics.packed_gf2, Default::default());

        let system = [
            MultivariatePolynomial::<2, Gf256>::parse("x^2 + 2*x*y + 1", ["x", "y"]).unwrap(),
            MultivariatePolynomial::<2, Gf256>::parse("x*y + y^2 + x", ["x", "y"]).unwrap(),
        ];
        let (basis, statistics) = f4_with_options(&system, ORDER, &residual).unwrap();
        let (generic, _) =
            f4_with_options(&system, ORDER, &options(Gf2Elimination::Generic)).unwrap();
        assert_eq!(basis, generic);
        let (_, full) =
            f4_with_options(&system, ORDER, &options(Gf2Elimination::FullWidth)).unwrap();
        assert!(statistics.packed_gf2.declined_batches > 0);
        assert_eq!(
            statistics.packed_gf2.declined_batches,
            full.packed_gf2.declined_batches
        );
        assert_eq!(statistics.packed_gf2.batches, full.packed_gf2.batches);

        let echelon = F4Options {
            reduce_batch_rows: false,
            ..residual
        };
        let (_, statistics) = f4_with_options(&random_mq::<5>(5, 5, 0.5), ORDER, &echelon).unwrap();
        assert_eq!(statistics.packed_gf2, Default::default());
    }

    /// An empty batch and a batch whose rows all reduce to known leads pass through unchanged.
    #[test]
    fn test_degenerate_batches() {
        let residual = options(Gf2Elimination::Packed);
        let system = random_mq::<4>(4, 4, 0.5);
        let basis = MonicBasis::new(&system, ORDER);
        let empty = reduce_batch(&basis, &[], ORDER, &residual).unwrap();
        assert!(empty.candidates.is_empty());
        assert_eq!(empty.statistics.elimination.rank, 0);

        let x = MultivariatePolynomial::<2, Zp2>::parse("x^2 + x", ["x", "y"]).unwrap();
        let y = MultivariatePolynomial::<2, Zp2>::parse("y^2 + y", ["x", "y"]).unwrap();
        let system = [x, y];
        let basis = MonicBasis::new(&system, ORDER);
        let pairs = [CriticalPair::new(&system, 0, 1, ORDER)];
        let generic =
            reduce_batch(&basis, &pairs, ORDER, &options(Gf2Elimination::Generic)).unwrap();
        let ours = reduce_batch(&basis, &pairs, ORDER, &residual).unwrap();
        assert_eq!(ours.candidates, generic.candidates);
        assert!(ours.candidates.is_empty());
        assert_eq!(ours.statistics.packed_gf2.batches, 1);
        assert_eq!(
            ours.statistics.elimination.rank + ours.statistics.elimination.zero_rows,
            ours.statistics.rows
        );
    }

    fn largest_batch<const N: usize>(
        system: &[MultivariatePolynomial<N, Zp2>],
    ) -> TracedBatch<N, Zp2> {
        let (_, _, trace) =
            trace_batches(system, ORDER, &options(Gf2Elimination::Generic)).unwrap();
        trace.largest().expect("at least one batch").clone()
    }

    /// The working set is charged to `max_live_bytes` beside the sparse matrix: admitted exactly,
    /// declined one byte below, and the generic route then answers the same.
    #[test]
    fn test_residual_bytes_are_charged_to_max_live_bytes() {
        let batch = largest_batch(&random_mq::<7>(77, 7, 0.5));
        let generic = replay(&batch, &options(Gf2Elimination::Generic)).unwrap();
        let at = |bytes: usize| F4Options {
            max_live_bytes: bytes,
            max_live_nonzeros: usize::MAX,
            ..options(Gf2Elimination::Packed)
        };
        let unlimited = replay(&batch, &at(usize::MAX)).unwrap();
        let s = &unlimited.statistics;
        let workspace = s.packed_gf2.workspace_bytes;
        assert_eq!(workspace, s.packed_gf2.residual.workspace_bytes);
        let entry_bytes = F4Options::bytes_per_entry::<Zp2>();
        let admitted = s.elimination.initial_nonzeros * entry_bytes + workspace;
        let bit_matrix =
            (s.rows - s.reducer_rows) * s.packed_gf2.residual.residual_columns.div_ceil(64) * 8;
        let exact = admitted.max(s.elimination.peak_nonzeros * entry_bytes + bit_matrix);
        let fits = replay(&batch, &at(exact)).unwrap();
        assert_eq!(fits.statistics.packed_gf2.batches, 1);
        assert_eq!(fits.candidates, generic.candidates);

        let declined = replay(&batch, &at(admitted - 1));
        match declined {
            Ok(outcome) => {
                assert_eq!(outcome.statistics.packed_gf2.batches, 0);
                assert_eq!(outcome.statistics.packed_gf2.declined_batches, 1);
                assert_eq!(outcome.candidates, generic.candidates);
            }
            Err(error) => assert!(matches!(error, F4Error::TooManyLiveBytes { .. })),
        }
    }

    /// The entry allowance binds on the write-back exactly at the reported peak, and a budget the
    /// generic route refuses stays refused.
    #[test]
    fn test_residual_write_back_honours_the_entry_allowance() {
        let batch = largest_batch(&random_mq::<7>(78, 7, 0.5));
        let residual = options(Gf2Elimination::Packed);
        let ours = replay(&batch, &residual).unwrap();
        assert_eq!(ours.statistics.packed_gf2.residual.batches, 1);
        let peak = ours.statistics.elimination.peak_nonzeros;
        let at = |entries: usize| F4Options {
            max_live_nonzeros: entries,
            max_live_bytes: usize::MAX,
            ..residual.clone()
        };
        assert_eq!(
            replay(&batch, &at(peak)).unwrap().candidates,
            ours.candidates
        );
        if peak > ours.statistics.elimination.initial_nonzeros {
            assert_eq!(
                replay(&batch, &at(peak - 1)).unwrap_err(),
                F4Error::TooManyNonzeros {
                    nonzeros: peak,
                    limit: peak - 1
                }
            );
        }

        let system = random_mq::<7>(79, 7, 0.5);
        let tight = |mode| F4Options {
            gf2_elimination: mode,
            ..F4Options::default().with_live_entries::<Zp2>(200)
        };
        let generic = f4_with_options(&system, ORDER, &tight(Gf2Elimination::Generic)).unwrap_err();
        let ours = f4_with_options(&system, ORDER, &tight(Gf2Elimination::Packed)).unwrap_err();
        assert_eq!(generic.stop_kind(), ours.stop_kind());
    }

    /// The default (#1092): `Auto` packs exactly the batches `AutoFullWidth` packs, every one of
    /// them on the residual route, and returns the same basis.
    #[test]
    fn test_auto_packs_the_full_width_batches_on_the_residual_route() {
        assert_eq!(F4Options::default().gf2_elimination, Gf2Elimination::Auto);
        for (n_system, system) in [
            (0, random_mq::<10>(3, 10, 0.3)),
            (1, random_mq::<10>(4, 20, 0.3)),
        ] {
            let (full_basis, full) =
                f4_with_options(&system, ORDER, &options(Gf2Elimination::AutoFullWidth)).unwrap();
            assert!(
                full.packed_gf2.batches > 0,
                "system {n_system} packs under AutoFullWidth"
            );
            assert!(
                full.packed_gf2.batches < full.batches,
                "system {n_system} leaves some batches generic"
            );
            assert_eq!(full.packed_gf2.residual, Default::default());
            let (basis, ours) = f4_with_options(&system, ORDER, &F4Options::default()).unwrap();
            assert_eq!(basis, full_basis, "system {n_system}");
            assert_eq!(ours.packed_gf2.batches, full.packed_gf2.batches);
            assert_eq!(ours.packed_gf2.residual.batches, full.packed_gf2.batches);
        }
    }
}
