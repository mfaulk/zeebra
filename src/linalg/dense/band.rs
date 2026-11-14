//! Research-only four-row bands for #715: one sparse pivot read feeds every lane at its column.
//!
//! Equivalence with the single-row loop rests on the sweep taking the smallest leading column over
//! the active lanes and, when that column has no pivot, promoting the lowest-indexed lane there.
//! A lane's leading column only grows, so a lane never revisits a column a higher-indexed lane
//! claimed, and every lane applies exactly the pivots, factors and normalization it would have
//! applied alone. `docs/research/multirow-reuse.md` gives the full argument.

use std::cell::{Cell, RefCell};

use super::accumulator::DenseAccumulator;
use crate::{
    linalg::{
        sparse::{EliminationStatistics, SparseMatrix, SparseRow},
        PivotIndex,
    },
    FiniteField,
};

/// Rows per band. Upstream measured eight as mixed; four is the hypothesis under test.
const LANES: usize = 4;

/// Which forward kernel the accumulated backend runs on this thread.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum Mode {
    /// The production single-row loop, unchanged.
    #[default]
    Single,
    /// Four separate dense rows; a pivot is read once and applied only to lanes that need it.
    Band4,
    /// Four rows interleaved per column; two or more needy lanes take one all-lane update.
    Lanes4,
}

/// Exact work for one matrix the band kernel eliminated.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct MatrixCensus {
    pub rows: usize,
    pub columns: usize,
    pub first: usize,
    /// Mean stored entries of the rows the bands processed, before reduction.
    pub target_entries: usize,
    pub bands: usize,
    pub partial_bands: usize,
    /// Target updates, which equals the single-row `row_operations`.
    pub pivot_applications: usize,
    /// Distinct pivot reads after sharing across lanes.
    pub pivot_reads: usize,
    /// Pivot entries summed over applications: the single-row arm's reads and products.
    pub entries_applied: usize,
    /// Pivot entries summed over distinct reads.
    pub entries_read: usize,
    /// Coefficient products executed, counting zero-factor lanes of an all-lane update.
    pub lane_products: usize,
    /// Distinct reads by how many lanes shared them, index 1 to 4.
    pub reads_by_lanes: [usize; LANES + 1],
    /// Pivots discovered inside a band and used by a later lane of the same band.
    pub intra_band_pivots: usize,
    pub new_pivots: usize,
    pub zero_rows: usize,
    /// Dense scratch held by the kernel, in bytes.
    pub scratch_bytes: usize,
}

/// Every matrix eliminated on this thread since the last [`take_census`].
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Census {
    pub matrices: Vec<MatrixCensus>,
}

thread_local! {
    static MODE: Cell<Mode> = const { Cell::new(Mode::Single) };
    static CENSUS: RefCell<Census> = RefCell::new(Census::default());
}

/// The mode selected on this thread.
pub fn mode() -> Mode {
    MODE.with(Cell::get)
}

/// Run `f` with `mode` selected on this thread, restoring the previous mode even on panic.
pub fn with_mode<T>(mode: Mode, f: impl FnOnce() -> T) -> T {
    struct Restore(Mode);
    impl Drop for Restore {
        fn drop(&mut self) {
            MODE.with(|cell| cell.set(self.0));
        }
    }
    let _restore = Restore(MODE.with(|cell| cell.replace(mode)));
    f()
}

/// A copy of this thread's census.
pub fn census() -> Census {
    CENSUS.with(|census| census.borrow().clone())
}

/// This thread's census, leaving it empty.
pub fn take_census() -> Census {
    CENSUS.with(|census| std::mem::take(&mut *census.borrow_mut()))
}

/// Four target rows held together while one sweep reduces them.
trait LaneStore<F: FiniteField> {
    fn load(&mut self, lane: usize, row: &SparseRow<F>);
    fn leading_column(&mut self, lane: usize) -> Option<usize>;
    fn leading_coefficient(&self, lane: usize) -> F;
    fn nonzeros(&self, lane: usize) -> usize;
    /// `lane -= factor * pivot` for every selected lane; returns the coefficient products executed.
    fn subtract(&mut self, lanes: &[usize], factors: &[F; LANES], pivot: &SparseRow<F>) -> usize;
    fn normalize(&mut self, lane: usize) -> bool;
    fn take(&mut self, lane: usize) -> SparseRow<F>;
    fn scratch_bytes(&self) -> usize;
}

/// Four production accumulators. A single needy lane takes the production loop verbatim.
struct Separate<F: FiniteField>([DenseAccumulator<F>; LANES]);

impl<F: FiniteField> LaneStore<F> for Separate<F> {
    fn load(&mut self, lane: usize, row: &SparseRow<F>) {
        self.0[lane].load(row);
    }
    fn leading_column(&mut self, lane: usize) -> Option<usize> {
        self.0[lane].leading_column()
    }
    fn leading_coefficient(&self, lane: usize) -> F {
        self.0[lane]
            .leading_coefficient()
            .expect("an active lane has a leading coefficient")
    }
    fn nonzeros(&self, lane: usize) -> usize {
        self.0[lane].nonzeros()
    }
    fn subtract(&mut self, lanes: &[usize], factors: &[F; LANES], pivot: &SparseRow<F>) -> usize {
        if let [lane] = lanes {
            self.0[*lane].subtract_scaled(pivot, factors[*lane]);
            return pivot.nonzeros();
        }
        match *lanes {
            [a, b] => shared(&mut self.0, [a, b], factors, pivot),
            [a, b, c] => shared(&mut self.0, [a, b, c], factors, pivot),
            [a, b, c, d] => shared(&mut self.0, [a, b, c, d], factors, pivot),
            _ => unreachable!("a band has at most {LANES} lanes"),
        }
        if let (Some(lead), Some(tail)) = (pivot.leading_column(), pivot.trailing_column()) {
            for &lane in lanes {
                let accumulator = &mut self.0[lane];
                accumulator.lead = accumulator.lead.min(lead);
                accumulator.tail = accumulator.tail.max(tail + 1);
            }
        }
        lanes.len() * pivot.nonzeros()
    }
    fn normalize(&mut self, lane: usize) -> bool {
        self.0[lane].normalize()
    }
    fn take(&mut self, lane: usize) -> SparseRow<F> {
        self.0[lane].take()
    }
    fn scratch_bytes(&self) -> usize {
        LANES * self.0[0].cells.capacity() * std::mem::size_of::<F>()
    }
}

/// One pass over the pivot for `K` lanes, with each lane's cells hoisted out of the loop.
fn shared<F: FiniteField, const K: usize>(
    accumulators: &mut [DenseAccumulator<F>; LANES],
    lanes: [usize; K],
    factors: &[F; LANES],
    pivot: &SparseRow<F>,
) {
    let selected = accumulators
        .get_disjoint_mut(lanes)
        .expect("needy lanes are distinct");
    let lane_factors: [F; K] = std::array::from_fn(|k| factors[lanes[k]]);
    let mut counts: [usize; K] = std::array::from_fn(|k| selected[k].nonzeros);
    let cells: [&mut [F]; K] = selected.map(|accumulator| accumulator.cells.as_mut_slice());
    for (column, coefficient) in pivot.entries() {
        for k in 0..K {
            let before = cells[k][*column];
            let after = before - lane_factors[k] * *coefficient;
            cells[k][*column] = after;
            counts[k] += usize::from(before.is_zero());
            counts[k] -= usize::from(after.is_zero());
        }
    }
    let selected = accumulators
        .get_disjoint_mut(lanes)
        .expect("needy lanes are distinct");
    for (accumulator, count) in selected.into_iter().zip(counts) {
        accumulator.nonzeros = count;
    }
}

/// Four rows interleaved per column, so an all-lane update touches one contiguous cell group.
struct Interleaved<F: FiniteField> {
    cells: Vec<[F; LANES]>,
    lead: [usize; LANES],
    tail: [usize; LANES],
    nonzeros: [usize; LANES],
}

impl<F: FiniteField> Interleaved<F> {
    fn new(num_columns: usize) -> Self {
        Self {
            cells: vec![[F::zero(); LANES]; num_columns],
            lead: [num_columns; LANES],
            tail: [0; LANES],
            nonzeros: [0; LANES],
        }
    }
}

impl<F: FiniteField> LaneStore<F> for Interleaved<F> {
    fn load(&mut self, lane: usize, row: &SparseRow<F>) {
        assert_eq!(self.nonzeros[lane], 0, "the lane still holds a row");
        for (column, coefficient) in row.entries() {
            self.cells[*column][lane] = *coefficient;
        }
        self.lead[lane] = row.leading_column().unwrap_or(self.cells.len());
        self.tail[lane] = row.trailing_column().map_or(0, |column| column + 1);
        self.nonzeros[lane] = row.nonzeros();
    }
    fn leading_column(&mut self, lane: usize) -> Option<usize> {
        if self.nonzeros[lane] == 0 {
            self.lead[lane] = self.cells.len();
            self.tail[lane] = 0;
            return None;
        }
        let mut column = self.lead[lane];
        while self.cells[column][lane].is_zero() {
            column += 1;
        }
        self.lead[lane] = column;
        Some(column)
    }
    fn leading_coefficient(&self, lane: usize) -> F {
        self.cells[self.lead[lane]][lane]
    }
    fn nonzeros(&self, lane: usize) -> usize {
        self.nonzeros[lane]
    }
    fn subtract(&mut self, lanes: &[usize], factors: &[F; LANES], pivot: &SparseRow<F>) -> usize {
        let products = if let [lane] = lanes {
            // One needy lane stays scalar: an all-lane update would multiply three zero factors.
            let lane = *lane;
            let factor = factors[lane];
            for (column, coefficient) in pivot.entries() {
                let before = self.cells[*column][lane];
                let after = before - factor * *coefficient;
                self.cells[*column][lane] = after;
                self.nonzeros[lane] += usize::from(before.is_zero());
                self.nonzeros[lane] -= usize::from(after.is_zero());
            }
            pivot.nonzeros()
        } else {
            // Lanes outside `lanes` carry a zero factor, which leaves their cells and counts as
            // they were; the fixed-width body is what the compiler can widen.
            let mut lane_factors = [F::zero(); LANES];
            for &lane in lanes {
                lane_factors[lane] = factors[lane];
            }
            let mut gained = [0usize; LANES];
            let mut lost = [0usize; LANES];
            for (column, coefficient) in pivot.entries() {
                let group = &mut self.cells[*column];
                for lane in 0..LANES {
                    let before = group[lane];
                    let after = before - lane_factors[lane] * *coefficient;
                    group[lane] = after;
                    gained[lane] += usize::from(before.is_zero());
                    lost[lane] += usize::from(after.is_zero());
                }
            }
            for lane in 0..LANES {
                self.nonzeros[lane] = self.nonzeros[lane] + gained[lane] - lost[lane];
            }
            LANES * pivot.nonzeros()
        };
        if let (Some(lead), Some(tail)) = (pivot.leading_column(), pivot.trailing_column()) {
            for &lane in lanes {
                self.lead[lane] = self.lead[lane].min(lead);
                self.tail[lane] = self.tail[lane].max(tail + 1);
            }
        }
        products
    }
    fn normalize(&mut self, lane: usize) -> bool {
        let coefficient = self.cells[self.lead[lane]][lane];
        if coefficient == F::ONE {
            return false;
        }
        let inverse = coefficient.inverse();
        for column in self.lead[lane]..self.tail[lane] {
            self.cells[column][lane] *= inverse;
        }
        true
    }
    fn take(&mut self, lane: usize) -> SparseRow<F> {
        let mut entries = Vec::with_capacity(self.nonzeros[lane]);
        for column in self.lead[lane]..self.tail[lane] {
            let cell = std::mem::replace(&mut self.cells[column][lane], F::zero());
            if !cell.is_zero() {
                entries.push((column, cell));
            }
        }
        debug_assert_eq!(entries.len(), self.nonzeros[lane]);
        self.lead[lane] = self.cells.len();
        self.tail[lane] = 0;
        self.nonzeros[lane] = 0;
        SparseRow::from_sorted_unchecked(entries)
    }
    fn scratch_bytes(&self) -> usize {
        self.cells.capacity() * std::mem::size_of::<[F; LANES]>()
    }
}

/// Rows `[first..]` reduced four at a time against `pivot_of_column`, in the selected mode.
pub(super) fn eliminate_from<F: FiniteField>(
    matrix: &mut SparseMatrix<F>,
    first: usize,
    pivot_of_column: &mut PivotIndex,
    statistics: &mut EliminationStatistics,
    resident: &mut usize,
    max_nonzeros: usize,
) -> Result<(), usize> {
    let columns = matrix.num_columns();
    let mut census = MatrixCensus {
        rows: matrix.num_rows(),
        columns,
        first,
        ..Default::default()
    };
    let result = match mode() {
        Mode::Single => unreachable!("the single-row mode never reaches the band kernel"),
        Mode::Band4 => sweep(
            matrix,
            first,
            pivot_of_column,
            statistics,
            resident,
            max_nonzeros,
            &mut Separate(std::array::from_fn(|_| DenseAccumulator::new(columns))),
            &mut census,
        ),
        Mode::Lanes4 => sweep(
            matrix,
            first,
            pivot_of_column,
            statistics,
            resident,
            max_nonzeros,
            &mut Interleaved::new(columns),
            &mut census,
        ),
    };
    CENSUS.with(|all| all.borrow_mut().matrices.push(census));
    result
}

#[allow(clippy::too_many_arguments)]
fn sweep<F: FiniteField, L: LaneStore<F>>(
    matrix: &mut SparseMatrix<F>,
    first: usize,
    pivot_of_column: &mut PivotIndex,
    statistics: &mut EliminationStatistics,
    resident: &mut usize,
    max_nonzeros: usize,
    lanes: &mut L,
    census: &mut MatrixCensus,
) -> Result<(), usize> {
    census.scratch_bytes = lanes.scratch_bytes();
    let rows = matrix.num_rows();
    let mut start = first;
    while start < rows {
        let width = LANES.min(rows - start);
        census.bands += 1;
        census.partial_bands += usize::from(width < LANES);
        let mut active = [false; LANES];
        // The lane that discovered each column's pivot inside this band, for the census only.
        let mut discovered: [Option<usize>; LANES] = [None; LANES];
        for (lane, flag) in active.iter_mut().enumerate().take(width) {
            let row = std::mem::take(&mut matrix.rows_mut()[start + lane]);
            *resident -= row.nonzeros();
            census.target_entries += row.nonzeros();
            lanes.load(lane, &row);
            *flag = true;
        }

        loop {
            let mut column = usize::MAX;
            for lane in 0..width {
                if !active[lane] {
                    continue;
                }
                match lanes.leading_column(lane) {
                    Some(lead) => column = column.min(lead),
                    None => {
                        matrix.rows_mut()[start + lane] = lanes.take(lane);
                        statistics.zero_rows += 1;
                        census.zero_rows += 1;
                        active[lane] = false;
                    }
                }
            }
            if column == usize::MAX {
                break;
            }
            let mut needy = [0usize; LANES];
            let mut count = 0;
            for lane in 0..width {
                if active[lane] && lanes.leading_column(lane) == Some(column) {
                    needy[count] = lane;
                    count += 1;
                }
            }
            let needy = &needy[..count];

            match pivot_of_column.pivot_of(column) {
                Some(pivot_index) => {
                    // Every pivot is monic, so each lane's factor is its own leading coefficient.
                    let mut factors = [F::zero(); LANES];
                    for &lane in needy {
                        factors[lane] = lanes.leading_coefficient(lane);
                    }
                    let pivot = matrix.row(pivot_index);
                    census.lane_products += lanes.subtract(needy, &factors, pivot);
                    census.pivot_applications += needy.len();
                    census.pivot_reads += 1;
                    census.entries_applied += needy.len() * pivot.nonzeros();
                    census.entries_read += pivot.nonzeros();
                    census.reads_by_lanes[needy.len()] += 1;
                    if pivot_index >= start && pivot_index < start + width {
                        debug_assert!(discovered.contains(&Some(column)));
                        census.intra_band_pivots += needy.len();
                    }
                    statistics.row_operations += needy.len();
                    let live = *resident
                        + (0..width)
                            .filter(|&lane| active[lane])
                            .map(|lane| lanes.nonzeros(lane))
                            .sum::<usize>();
                    statistics.peak_nonzeros = statistics.peak_nonzeros.max(live);
                    if live > max_nonzeros {
                        return Err(live);
                    }
                }
                None => {
                    // The lowest-indexed lane is the row the single-row loop reaches first.
                    let lane = needy[0];
                    if lanes.normalize(lane) {
                        statistics.pivot_inversions += 1;
                    }
                    pivot_of_column.insert(column, start + lane);
                    statistics.rank += 1;
                    census.new_pivots += 1;
                    discovered[lane] = Some(column);
                    let row = lanes.take(lane);
                    *resident += row.nonzeros();
                    statistics.peak_nonzeros = statistics.peak_nonzeros.max(*resident);
                    matrix.rows_mut()[start + lane] = row;
                    active[lane] = false;
                }
            }
        }
        start += width;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{take_census, with_mode, Mode};
    use crate::{
        fields::{Zp13, Zp2147483647, Zp32003},
        linalg::{
            reduce_rows_against_pivots_with, row_echelon_with,
            sparse::{EliminationStatistics, SparseMatrix, SparseRow},
            Backend,
        },
        FiniteField,
    };

    const BANDS: [Mode; 2] = [Mode::Band4, Mode::Lanes4];

    fn matrix<F: FiniteField>(columns: usize, rows: &[&[(usize, u64)]]) -> SparseMatrix<F> {
        SparseMatrix::new(
            columns,
            rows.iter()
                .map(|row| {
                    SparseRow::new(
                        &row.iter()
                            .map(|(column, value)| (*column, F::new(*value)))
                            .collect::<Vec<_>>(),
                    )
                })
                .collect(),
        )
    }

    /// A deterministic pseudo-random sparse matrix; `density` is in percent.
    fn random<F: FiniteField>(
        seed: u64,
        rows: usize,
        columns: usize,
        density: u64,
    ) -> SparseMatrix<F> {
        let mut state = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let mut built = Vec::with_capacity(rows);
        for _ in 0..rows {
            let mut entries: Vec<(usize, F)> = Vec::new();
            for column in 0..columns {
                if next() % 100 < density {
                    entries.push((column, F::new(next() % 1000 + 1)));
                }
            }
            built.push(SparseRow::new(&entries));
        }
        SparseMatrix::new(columns, built)
    }

    fn comparable(statistics: &EliminationStatistics) -> [usize; 5] {
        [
            statistics.rank,
            statistics.zero_rows,
            statistics.row_operations,
            statistics.pivot_inversions,
            statistics.final_nonzeros,
        ]
    }

    /// Echelon under every band mode equals the single-row result row for row.
    fn assert_echelon_matches<F: FiniteField>(original: &SparseMatrix<F>) {
        let mut single = original.clone();
        let expected = row_echelon_with(Backend::Adaptive, &mut single, usize::MAX).unwrap();
        for band in BANDS {
            let mut candidate = original.clone();
            let actual = with_mode(band, || {
                row_echelon_with(Backend::Adaptive, &mut candidate, usize::MAX).unwrap()
            });
            assert_eq!(candidate.rows(), single.rows(), "{band:?} rows differ");
            assert_eq!(
                comparable(&actual),
                comparable(&expected),
                "{band:?} statistics differ"
            );
        }
    }

    /// Block reduction under every band mode equals the single-row result row for row.
    fn assert_block_matches<F: FiniteField>(original: &SparseMatrix<F>, split: usize) {
        let mut single = original.clone();
        let expected =
            reduce_rows_against_pivots_with(Backend::Adaptive, &mut single, split, usize::MAX)
                .unwrap();
        for band in BANDS {
            let mut candidate = original.clone();
            let actual = with_mode(band, || {
                reduce_rows_against_pivots_with(
                    Backend::Adaptive,
                    &mut candidate,
                    split,
                    usize::MAX,
                )
                .unwrap()
            });
            assert_eq!(candidate.rows(), single.rows(), "{band:?} rows differ");
            assert_eq!(
                comparable(&actual),
                comparable(&expected),
                "{band:?} statistics differ"
            );
        }
    }

    /// The default mode is the production single-row path, and `with_mode` restores it.
    #[test]
    fn test_mode_defaults_to_single_and_restores() {
        assert_eq!(super::mode(), Mode::Single);
        with_mode(Mode::Lanes4, || assert_eq!(super::mode(), Mode::Lanes4));
        assert_eq!(super::mode(), Mode::Single);
    }

    /// A later lane is reduced by a pivot an earlier lane of the same band just discovered.
    #[test]
    fn test_intra_band_new_pivot_feeds_later_lanes() {
        let original = matrix::<Zp13>(
            5,
            &[
                &[(0, 2), (2, 1)],
                &[(0, 3), (1, 1)],
                &[(0, 1), (2, 4), (4, 1)],
                &[(1, 5), (3, 2)],
            ],
        );
        take_census();
        assert_echelon_matches(&original);
        let census = take_census();
        assert!(census.matrices.iter().all(|m| m.intra_band_pivots > 0));
    }

    /// Two lanes sharing a leading column take one pivot read between them.
    #[test]
    fn test_shared_column_is_read_once() {
        let original = matrix::<Zp13>(
            6,
            &[
                &[(0, 1), (3, 2)],
                &[(1, 1), (4, 1)],
                &[(0, 4), (5, 1)],
                &[(0, 7), (1, 3), (2, 1)],
            ],
        );
        take_census();
        assert_block_matches(&original, 2);
        let census = take_census();
        for matrix in census.matrices {
            assert_eq!(matrix.entries_applied, 2 * 2 + 2);
            assert!(matrix.reads_by_lanes[2] >= 1, "{matrix:?}");
            assert!(matrix.entries_read < matrix.entries_applied);
        }
    }

    /// Rows that cancel to zero, including a whole band of zeros, are retired as zero rows.
    #[test]
    fn test_zero_and_cancelling_rows() {
        let original = matrix::<Zp13>(
            4,
            &[
                &[(0, 1), (1, 2)],
                &[(0, 2), (1, 4)],
                &[],
                &[(0, 3), (1, 6)],
                &[],
                &[],
                &[],
                &[],
            ],
        );
        assert_echelon_matches(&original);
        assert_echelon_matches(&matrix::<Zp13>(3, &[&[], &[], &[]]));
    }

    /// Tails shorter than a band and single-row matrices match the single-row loop.
    #[test]
    fn test_partial_bands() {
        for rows in 1..=9 {
            assert_echelon_matches(&random::<Zp13>(rows as u64, rows, 12, 40));
        }
        take_census();
        assert_echelon_matches(&random::<Zp13>(5, 5, 12, 40));
        assert!(take_census().matrices.iter().all(|m| m.partial_bands == 1));
    }

    /// Rank-deficient and degenerate shapes match, including duplicated rows and empty widths.
    #[test]
    fn test_rank_deficient_and_degenerate() {
        let mut duplicated = random::<Zp32003>(7, 6, 10, 50);
        let copy = duplicated.rows().to_vec();
        let mut rows = copy.clone();
        rows.extend(copy);
        duplicated = SparseMatrix::new(10, rows);
        assert_echelon_matches(&duplicated);
        assert_echelon_matches(&matrix::<Zp13>(0, &[&[], &[]]));
        assert_echelon_matches(&SparseMatrix::<Zp13>::new(5, Vec::new()));
        // Tall and narrow: rank at most two, most rows cancel.
        assert_echelon_matches(&random::<Zp13>(11, 20, 2, 70));
    }

    /// Random matrices across fields, densities and splits match the single-row loop exactly.
    #[test]
    fn test_random_matrices_across_fields() {
        for seed in 0..40 {
            let density = [5, 15, 40, 80][seed as usize % 4];
            assert_echelon_matches(&random::<Zp13>(seed, 17, 23, density));
            assert_echelon_matches(&random::<Zp32003>(seed, 19, 31, density));
            assert_echelon_matches(&random::<Zp2147483647>(seed, 13, 29, density));
        }
    }

    /// A monic triangular upper block followed by random rows matches, as does a full echelon.
    #[test]
    fn test_block_reduction_against_an_upper_block() {
        for seed in 0..20 {
            let columns = 24;
            let split = 8;
            let lower = random::<Zp32003>(seed + 100, 14, columns, 30);
            let mut rows: Vec<SparseRow<Zp32003>> = (0..split)
                .map(|index| {
                    let mut entries = vec![(index * 3, Zp32003::new(1))];
                    entries.extend(
                        (index * 3 + 1..columns)
                            .filter(|column| (column + seed as usize).is_multiple_of(4))
                            .map(|column| (column, Zp32003::new(column as u64 + 2))),
                    );
                    SparseRow::new(&entries)
                })
                .collect();
            // Lower rows must not lead with a reducer's column, as symbolic preprocessing ensures
            // for F4; the generic entry point does not require it, so both shapes are covered.
            rows.extend(lower.rows().iter().cloned());
            let original = SparseMatrix::new(columns, rows);
            assert_block_matches(&original, split);
            assert_block_matches(&original, 0);
        }
    }

    /// An entry budget the single-row loop exceeds is reported, not silently ignored, by a band.
    #[test]
    fn test_budget_refusal() {
        let original = random::<Zp32003>(3, 16, 40, 60);
        let mut probe = original.clone();
        let initial = original.nonzeros();
        let statistics = row_echelon_with(Backend::Adaptive, &mut probe, usize::MAX).unwrap();
        assert!(statistics.peak_nonzeros > initial);
        for band in BANDS {
            let mut candidate = original.clone();
            let refused = with_mode(band, || {
                row_echelon_with(Backend::Adaptive, &mut candidate, initial)
            });
            assert!(refused.is_err(), "{band:?} accepted a budget it exceeds");
        }
    }

    fn assert_basis_matches<const N: usize, F: FiniteField>(
        system: Vec<crate::MultivariatePolynomial<N, F>>,
    ) {
        use crate::{
            grobner::{f4_with_options, F4Options},
            MonomialOrder,
        };
        let order = MonomialOrder::GradedReverseLexicographic;
        let options = F4Options::default();
        let (expected, statistics) = f4_with_options(&system, order, &options).unwrap();
        for band in BANDS {
            take_census();
            let (actual, banded) =
                with_mode(band, || f4_with_options(&system, order, &options).unwrap());
            assert_eq!(actual, expected, "{band:?} basis differs");
            assert_eq!(
                banded.batches, statistics.batches,
                "{band:?} trajectory differs"
            );
            let census = take_census();
            assert!(
                !census.matrices.is_empty(),
                "{band:?} never ran the band kernel"
            );
        }
    }

    /// The default F4 configuration returns the identical reduced basis under every band mode.
    #[test]
    fn test_full_basis_equality_on_real_systems() {
        use crate::grobner::benchmark_systems::{cyclic, katsura};
        assert_basis_matches(katsura::<5, Zp32003>());
        assert_basis_matches(cyclic::<5, Zp32003>());
        assert_basis_matches(katsura::<5, Zp2147483647>());
        assert_basis_matches(cyclic::<4, Zp2147483647>());
    }
}
