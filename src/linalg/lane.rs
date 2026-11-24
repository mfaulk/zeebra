//! Forward elimination over a small prime in `u32` lanes with delayed reduction (#945).
//!
//! A cell holds the field's raw representative, possibly unreduced. Multiplying a raw pivot entry
//! by a canonical multiplier gives the raw form of the product in both canonical and Montgomery
//! representations, so a row operation is integer multiply-adds with no modular reduction.
//!
//! Invariant: every cell is below `bound`, a multiple of `p` with `bound + (p - 1)^2 < 2^32`. One
//! branchless conditional subtract per product restores it. When `p + columns * (p - 1)^2` fits,
//! which holds for GF(31) at any realistic width, the subtract is compiled out.
//!
//! Pivots are stored dense from just after their lead to their tail once their span density
//! reaches [`LaneKernel::dense_percent`], and sparse otherwise. The output matches
//! [`crate::linalg::reduce_rows_against_pivots_with`] entry for entry; `peak_nonzeros` is sampled
//! at row boundaries only.

use crate::{
    linalg::sparse::{EliminationStatistics, SparseMatrix, SparseRow},
    FiniteField,
};

/// The largest prime a lane accepts: above it, `2 (p - 1)^2 + p` overflows a `u32`.
pub const MAX_LANE_PRIME: u32 = 46_337;

const NONE: u32 = u32::MAX;

/// A prime field viewed as `u32` lanes. Obtained from [`FiniteField::small_prime_lane`].
pub struct Lane<F> {
    modulus: u32,
    bound: u32,
    fastmod: u64,
    raw: fn(&F) -> u32,
    element: fn(u32) -> F,
    canonical: fn(&F) -> u32,
}

impl<F> Clone for Lane<F> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<F> Copy for Lane<F> {}

impl<F> std::fmt::Debug for Lane<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Lane")
            .field("modulus", &self.modulus)
            .finish()
    }
}

impl<F: FiniteField> Lane<F> {
    /// A lane for the prime `modulus`, or `None` above [`MAX_LANE_PRIME`].
    ///
    /// `raw` and `element` must be inverse bijections on `[0, modulus)`, linear in the sense that
    /// `raw(a * b) == raw(a) * canonical(b) mod modulus`.
    pub fn new(
        modulus: u32,
        raw: fn(&F) -> u32,
        element: fn(u32) -> F,
        canonical: fn(&F) -> u32,
    ) -> Option<Self> {
        if !(2..=MAX_LANE_PRIME).contains(&modulus) {
            return None;
        }
        let square = (modulus - 1) * (modulus - 1);
        let bound = (u32::MAX - square) / modulus * modulus;
        debug_assert!(bound >= square);
        Some(Self {
            modulus,
            bound,
            fastmod: u64::MAX / u64::from(modulus) + 1,
            raw,
            element,
            canonical,
        })
    }

    /// The prime.
    pub fn modulus(&self) -> u32 {
        self.modulus
    }

    /// `x mod p` by Lemire's multiply-high, exact for every `u32`.
    #[inline(always)]
    fn reduce(&self, x: u32) -> u32 {
        let low = self.fastmod.wrapping_mul(u64::from(x));
        ((u128::from(low) * u128::from(self.modulus)) >> 64) as u32
    }

    /// Whether `columns` row operations on one cell can never leave a `u32`.
    fn needs_correction(&self, columns: usize) -> bool {
        let square = u64::from(self.modulus - 1).pow(2);
        (columns as u64)
            .checked_mul(square)
            .and_then(|total| total.checked_add(u64::from(self.modulus)))
            .is_none_or(|total| total > u64::from(u32::MAX))
    }
}

/// One pivot row, its unit lead omitted.
#[derive(Clone, Debug)]
enum Pivot {
    Sparse { columns: Vec<u32>, values: Vec<u16> },
    Dense { start: u32, values: Vec<u16> },
}

impl Pivot {
    fn tail(&self) -> usize {
        match self {
            Pivot::Sparse { columns, .. } => columns.last().map_or(0, |&c| c as usize + 1),
            Pivot::Dense { start, values } => *start as usize + values.len(),
        }
    }

    /// `(column, raw)` for every stored nonzero, in column order.
    fn entries(&self) -> Box<dyn Iterator<Item = (usize, u32)> + '_> {
        match self {
            Pivot::Sparse { columns, values } => Box::new(
                columns
                    .iter()
                    .zip(values)
                    .map(|(&c, &v)| (c as usize, u32::from(v))),
            ),
            Pivot::Dense { start, values } => Box::new(
                values
                    .iter()
                    .enumerate()
                    .filter(|(_, &v)| v != 0)
                    .map(move |(k, &v)| (*start as usize + k, u32::from(v))),
            ),
        }
    }
}

/// The kernel's one tuning knob.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LaneKernel {
    /// A pivot is stored dense when its nonzeros are at least this percentage of its span. `0`
    /// stores every pivot dense; above `100` stores none.
    pub dense_percent: u32,
}

impl Default for LaneKernel {
    fn default() -> Self {
        Self { dense_percent: 25 }
    }
}

impl LaneKernel {
    /// [`crate::linalg::reduce_rows_against_pivots_with`] through a `u32` lane.
    ///
    /// # Panics
    /// If an upper row is not normalized, or two upper rows share a lead.
    ///
    /// # Errors
    /// The live entry count, sampled at row boundaries, that crossed `max_nonzeros`.
    pub fn reduce_rows_against_pivots<F: FiniteField>(
        &self,
        lane: &Lane<F>,
        matrix: &mut SparseMatrix<F>,
        split: usize,
        max_nonzeros: usize,
    ) -> Result<EliminationStatistics, usize> {
        assert!(
            split <= matrix.num_rows(),
            "a split of {split} in a matrix of {} rows",
            matrix.num_rows()
        );
        let columns = matrix.num_columns();
        assert!(
            columns < NONE as usize,
            "{columns} columns do not fit a u32 index"
        );
        let initial_nonzeros = matrix.nonzeros();
        let mut statistics = EliminationStatistics {
            initial_nonzeros,
            peak_nonzeros: initial_nonzeros,
            ..Default::default()
        };
        if initial_nonzeros > max_nonzeros {
            return Err(initial_nonzeros);
        }

        let mut pivot_at = vec![NONE; columns];
        let mut pivot_row = Vec::new();
        let mut pivots = Vec::new();
        let mut scratch: Vec<(u32, u16)> = Vec::new();
        for index in 0..split {
            let row = matrix.row(index);
            let Some(lead) = row.leading_column() else {
                statistics.zero_rows += 1;
                continue;
            };
            assert_eq!(
                row.leading_coefficient(),
                Some(F::ONE),
                "pivot row {index} is not normalized"
            );
            if pivot_at[lead] != NONE {
                panic!(
                    "pivot rows {} and {index} both lead with column {lead}",
                    pivot_row[pivot_at[lead] as usize]
                );
            }
            scratch.clear();
            scratch.extend(
                row.entries()[1..]
                    .iter()
                    .map(|(c, v)| (*c as u32, (lane.raw)(v) as u16)),
            );
            pivot_at[lead] = pivots.len() as u32;
            pivot_row.push(index);
            pivots.push(self.pivot(lead, &scratch));
            statistics.rank += 1;
        }

        let correct = lane.needs_correction(columns);
        let one = (lane.raw)(&F::ONE);
        let mut cells = vec![0u32; columns];
        let mut resident = initial_nonzeros;
        // (row index, lead, nonzeros) for each pair row that became a pivot.
        let mut finished: Vec<(usize, usize, usize, usize)> = Vec::new();
        for index in split..matrix.num_rows() {
            let row = std::mem::take(&mut matrix.rows_mut()[index]);
            resident -= row.nonzeros();
            let (Some(mut column), Some(last)) = (row.leading_column(), row.trailing_column())
            else {
                statistics.zero_rows += 1;
                continue;
            };
            let mut tail = last + 1;
            for (c, v) in row.entries() {
                cells[*c] = (lane.raw)(v);
            }
            drop(row);

            let mut lead = None;
            while column < tail {
                let x = cells[column];
                if x != 0 {
                    let r = lane.reduce(x);
                    if r != 0 {
                        let slot = pivot_at[column];
                        if slot == NONE {
                            lead = Some((column, r));
                            break;
                        }
                        let pivot = &pivots[slot as usize];
                        let negated = lane.modulus - (lane.canonical)(&(lane.element)(r));
                        if correct {
                            apply::<true>(&mut cells, pivot, negated, lane.bound);
                        } else {
                            apply::<false>(&mut cells, pivot, negated, lane.bound);
                        }
                        statistics.row_operations += 1;
                        tail = tail.max(pivot.tail());
                    }
                    cells[column] = 0;
                }
                column += 1;
            }

            let Some((lead, r)) = lead else {
                statistics.zero_rows += 1;
                continue;
            };
            if r != one {
                statistics.pivot_inversions += 1;
            }
            let inverse = (lane.canonical)(&(lane.element)(r).inverse());
            cells[lead] = 0;
            scratch.clear();
            for (c, cell) in cells.iter_mut().enumerate().take(tail).skip(lead + 1) {
                let x = std::mem::take(cell);
                if x != 0 {
                    let v = lane.reduce(x);
                    if v != 0 {
                        scratch.push((c as u32, lane.reduce(v * inverse) as u16));
                    }
                }
            }
            let nonzeros = scratch.len() + 1;
            resident += nonzeros;
            statistics.peak_nonzeros = statistics.peak_nonzeros.max(resident);
            if resident > max_nonzeros {
                return Err(resident);
            }
            pivot_at[lead] = pivots.len() as u32;
            finished.push((index, lead, nonzeros, pivots.len()));
            pivot_row.push(index);
            pivots.push(self.pivot(lead, &scratch));
            statistics.rank += 1;
        }

        // Back to field elements one pivot at a time, so both copies are never whole at once.
        for (index, lead, nonzeros, slot) in finished {
            let pivot = std::mem::replace(
                &mut pivots[slot],
                Pivot::Sparse {
                    columns: Vec::new(),
                    values: Vec::new(),
                },
            );
            let mut entries = Vec::with_capacity(nonzeros);
            entries.push((lead, F::ONE));
            entries.extend(pivot.entries().map(|(c, v)| (c, (lane.element)(v))));
            debug_assert_eq!(entries.len(), nonzeros);
            // Ascending columns from the lead, zeros skipped: canonical by construction.
            matrix.rows_mut()[index] = SparseRow::from_sorted_unchecked(entries);
        }
        statistics.final_nonzeros = resident;
        debug_assert_eq!(statistics.final_nonzeros, matrix.nonzeros());
        debug_assert_eq!(statistics.rank + statistics.zero_rows, matrix.num_rows());
        Ok(statistics)
    }

    /// A pivot from its strictly-right-of-lead `(column, raw)` entries, dense if dense enough.
    fn pivot(&self, lead: usize, entries: &[(u32, u16)]) -> Pivot {
        let Some(&(last, _)) = entries.last() else {
            return Pivot::Sparse {
                columns: Vec::new(),
                values: Vec::new(),
            };
        };
        let start = lead + 1;
        let span = last as usize + 1 - start;
        if entries.len() as u64 * 100 >= u64::from(self.dense_percent) * span as u64 {
            let mut values = vec![0u16; span];
            for &(c, v) in entries {
                values[c as usize - start] = v;
            }
            Pivot::Dense {
                start: start as u32,
                values,
            }
        } else {
            Pivot::Sparse {
                columns: entries.iter().map(|e| e.0).collect(),
                values: entries.iter().map(|e| e.1).collect(),
            }
        }
    }
}

/// A monic row in lane form for [`LaneWorkspace`], its unit lead omitted.
#[derive(Clone, Debug)]
pub struct LaneRow {
    lead: u32,
    body: Pivot,
    nonzeros: u64,
}

impl LaneRow {
    /// `row`, whose first entry is its lead with coefficient one, stored under `kernel`'s policy.
    pub fn from_monic<F: FiniteField>(
        lane: &Lane<F>,
        kernel: LaneKernel,
        row: &[(u32, F)],
    ) -> Self {
        debug_assert!(row.first().is_some_and(|e| e.1 == F::ONE), "a monic row");
        let entries: Vec<(u32, u16)> = row
            .iter()
            .skip(1)
            .map(|(c, v)| (*c, (lane.raw)(v) as u16))
            .collect();
        let lead = row.first().map_or(0, |e| e.0 as usize);
        Self {
            lead: lead as u32,
            nonzeros: entries.len() as u64,
            body: kernel.pivot(lead, &entries),
        }
    }

    /// The lead column.
    pub fn lead(&self) -> u32 {
        self.lead
    }

    /// The monic field row this was made from.
    pub fn to_field<F: FiniteField>(&self, lane: &Lane<F>) -> Vec<(u32, F)> {
        let mut row = Vec::with_capacity(self.nonzeros as usize + 1);
        row.push((self.lead, F::ONE));
        row.extend(
            self.body
                .entries()
                .map(|(c, v)| (c as u32, (lane.element)(v))),
        );
        row
    }

    /// Nonzeros right of the lead: the products one application costs.
    pub fn nonzeros(&self) -> u64 {
        self.nonzeros
    }

    /// Bytes the row holds on the heap.
    pub fn bytes(&self) -> usize {
        match &self.body {
            Pivot::Sparse { columns, values } => columns.len() * 4 + values.len() * 2,
            Pivot::Dense { values, .. } => values.len() * 2,
        }
    }
}

/// A `u32`-lane working row that fully reduces, the shape of the signature engine's workspace.
#[derive(Clone, Debug)]
pub struct LaneWorkspace<F> {
    lane: Lane<F>,
    cells: Vec<u32>,
    correct: bool,
}

impl<F: FiniteField> LaneWorkspace<F> {
    /// A zero workspace over `columns` columns.
    pub fn new(lane: Lane<F>, columns: usize) -> Self {
        Self {
            correct: lane.needs_correction(columns),
            lane,
            cells: vec![0; columns],
        }
    }

    /// Reduces `entries` (ascending columns) column by column with whatever `pivot` offers, and
    /// returns the entries left at unpivoted columns, unnormalized, and the products spent.
    /// `pivot` is consulted once per column that is nonzero when reached, in ascending order.
    pub fn reduce<'p>(
        &mut self,
        entries: &[(u32, F)],
        pivot: impl FnMut(usize) -> Option<&'p LaneRow>,
    ) -> (Vec<(u32, F)>, u64) {
        let (Some(&(first, _)), Some(&(last, _))) = (entries.first(), entries.last()) else {
            return (Vec::new(), 0);
        };
        let lane = self.lane;
        for (c, v) in entries {
            self.cells[*c as usize] = (lane.raw)(v);
        }
        let (mut column, mut tail) = (first as usize, last as usize + 1);
        let (mut out, mut products) = (Vec::new(), 0);
        let mut pivot = pivot;
        while column < tail {
            let x = std::mem::take(&mut self.cells[column]);
            if x != 0 {
                let r = lane.reduce(x);
                if r != 0 {
                    match pivot(column) {
                        Some(row) => {
                            let negated = lane.modulus - (lane.canonical)(&(lane.element)(r));
                            if self.correct {
                                apply::<true>(&mut self.cells, &row.body, negated, lane.bound);
                            } else {
                                apply::<false>(&mut self.cells, &row.body, negated, lane.bound);
                            }
                            products += row.nonzeros;
                            tail = tail.max(row.body.tail());
                        }
                        None => out.push((column as u32, (lane.element)(r))),
                    }
                }
            }
            column += 1;
        }
        (out, products)
    }
}

/// `cells += negated * pivot`, keeping every cell below `bound` when `CORRECT`.
#[inline(always)]
fn apply<const CORRECT: bool>(cells: &mut [u32], pivot: &Pivot, negated: u32, bound: u32) {
    #[inline(always)]
    fn step<const CORRECT: bool>(cell: &mut u32, value: u16, negated: u32, bound: u32) {
        let sum = *cell + u32::from(value) * negated;
        *cell = if CORRECT {
            sum.min(sum.wrapping_sub(bound))
        } else {
            sum
        };
    }
    match pivot {
        Pivot::Dense { start, values } => {
            let start = *start as usize;
            let target = &mut cells[start..start + values.len()];
            for (cell, &value) in target.iter_mut().zip(values) {
                step::<CORRECT>(cell, value, negated, bound);
            }
        }
        Pivot::Sparse { columns, values } => {
            for (&c, &value) in columns.iter().zip(values) {
                step::<CORRECT>(&mut cells[c as usize], value, negated, bound);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Lane, LaneKernel, LaneRow, LaneWorkspace, MAX_LANE_PRIME};
    use crate::{
        fields::{Mersenne31, Zp31, Zp32003},
        linalg::{
            reduce_rows_against_pivots_with,
            sparse::{EliminationStatistics, SparseMatrix, SparseRow},
            Backend,
        },
        FiniteField, One,
    };
    use rand::{rngs::StdRng, Rng, SeedableRng};

    /// A reducer block with distinct unit leads, then pair rows that fill in under reduction.
    fn block_matrix<F: FiniteField>(
        rng: &mut StdRng,
        columns: usize,
        reducers: usize,
        pairs: usize,
        density: f64,
    ) -> (SparseMatrix<F>, usize) {
        let mut leads: Vec<usize> = (0..columns).collect();
        for k in (1..leads.len()).rev() {
            leads.swap(k, rng.gen_range(0..=k));
        }
        let mut leads: Vec<usize> = leads[..reducers].to_vec();
        leads.sort_unstable();
        let mut rows = Vec::new();
        for &lead in &leads {
            let mut entries = vec![(lead, F::one())];
            for c in lead + 1..columns {
                if rng.gen_bool(density) {
                    entries.push((c, F::new(rng.gen_range(1..u64::MAX))));
                }
            }
            rows.push(SparseRow::new(&entries));
        }
        for _ in 0..pairs {
            let mut entries = Vec::new();
            for c in 0..columns {
                if rng.gen_bool(density) {
                    entries.push((c, F::new(rng.gen_range(0..u64::MAX))));
                }
            }
            rows.push(SparseRow::new(&entries));
        }
        // A duplicate pair row, so some row reduces to zero.
        if pairs > 0 {
            let copy = rows[reducers].clone();
            rows.push(copy);
        }
        (SparseMatrix::new(columns, rows), reducers)
    }

    fn work(statistics: &EliminationStatistics) -> [usize; 6] {
        [
            statistics.rank,
            statistics.zero_rows,
            statistics.initial_nonzeros,
            statistics.final_nonzeros,
            statistics.row_operations,
            statistics.pivot_inversions,
        ]
    }

    fn agrees_with_accumulator<F: FiniteField>(seed: u64, kernel: LaneKernel, density: f64) {
        let lane = F::small_prime_lane().expect("a small prime");
        let mut rng = StdRng::seed_from_u64(seed);
        let (matrix, split) = block_matrix::<F>(&mut rng, 90, 40, 45, density);
        let mut expected = matrix.clone();
        let reference =
            reduce_rows_against_pivots_with(Backend::Adaptive, &mut expected, split, usize::MAX)
                .unwrap();
        let mut actual = matrix;
        let statistics = kernel
            .reduce_rows_against_pivots(&lane, &mut actual, split, usize::MAX)
            .unwrap();
        assert_eq!(actual.rows(), expected.rows(), "seed {seed}, {kernel:?}");
        assert_eq!(work(&statistics), work(&reference), "seed {seed}");
    }

    /// The lane kernel's rows and work counters equal the shipped accumulator's over GF(31).
    #[test]
    fn test_gf31_matches_the_accumulator_kernel() {
        for seed in 0..12 {
            for dense_percent in [0, 25, 101] {
                agrees_with_accumulator::<Zp31>(seed, LaneKernel { dense_percent }, 0.15);
            }
        }
    }

    /// Over GF(32003) the conditional subtract runs on every product, and the result still agrees.
    #[test]
    fn test_gf32003_matches_the_accumulator_kernel() {
        for seed in 0..12 {
            for dense_percent in [0, 25, 101] {
                agrees_with_accumulator::<Zp32003>(seed, LaneKernel { dense_percent }, 0.3);
            }
        }
    }

    /// Hundreds of row operations land on one cell, far past GF(32003)'s four-product headroom.
    #[test]
    fn test_one_cell_survives_many_maximal_products() {
        type F = Zp32003;
        let columns = 400;
        let minus_one = -F::one();
        // Reducer k leads at column k and carries p - 1 in the last column.
        let mut rows: Vec<SparseRow<F>> = (0..columns - 1)
            .map(|k| SparseRow::new(&[(k, F::one()), (columns - 1, minus_one)]))
            .collect();
        rows.push(SparseRow::new(
            &(0..columns).map(|c| (c, minus_one)).collect::<Vec<_>>(),
        ));
        let matrix = SparseMatrix::new(columns, rows);
        let mut expected = matrix.clone();
        reduce_rows_against_pivots_with(Backend::Adaptive, &mut expected, columns - 1, usize::MAX)
            .unwrap();
        let mut actual = matrix;
        LaneKernel::default()
            .reduce_rows_against_pivots(
                &F::small_prime_lane().unwrap(),
                &mut actual,
                columns - 1,
                usize::MAX,
            )
            .unwrap();
        assert_eq!(actual.rows(), expected.rows());
    }

    /// A live-entry budget below what the result holds is refused.
    #[test]
    fn test_a_crossed_budget_is_refused() {
        let mut rng = StdRng::seed_from_u64(7);
        let (mut matrix, split) = block_matrix::<Zp31>(&mut rng, 60, 20, 30, 0.2);
        let initial = matrix.nonzeros();
        let lane = Zp31::small_prime_lane().unwrap();
        assert!(LaneKernel::default()
            .reduce_rows_against_pivots(&lane, &mut matrix, split, initial)
            .is_err());
    }

    /// Small 32-bit primes get a lane; wide primes and 64-bit types do not.
    #[test]
    fn test_only_small_primes_get_a_lane() {
        assert_eq!(Zp31::small_prime_lane().unwrap().modulus(), 31);
        assert_eq!(Zp32003::small_prime_lane().unwrap().modulus(), 32003);
        assert!(Mersenne31::small_prime_lane().is_none());
        assert!(crate::fields::Zp13::small_prime_lane().is_none());
        assert!(Lane::<Zp31>::new(MAX_LANE_PRIME + 1, |_| 0, |_| Zp31::one(), |_| 0).is_none());
    }

    /// The fast remainder is exact at the edges of the `u32` range.
    #[test]
    fn test_reduce_is_exact() {
        for lane in [
            Zp31::small_prime_lane().unwrap().modulus(),
            Zp32003::small_prime_lane().unwrap().modulus(),
            MAX_LANE_PRIME,
        ]
        .map(|p| Lane::<Zp31>::new(p, |_| 0, |_| Zp31::one(), |_| 0).unwrap())
        {
            let p = lane.modulus();
            for x in [
                0,
                1,
                p - 1,
                p,
                p + 1,
                u32::MAX - 1,
                u32::MAX,
                0x8000_0000,
                lane.bound,
            ] {
                assert_eq!(lane.reduce(x), x % p, "{x} mod {p}");
            }
        }
    }
    /// The plain field-arithmetic full reduction the workspace must reproduce.
    fn reference<F: FiniteField>(
        columns: usize,
        entries: &[(u32, F)],
        pivots: &[Option<Vec<(u32, F)>>],
    ) -> (Vec<(u32, F)>, u64) {
        let mut cells = vec![F::zero(); columns];
        for (c, v) in entries {
            cells[*c as usize] = *v;
        }
        let (mut out, mut products) = (Vec::new(), 0);
        for c in 0..columns {
            let v = cells[c];
            if v.is_zero() {
                continue;
            }
            match &pivots[c] {
                Some(row) => {
                    for (cc, w) in &row[1..] {
                        cells[*cc as usize] -= *w * v;
                    }
                    products += (row.len() - 1) as u64;
                }
                None => out.push((c as u32, v)),
            }
        }
        (out, products)
    }

    fn agrees_with_reference<F: FiniteField>(seed: u64, dense_percent: u32) {
        let lane = F::small_prime_lane().unwrap();
        let kernel = LaneKernel { dense_percent };
        let mut rng = StdRng::seed_from_u64(seed);
        let columns = 70;
        let random_tail = |rng: &mut StdRng, from: usize, density: f64| {
            let mut row = Vec::new();
            for c in from..columns {
                if rng.gen_bool(density) {
                    row.push((c as u32, F::new(rng.gen_range(1..u64::MAX))));
                }
            }
            row
        };
        let pivots: Vec<Option<Vec<(u32, F)>>> = (0..columns)
            .map(|c| {
                rng.gen_bool(0.6).then(|| {
                    let mut row = vec![(c as u32, F::one())];
                    let density = if rng.gen_bool(0.5) { 0.9 } else { 0.05 };
                    row.extend(random_tail(&mut rng, c + 1, density));
                    row
                })
            })
            .collect();
        let lanes: Vec<Option<LaneRow>> = pivots
            .iter()
            .map(|p| {
                p.as_ref()
                    .map(|row| LaneRow::from_monic(&lane, kernel, row))
            })
            .collect();
        let mut workspace = LaneWorkspace::new(lane, columns);
        for _ in 0..8 {
            let entries = random_tail(&mut rng, 0, 0.3);
            let mut seen = Vec::new();
            let actual = workspace.reduce(&entries, |c| {
                seen.push(c);
                lanes[c].as_ref()
            });
            assert_eq!(actual, reference(columns, &entries, &pivots), "seed {seed}");
            assert!(seen.windows(2).all(|w| w[0] < w[1]), "ascending, once each");
        }
    }

    /// The workspace's full reduction equals plain field arithmetic, product count included.
    #[test]
    fn test_workspace_matches_a_field_reference() {
        for seed in 0..10 {
            for dense_percent in [0, 25, 101] {
                agrees_with_reference::<Zp31>(seed, dense_percent);
                agrees_with_reference::<Zp32003>(seed, dense_percent);
            }
        }
    }

    /// A dense lane row is smaller than its sparse form, and both report their heap bytes.
    #[test]
    fn test_lane_row_bytes_follow_the_storage_policy() {
        let lane = Zp31::small_prime_lane().unwrap();
        let row: Vec<(u32, Zp31)> = (0..101).map(|c| (c, Zp31::one())).collect();
        let dense = LaneRow::from_monic(&lane, LaneKernel { dense_percent: 0 }, &row);
        let sparse = LaneRow::from_monic(&lane, LaneKernel { dense_percent: 101 }, &row);
        assert_eq!(dense.bytes(), 100 * 2);
        assert_eq!(sparse.bytes(), 100 * 6);
    }
    /// A lane row converts back to the monic field row it was made from, under either storage.
    #[test]
    fn test_lane_row_round_trips_to_its_field_row() {
        let lane = Zp32003::small_prime_lane().unwrap();
        let mut rng = StdRng::seed_from_u64(3);
        let mut row = vec![(5u32, Zp32003::one())];
        for c in 6..90u32 {
            if rng.gen_bool(0.4) {
                row.push((c, Zp32003::new(rng.gen_range(1..32003))));
            }
        }
        for dense_percent in [0, 101] {
            let lane_row = LaneRow::from_monic(&lane, LaneKernel { dense_percent }, &row);
            assert_eq!(lane_row.lead(), 5);
            assert_eq!(lane_row.to_field(&lane), row);
        }
    }
}
