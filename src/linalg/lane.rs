//! Forward elimination over a prime field in `u32` lanes with delayed reduction (#945, #1183).
//!
//! A cell holds the field's raw representative, possibly unreduced. Multiplying a raw pivot entry
//! by a canonical multiplier gives the raw form of the product in both canonical and Montgomery
//! representations, so a row operation is integer multiply-adds with no modular reduction.
//!
//! Two widths share the kernels:
//!
//! - the small lane (#945), for primes up to [`MAX_LANE_PRIME`]: `u16` pivot values, `u32` cells;
//! - the 31-bit lane (#1183), for primes up to [`MAX_LANE31_PRIME`]: `u32` pivot values, `u64`
//!   cells. Mersenne31, BabyBear and KoalaBear are in range.
//!
//! Invariant: every cell is below `bound`, a multiple of `p` with `bound + (p - 1)^2` inside the
//! cell and `bound >= (p - 1)^2`. One branchless conditional subtract per product restores it.
//! When `p + columns * (p - 1)^2` fits the cell, which holds for GF(31) at any realistic width,
//! the subtract is compiled out. The proof for every admitted prime is in
//! `docs/research/31-bit-lane.md`.
//!
//! Pivots are stored dense from just after their lead to their tail once their span density
//! reaches [`LaneKernel::dense_percent`], and sparse otherwise. The output matches
//! [`crate::linalg::reduce_rows_against_pivots_with`] entry for entry; `peak_nonzeros` is sampled
//! at row boundaries only.

use crate::{
    linalg::sparse::{EliminationStatistics, SparseMatrix, SparseRow},
    FiniteField,
};

/// The largest prime the small lane accepts: above it, `2 (p - 1)^2 + p` overflows a `u32`.
pub const MAX_LANE_PRIME: u32 = 46_337;

/// The largest prime the 31-bit lane accepts, 2^31 - 1. `2 (p - 1)^2 + p` stays below 2^63.
pub const MAX_LANE31_PRIME: u32 = (1 << 31) - 1;

const NONE: u32 = u32::MAX;

/// Which pair of widths a lane computes in.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Kind {
    Small,
    ThirtyOne,
}

/// A prime field viewed as `u32` lanes. Obtained from [`FiniteField::small_prime_lane`] or
/// [`FiniteField::prime31_lane`].
pub struct Lane<F> {
    modulus: u32,
    kind: Kind,
    /// The cell invariant's bound, a multiple of `modulus`.
    bound: u64,
    /// Small lane: Lemire's `2^64 / p`, rounded up. 31-bit lane: Barrett's `(2^64 - 1) / p`.
    magic: u64,
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
            .field("kind", &self.kind)
            .finish()
    }
}

impl<F> Lane<F> {
    /// A small lane for the prime `modulus`, or `None` above [`MAX_LANE_PRIME`].
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
            kind: Kind::Small,
            bound: u64::from(bound),
            magic: u64::MAX / u64::from(modulus) + 1,
            raw,
            element,
            canonical,
        })
    }

    /// A 31-bit lane for the prime `modulus`, or `None` above [`MAX_LANE31_PRIME`]. The
    /// conversions are as for [`Self::new`].
    ///
    /// Any `modulus` from 2 up is exact here; [`FiniteField::prime31_lane`] offers it only above
    /// [`MAX_LANE_PRIME`], so a field has at most one lane.
    pub fn new_31(
        modulus: u32,
        raw: fn(&F) -> u32,
        element: fn(u32) -> F,
        canonical: fn(&F) -> u32,
    ) -> Option<Self> {
        if !(2..=MAX_LANE31_PRIME).contains(&modulus) {
            return None;
        }
        let p = u64::from(modulus);
        let square = (p - 1) * (p - 1);
        let bound = (u64::MAX - square) / p * p;
        debug_assert!(bound >= square);
        Some(Self {
            modulus,
            kind: Kind::ThirtyOne,
            bound,
            magic: u64::MAX / p,
            raw,
            element,
            canonical,
        })
    }

    /// The prime.
    pub fn modulus(&self) -> u32 {
        self.modulus
    }

    /// The canonical representative of `x`, in `[0, p)`.
    pub fn canonical(&self, x: &F) -> u32 {
        (self.canonical)(x)
    }

    /// Bytes one working-row cell takes: 4 in the small lane, 8 in the 31-bit lane.
    pub fn cell_bytes(&self) -> usize {
        match self.kind {
            Kind::Small => size_of::<u32>(),
            Kind::ThirtyOne => size_of::<u64>(),
        }
    }

    /// `x mod p` by Lemire's multiply-high, exact for every `u32`. Small lane only.
    #[inline(always)]
    fn reduce(&self, x: u32) -> u32 {
        let low = self.magic.wrapping_mul(u64::from(x));
        ((u128::from(low) * u128::from(self.modulus)) >> 64) as u32
    }

    /// `x mod p` by Barrett reduction, exact for every `u64`. 31-bit lane only.
    ///
    /// With `m = floor((2^64 - 1) / p) >= 2^64 / p - 1`, the quotient estimate
    /// `q = floor(x m / 2^64)` is at most `floor(x / p)` and above `x / p - 2`, so `x - q p` is
    /// below `2p` and one subtract finishes.
    #[inline(always)]
    fn reduce_wide(&self, x: u64) -> u32 {
        let p = u64::from(self.modulus);
        let q = ((u128::from(x) * u128::from(self.magic)) >> 64) as u64;
        let r = x - q * p;
        (if r >= p { r - p } else { r }) as u32
    }

    /// Whether `columns` row operations on one cell could leave the cell's width.
    fn needs_correction(&self, columns: usize) -> bool {
        let ceiling = match self.kind {
            Kind::Small => u128::from(u32::MAX),
            Kind::ThirtyOne => u128::from(u64::MAX),
        };
        let square = u128::from(self.modulus - 1).pow(2);
        (columns as u128)
            .checked_mul(square)
            .and_then(|total| total.checked_add(u128::from(self.modulus)))
            .is_none_or(|total| total > ceiling)
    }
}

/// One pivot row, its unit lead omitted, with values of width `V`.
#[derive(Clone, Debug)]
enum Pivot<V> {
    Sparse { columns: Vec<u32>, values: Vec<V> },
    Dense { start: u32, values: Vec<V> },
}

impl<V: Copy + Default + Eq + Into<u32>> Pivot<V> {
    fn empty() -> Self {
        Pivot::Sparse {
            columns: Vec::new(),
            values: Vec::new(),
        }
    }

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
                    .map(|(&c, &v)| (c as usize, v.into())),
            ),
            Pivot::Dense { start, values } => Box::new(
                values
                    .iter()
                    .enumerate()
                    .filter(|(_, &v)| v != V::default())
                    .map(move |(k, &v)| (*start as usize + k, v.into())),
            ),
        }
    }

    /// Bytes the pivot holds on the heap.
    fn bytes(&self) -> usize {
        match self {
            Pivot::Sparse { columns, values } => {
                columns.len() * size_of::<u32>() + values.len() * size_of::<V>()
            }
            Pivot::Dense { values, .. } => values.len() * size_of::<V>(),
        }
    }
}

/// A [`LaneRow`]'s body in its lane's width.
#[derive(Clone, Debug)]
enum Body {
    Small(Pivot<u16>),
    ThirtyOne(Pivot<u32>),
}

/// A lane's widths and the arithmetic between them; the kernels are generic over it.
trait Word {
    /// A pivot value, below `p`.
    type Value: Copy + Default + Eq + Into<u32> + std::fmt::Debug;
    /// A working-row cell, below the lane's bound.
    type Cell: Copy + Default + Eq;

    fn value(raw: u32) -> Self::Value;
    fn cell(raw: u32) -> Self::Cell;
    fn bound<F>(lane: &Lane<F>) -> Self::Cell;
    /// `x mod p`.
    fn reduce<F>(lane: &Lane<F>, x: Self::Cell) -> u32;
    /// `a b mod p` for `a, b < p`.
    fn product<F>(lane: &Lane<F>, a: u32, b: u32) -> u32;
    /// `cell += value * negated`, then below `bound` again when `CORRECT`.
    fn step<const CORRECT: bool>(
        cell: &mut Self::Cell,
        value: Self::Value,
        negated: u32,
        bound: Self::Cell,
    );
    fn wrap(pivot: Pivot<Self::Value>) -> Body;
    fn unwrap(body: &Body) -> &Pivot<Self::Value>;
}

/// The small lane: `u16` values, `u32` cells.
struct Small;

/// The 31-bit lane: `u32` values, `u64` cells.
struct Wide;

impl Word for Small {
    type Value = u16;
    type Cell = u32;

    #[inline(always)]
    fn value(raw: u32) -> u16 {
        raw as u16
    }

    #[inline(always)]
    fn cell(raw: u32) -> u32 {
        raw
    }

    #[inline(always)]
    fn bound<F>(lane: &Lane<F>) -> u32 {
        lane.bound as u32
    }

    #[inline(always)]
    fn reduce<F>(lane: &Lane<F>, x: u32) -> u32 {
        lane.reduce(x)
    }

    #[inline(always)]
    fn product<F>(lane: &Lane<F>, a: u32, b: u32) -> u32 {
        lane.reduce(a * b)
    }

    #[inline(always)]
    fn step<const CORRECT: bool>(cell: &mut u32, value: u16, negated: u32, bound: u32) {
        let sum = *cell + u32::from(value) * negated;
        *cell = if CORRECT {
            sum.min(sum.wrapping_sub(bound))
        } else {
            sum
        };
    }

    fn wrap(pivot: Pivot<u16>) -> Body {
        Body::Small(pivot)
    }

    #[inline(always)]
    fn unwrap(body: &Body) -> &Pivot<u16> {
        match body {
            Body::Small(pivot) => pivot,
            Body::ThirtyOne(_) => unreachable!("a 31-bit pivot in a small lane"),
        }
    }
}

impl Word for Wide {
    type Value = u32;
    type Cell = u64;

    #[inline(always)]
    fn value(raw: u32) -> u32 {
        raw
    }

    #[inline(always)]
    fn cell(raw: u32) -> u64 {
        u64::from(raw)
    }

    #[inline(always)]
    fn bound<F>(lane: &Lane<F>) -> u64 {
        lane.bound
    }

    #[inline(always)]
    fn reduce<F>(lane: &Lane<F>, x: u64) -> u32 {
        lane.reduce_wide(x)
    }

    #[inline(always)]
    fn product<F>(lane: &Lane<F>, a: u32, b: u32) -> u32 {
        lane.reduce_wide(u64::from(a) * u64::from(b))
    }

    #[inline(always)]
    fn step<const CORRECT: bool>(cell: &mut u64, value: u32, negated: u32, bound: u64) {
        let sum = *cell + u64::from(value) * u64::from(negated);
        *cell = if CORRECT {
            sum.min(sum.wrapping_sub(bound))
        } else {
            sum
        };
    }

    fn wrap(pivot: Pivot<u32>) -> Body {
        Body::ThirtyOne(pivot)
    }

    #[inline(always)]
    fn unwrap(body: &Body) -> &Pivot<u32> {
        match body {
            Body::ThirtyOne(pivot) => pivot,
            Body::Small(_) => unreachable!("a small pivot in a 31-bit lane"),
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
        match lane.kind {
            Kind::Small => self.reduce_rows::<Small, F>(lane, matrix, split, max_nonzeros),
            Kind::ThirtyOne => self.reduce_rows::<Wide, F>(lane, matrix, split, max_nonzeros),
        }
    }

    fn reduce_rows<W: Word, F: FiniteField>(
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
        let mut pivots: Vec<Pivot<W::Value>> = Vec::new();
        let mut scratch: Vec<(u32, W::Value)> = Vec::new();
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
                    .map(|(c, v)| (*c as u32, W::value((lane.raw)(v)))),
            );
            pivot_at[lead] = pivots.len() as u32;
            pivot_row.push(index);
            pivots.push(self.pivot(lead, &scratch));
            statistics.rank += 1;
        }

        let correct = lane.needs_correction(columns);
        let bound = W::bound(lane);
        let zero = W::Cell::default();
        let one = (lane.raw)(&F::ONE);
        let mut cells = vec![zero; columns];
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
                cells[*c] = W::cell((lane.raw)(v));
            }
            drop(row);

            let mut lead = None;
            while column < tail {
                let x = cells[column];
                if x != zero {
                    let r = W::reduce(lane, x);
                    if r != 0 {
                        let slot = pivot_at[column];
                        if slot == NONE {
                            lead = Some((column, r));
                            break;
                        }
                        let pivot = &pivots[slot as usize];
                        let negated = lane.modulus - (lane.canonical)(&(lane.element)(r));
                        if correct {
                            apply::<W, true>(&mut cells, pivot, negated, bound);
                        } else {
                            apply::<W, false>(&mut cells, pivot, negated, bound);
                        }
                        statistics.row_operations += 1;
                        tail = tail.max(pivot.tail());
                    }
                    cells[column] = zero;
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
            cells[lead] = zero;
            scratch.clear();
            for (c, cell) in cells.iter_mut().enumerate().take(tail).skip(lead + 1) {
                let x = std::mem::take(cell);
                if x != zero {
                    let v = W::reduce(lane, x);
                    if v != 0 {
                        scratch.push((c as u32, W::value(W::product(lane, v, inverse))));
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
            let pivot = std::mem::replace(&mut pivots[slot], Pivot::empty());
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
    fn pivot<V: Copy + Default + Eq + Into<u32>>(
        &self,
        lead: usize,
        entries: &[(u32, V)],
    ) -> Pivot<V> {
        let Some(&(last, _)) = entries.last() else {
            return Pivot::empty();
        };
        let start = lead + 1;
        let span = last as usize + 1 - start;
        if entries.len() as u64 * 100 >= u64::from(self.dense_percent) * span as u64 {
            let mut values = vec![V::default(); span];
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
    body: Body,
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
        match lane.kind {
            Kind::Small => Self::build::<Small, F>(lane, kernel, row),
            Kind::ThirtyOne => Self::build::<Wide, F>(lane, kernel, row),
        }
    }

    fn build<W: Word, F: FiniteField>(
        lane: &Lane<F>,
        kernel: LaneKernel,
        row: &[(u32, F)],
    ) -> Self {
        let entries: Vec<(u32, W::Value)> = row
            .iter()
            .skip(1)
            .map(|(c, v)| (*c, W::value((lane.raw)(v))))
            .collect();
        let lead = row.first().map_or(0, |e| e.0 as usize);
        Self {
            lead: lead as u32,
            nonzeros: entries.len() as u64,
            body: W::wrap(kernel.pivot(lead, &entries)),
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
        let entries = match &self.body {
            Body::Small(pivot) => pivot.entries(),
            Body::ThirtyOne(pivot) => pivot.entries(),
        };
        row.extend(entries.map(|(c, v)| (c as u32, (lane.element)(v))));
        row
    }

    /// Nonzeros right of the lead: the products one application costs.
    pub fn nonzeros(&self) -> u64 {
        self.nonzeros
    }

    /// Bytes the row holds on the heap.
    pub fn bytes(&self) -> usize {
        match &self.body {
            Body::Small(pivot) => pivot.bytes(),
            Body::ThirtyOne(pivot) => pivot.bytes(),
        }
    }
}

/// A working row in its lane's cell width.
#[derive(Clone, Debug)]
enum Cells {
    Small(Vec<u32>),
    ThirtyOne(Vec<u64>),
}

/// A `u32`-lane working row that fully reduces, the shape of the signature engine's workspace.
#[derive(Clone, Debug)]
pub struct LaneWorkspace<F> {
    lane: Lane<F>,
    cells: Cells,
    correct: bool,
}

impl<F: FiniteField> LaneWorkspace<F> {
    /// A zero workspace over `columns` columns.
    pub fn new(lane: Lane<F>, columns: usize) -> Self {
        Self {
            correct: lane.needs_correction(columns),
            cells: match lane.kind {
                Kind::Small => Cells::Small(vec![0; columns]),
                Kind::ThirtyOne => Cells::ThirtyOne(vec![0; columns]),
            },
            lane,
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
        match &mut self.cells {
            Cells::Small(cells) => {
                reduce_in::<Small, F>(&self.lane, cells, self.correct, entries, pivot)
            }
            Cells::ThirtyOne(cells) => {
                reduce_in::<Wide, F>(&self.lane, cells, self.correct, entries, pivot)
            }
        }
    }
}

/// [`LaneWorkspace::reduce`] in one width.
#[inline(always)]
fn reduce_in<'p, W: Word, F: FiniteField>(
    lane: &Lane<F>,
    cells: &mut [W::Cell],
    correct: bool,
    entries: &[(u32, F)],
    mut pivot: impl FnMut(usize) -> Option<&'p LaneRow>,
) -> (Vec<(u32, F)>, u64) {
    let (Some(&(first, _)), Some(&(last, _))) = (entries.first(), entries.last()) else {
        return (Vec::new(), 0);
    };
    let (zero, bound) = (W::Cell::default(), W::bound(lane));
    for (c, v) in entries {
        cells[*c as usize] = W::cell((lane.raw)(v));
    }
    let (mut column, mut tail) = (first as usize, last as usize + 1);
    let (mut out, mut products) = (Vec::new(), 0);
    while column < tail {
        let x = std::mem::take(&mut cells[column]);
        if x != zero {
            let r = W::reduce(lane, x);
            if r != 0 {
                match pivot(column) {
                    Some(row) => {
                        let body = W::unwrap(&row.body);
                        let negated = lane.modulus - (lane.canonical)(&(lane.element)(r));
                        if correct {
                            apply::<W, true>(cells, body, negated, bound);
                        } else {
                            apply::<W, false>(cells, body, negated, bound);
                        }
                        products += row.nonzeros;
                        tail = tail.max(body.tail());
                    }
                    None => out.push((column as u32, (lane.element)(r))),
                }
            }
        }
        column += 1;
    }
    (out, products)
}

/// `cells += negated * pivot`, keeping every cell below `bound` when `CORRECT`.
#[inline(always)]
fn apply<W: Word, const CORRECT: bool>(
    cells: &mut [W::Cell],
    pivot: &Pivot<W::Value>,
    negated: u32,
    bound: W::Cell,
) {
    match pivot {
        Pivot::Dense { start, values } => {
            let start = *start as usize;
            let target = &mut cells[start..start + values.len()];
            for (cell, &value) in target.iter_mut().zip(values) {
                W::step::<CORRECT>(cell, value, negated, bound);
            }
        }
        Pivot::Sparse { columns, values } => {
            for (&c, &value) in columns.iter().zip(values) {
                W::step::<CORRECT>(&mut cells[c as usize], value, negated, bound);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        Lane, LaneKernel, LaneRow, LaneWorkspace, Wide, Word, MAX_LANE31_PRIME, MAX_LANE_PRIME,
    };
    use crate::{
        fields::{
            BabyBear, KoalaBear, Mersenne31, PrimeFieldElement32, PrimeFieldElement64, Zp13,
            Zp2147483647, Zp31, Zp32003,
        },
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

    /// Whichever lane the field has.
    fn any_lane<F: FiniteField>() -> Lane<F> {
        F::small_prime_lane()
            .or_else(F::prime31_lane)
            .expect("a lane prime")
    }

    fn agrees_with_accumulator<F: FiniteField>(seed: u64, kernel: LaneKernel, density: f64) {
        agrees_on_lane(seed, kernel, density, &any_lane::<F>());
    }

    fn agrees_on_lane<F: FiniteField>(seed: u64, kernel: LaneKernel, density: f64, lane: &Lane<F>) {
        let mut rng = StdRng::seed_from_u64(seed);
        let (matrix, split) = block_matrix::<F>(&mut rng, 90, 40, 45, density);
        let mut expected = matrix.clone();
        let reference =
            reduce_rows_against_pivots_with(Backend::Adaptive, &mut expected, split, usize::MAX)
                .unwrap();
        let mut actual = matrix;
        let statistics = kernel
            .reduce_rows_against_pivots(lane, &mut actual, split, usize::MAX)
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
        maximal_products_on_one_cell::<Zp32003>();
    }

    /// The largest supported prime: one cell takes maximal products with one product of headroom.
    #[test]
    fn test_the_largest_lane_prime_is_exact() {
        type F = PrimeFieldElement32<MAX_LANE_PRIME>;
        assert_eq!(F::small_prime_lane().unwrap().modulus(), MAX_LANE_PRIME);
        maximal_products_on_one_cell::<F>();
        for seed in 0..6 {
            for dense_percent in [0, 25, 101] {
                agrees_with_accumulator::<F>(seed, LaneKernel { dense_percent }, 0.3);
                agrees_with_reference::<F>(seed, dense_percent);
            }
        }
    }

    /// The first prime above the bound keeps the field route.
    #[test]
    fn test_the_first_prime_above_the_bound_gets_no_lane() {
        assert!(PrimeFieldElement32::<46_349>::small_prime_lane().is_none());
    }

    fn maximal_products_on_one_cell<F: FiniteField>() {
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
            .reduce_rows_against_pivots(&any_lane::<F>(), &mut actual, columns - 1, usize::MAX)
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
                lane.bound as u32,
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
        let lane = any_lane::<F>();
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

    // #1183: the 31-bit lane.

    const BABY_BEAR: u32 = 2_013_265_921;
    const KOALA_BEAR: u32 = 2_130_706_433;
    /// The named primes and the edges of the admitted range.
    const THIRTY_ONE_BIT_PRIMES: [u32; 5] = [
        46_349,
        BABY_BEAR,
        KOALA_BEAR,
        2_147_483_629,
        MAX_LANE31_PRIME,
    ];

    /// A 31-bit lane on `p` for its arithmetic alone; its conversions are never called.
    fn arithmetic_31(p: u32) -> Lane<Zp31> {
        Lane::new_31(p, |_| 0, |_| Zp31::one(), |_| 0).unwrap()
    }

    /// A 31-bit lane over `GF(P)` on canonical residues, so the wide kernel can be run at small
    /// primes, where rows cancel to zero often.
    fn canonical_31<const P: u32>() -> Lane<PrimeFieldElement32<P>> {
        Lane::new_31(
            P,
            PrimeFieldElement32::<P>::value,
            |r| PrimeFieldElement32::<P>::new(u64::from(r)),
            PrimeFieldElement32::<P>::value,
        )
        .unwrap()
    }

    /// Fields at 46,337 < p < 2^31 get a 31-bit lane and no small one; every other field none.
    #[test]
    fn test_31_bit_lane_admits_exactly_its_range() {
        assert_eq!(
            Mersenne31::prime31_lane().unwrap().modulus(),
            MAX_LANE31_PRIME
        );
        assert_eq!(BabyBear::prime31_lane().unwrap().modulus(), BABY_BEAR);
        assert_eq!(KoalaBear::prime31_lane().unwrap().modulus(), KOALA_BEAR);
        assert_eq!(
            Zp2147483647::prime31_lane().unwrap().modulus(),
            MAX_LANE31_PRIME
        );
        assert_eq!(
            PrimeFieldElement32::<46_349>::prime31_lane()
                .unwrap()
                .modulus(),
            46_349
        );
        assert!(PrimeFieldElement32::<46_349>::small_prime_lane().is_none());
        assert!(BabyBear::small_prime_lane().is_none());
        // The small lane's primes keep it and get no second one.
        assert!(PrimeFieldElement32::<MAX_LANE_PRIME>::prime31_lane().is_none());
        assert!(Zp32003::prime31_lane().is_none());
        assert!(Zp31::prime31_lane().is_none());
        // Primes above 2^31 get neither.
        assert!(PrimeFieldElement32::<2_147_483_659>::prime31_lane().is_none());
        assert!(PrimeFieldElement32::<4_294_967_291>::prime31_lane().is_none());
        assert!(PrimeFieldElement64::<2_147_483_659>::prime31_lane().is_none());
        assert!(PrimeFieldElement64::<18446744069414584321>::prime31_lane().is_none());
        assert!(Zp13::prime31_lane().is_none());
        assert!(
            Lane::<Zp31>::new_31(MAX_LANE31_PRIME + 1, |_| 0, |_| Zp31::one(), |_| 0).is_none()
        );
        assert!(Lane::<Zp31>::new_31(1, |_| 0, |_| Zp31::one(), |_| 0).is_none());
    }

    /// The overflow proof's arithmetic, exactly: `bound` is a multiple of `p` that holds one more
    /// product inside a `u64`, and is at least a product, so one subtract restores it. Every term
    /// is monotone in `p`, so the largest admitted prime covers the range.
    #[test]
    fn test_31_bit_bound_holds_for_every_admitted_prime() {
        for p in THIRTY_ONE_BIT_PRIMES {
            let bound = u128::from(arithmetic_31(p).bound);
            let p = u128::from(p);
            let square = (p - 1) * (p - 1);
            assert_eq!(bound % p, 0, "{p}");
            assert!(bound >= square, "{p}");
            assert!(bound + square <= u128::from(u64::MAX), "{p}");
            assert!(
                bound >= 1 << 63,
                "{p}: the headroom is about 2^63 even at 2^31 - 1"
            );
        }
    }

    /// A cell at `bound - 1` takes the largest product, `(p - 1)^2`, ten thousand times: no
    /// overflow (a debug build panics on one), the invariant holds and the residue is exact. Then
    /// random cells and products against `u128` arithmetic.
    #[test]
    fn test_31_bit_step_survives_worst_case_products() {
        for p in THIRTY_ONE_BIT_PRIMES {
            let bound = arithmetic_31(p).bound;
            let modulus = u128::from(p);
            let mut cell = bound - 1;
            let mut exact = u128::from(cell) % modulus;
            for _ in 0..10_000 {
                Wide::step::<true>(&mut cell, p - 1, p - 1, bound);
                exact = (exact + u128::from(p - 1) * u128::from(p - 1)) % modulus;
                assert!(cell < bound, "{p}");
                assert_eq!(u128::from(cell) % modulus, exact, "{p}");
            }
            let mut rng = StdRng::seed_from_u64(u64::from(p));
            for _ in 0..10_000 {
                let mut cell = rng.gen_range(0..bound);
                let (value, negated) = (rng.gen_range(0..p), rng.gen_range(0..p));
                let expected =
                    (u128::from(cell) + u128::from(value) * u128::from(negated)) % modulus;
                Wide::step::<true>(&mut cell, value, negated, bound);
                assert!(cell < bound, "{p}");
                assert_eq!(u128::from(cell) % modulus, expected, "{p}");
            }
        }
    }

    /// The 31-bit remainder is exact across the whole `u64` range.
    #[test]
    fn test_31_bit_reduce_is_exact() {
        for p in THIRTY_ONE_BIT_PRIMES.into_iter().chain([2, 3, 31, 32003]) {
            let lane = arithmetic_31(p);
            let q = u64::from(p);
            let mut inputs = vec![
                0,
                1,
                q - 1,
                q,
                q + 1,
                (q - 1) * (q - 1),
                lane.bound - 1,
                lane.bound,
                1 << 63,
                u64::MAX - 1,
                u64::MAX,
            ];
            let mut rng = StdRng::seed_from_u64(q);
            inputs.extend((0..10_000).map(|_| rng.gen::<u64>()));
            for x in inputs {
                assert_eq!(u64::from(lane.reduce_wide(x)), x % q, "{x} mod {p}");
            }
        }
    }

    /// The 31-bit lane's echelon form and work counters equal the accumulator kernel's, under
    /// every storage policy, over 32- and 64-bit field types.
    #[test]
    fn test_31_bit_lane_matches_the_accumulator_kernel() {
        for seed in 0..6 {
            for dense_percent in [0, 25, 101] {
                let kernel = LaneKernel { dense_percent };
                agrees_with_accumulator::<Mersenne31>(seed, kernel, 0.3);
                agrees_with_accumulator::<BabyBear>(seed, kernel, 0.3);
                agrees_with_accumulator::<KoalaBear>(seed, kernel, 0.3);
                agrees_with_accumulator::<Zp2147483647>(seed, kernel, 0.3);
                agrees_with_accumulator::<PrimeFieldElement32<46_349>>(seed, kernel, 0.3);
            }
        }
    }

    /// The wide kernel at small primes, where rows cancel often. At GF(31) the correction is
    /// compiled out; at 2^31 - 1 it runs from five columns on.
    #[test]
    fn test_31_bit_kernel_is_exact_at_small_primes() {
        for seed in 0..8 {
            for dense_percent in [0, 25, 101] {
                let kernel = LaneKernel { dense_percent };
                agrees_on_lane(seed, kernel, 0.3, &canonical_31::<31>());
                agrees_on_lane(seed, kernel, 0.3, &canonical_31::<32003>());
            }
        }
        assert!(!arithmetic_31(31).needs_correction(1 << 20));
        // bounds.py's λ = 4 at 2^31 - 1: four products fit a u64 above a residue, five do not.
        assert!(!arithmetic_31(MAX_LANE31_PRIME).needs_correction(4));
        assert!(arithmetic_31(MAX_LANE31_PRIME).needs_correction(5));
    }

    /// Hundreds of maximal products on one cell at each named 31-bit prime.
    #[test]
    fn test_31_bit_lane_survives_many_maximal_products() {
        maximal_products_on_one_cell::<Mersenne31>();
        maximal_products_on_one_cell::<BabyBear>();
        maximal_products_on_one_cell::<KoalaBear>();
        maximal_products_on_one_cell::<Zp2147483647>();
    }

    /// The 31-bit workspace's full reduction equals plain field arithmetic.
    #[test]
    fn test_31_bit_workspace_matches_a_field_reference() {
        for seed in 0..10 {
            for dense_percent in [0, 25, 101] {
                agrees_with_reference::<Mersenne31>(seed, dense_percent);
                agrees_with_reference::<BabyBear>(seed, dense_percent);
                agrees_with_reference::<KoalaBear>(seed, dense_percent);
                agrees_with_reference::<Zp2147483647>(seed, dense_percent);
            }
        }
    }

    /// A 31-bit lane row stores `u32` values, half a `u64` field's coefficient bytes, and its
    /// working cells are `u64`.
    #[test]
    fn test_31_bit_lane_row_stores_u32_values() {
        let lane = Zp2147483647::prime31_lane().unwrap();
        let row: Vec<(u32, Zp2147483647)> = (0..101)
            .map(|c| (c, Zp2147483647::new(if c == 0 { 1 } else { 2_147_483_646 })))
            .collect();
        let dense = LaneRow::from_monic(&lane, LaneKernel { dense_percent: 0 }, &row);
        let sparse = LaneRow::from_monic(&lane, LaneKernel { dense_percent: 101 }, &row);
        assert_eq!(dense.bytes(), 100 * 4);
        assert_eq!(sparse.bytes(), 100 * 8);
        assert_eq!(dense.to_field(&lane), row);
        assert_eq!(sparse.to_field(&lane), row);
        assert_eq!(lane.cell_bytes(), 8);
        assert_eq!(Zp31::small_prime_lane().unwrap().cell_bytes(), 4);
    }
}
