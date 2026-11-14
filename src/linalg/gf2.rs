//! Research prototype for #272; `docs/research/characteristic-two-linear-algebra.md` has the
//! measurements and the decision. Not wired into F4.

use crate::{
    fields::Zp2,
    linalg::sparse::{SparseMatrix, SparseRow},
    One,
};

/// A dense matrix over `GF(2)`, one bit per coefficient, rows packed into `u64` words.
///
/// Bits past `num_columns` in a row's last word are always zero; every operation preserves that.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BitMatrix {
    num_rows: usize,
    num_columns: usize,
    stride: usize,
    words: Vec<u64>,
}

/// Work counters for a packed elimination.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct PackedStatistics {
    /// The number of pivots found.
    pub rank: usize,
    /// Whole-row `xor`s performed, including those that build Four Russians tables.
    pub row_xors: usize,
    /// Four Russians tables built; zero for plain Gauss-Jordan.
    pub tables: usize,
}

impl BitMatrix {
    pub fn zero(num_rows: usize, num_columns: usize) -> Self {
        let stride = num_columns.div_ceil(64);
        Self {
            num_rows,
            num_columns,
            stride,
            words: vec![0; num_rows * stride],
        }
    }

    pub fn num_rows(&self) -> usize {
        self.num_rows
    }

    pub fn num_columns(&self) -> usize {
        self.num_columns
    }

    /// Bytes of coefficient storage.
    pub fn bytes(&self) -> usize {
        self.words.len() * size_of::<u64>()
    }

    pub fn get(&self, row: usize, column: usize) -> bool {
        assert!(row < self.num_rows && column < self.num_columns);
        (self.words[row * self.stride + column / 64] >> (column % 64)) & 1 == 1
    }

    pub fn set(&mut self, row: usize, column: usize, value: bool) {
        assert!(row < self.num_rows && column < self.num_columns);
        let word = &mut self.words[row * self.stride + column / 64];
        let mask = 1u64 << (column % 64);
        if value {
            *word |= mask;
        } else {
            *word &= !mask;
        }
    }

    pub fn from_sparse(matrix: &SparseMatrix<Zp2>) -> Self {
        let mut packed = Self::zero(matrix.num_rows(), matrix.num_columns());
        for (index, row) in matrix.rows().iter().enumerate() {
            let words = packed.row_mut(index);
            // A canonical sparse row holds only nonzero coefficients, and over GF(2) those are one.
            for (column, _) in row.entries() {
                words[column / 64] |= 1 << (column % 64);
            }
        }
        packed
    }

    pub fn to_sparse(&self) -> SparseMatrix<Zp2> {
        let rows = (0..self.num_rows)
            .map(|index| {
                let mut entries = Vec::new();
                for (w, &word) in self.row(index).iter().enumerate() {
                    let mut bits = word;
                    while bits != 0 {
                        entries.push((w * 64 + bits.trailing_zeros() as usize, Zp2::one()));
                        bits &= bits - 1;
                    }
                }
                SparseRow::from_sorted(entries).expect("columns ascend and coefficients are one")
            })
            .collect();
        SparseMatrix::new(self.num_columns, rows)
    }

    fn row(&self, index: usize) -> &[u64] {
        &self.words[index * self.stride..(index + 1) * self.stride]
    }

    fn row_mut(&mut self, index: usize) -> &mut [u64] {
        &mut self.words[index * self.stride..(index + 1) * self.stride]
    }

    fn word(&self, row: usize, word: usize) -> u64 {
        self.words[row * self.stride + word]
    }

    fn swap_rows(&mut self, a: usize, b: usize) {
        if a != b {
            let (low, high) = (a.min(b), a.max(b));
            let (head, tail) = self.words.split_at_mut(high * self.stride);
            head[low * self.stride..(low + 1) * self.stride]
                .swap_with_slice(&mut tail[..self.stride]);
        }
    }

    /// `row[target] ^= row[source]` over words `from..`.
    fn xor_rows(&mut self, target: usize, source: usize, from: usize) {
        debug_assert_ne!(target, source);
        let stride = self.stride;
        let (destination, origin) = if target < source {
            let (head, tail) = self.words.split_at_mut(source * stride);
            (
                &mut head[target * stride..(target + 1) * stride],
                &tail[..stride],
            )
        } else {
            let (head, tail) = self.words.split_at_mut(target * stride);
            (
                &mut tail[..stride],
                &head[source * stride..(source + 1) * stride],
            )
        };
        xor_into(&mut destination[from..], &origin[from..]);
    }
}

#[inline]
fn xor_into(destination: &mut [u64], source: &[u64]) {
    for (d, s) in destination.iter_mut().zip(source) {
        *d ^= *s;
    }
}

/// Reduced row echelon form by plain Gauss-Jordan: one row `xor` per (pivot, row) incidence.
///
/// The nonzero rows of the result come first, in increasing pivot column; zero rows follow.
pub fn reduced_row_echelon_packed(matrix: &mut BitMatrix) -> PackedStatistics {
    let mut statistics = PackedStatistics::default();
    let mut rank = 0;
    for column in 0..matrix.num_columns {
        if rank == matrix.num_rows {
            break;
        }
        let (word, mask) = (column / 64, 1u64 << (column % 64));
        let Some(pivot) = (rank..matrix.num_rows).find(|&row| matrix.word(row, word) & mask != 0)
        else {
            continue;
        };
        matrix.swap_rows(rank, pivot);
        for row in 0..matrix.num_rows {
            if row != rank && matrix.word(row, word) & mask != 0 {
                matrix.xor_rows(row, rank, word);
                statistics.row_xors += 1;
            }
        }
        rank += 1;
    }
    statistics.rank = rank;
    statistics
}

/// Reduced row echelon form by the Method of Four Russians, `k` pivots per lookup table.
///
/// Same output as [`reduced_row_echelon_packed`]. Pivots are found a 64-column word at a time by
/// Gauss-Jordan on that word alone; the word's pivot rows are then reduced against each other, and
/// every other row is cleared at `k` pivots per `xor` from a table of all `2^k` combinations.
///
/// The table index is read from a row's *unreduced* bits at the pivot columns, which is sound
/// because the pivot rows are mutually reduced: the one combination of them that clears every
/// pivot column of a row is the one selected by that row's own bits there.
///
/// # Panics
/// If `k` is not in `1..=MAX_TABLE_BITS`.
pub fn reduced_row_echelon_four_russians(matrix: &mut BitMatrix, k: usize) -> PackedStatistics {
    assert!(
        (1..=MAX_TABLE_BITS).contains(&k),
        "table width {k} is outside 1..={MAX_TABLE_BITS}"
    );
    let mut statistics = PackedStatistics::default();
    let stride = matrix.stride;
    let mut table: Vec<u64> = Vec::new();
    let mut window: Vec<u64> = Vec::new();
    let mut pivot_bits: Vec<u32> = Vec::with_capacity(64);
    let mut rank = 0;

    for word in 0..stride {
        if rank == matrix.num_rows {
            break;
        }
        // Rows from `rank` on are zero left of this word, so the word is their whole leading part.
        window.clear();
        window.extend((rank..matrix.num_rows).map(|row| matrix.word(row, word)));
        pivot_bits.clear();
        for bit in 0..64u32 {
            let found = pivot_bits.len();
            if found == window.len() {
                break;
            }
            let mask = 1u64 << bit;
            let Some(local) = (found..window.len()).find(|&i| window[i] & mask != 0) else {
                continue;
            };
            window.swap(found, local);
            matrix.swap_rows(rank + found, rank + local);
            let pivot = window[found];
            for (i, entry) in window.iter_mut().enumerate() {
                if i != found && *entry & mask != 0 {
                    *entry ^= pivot;
                }
            }
            pivot_bits.push(bit);
        }
        let found = pivot_bits.len();
        if found == 0 {
            continue;
        }

        // Reduce the pivot rows against each other: forward, then back.
        for j in 0..found {
            for l in 0..j {
                if (matrix.word(rank + j, word) >> pivot_bits[l]) & 1 == 1 {
                    matrix.xor_rows(rank + j, rank + l, word);
                    statistics.row_xors += 1;
                }
            }
        }
        for j in (0..found).rev() {
            for l in j + 1..found {
                if (matrix.word(rank + j, word) >> pivot_bits[l]) & 1 == 1 {
                    matrix.xor_rows(rank + j, rank + l, word);
                    statistics.row_xors += 1;
                }
            }
        }

        let width = stride - word;
        for group in (0..found).step_by(k) {
            let bits = &pivot_bits[group..found.min(group + k)];
            let entries = 1usize << bits.len();
            table.clear();
            table.resize(entries * width, 0);
            for index in 1..entries {
                let (previous, pivot) = (index & (index - 1), index.trailing_zeros() as usize);
                let source = matrix.row(rank + group + pivot);
                let (before, current) = table.split_at_mut(index * width);
                let current = &mut current[..width];
                current.copy_from_slice(&before[previous * width..(previous + 1) * width]);
                xor_into(current, &source[word..]);
                statistics.row_xors += 1;
            }
            statistics.tables += 1;

            let contiguous = bits.windows(2).all(|pair| pair[1] == pair[0] + 1);
            let (shift, mask) = (bits[0], (entries - 1) as u64);
            let pivots = rank + group..rank + group + bits.len();
            for row in 0..matrix.num_rows {
                if pivots.contains(&row) {
                    continue;
                }
                let leading = matrix.word(row, word);
                let index = if contiguous {
                    ((leading >> shift) & mask) as usize
                } else {
                    bits.iter().enumerate().fold(0, |index, (b, &bit)| {
                        index | (((leading >> bit) & 1) as usize) << b
                    })
                };
                if index != 0 {
                    let start = row * stride + word;
                    xor_into(
                        &mut matrix.words[start..start + width],
                        &table[index * width..(index + 1) * width],
                    );
                    statistics.row_xors += 1;
                }
            }
        }
        rank += found;
    }
    statistics.rank = rank;
    statistics
}

/// The largest supported table width: a table holds `2^k` rows.
pub const MAX_TABLE_BITS: usize = 10;

#[cfg(test)]
mod tests {
    use super::{
        reduced_row_echelon_four_russians, reduced_row_echelon_packed, BitMatrix, MAX_TABLE_BITS,
    };
    use crate::{
        fields::Zp2,
        linalg::sparse::{reduced_row_echelon, SparseMatrix, SparseRow},
        One,
    };
    use rand::{prelude::StdRng, Rng, SeedableRng};

    fn random_sparse(
        rng: &mut StdRng,
        rows: usize,
        columns: usize,
        density: f64,
    ) -> SparseMatrix<Zp2> {
        let rows = (0..rows)
            .map(|_| {
                let entries: Vec<(usize, Zp2)> = (0..columns)
                    .filter(|_| rng.gen_bool(density))
                    .map(|column| (column, Zp2::one()))
                    .collect();
                SparseRow::new(&entries)
            })
            .collect();
        SparseMatrix::new(columns, rows)
    }

    /// Rows that are random sums of `rank` base rows, so the matrix has rank at most `rank`.
    fn rank_deficient(
        rng: &mut StdRng,
        rows: usize,
        columns: usize,
        rank: usize,
    ) -> SparseMatrix<Zp2> {
        let base = BitMatrix::from_sparse(&random_sparse(rng, rank, columns, 0.3));
        let mut out = BitMatrix::zero(rows, columns);
        for row in 0..rows {
            for b in 0..rank {
                if rng.gen_bool(0.5) {
                    for column in 0..columns {
                        if base.get(b, column) {
                            let bit = out.get(row, column);
                            out.set(row, column, !bit);
                        }
                    }
                }
            }
        }
        out.to_sparse()
    }

    /// The generic kernel's RREF as its nonzero rows in pivot order.
    fn generic_rref(matrix: &SparseMatrix<Zp2>) -> (Vec<SparseRow<Zp2>>, usize) {
        let mut working = matrix.clone();
        let statistics = reduced_row_echelon(&mut working);
        working.sort_rows_by_leading_column();
        let rows = working
            .rows()
            .iter()
            .filter(|row| !row.is_zero())
            .cloned()
            .collect();
        (rows, statistics.rank)
    }

    fn packed_rref(matrix: &SparseMatrix<Zp2>, k: Option<usize>) -> (Vec<SparseRow<Zp2>>, usize) {
        let mut packed = BitMatrix::from_sparse(matrix);
        let statistics = match k {
            None => reduced_row_echelon_packed(&mut packed),
            Some(k) => reduced_row_echelon_four_russians(&mut packed, k),
        };
        let sparse = packed.to_sparse();
        let rows: Vec<_> = sparse.rows().to_vec();
        assert!(
            rows[statistics.rank.min(rows.len())..]
                .iter()
                .all(SparseRow::is_zero),
            "zero rows must follow the {} pivot rows",
            statistics.rank
        );
        (rows[..statistics.rank].to_vec(), statistics.rank)
    }

    fn assert_all_kernels_agree(matrix: &SparseMatrix<Zp2>) {
        let expected = generic_rref(matrix);
        assert_eq!(
            packed_rref(matrix, None),
            expected,
            "plain Gauss-Jordan disagreed"
        );
        for k in [1, 2, 3, 4, 6, 8, MAX_TABLE_BITS] {
            assert_eq!(
                packed_rref(matrix, Some(k)),
                expected,
                "Four Russians k={k} disagreed"
            );
        }
    }

    /// Packing and unpacking is the identity, including partial last words and empty shapes.
    #[test]
    fn test_sparse_round_trip_across_word_tails() {
        let mut rng = StdRng::seed_from_u64(1);
        for columns in [0, 1, 63, 64, 65, 127, 128, 130] {
            for rows in [0, 1, 5] {
                let matrix = random_sparse(&mut rng, rows, columns, 0.4);
                let packed = BitMatrix::from_sparse(&matrix);
                assert_eq!((packed.num_rows(), packed.num_columns()), (rows, columns));
                assert_eq!(packed.to_sparse(), matrix, "{rows}x{columns}");
            }
        }
    }

    /// `set` and `get` address the bit they name and no other.
    #[test]
    fn test_set_and_get_address_one_bit() {
        let mut matrix = BitMatrix::zero(3, 130);
        matrix.set(1, 64, true);
        matrix.set(2, 129, true);
        assert!(matrix.get(1, 64) && matrix.get(2, 129));
        assert_eq!(matrix.to_sparse().nonzeros(), 2);
        matrix.set(1, 64, false);
        assert!(!matrix.get(1, 64));
        assert_eq!(matrix.to_sparse().nonzeros(), 1);
    }

    /// Every packed kernel matches the generic kernel's RREF and rank on random full-rank-ish matrices.
    #[test]
    fn test_rref_agrees_with_generic_kernel_on_random_matrices() {
        let mut rng = StdRng::seed_from_u64(272);
        for &(rows, columns) in &[
            (1, 1),
            (3, 70),
            (20, 20),
            (40, 130),
            (130, 40),
            (100, 200),
            (64, 64),
            (65, 129),
        ] {
            for density in [0.02, 0.1, 0.5] {
                assert_all_kernels_agree(&random_sparse(&mut rng, rows, columns, density));
            }
        }
    }

    /// Every packed kernel matches the generic kernel on rank-deficient matrices with dependent rows.
    #[test]
    fn test_rref_agrees_with_generic_kernel_on_rank_deficient_matrices() {
        let mut rng = StdRng::seed_from_u64(2720);
        for &(rows, columns, rank) in &[
            (10, 10, 3),
            (50, 100, 7),
            (200, 150, 20),
            (90, 300, 65),
            (300, 70, 1),
        ] {
            let matrix = rank_deficient(&mut rng, rows, columns, rank);
            let (_, generic_rank) = generic_rref(&matrix);
            assert!(generic_rank <= rank);
            assert_all_kernels_agree(&matrix);
        }
    }

    /// Zero matrices, duplicated rows and empty shapes reduce to rank zero or the duplicate's rank.
    #[test]
    fn test_degenerate_matrices() {
        for (rows, columns) in [(0, 0), (0, 5), (5, 0), (4, 70)] {
            let zero = SparseMatrix::<Zp2>::zero(rows, columns);
            assert_all_kernels_agree(&zero);
            assert_eq!(packed_rref(&zero, Some(4)).1, 0);
        }
        let row = SparseRow::new(&[(3, Zp2::one()), (64, Zp2::one()), (99, Zp2::one())]);
        let duplicated = SparseMatrix::new(100, vec![row.clone(), row.clone(), row]);
        assert_all_kernels_agree(&duplicated);
        assert_eq!(packed_rref(&duplicated, None).1, 1);
    }

    /// Four Russians performs fewer row `xor`s than plain Gauss-Jordan on a dense 1024-square matrix, where the tables amortize.
    #[test]
    fn test_four_russians_saves_row_operations() {
        let mut rng = StdRng::seed_from_u64(7);
        let matrix = BitMatrix::from_sparse(&random_sparse(&mut rng, 1024, 1024, 0.5));
        let plain = reduced_row_echelon_packed(&mut matrix.clone());
        let four = reduced_row_echelon_four_russians(&mut matrix.clone(), 8);
        assert_eq!(plain.rank, four.rank);
        assert!(
            four.row_xors * 2 < plain.row_xors,
            "{four:?} against {plain:?}"
        );
        assert!(four.tables > 0 && plain.tables == 0);
    }

    /// A table width of zero is refused rather than looping forever.
    #[test]
    #[should_panic(expected = "table width")]
    fn test_zero_table_width_is_refused() {
        reduced_row_echelon_four_russians(&mut BitMatrix::zero(2, 2), 0);
    }

    /// The packed kernels agree with the generic kernel on the Macaulay matrices F4 builds for a
    /// Boolean system with its field equations.
    #[test]
    fn test_rref_agrees_on_characteristic_two_f4_matrices() {
        use crate::{
            grobner::{
                benchmark_systems::katsura,
                f4::{
                    f4_observed, options::F4Options, symbolic::MonicBasis, BatchObserver,
                    MacaulayMatrix,
                },
                field_equations::with_field_equations,
                pairs::CriticalPair,
            },
            MonomialOrder,
        };

        struct Collect(Vec<SparseMatrix<Zp2>>);
        impl BatchObserver<4, Zp2> for Collect {
            fn batch(&mut self, _: &MonicBasis<4, Zp2>, _: &[CriticalPair<4>]) {}
            fn matrix(&mut self, matrix: &MacaulayMatrix<4, Zp2>) {
                self.0.push(matrix.matrix().clone());
            }
        }

        let system = with_field_equations(&katsura::<4, Zp2>()).expect("GF(2) has an order");
        let mut collect = Collect(Vec::new());
        f4_observed(
            &system,
            MonomialOrder::GradedReverseLexicographic,
            &F4Options::default(),
            &mut collect,
        )
        .expect("katsura-4 over GF(2) solves");
        assert!(!collect.0.is_empty());
        for matrix in &collect.0 {
            assert_all_kernels_agree(matrix);
        }
    }
}
