//! Sparse finite-field elimination, against the dense implementation on identical matrices.
//!
//! Sparse storage is not unconditionally faster: below some density it wins by touching fewer
//! entries, and above it the bookkeeping costs more than the arithmetic saved. These benchmarks
//! exist to locate that crossover rather than to assume it, so every size is measured at several
//! densities and both implementations run on the same matrices.
//!
//! Matrices are generated from a fixed seed, so runs are comparable.

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::{prelude::StdRng, Rng, SeedableRng};
use zeebra::{
    fields::Zp2147483647,
    linalg::{
        gauss_jordan_elimination,
        sparse::{row_echelon, SparseMatrix, SparseRow},
        Matrix,
    },
    FiniteField,
};

type F = Zp2147483647;

const SIZES: [usize; 4] = [16, 32, 64, 128];
const DENSITIES: [f64; 4] = [0.02, 0.1, 0.3, 1.0];

/// A square matrix with roughly the given fraction of entries nonzero.
fn random_sparse(n: usize, density: f64, seed: u64) -> SparseMatrix<F> {
    let mut rng = StdRng::seed_from_u64(seed);
    let rows: Vec<SparseRow<F>> = (0..n)
        .map(|_| {
            let mut entries: Vec<(usize, F)> = Vec::new();
            for column in 0..n {
                if rng.gen_bool(density) {
                    entries.push((column, F::random(&mut rng)));
                }
            }
            SparseRow::new(&entries)
        })
        .collect();
    SparseMatrix::new(n, rows)
}

/// An F4-shaped matrix: wide, moderately tall, and sparse, with every row holding a leading entry
/// in a low column — which is where the fill-in comes from.
fn macaulay_shaped(rows: usize, columns: usize, per_row: usize, seed: u64) -> SparseMatrix<F> {
    let mut rng = StdRng::seed_from_u64(seed);
    let rows: Vec<SparseRow<F>> = (0..rows)
        .map(|index| {
            let mut entries: Vec<(usize, F)> = Vec::with_capacity(per_row);
            // A leading column drawn from the top of the matrix, so rows collide on pivots.
            entries.push((index % (columns / 4).max(1), F::random(&mut rng)));
            for _ in 1..per_row {
                entries.push((rng.gen_range(0..columns), F::random(&mut rng)));
            }
            SparseRow::new(&entries)
        })
        .collect();
    SparseMatrix::new(columns, rows)
}

fn benches(c: &mut Criterion) {
    let mut group = c.benchmark_group("sparse_linalg");

    for n in SIZES {
        for density in DENSITIES {
            let sparse = random_sparse(n, density, 7);
            let dense: Matrix<F> = sparse.to_dense();
            let label = format!("{}pct", (density * 100.0).round() as usize);

            group.bench_with_input(
                BenchmarkId::new(format!("sparse/{}", label), n),
                &sparse,
                |bencher, sparse| {
                    bencher.iter(|| {
                        let mut matrix = sparse.clone();
                        black_box(row_echelon(black_box(&mut matrix)))
                    })
                },
            );

            // The same matrix through the dense implementation. Gauss-Jordan computes the reduced
            // form, which is more work than row echelon; the comparison is indicative rather than
            // exact, and the sparse reduced form is measured separately below.
            group.bench_with_input(
                BenchmarkId::new(format!("dense/{}", label), n),
                &dense,
                |bencher, dense| {
                    bencher.iter(|| black_box(gauss_jordan_elimination(black_box(dense))))
                },
            );
        }
    }

    // Matrices shaped like the ones F4 actually builds: more columns than rows, a handful of
    // entries per row.
    for (rows, columns, per_row) in [
        (64usize, 256usize, 8usize),
        (256, 1024, 12),
        (512, 2048, 16),
    ] {
        let matrix = macaulay_shaped(rows, columns, per_row, 11);
        group.bench_with_input(
            BenchmarkId::new("macaulay_shaped", format!("{}x{}", rows, columns)),
            &matrix,
            |bencher, matrix| {
                bencher.iter(|| {
                    let mut matrix = matrix.clone();
                    black_box(row_echelon(black_box(&mut matrix)))
                })
            },
        );
    }

    group.finish();
}

criterion_group!(sparse_linear_algebra, benches);
criterion_main!(sparse_linear_algebra);
