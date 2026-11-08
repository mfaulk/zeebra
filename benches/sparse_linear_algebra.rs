//! Sparse finite-field elimination, against the dense implementation on identical matrices.
//!
//! Sparse storage is not unconditionally faster: below some density it wins by touching fewer
//! entries, and above it the bookkeeping costs more than the arithmetic saved. These benchmarks
//! exist to locate that crossover rather than to assume it, so every size is measured at several
//! densities and both implementations run on the same matrices.
//!
//! Matrices are generated from a fixed seed, so runs are comparable.
//!
//! Three groups. `sparse_linalg` compares sparse row echelon against dense *reduced* row echelon,
//! which does a second back-substitution pass the sparse side never does — indicative, and not
//! evidence about storage. `matched_echelon` runs the identical algorithm under each backend of
//! `linalg::echelon` and times the representation conversion in its own benchmark, which is the
//! comparison a crossover can be read off. `sparse_rref` measures the sparse reduced form, whose
//! second pass neither of the others covers.

use criterion::{black_box, criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion};
use rand::{prelude::StdRng, Rng, SeedableRng};
use zeebra::{
    fields::Zp2147483647,
    linalg::{
        gauss_jordan_elimination, row_echelon_with,
        sparse::{reduced_row_echelon, row_echelon, SparseMatrix, SparseRow},
        Backend, DenseRows, Matrix,
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
criterion_main!(sparse_linear_algebra, matched, rref);

// ---------------------------------------------------------------------------------------------
// The reduced form, which is a second pass the groups above do not measure.
//
// Back-substitution's cost is set by how many rows actually hold each pivot column, so the two
// shapes below answer different questions. A random square matrix at low density fills in until it
// is near-dense, by which point every row holds every pivot column and there is nothing to skip; a
// banded matrix stays sparse through the elimination, and is where an index over the pivot columns
// has something to save.
// ---------------------------------------------------------------------------------------------

/// A banded matrix: every entry within `bandwidth / 2` columns of the diagonal.
///
/// Gaussian elimination on a banded matrix fills in only inside the band, so the result is as
/// sparse as the input and the rank is essentially full — the shape where `rank * num_rows` and the
/// entries actually present are orders of magnitude apart.
fn banded(n: usize, bandwidth: usize, seed: u64) -> SparseMatrix<F> {
    let mut rng = StdRng::seed_from_u64(seed);
    let half = (bandwidth / 2) as isize;
    let rows: Vec<SparseRow<F>> = (0..n)
        .map(|index| {
            let mut entries: Vec<(usize, F)> = Vec::with_capacity(bandwidth);
            for offset in -half..=half {
                let column = index as isize + offset;
                if (0..n as isize).contains(&column) {
                    entries.push((column as usize, F::random(&mut rng)));
                }
            }
            SparseRow::new(&entries)
        })
        .collect();
    SparseMatrix::new(n, rows)
}

fn reduced_forms(c: &mut Criterion) {
    let mut group = c.benchmark_group("sparse_rref");
    group.sample_size(20);

    for n in [64usize, 128, 256] {
        for density in DENSITIES {
            let matrix = random_sparse(n, density, 7);
            group.bench_with_input(
                BenchmarkId::new(
                    format!("square/{}pct", (density * 100.0).round() as usize),
                    n,
                ),
                &matrix,
                |bencher, matrix| {
                    bencher.iter_batched_ref(
                        || matrix.clone(),
                        |matrix| black_box(reduced_row_echelon(matrix)),
                        BatchSize::SmallInput,
                    )
                },
            );
        }
    }

    for n in [512usize, 2048, 4096] {
        let matrix = banded(n, 8, 13);
        group.bench_with_input(
            BenchmarkId::new("banded/8", n),
            &matrix,
            |bencher, matrix| {
                bencher.iter_batched_ref(
                    || matrix.clone(),
                    |matrix| black_box(reduced_row_echelon(matrix)),
                    BatchSize::SmallInput,
                )
            },
        );
    }

    group.finish();
}

criterion_group!(rref, reduced_forms);

// ---------------------------------------------------------------------------------------------
// A matched-contract comparison.
//
// The group above compares sparse row echelon against dense *reduced* row echelon, which performs
// a second back-substitution pass the sparse side never does, so it cannot separate the cost of a
// representation from the cost of an algorithm. The group below runs the identical algorithm under
// each backend — same pivot rule, same normalization, same statistics — on the identical matrices,
// and times the representation conversion separately, because densifying a matrix is real cost but
// it is not elimination.
// ---------------------------------------------------------------------------------------------

/// The shapes an F4 elimination actually sees, beside the square sweep.
const SHAPES: [(usize, usize, usize); 4] = [
    (64, 256, 8),
    (256, 1024, 12),
    (512, 2048, 16),
    (1024, 1024, 20),
];

fn matched_contract(c: &mut Criterion) {
    let mut group = c.benchmark_group("matched_echelon");
    group.sample_size(20);

    for n in SIZES {
        for density in DENSITIES {
            let matrix = random_sparse(n, density, 7);
            let label = format!("{}pct/{}", (density * 100.0).round() as usize, n);

            for backend in [Backend::Sparse, Backend::Dense, Backend::Adaptive] {
                group.bench_with_input(
                    BenchmarkId::new(format!("square/{:?}", backend), &label),
                    &matrix,
                    |bencher, matrix| {
                        bencher.iter_batched_ref(
                            || matrix.clone(),
                            |matrix| {
                                black_box(
                                    row_echelon_with(backend, matrix, usize::MAX)
                                        .expect("unbounded cannot fail"),
                                )
                            },
                            BatchSize::SmallInput,
                        )
                    },
                );
            }

            // What the dense backend pays before and after the algorithm, on its own.
            group.bench_with_input(
                BenchmarkId::new("square/conversion", &label),
                &matrix,
                |bencher, matrix| {
                    bencher.iter(|| {
                        let dense = DenseRows::from_sparse(black_box(matrix));
                        black_box(dense.to_sparse())
                    })
                },
            );
        }
    }

    for (rows, columns, per_row) in SHAPES {
        let matrix = macaulay_shaped(rows, columns, per_row, 11);
        let label = format!("{}x{}", rows, columns);

        for backend in [Backend::Sparse, Backend::Dense, Backend::Adaptive] {
            group.bench_with_input(
                BenchmarkId::new(format!("macaulay/{:?}", backend), &label),
                &matrix,
                |bencher, matrix| {
                    bencher.iter_batched_ref(
                        || matrix.clone(),
                        |matrix| {
                            black_box(
                                row_echelon_with(backend, matrix, usize::MAX)
                                    .expect("unbounded cannot fail"),
                            )
                        },
                        BatchSize::SmallInput,
                    )
                },
            );
        }

        group.bench_with_input(
            BenchmarkId::new("macaulay/conversion", &label),
            &matrix,
            |bencher, matrix| {
                bencher.iter(|| {
                    let dense = DenseRows::from_sparse(black_box(matrix));
                    black_box(dense.to_sparse())
                })
            },
        );
    }

    group.finish();
}

criterion_group!(matched, matched_contract);
