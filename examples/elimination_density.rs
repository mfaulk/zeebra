//! How dense an F4 matrix really is, and what a dense representation costs on it.
//!
//! Two measurements that a wall-clock benchmark cannot report.
//!
//! First, **which density a selection policy should read**. A global density of a fraction of a
//! percent is consistent with a few nearly full rows, so a policy keyed on the whole matrix would
//! be keyed on the wrong number. The row-density distribution is reported both as built and at
//! each row's own peak during its reduction — the latter is the quantity a per-row representation
//! switch would have to predict — along with the density of the densest 64x64 blocks, which is the
//! quantity a block policy would read.
//!
//! Second, **sparse against dense at a matched contract, with conversion separated**. Every backend
//! runs the same algorithm, so the elimination times are comparable; densifying and sparsifying is
//! real cost but it is not the algorithm, so it is reported in its own column.
//!
//! The last table divides that time by `EliminationStatistics::row_operations`, which every backend
//! reports identically. A change inside a row operation moves nanoseconds per operation and leaves
//! the count alone; a change to the pivot rule would move the count, and is a different claim.
//!
//! ```text
//! cargo run --release --example elimination_density            # the default instances
//! cargo run --release --example elimination_density -- list    # the instances available
//! cargo run --release --example elimination_density -- katsura-7/grevlex
//! ```
//!
//! The dense backend allocates `num_rows * num_columns` cells per matrix whatever the entry budget
//! says, so the largest instances are not in the default set: katsura-7 grevlex builds a
//! 6810 x 6862 matrix, which is 374 MB of field elements for a matrix holding 105k entries.

use std::time::{Duration, Instant};

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura},
        f4::{
            macaulay::MacaulayMatrix,
            symbolic::{symbolic_preprocessing_with, ReducerCache},
        },
        trace_batches, F4Options,
    },
    linalg::{
        row_echelon_with,
        sparse::{SparseMatrix, SparseRow},
        Backend, DenseRows,
    },
    MonomialOrder, MultivariatePolynomial,
};

type F = Zp2147483647;

/// Instances whose matrices are small enough for a dense representation to be measured at all.
const DEFAULT: [&str; 6] = [
    "cyclic-4/lex",
    "cyclic-5/grevlex",
    "katsura-5/lex",
    "katsura-5/grevlex",
    "katsura-6/grlex",
    "katsura-6/grevlex",
];

/// Everything that can be named, including the instances that are too large by default.
const AVAILABLE: [&str; 8] = [
    "cyclic-4/lex",
    "cyclic-5/lex",
    "cyclic-5/grevlex",
    "katsura-5/lex",
    "katsura-5/grevlex",
    "katsura-6/grlex",
    "katsura-6/grevlex",
    "katsura-7/grevlex",
];

fn order_of(name: &str) -> MonomialOrder {
    match name {
        "lex" => MonomialOrder::Lexicographic,
        "grlex" => MonomialOrder::GradedLexicographic,
        "grevlex" => MonomialOrder::GradedReverseLexicographic,
        other => panic!("unknown order {}", other),
    }
}

/// Every Macaulay matrix one instance builds, in the order F4 builds them.
fn matrices(instance: &str) -> Vec<SparseMatrix<F>> {
    let (system, order) = instance
        .split_once('/')
        .expect("an instance is named system/order");
    let order = order_of(order);
    let options = F4Options::baseline();

    match system {
        "cyclic-4" => collect(&cyclic::<4, F>(), order, &options),
        "cyclic-5" => collect(&cyclic::<5, F>(), order, &options),
        "katsura-5" => collect(&katsura::<5, F>(), order, &options),
        "katsura-6" => collect(&katsura::<6, F>(), order, &options),
        "katsura-7" => collect(&katsura::<7, F>(), order, &options),
        other => panic!("unknown system {}", other),
    }
}

fn collect<const N: usize>(
    system: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    options: &F4Options,
) -> Vec<SparseMatrix<F>> {
    let (_, _, trace) = trace_batches(system, order, options).expect("within limits");
    trace
        .batches()
        .iter()
        .filter_map(|batch| {
            let preprocessed = symbolic_preprocessing_with(
                &batch.basis,
                &batch.pairs,
                options.max_matrix_rows,
                options.reducer_selection,
                &mut ReducerCache::disabled(),
            )
            .ok()?;
            Some(
                MacaulayMatrix::build(&batch.basis, &preprocessed, order)
                    .matrix()
                    .clone(),
            )
        })
        .collect()
}

/// The percentile of a sorted sample, by nearest rank.
fn percentile(sorted: &[f64], fraction: f64) -> f64 {
    if sorted.is_empty() {
        return 0.0;
    }
    let position = ((sorted.len() as f64 - 1.0) * fraction).round() as usize;
    sorted[position]
}

/// Each row's nonzero count at its own peak during elimination, and the matrix's peak.
///
/// Runs the same elimination the sparse backend runs, over a copy of the rows, instrumented to
/// record how dense each row ever became. A row that is briefly full is exactly the case a
/// per-row representation switch would exist for, and nothing in `EliminationStatistics` reports
/// it: `peak_nonzeros` is a total over the whole matrix.
fn row_peaks(matrix: &SparseMatrix<F>) -> Vec<usize> {
    let mut rows: Vec<SparseRow<F>> = matrix.rows().to_vec();
    let mut peaks = vec![0usize; rows.len()];
    let mut pivot_of_column: std::collections::HashMap<usize, usize> =
        std::collections::HashMap::new();
    let mut scratch: Vec<(usize, F)> = Vec::new();

    for index in 0..rows.len() {
        let mut row = std::mem::take(&mut rows[index]);
        let mut peak = row.nonzeros();

        while let Some(column) = row.leading_column() {
            match pivot_of_column.get(&column) {
                Some(&pivot_index) => {
                    let factor = row.leading_coefficient().expect("a leading column");
                    row.subtract_scaled(&rows[pivot_index], &factor, &mut scratch);
                    peak = peak.max(row.nonzeros());
                }
                None => {
                    row.normalize();
                    pivot_of_column.insert(column, index);
                    break;
                }
            }
        }

        peaks[index] = peak;
        rows[index] = row;
    }

    peaks
}

/// The densities of the `size x size` blocks of a matrix, descending.
fn block_densities(matrix: &SparseMatrix<F>, size: usize) -> Vec<f64> {
    let row_blocks = matrix.num_rows().div_ceil(size);
    let column_blocks = matrix.num_columns().div_ceil(size);
    if row_blocks == 0 || column_blocks == 0 {
        return Vec::new();
    }

    let mut counts = vec![0usize; row_blocks * column_blocks];
    for (index, row) in matrix.rows().iter().enumerate() {
        let row_block = index / size;
        for (column, _) in row.entries() {
            counts[row_block * column_blocks + column / size] += 1;
        }
    }

    let mut densities: Vec<f64> = counts
        .iter()
        .enumerate()
        .map(|(block, count)| {
            let rows = (matrix.num_rows() - (block / column_blocks) * size).min(size);
            let columns = (matrix.num_columns() - (block % column_blocks) * size).min(size);
            *count as f64 / (rows * columns) as f64
        })
        .collect();
    densities.sort_by(|a, b| b.partial_cmp(a).expect("no NaN"));
    densities
}

/// One elimination of every matrix, under one backend, with the work it reported.
///
/// The row-operation count is the denominator the per-operation cost is taken against. It is a
/// function of the matrices and the pivot rule alone — every backend reports the same one — so a
/// change in nanoseconds per operation is a change in the cost of an operation and not in how many
/// there were.
fn time_elimination(matrices: &[SparseMatrix<F>], backend: Backend) -> (Duration, usize) {
    let mut elapsed = Duration::ZERO;
    let mut row_operations = 0;
    for matrix in matrices {
        let mut matrix = matrix.clone();
        let start = Instant::now();
        let statistics =
            row_echelon_with(backend, &mut matrix, usize::MAX).expect("unbounded cannot fail");
        elapsed += start.elapsed();
        row_operations += statistics.row_operations;
    }
    (elapsed, row_operations)
}

/// Densifying and sparsifying every matrix, which is what the dense backend pays before and after.
fn time_conversion(matrices: &[SparseMatrix<F>]) -> Duration {
    let mut elapsed = Duration::ZERO;
    for matrix in matrices {
        let start = Instant::now();
        let dense = DenseRows::from_sparse(matrix);
        let back = dense.to_sparse();
        elapsed += start.elapsed();
        assert_eq!(&back, matrix, "conversion must round-trip");
    }
    elapsed
}

fn millis(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1000.0
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    if arguments.first().map(String::as_str) == Some("list") {
        println!("instances:");
        for instance in AVAILABLE {
            let included = if DEFAULT.contains(&instance) {
                ""
            } else {
                "   (not in the default set: the dense representation is large)"
            };
            println!("  {}{}", instance, included);
        }
        return;
    }

    let instances: Vec<String> = if arguments.is_empty() {
        DEFAULT.iter().map(|s| s.to_string()).collect()
    } else {
        arguments
    };

    println!("# Shape and density, as built");
    println!(
        "| instance | matrices | largest rows x cols | global density | row nnz/width p50 | p90 | p99 | max |"
    );
    println!("|---|---|---|---|---|---|---|---|");

    let mut harvested: Vec<(String, Vec<SparseMatrix<F>>)> = Vec::new();
    for instance in &instances {
        let built = matrices(instance);
        let largest = built
            .iter()
            .max_by_key(|matrix| matrix.num_rows() * matrix.num_columns());

        let mut row_densities: Vec<f64> = Vec::new();
        let mut entries = 0usize;
        let mut cells = 0usize;
        for matrix in &built {
            if matrix.num_columns() == 0 {
                continue;
            }
            entries += matrix.nonzeros();
            cells += matrix.num_rows() * matrix.num_columns();
            for row in matrix.rows() {
                row_densities.push(row.nonzeros() as f64 / matrix.num_columns() as f64);
            }
        }
        row_densities.sort_by(|a, b| a.partial_cmp(b).expect("no NaN"));

        println!(
            "| {} | {} | {} x {} | {:.4}% | {:.2}% | {:.2}% | {:.2}% | {:.2}% |",
            instance,
            built.len(),
            largest.map_or(0, |m| m.num_rows()),
            largest.map_or(0, |m| m.num_columns()),
            if cells == 0 {
                0.0
            } else {
                100.0 * entries as f64 / cells as f64
            },
            100.0 * percentile(&row_densities, 0.50),
            100.0 * percentile(&row_densities, 0.90),
            100.0 * percentile(&row_densities, 0.99),
            100.0 * percentile(&row_densities, 1.0),
        );

        harvested.push((instance.clone(), built));
    }

    println!();
    println!("# Density during and after elimination, on each instance's largest matrix");
    println!(
        "| instance | rows x cols | built | peak | final | row peak/width p50 | p90 | p99 | max | rows over 50% |"
    );
    println!("|---|---|---|---|---|---|---|---|---|---|");

    for (instance, built) in &harvested {
        let Some(largest) = built
            .iter()
            .max_by_key(|matrix| matrix.num_rows() * matrix.num_columns())
        else {
            continue;
        };
        if largest.num_columns() == 0 {
            continue;
        }

        let peaks = row_peaks(largest);
        let mut peak_densities: Vec<f64> = peaks
            .iter()
            .map(|peak| *peak as f64 / largest.num_columns() as f64)
            .collect();
        peak_densities.sort_by(|a, b| a.partial_cmp(b).expect("no NaN"));
        let over_half = peak_densities.iter().filter(|d| **d > 0.5).count();

        let mut reduced = largest.clone();
        let statistics =
            row_echelon_with(Backend::Sparse, &mut reduced, usize::MAX).expect("unbounded");

        println!(
            "| {} | {} x {} | {} | {} | {} | {:.2}% | {:.2}% | {:.2}% | {:.2}% | {} of {} |",
            instance,
            largest.num_rows(),
            largest.num_columns(),
            statistics.initial_nonzeros,
            statistics.peak_nonzeros,
            statistics.final_nonzeros,
            100.0 * percentile(&peak_densities, 0.50),
            100.0 * percentile(&peak_densities, 0.90),
            100.0 * percentile(&peak_densities, 0.99),
            100.0 * percentile(&peak_densities, 1.0),
            over_half,
            peaks.len(),
        );
    }

    println!();
    println!("# Block density of the largest matrix, 64 x 64 blocks");
    println!("| instance | blocks | densest | p99 | p90 | median | blocks over 10% | over 50% |");
    println!("|---|---|---|---|---|---|---|---|");

    for (instance, built) in &harvested {
        let Some(largest) = built
            .iter()
            .max_by_key(|matrix| matrix.num_rows() * matrix.num_columns())
        else {
            continue;
        };
        let densities = block_densities(largest, 64);
        if densities.is_empty() {
            continue;
        }
        // Sorted descending, so the nearest-rank percentile reads from the other end.
        println!(
            "| {} | {} | {:.2}% | {:.2}% | {:.2}% | {:.2}% | {} | {} |",
            instance,
            densities.len(),
            100.0 * densities[0],
            100.0 * percentile(&densities, 0.01),
            100.0 * percentile(&densities, 0.10),
            100.0 * percentile(&densities, 0.50),
            densities.iter().filter(|d| **d > 0.10).count(),
            densities.iter().filter(|d| **d > 0.50).count(),
        );
    }

    println!();
    println!("# Elimination of every matrix of an instance, by backend. Milliseconds.");
    println!(
        "| instance | sparse | dense | adaptive | dense conversion | dense total | dense/sparse |"
    );
    println!("|---|---|---|---|---|---|---|");

    let mut per_operation: Vec<(String, Backend, Duration, usize, usize)> = Vec::new();

    for (instance, built) in &harvested {
        let (sparse, sparse_ops) = time_elimination(built, Backend::Sparse);
        let (dense, dense_ops) = time_elimination(built, Backend::Dense);
        let (adaptive, adaptive_ops) = time_elimination(built, Backend::Adaptive);
        let conversion = time_conversion(built);

        // Pivot storage is `4 * num_columns` bytes for the widest matrix of the instance, since
        // one index is built per elimination and freed with it; the peak is the widest.
        let widest = built
            .iter()
            .map(SparseMatrix::num_columns)
            .max()
            .unwrap_or(0);
        for (backend, elapsed, operations) in [
            (Backend::Sparse, sparse, sparse_ops),
            (Backend::Dense, dense, dense_ops),
            (Backend::Adaptive, adaptive, adaptive_ops),
        ] {
            per_operation.push((instance.clone(), backend, elapsed, operations, widest));
        }

        // The dense elimination as reported includes its own conversions, because the backend has
        // to perform them; the conversion column says how much of it they are.
        println!(
            "| {} | {:.2} | {:.2} | {:.2} | {:.2} | {:.2} | {:.2}x |",
            instance,
            millis(sparse),
            millis(dense) - millis(conversion),
            millis(adaptive),
            millis(conversion),
            millis(dense),
            millis(dense) / millis(sparse),
        );
    }

    println!();
    println!("# Per-operation cost of elimination, by backend");
    println!("| instance | backend | ms | row operations | ns/op | widest | pivot index KiB |");
    println!("|---|---|---|---|---|---|---|");
    for (instance, backend, elapsed, operations, widest) in &per_operation {
        let nanos_per_operation = if *operations == 0 {
            f64::NAN
        } else {
            elapsed.as_secs_f64() * 1e9 / *operations as f64
        };
        println!(
            "| {} | {:?} | {:.2} | {} | {:.1} | {} | {:.1} |",
            instance,
            backend,
            millis(*elapsed),
            operations,
            nanos_per_operation,
            widest,
            *widest as f64 * 4.0 / 1024.0,
        );
    }
}
