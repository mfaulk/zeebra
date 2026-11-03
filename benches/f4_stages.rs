//! F4's stages benchmarked separately, on the batches F4 actually builds.
//!
//! `benches/grobner.rs` times whole computations, which says whether something got faster. It
//! cannot say whether a change *removed* cost or merely *moved* it from one stage to another —
//! and moving it is the usual outcome of a change to symbolic preprocessing, which trades a
//! smaller matrix for more work finding it.
//!
//! Each group replays one stage over every batch of a real run:
//!
//! - `symbolic` — the closure, from the basis and the pairs.
//! - `construction` — the monomial-to-column map and writing the entries.
//! - `elimination` — row echelon on the matrices as built.
//! - `batch` — all three plus candidate extraction, i.e. one whole `reduce_batch`.
//!
//! The batches come from `zeebra::grobner::trace_batches`, not from a synthetic generator: an F4
//! matrix is wide, tall, a few entries per row, with leading entries colliding in low columns, and
//! a density sweep does not reproduce that shape.
//!
//! The groups are directly comparable to each other, because every one iterates over the same
//! batches in the same order. Summing a system's four group medians is *not* the whole computation:
//! pair selection, basis bookkeeping, and interreduction are outside every stage.

use criterion::{
    black_box, criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion, Throughput,
};
use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura},
        f4::{
            macaulay::MacaulayMatrix,
            observer::TracedBatch,
            reduce_batch,
            symbolic::{symbolic_preprocessing_with, ReducerCache},
        },
        trace_batches, F4Options, ReducerSelection,
    },
    linalg::{echelon::row_echelon_with, Backend},
    MonomialOrder, MultivariatePolynomial,
};

type F = Zp2147483647;

/// The instances the stage comparison is run on.
///
/// Deliberately small in number: each group replays *every* batch of each instance, so the cost is
/// the whole computation's stage cost per iteration. katsura-6 grevlex is here because it is the
/// milestone's headline target; katsura-5 lex because it is where batching pays most; cyclic-5
/// grevlex for a different family.
const INSTANCES: [(&str, MonomialOrder); 4] = [
    (
        "katsura-6/grevlex",
        MonomialOrder::GradedReverseLexicographic,
    ),
    ("katsura-6/grlex", MonomialOrder::GradedLexicographic),
    ("katsura-5/lex", MonomialOrder::Lexicographic),
    (
        "cyclic-5/grevlex",
        MonomialOrder::GradedReverseLexicographic,
    ),
];

/// The traced batches of each instance, collected once and reused by every group.
fn instances() -> Vec<(String, MonomialOrder, Batches)> {
    let options = F4Options::baseline();
    let mut collected = Vec::new();

    for (label, order) in INSTANCES {
        let batches = match label {
            "katsura-6/grevlex" | "katsura-6/grlex" => {
                Batches::Six(trace(&katsura::<6, F>(), order, &options))
            }
            "katsura-5/lex" => Batches::Five(trace(&katsura::<5, F>(), order, &options)),
            "cyclic-5/grevlex" => Batches::Five(trace(&cyclic::<5, F>(), order, &options)),
            other => panic!("unlisted instance {}", other),
        };
        collected.push((label.to_string(), order, batches));
    }

    collected
}

fn trace<const N: usize>(
    system: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    options: &F4Options,
) -> Vec<TracedBatch<N, F>> {
    let (_, _, trace) = trace_batches(system, order, options).expect("within limits");
    trace.batches().to_vec()
}

/// `N` is a const generic, so a collection of instances of different sizes needs a sum type.
enum Batches {
    Five(Vec<TracedBatch<5, F>>),
    Six(Vec<TracedBatch<6, F>>),
}

/// Total matrix rows across an instance's batches, as the throughput unit.
///
/// Rows rather than batches: a stage's cost scales with the matrix, and reporting per-row figures
/// makes two instances with very different batch counts comparable.
fn rows<const N: usize>(batches: &[TracedBatch<N, F>], order: MonomialOrder) -> u64 {
    let options = F4Options::baseline();
    batches
        .iter()
        .map(|batch| {
            symbolic_preprocessing_with(
                &batch.basis,
                &batch.pairs,
                options.max_matrix_rows,
                ReducerSelection::FirstApplicable,
                &mut ReducerCache::disabled(),
            )
            .map(|preprocessed| {
                let _ = order;
                preprocessed.rows.len() as u64
            })
            .unwrap_or(0)
        })
        .sum()
}

fn bench_symbolic<const N: usize>(
    group: &mut criterion::BenchmarkGroup<'_, criterion::measurement::WallTime>,
    label: &str,
    batches: &[TracedBatch<N, F>],
) {
    let options = F4Options::baseline();
    group.bench_function(BenchmarkId::new("symbolic", label), |bencher| {
        bencher.iter(|| {
            for batch in batches {
                black_box(
                    symbolic_preprocessing_with(
                        &batch.basis,
                        &batch.pairs,
                        options.max_matrix_rows,
                        options.reducer_selection,
                        &mut ReducerCache::new(options.reducer_cache),
                    )
                    .expect("within limits"),
                );
            }
        })
    });
}

fn bench_construction<const N: usize>(
    group: &mut criterion::BenchmarkGroup<'_, criterion::measurement::WallTime>,
    label: &str,
    batches: &[TracedBatch<N, F>],
    order: MonomialOrder,
) {
    let options = F4Options::baseline();

    // Preprocessing is done once, outside the measurement, so this times construction alone.
    let preprocessed: Vec<_> = batches
        .iter()
        .map(|batch| {
            symbolic_preprocessing_with(
                &batch.basis,
                &batch.pairs,
                options.max_matrix_rows,
                options.reducer_selection,
                &mut ReducerCache::disabled(),
            )
            .expect("within limits")
        })
        .collect();

    group.bench_function(BenchmarkId::new("construction", label), |bencher| {
        bencher.iter(|| {
            for (batch, preprocessed) in batches.iter().zip(preprocessed.iter()) {
                black_box(MacaulayMatrix::build(&batch.basis, preprocessed, order));
            }
        })
    });
}

fn bench_elimination<const N: usize>(
    group: &mut criterion::BenchmarkGroup<'_, criterion::measurement::WallTime>,
    label: &str,
    batches: &[TracedBatch<N, F>],
    order: MonomialOrder,
) {
    let options = F4Options::baseline();

    // The matrices as built. Cloned per iteration, because elimination is in place; the clone is
    // outside the timed closure, which is what `iter_batched` is for.
    let matrices: Vec<_> = batches
        .iter()
        .map(|batch| {
            let preprocessed = symbolic_preprocessing_with(
                &batch.basis,
                &batch.pairs,
                options.max_matrix_rows,
                options.reducer_selection,
                &mut ReducerCache::disabled(),
            )
            .expect("within limits");
            MacaulayMatrix::build(&batch.basis, &preprocessed, order)
                .matrix()
                .clone()
        })
        .collect();

    for backend in [Backend::Sparse, Backend::Dense, Backend::Adaptive] {
        group.bench_function(
            BenchmarkId::new(format!("elimination/{:?}", backend), label),
            |bencher| {
                bencher.iter_batched(
                    || matrices.clone(),
                    |mut matrices| {
                        for matrix in matrices.iter_mut() {
                            black_box(
                                row_echelon_with(backend, matrix, options.max_live_nonzeros)
                                    .expect("within limits"),
                            );
                        }
                    },
                    BatchSize::SmallInput,
                )
            },
        );
    }
}

fn bench_batch<const N: usize>(
    group: &mut criterion::BenchmarkGroup<'_, criterion::measurement::WallTime>,
    label: &str,
    batches: &[TracedBatch<N, F>],
    order: MonomialOrder,
) {
    let options = F4Options::baseline();
    group.bench_function(BenchmarkId::new("batch", label), |bencher| {
        bencher.iter(|| {
            for batch in batches {
                black_box(
                    reduce_batch(&batch.basis, &batch.pairs, order, &options)
                        .expect("within limits"),
                );
            }
        })
    });
}

fn stages(c: &mut Criterion) {
    let mut group = c.benchmark_group("f4_stages");
    // Every iteration replays a whole computation's worth of one stage, so the defaults would run
    // for minutes per instance.
    group.sample_size(10);

    for (label, order, batches) in instances() {
        match &batches {
            Batches::Five(batches) => {
                group.throughput(Throughput::Elements(rows(batches, order)));
                bench_symbolic(&mut group, &label, batches);
                bench_construction(&mut group, &label, batches, order);
                bench_elimination(&mut group, &label, batches, order);
                bench_batch(&mut group, &label, batches, order);
            }
            Batches::Six(batches) => {
                group.throughput(Throughput::Elements(rows(batches, order)));
                bench_symbolic(&mut group, &label, batches);
                bench_construction(&mut group, &label, batches, order);
                bench_elimination(&mut group, &label, batches, order);
                bench_batch(&mut group, &label, batches, order);
            }
        }
    }

    group.finish();
}

criterion_group!(f4_stages, stages);
criterion_main!(f4_stages);
