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
//! - `elimination` — row echelon on the matrices as built, under each backend.
//! - `conversion` — densifying and sparsifying those matrices, which the dense backend pays
//!   around the algorithm and which is therefore reported apart from it.
//! - `batch` — all three plus candidate extraction, i.e. one whole `reduce_batch`.
//!
//! The batches come from `zeebra::grobner::trace_batches`, not from a synthetic generator: an F4
//! matrix is wide, tall, a few entries per row, with leading entries colliding in low columns, and
//! a density sweep does not reproduce that shape.
//!
//! - `interreduction` — the final pass, over the basis F4 actually produced.
//!
//! The groups are directly comparable to each other, because every one iterates over the same
//! batches in the same order. Summing a system's group medians is *not* the whole computation:
//! pair selection and basis bookkeeping are outside every stage.
//!
//! `interreduction` is the odd one out and is here because it was missing. It runs **once** per
//! computation rather than per batch, so it is not comparable to the per-batch groups — and it is
//! the stage `docs/research/groebner-jl-gap.md` §3 measures at **80.69%** of `mq-random-10` and
//! **13 871x** Groebner.jl's, which had no Criterion coverage at all. Its input is the basis before
//! interreduction, taken from a real run, because the shape that makes the stage expensive is a
//! basis of a few hundred elements whose entire monomial support is a few hundred monomials.

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
        interreduce_for_benchmark, trace_batches, F4Options, ReducerSelection,
    },
    linalg::{echelon::row_echelon_with, Backend, DenseRows},
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

/// Densifying and sparsifying the matrices as built, which is what the dense backend pays around
/// the algorithm.
///
/// Reported as its own benchmark rather than folded into `elimination/Dense`: conversion is real
/// cost, but it is not elimination, and a comparison that conflates the two cannot say whether a
/// representation or a conversion is what made the difference.
fn bench_conversion<const N: usize>(
    group: &mut criterion::BenchmarkGroup<'_, criterion::measurement::WallTime>,
    label: &str,
    batches: &[TracedBatch<N, F>],
    order: MonomialOrder,
) {
    let options = F4Options::baseline();
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

    group.bench_function(BenchmarkId::new("conversion", label), |bencher| {
        bencher.iter(|| {
            for matrix in &matrices {
                let dense = DenseRows::from_sparse(black_box(matrix));
                black_box(dense.to_sparse());
            }
        })
    });
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

/// The final interreduction, over the basis F4 produced before it.
///
/// The input is the last traced batch's basis plus that batch's candidates — i.e. exactly what
/// `f4_into` hands the stage — cloned per iteration, because the stage consumes it.
fn bench_interreduction<const N: usize>(
    group: &mut criterion::BenchmarkGroup<'_, criterion::measurement::WallTime>,
    label: &str,
    batches: &[TracedBatch<N, F>],
    order: MonomialOrder,
) {
    // The basis as it stood entering the last batch, which is the largest any batch saw and the
    // closest this trace gets to the pre-interreduction basis.
    let Some(last) = batches.last() else {
        return;
    };
    let basis: Vec<_> = (0..last.basis.len())
        .map(|i| MultivariatePolynomial::new(&last.basis.element(i).terms))
        .collect();
    if basis.len() < 2 {
        // One element is already reduced, so there is nothing to time.
        return;
    }

    group.bench_function(BenchmarkId::new("interreduction", label), |bencher| {
        bencher.iter_batched(
            || basis.clone(),
            |basis| black_box(interreduce_for_benchmark(basis, order)),
            BatchSize::LargeInput,
        )
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
                bench_conversion(&mut group, &label, batches, order);
                bench_batch(&mut group, &label, batches, order);
                bench_interreduction(&mut group, &label, batches, order);
            }
            Batches::Six(batches) => {
                group.throughput(Throughput::Elements(rows(batches, order)));
                bench_symbolic(&mut group, &label, batches);
                bench_construction(&mut group, &label, batches, order);
                bench_elimination(&mut group, &label, batches, order);
                bench_conversion(&mut group, &label, batches, order);
                bench_batch(&mut group, &label, batches, order);
                bench_interreduction(&mut group, &label, batches, order);
            }
        }
    }

    group.finish();
}

criterion_group!(f4_stages, stages);
criterion_main!(f4_stages);
