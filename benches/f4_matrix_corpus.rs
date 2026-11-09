//! Elimination, benchmarked over the pinned corpus of real Macaulay matrices.
//!
//! `benches/f4_stages.rs` times elimination over *every* batch of four katsura/cyclic instances
//! over one field under `F4Options::baseline()`. That is a whole computation's elimination cost per
//! iteration, which is the right unit for "did the stage get faster" and the wrong one for "which
//! kernel is faster on which matrix" — the shapes are summed over and the field is fixed.
//!
//! This benchmarks **one matrix at a time**, named and pinned by digest, across five fields and
//! three scaffolding regimes, under both option presets. Criterion's throughput is set from the
//! matrix's nonzero count, so the per-matrix figure is entries per second and two matrices of very
//! different size are comparable.
//!
//! The matrices come from [`walk_corpus`], which re-derives each fingerprint and refuses to hand
//! over a matrix that is not the pinned one. A benchmark here therefore cannot be a benchmark of a
//! matrix that drifted — the failure mode #517, #412 and #317 each paid for.
//!
//! Fill-in is a property of the matrix and the kernel rather than of the clock, so it is printed to
//! stderr once at startup instead of being folded into a Criterion statistic.
//!
//! ```text
//! cargo bench --bench f4_matrix_corpus
//! cargo bench --bench f4_matrix_corpus -- katsura-6/grevlex/m31/default
//! ```

use criterion::{
    black_box, criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion, Throughput,
};
use zeebra::{
    grobner::f4::{
        matrix_corpus::{walk_corpus, CapturedMatrix, CorpusVisitor, MatrixSpec},
        options::ReductionStrategy,
        structured::{eliminate_to, BlockPlan, RowForm},
    },
    linalg::Backend,
    FiniteField,
};

const BACKENDS: [(&str, Backend); 3] = [
    ("sparse", Backend::Sparse),
    ("dense", Backend::Dense),
    ("adaptive", Backend::Adaptive),
];

struct Elimination<'c> {
    criterion: &'c mut Criterion,
}

impl CorpusVisitor for Elimination<'_> {
    fn visit<const N: usize, F: FiniteField>(
        &mut self,
        spec: &MatrixSpec,
        captured: &CapturedMatrix<N, F>,
    ) {
        let options = spec.options.options();
        let plan = match options.reduction {
            ReductionStrategy::Unstructured => BlockPlan::Baseline,
            ReductionStrategy::Structured => BlockPlan::ReducersFirstBlock,
        };
        let form = if options.reduce_batch_rows {
            RowForm::Reduced
        } else {
            RowForm::Echelon
        };
        let allowance = options.live_entry_allowance::<F>();
        let fingerprint = &captured.fingerprint;

        let mut group = self.criterion.benchmark_group("corpus_elimination");
        group.throughput(Throughput::Elements(fingerprint.nonzeros as u64));

        // One elimination per backend outside the measurement, which does two jobs: it finds out
        // whether that backend can run this matrix at all, and — for the backend the entry's own
        // preset selects — it is where the fill-in figure comes from, so the fill-in and the
        // timings describe the same matrix under the same contract.
        //
        // `Backend::Dense` cannot run the whole corpus. On `mq-random-10` it reaches 75 449 540
        // live entries against the 20 000 000 the allowance admits, and its cell buffer alone
        // would be 2.4 GB. A refusal is a real property of the pair and is reported; benchmarking
        // through an `expect` would make the suite's coverage depend on which matrices fit.
        let mut runnable: Vec<(&str, Backend)> = Vec::new();
        let mut fill_in = "the preset's own backend refused this matrix".to_string();
        for (name, backend) in BACKENDS {
            let mut probe = captured.matrix.clone();
            match eliminate_to(plan, form, backend, &mut probe, allowance) {
                Ok(outcome) => {
                    if backend == options.elimination {
                        let statistics = outcome.statistics;
                        fill_in = format!(
                            "fill-in peak {:.2}x final {:.2}x rank {}",
                            statistics.peak_nonzeros as f64 / fingerprint.nonzeros.max(1) as f64,
                            statistics.final_nonzeros as f64 / fingerprint.nonzeros.max(1) as f64,
                            statistics.rank
                        );
                    }
                    runnable.push((name, backend));
                }
                Err(nonzeros) => eprintln!(
                    "  {:<10} refused {} at {} live entries against an allowance of {}",
                    name, spec.label, nonzeros, allowance
                ),
            }
        }

        eprintln!(
            "{:<42} {:>6}x{:<6} red {:>5.1}%  nz {:>8}  density {:.5}  {}",
            spec.label,
            fingerprint.rows,
            fingerprint.columns,
            100.0 * fingerprint.reducer_share(),
            fingerprint.nonzeros,
            fingerprint.density(),
            fill_in,
        );

        for (name, backend) in runnable {
            group.bench_function(BenchmarkId::new(name, spec.label), |bencher| {
                // Elimination is in place, so each iteration needs its own copy. `iter_batched`
                // keeps the clone out of the measured region.
                bencher.iter_batched(
                    || captured.matrix.clone(),
                    |mut matrix| {
                        black_box(
                            eliminate_to(plan, form, backend, &mut matrix, allowance)
                                .expect("the probe above established this arm can run it"),
                        );
                    },
                    BatchSize::SmallInput,
                );
            });
        }
        group.finish();
    }
}

fn corpus_elimination(criterion: &mut Criterion) {
    eprintln!("the pinned corpus, as captured:");
    let mut elimination = Elimination { criterion };
    walk_corpus(&mut elimination).expect("the corpus captures and matches its pinned digests");
}

criterion_group!(benches, corpus_elimination);
criterion_main!(benches);
