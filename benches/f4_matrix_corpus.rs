//! Elimination on digest-checked live matrices; the large set requires ZEEBRA_F4_LARGE_CORPUS=1.

use criterion::{
    black_box, criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion, Throughput,
};
use zeebra::{
    grobner::f4::{
        matrix_corpus::{
            walk_corpus, walk_large_corpus, CapturedMatrix, CorpusVisitor, MatrixSpec,
        },
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

        // Probe each arm before timing: a budget refusal is a result, not a runnable benchmark.
        let mut runnable: Vec<(&str, Backend)> = Vec::new();
        let mut fill_in = "the preset's own backend refused this matrix".to_string();
        for (name, backend) in BACKENDS {
            // The large set targets sparse kernels; avoid an enormous dense cell buffer.
            if fingerprint.nonzeros > 10_000_000 && backend == Backend::Dense {
                continue;
            }
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
                    if fingerprint.nonzeros > 10_000_000 {
                        BatchSize::PerIteration
                    } else {
                        BatchSize::SmallInput
                    },
                );
            });
        }
        group.finish();
    }
}

fn corpus_elimination(criterion: &mut Criterion) {
    eprintln!("the pinned corpus, as captured:");
    let mut elimination = Elimination { criterion };
    if std::env::var("ZEEBRA_F4_LARGE_CORPUS").as_deref() == Ok("1") {
        walk_large_corpus(&mut elimination).expect("the large corpus captures as pinned");
    } else {
        walk_corpus(&mut elimination).expect("the corpus captures and matches its pinned digests");
    }
}

criterion_group!(benches, corpus_elimination);
criterion_main!(benches);
