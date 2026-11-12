//! Inspect, pin and verify live F4 matrix captures; large modes are explicit opt-in.

use std::time::{Duration, Instant};

use zeebra::{
    grobner::{
        f4::{
            f4_with_options,
            matrix_corpus::{
                corpus, large_corpus, walk_corpus_with, walk_large_corpus_with, CapturedMatrix,
                CorpusVisitor, MatrixSpec,
            },
            options::ReductionStrategy,
            rebuild_matrix,
            structured::{eliminate_to, BlockPlan, RowForm},
        },
        F4Options,
    },
    linalg::Backend,
    FiniteField,
};

/// Repetitions per arm. Odd, so the median is an observation rather than a mean of two.
const REPS: usize = 3;

const ARMS: [(&str, Backend); 2] = [("sparse", Backend::Sparse), ("adaptive", Backend::Adaptive)];

fn main() {
    let mode = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "list".to_string());
    match mode.as_str() {
        "list" => list(false),
        "list-large" => list(true),
        "check" => check(false),
        "check-large" => check(true),
        "check-all" => {
            check(false);
            check(true);
        }
        "pin" => pin(false),
        "pin-large" => pin(true),
        "predict" => predict(),
        other => {
            eprintln!(
                "unknown mode {}; try list[-large], check[-large], pin[-large], check-all or predict",
                other
            );
            std::process::exit(64);
        }
    }
}

fn walk_selected<V: CorpusVisitor>(
    visitor: &mut V,
    large: bool,
    verify: bool,
) -> Result<(), zeebra::grobner::f4::matrix_corpus::CorpusError> {
    if large {
        walk_large_corpus_with(visitor, verify)
    } else {
        walk_corpus_with(visitor, verify)
    }
}

/// The corpus as pinned, with the derived shares the regime bands are asserted against.
fn list(large: bool) {
    println!(
        "| label | field | bits | preset | batch | rows | cols | red% | nz | density | regime | digest | entry cap | byte cap | selector |"
    );
    println!("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|");
    for spec in if large { large_corpus() } else { corpus() } {
        let options = spec.options.options();
        let f = &spec.fingerprint;
        println!(
            "| `{}` | {} | {} | {} | {} | {} | {} | {:.1} | {} | {:.4} | {} | `{}` | {} | {} | {:?} |",
            spec.label,
            spec.field,
            spec.field_bits,
            spec.options.name(),
            f.batch_index,
            f.rows,
            f.columns,
            100.0 * f.reducer_share(),
            f.nonzeros,
            f.density(),
            spec.regime.name(),
            f.digest, options.max_live_nonzeros, options.max_live_bytes, spec.selector
        );
    }
}

/// Capture every entry, verify it, and say so.
fn check(large: bool) {
    struct Count {
        entries: usize,
    }
    impl CorpusVisitor for Count {
        fn visit<const N: usize, F: FiniteField>(
            &mut self,
            spec: &MatrixSpec,
            captured: &CapturedMatrix<N, F>,
        ) {
            self.entries += 1;
            println!(
                "ok  {:<42} {}x{} nz {} observed_batches {} completed {}",
                spec.label,
                captured.fingerprint.rows,
                captured.fingerprint.columns,
                captured.fingerprint.nonzeros,
                captured.batches,
                captured.completed
            );
        }
    }

    let mut count = Count { entries: 0 };
    match walk_selected(&mut count, large, true) {
        Ok(()) => println!("\n{} entries, every one as pinned", count.entries),
        Err(error) => {
            eprintln!("\nCORPUS DRIFTED: {}", error);
            std::process::exit(1);
        }
    }
}

/// Re-derive the pinned table.
fn pin(large: bool) {
    struct Pin;
    impl CorpusVisitor for Pin {
        fn visit<const N: usize, F: FiniteField>(
            &mut self,
            spec: &MatrixSpec,
            captured: &CapturedMatrix<N, F>,
        ) {
            let f = &captured.fingerprint;
            // The regime is derived from the capture rather than echoed from the spec, so a
            // re-pin moves the band with the matrix instead of pinning a stale claim.
            let regime = zeebra::grobner::f4::matrix_corpus::Regime::of(f.reducer_share());
            println!(
                "        {}, {}, {}, {}, {}, \"{}\";   // red {:.1}%  density {:.4}  regime {}",
                spec.label,
                f.batch_index,
                f.rows,
                f.columns,
                f.reducer_rows,
                f.digest,
                100.0 * f.reducer_share(),
                f.density(),
                regime.name(),
            );
            println!(
                "            nonzeros {}  batches {} completed {}",
                f.nonzeros, captured.batches, captured.completed
            );
        }
    }

    if let Err(error) = walk_selected(&mut Pin, large, false) {
        eprintln!("capture failed: {}", error);
        std::process::exit(1);
    }
}

/// Does the corpus rank two elimination kernels the way a whole run does?
fn predict() {
    struct Predict {
        rows: Vec<Row>,
    }

    struct Row {
        label: &'static str,
        rows: usize,
        columns: usize,
        nonzeros: usize,
        /// Median elimination time per arm, on the corpus matrix.
        micro: [Duration; ARMS.len()],
        /// Median whole-run time per arm, same instance and options but for the backend.
        ///
        /// `None` when an arm refused the instance. A backend that crosses a budget the other does
        /// not is a real outcome and not a timing, so it is reported rather than folded in: the
        /// dense accumulator's row-wide buffer is not charged to `max_live_bytes`, so the two arms
        /// do not admit exactly the same computations.
        macro_: Option<[Duration; ARMS.len()]>,
    }

    impl CorpusVisitor for Predict {
        fn visit<const N: usize, F: FiniteField>(
            &mut self,
            spec: &MatrixSpec,
            captured: &CapturedMatrix<N, F>,
        ) {
            let options = spec.options.options();

            // The matrix is the captured one, and the rebuild is asserted against it here rather
            // than only in the unit tests: a figure published from this example must not be a
            // figure about a matrix the live path does not build.
            let rebuilt = rebuild_matrix(captured, spec.order, &options)
                .expect("the captured batch rebuilds within its own budgets");
            assert_eq!(
                rebuilt, captured.matrix,
                "{}: the rebuild diverged from the captured matrix",
                spec.label
            );

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

            let mut micro = [Vec::new(), Vec::new()];
            let mut macro_ = [Vec::new(), Vec::new()];
            let mut refused = false;

            // Interleaved, so a drift in the machine's state over the run cannot be read as a
            // difference between the arms.
            for _ in 0..REPS {
                for (arm, (_, backend)) in ARMS.iter().enumerate() {
                    let mut matrix = captured.matrix.clone();
                    let started = Instant::now();
                    let outcome = eliminate_to(plan, form, *backend, &mut matrix, allowance)
                        .expect("within the allowance the live run used");
                    micro[arm].push(started.elapsed());
                    // Read the outcome, so the elimination cannot be optimized away.
                    assert!(outcome.statistics.rank <= matrix.num_rows());
                }

                for (arm, (name, backend)) in ARMS.iter().enumerate() {
                    let whole = F4Options {
                        elimination: *backend,
                        ..options
                    };
                    let started = Instant::now();
                    match f4_with_options(&captured.generators, spec.order, &whole) {
                        Ok((basis, _)) => {
                            macro_[arm].push(started.elapsed());
                            assert!(!basis.is_empty());
                        }
                        Err(error) => {
                            eprintln!(
                                "{}: the whole run refused under {}: {:?}",
                                spec.label, name, error
                            );
                            refused = true;
                        }
                    }
                }
                if refused {
                    break;
                }
            }

            self.rows.push(Row {
                label: spec.label,
                rows: captured.fingerprint.rows,
                columns: captured.fingerprint.columns,
                nonzeros: captured.fingerprint.nonzeros,
                micro: [median(&mut micro[0]), median(&mut micro[1])],
                macro_: if refused {
                    None
                } else {
                    Some([median(&mut macro_[0]), median(&mut macro_[1])])
                },
            });
        }
    }

    let mut predict = Predict { rows: Vec::new() };
    if let Err(error) = walk_corpus_with(&mut predict, true) {
        eprintln!("capture failed: {}", error);
        std::process::exit(1);
    }

    println!("| label | rows | cols | nz | micro sparse | micro adaptive | micro ratio | run sparse | run adaptive | run ratio | agree |");
    println!("|---|---|---|---|---|---|---|---|---|---|---|");
    let mut agreed = 0usize;
    let mut compared = 0usize;
    for row in &predict.rows {
        let micro_ratio = ratio(row.micro[0], row.micro[1]);
        let (whole, macro_cell, agree_cell) = match row.macro_ {
            Some(whole) => {
                let macro_ratio = ratio(whole[0], whole[1]);
                compared += 1;
                // The ranking, not the magnitude: both rankings pick the same arm, or they do not.
                let agree = (micro_ratio > 1.0) == (macro_ratio > 1.0);
                if agree {
                    agreed += 1;
                }
                (
                    format!("{:.3} ms | {:.3} ms", ms(whole[0]), ms(whole[1])),
                    format!("{:.2}x", macro_ratio),
                    (if agree { "yes" } else { "**NO**" }).to_string(),
                )
            }
            None => (
                "refused | refused".to_string(),
                "—".to_string(),
                "n/a".to_string(),
            ),
        };
        println!(
            "| `{}` | {} | {} | {} | {:.3} ms | {:.3} ms | {:.2}x | {} | {} | {} |",
            row.label,
            row.rows,
            row.columns,
            row.nonzeros,
            ms(row.micro[0]),
            ms(row.micro[1]),
            micro_ratio,
            whole,
            macro_cell,
            agree_cell
        );
    }
    println!(
        "\nrankings agreeing: {} of {} entries where both arms completed ({} entries total)",
        agreed,
        compared,
        predict.rows.len()
    );
}

fn median(samples: &mut [Duration]) -> Duration {
    samples.sort_unstable();
    samples[samples.len() / 2]
}

fn ms(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1e3
}

/// `a` over `b`, so above one means the second arm is faster.
fn ratio(a: Duration, b: Duration) -> f64 {
    if b.is_zero() {
        f64::INFINITY
    } else {
        a.as_secs_f64() / b.as_secs_f64()
    }
}
