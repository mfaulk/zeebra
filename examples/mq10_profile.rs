//! One digest-pinned MQ10 computation; stage clocks and passive work counters are independent controls.
use std::time::Instant;
use zeebra::{
    fields::{Zp2147483647, Zp32003},
    grobner::{
        differential::polynomial_to_string, external::corpus, f4_with_options, F4Options,
        F4Statistics,
    },
    util::Json,
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

#[cfg(feature = "research-work")]
#[path = "support/selective_backward.rs"]
mod selective_backward;

#[derive(Clone, Copy)]
struct RunMode<'a> {
    workers: Option<usize>,
    dynamic: bool,
    backward: Option<&'a str>,
}

#[cfg(feature = "research-work")]
struct ConcurrentObserver<'a> {
    backward: Option<&'a str>,
    config: zeebra::linalg::concurrent::Config,
    batches: Vec<Json>,
    fallbacks: usize,
}

#[cfg(feature = "research-work")]
impl<const N: usize, F: FiniteField + Send + Sync> zeebra::grobner::f4::BatchObserver<N, F>
    for ConcurrentObserver<'_>
{
    fn batch(
        &mut self,
        _: &zeebra::grobner::f4::symbolic::MonicBasis<N, F>,
        _: &[zeebra::grobner::pairs::CriticalPair<N>],
    ) {
    }

    fn eliminate(
        &mut self,
        matrix: &mut zeebra::grobner::f4::macaulay::MacaulayMatrix<N, F>,
        options: &F4Options,
    ) -> Option<Result<zeebra::grobner::f4::structured::BlockOutcome, usize>> {
        use zeebra::{
            grobner::{
                f4::structured::{check_reducer_block, BlockOutcome},
                ReductionStrategy,
            },
            linalg::{concurrent, sparse::back_substitute_pivots_within, Backend},
        };
        if options.reduction != ReductionStrategy::Structured
            || options.elimination != Backend::Adaptive
        {
            self.fallbacks += 1;
            return None;
        }
        let mut input_leads = vec![
            false;
            if self.backward.is_some() {
                matrix.num_columns()
            } else {
                0
            }
        ];
        if self.backward.is_some() {
            for row in matrix.matrix().rows() {
                if let Some(c) = row.leading_column() {
                    input_leads[c] = true;
                }
            }
        }
        let split = matrix.partition_reducers_first();
        check_reducer_block(matrix.matrix(), split).expect("symbolic reducer invariant");
        let config = concurrent::Config {
            max_entries: options.live_entry_allowance::<F>(),
            ..self.config
        };
        let digest = config
            .measure_work
            .then(|| zeebra::grobner::f4::matrix_corpus::digest_of(matrix));
        let started = Instant::now();
        let report = match concurrent::reduce(
            matrix.matrix_mut(),
            split,
            &config,
            &std::sync::atomic::AtomicBool::new(false),
        ) {
            Ok(report) => report,
            Err(concurrent::Error::Entries { .. } | concurrent::Error::Workspace { .. }) => {
                self.fallbacks += 1;
                return None;
            }
            Err(error) => panic!("concurrent elimination failed: {error:?}"),
        };
        let forward = started.elapsed();
        let mut statistics = report.statistics.clone();
        let started = Instant::now();
        let mut backward_details = Json::Null;
        let backward = if options.reduce_batch_rows && self.backward == Some("dense-selected") {
            let selected: Vec<_> = matrix
                .matrix()
                .rows()
                .iter()
                .map(|r| r.leading_column().is_some_and(|c| !input_leads[c]))
                .collect();
            let report = match zeebra::linalg::selective::reduce(
                matrix.matrix_mut(),
                &selected,
                config.max_entries,
                64 * 1024 * 1024,
                &mut statistics,
            ) {
                Ok(r) => r,
                Err(zeebra::linalg::selective::Error::Entries(n)) => return Some(Err(n)),
                Err(e) => panic!("selective research refusal: {e:?}"),
            };
            backward_details = selective_backward::details(&report);
            Some(report.targets)
        } else if options.reduce_batch_rows {
            match back_substitute_pivots_within(
                matrix.matrix_mut(),
                config.max_entries,
                &mut statistics,
            ) {
                Ok(rows) => Some(rows),
                Err(nonzeros) => return Some(Err(nonzeros)),
            }
        } else {
            None
        };
        let backward_time = started.elapsed();
        self.batches.push(Json::object([
            (
                "batch_index",
                Json::size(self.batches.len() + self.fallbacks),
            ),
            (
                "input_matrix_digest",
                digest.map_or(Json::Null, Json::string),
            ),
            ("rows", Json::size(matrix.num_rows())),
            ("columns", Json::size(matrix.num_columns())),
            ("split", Json::size(split)),
            ("forward_ns", Json::nanos(forward)),
            ("backward_ns", Json::nanos(backward_time)),
            ("backward_details", backward_details),
            ("successes", Json::size(report.successful_publications)),
            ("retries", Json::size(report.failed_publications)),
            ("products", Json::size(report.products)),
            ("inherited_products", Json::size(report.inherited_products)),
            (
                "discovered_products",
                Json::size(report.discovered_products),
            ),
            ("retry_products", Json::size(report.retry_products)),
            (
                "peak_reserved_entries",
                Json::size(report.peak_reserved_entries),
            ),
            ("workspace_bytes", Json::size(report.workspace_bytes)),
            ("scheduling_ns", Json::int(report.scheduling_ns)),
            ("publication_ns", Json::int(report.publication_ns)),
            ("work", report.work.json()),
            (
                "worker_rows",
                Json::Array(report.worker_rows.into_iter().map(Json::size).collect()),
            ),
            (
                "worker_ns",
                Json::Array(report.worker_ns.into_iter().map(Json::int).collect()),
            ),
        ]));
        Some(Ok(BlockOutcome {
            statistics,
            free_pivots: split,
            back_substituted_rows: backward,
        }))
    }
}

fn execute<T>(f: impl FnOnce() -> T) -> T {
    f()
}

fn statistics(s: &F4Statistics, measured: bool) -> Json {
    let time = |duration| {
        if measured {
            Json::nanos(duration)
        } else {
            Json::Null
        }
    };
    let t = s.stages;
    let c = t.construction_split;
    Json::object([
        ("total_ns", time(s.total)),
        ("symbolic_ns", time(t.symbolic)),
        ("construction_ns", time(t.construction)),
        ("elimination_ns", time(t.elimination)),
        ("extraction_ns", time(t.extraction)),
        ("interreduction_ns", time(t.interreduction)),
        ("other_ns", time(s.total.saturating_sub(t.sum()))),
        ("construction_collect_ns", time(c.collect)),
        ("construction_sort_ns", time(c.sort)),
        ("construction_map_ns", time(c.map)),
        ("construction_scatter_ns", time(c.scatter)),
        ("construction_scatter_rows_ns", time(c.scatter_rows)),
        ("construction_scatter_assemble_ns", time(c.scatter_assemble)),
        ("batches", Json::size(s.batches)),
        ("pairs_considered", Json::size(s.pairs_considered)),
        ("pairs_reduced", Json::size(s.pairs_reduced)),
        ("elements_added", Json::size(s.elements_added)),
        ("empty_batches", Json::size(s.empty_batches)),
        ("max_matrix_rows", Json::size(s.max_matrix_rows)),
        ("max_matrix_columns", Json::size(s.max_matrix_columns)),
        ("max_live_nonzeros", Json::size(s.max_live_nonzeros)),
        (
            "max_live_nonzeros_as_built",
            Json::size(s.max_live_nonzeros_as_built),
        ),
        ("row_operations", Json::size(s.row_operations)),
        ("reducer_rows_reused", Json::size(s.reducer_rows_reused)),
        ("divisor_queries", Json::size(s.divisor_queries)),
        ("divisor_scan_steps", Json::size(s.divisor_scan_steps)),
        ("peak_basis_elements", Json::size(s.peak_basis_elements)),
        ("peak_basis_terms", Json::size(s.peak_basis_terms)),
        (
            "degree_sequence",
            Json::Array(s.step_degrees.iter().map(|d| Json::int(*d)).collect()),
        ),
        (
            "candidate_reduction",
            Json::object([
                ("batches", Json::size(s.candidate_reduction.batches)),
                ("targets", Json::size(s.candidate_reduction.targets)),
                (
                    "coefficient_products",
                    Json::size(s.candidate_reduction.coefficient_products),
                ),
                (
                    "workspace_bytes",
                    Json::size(s.candidate_reduction.workspace_bytes),
                ),
                (
                    "reserved_entries",
                    Json::size(s.candidate_reduction.reserved_entries),
                ),
                (
                    "peak_sparse_capacity_entries",
                    Json::size(s.candidate_reduction.peak_sparse_capacity_entries),
                ),
                (
                    "fallback_batches",
                    Json::size(s.candidate_reduction.fallback_batches),
                ),
            ]),
        ),
        ("full_statistics", Json::string(format!("{s:#?}"))),
    ])
}

fn run<const N: usize, F: FiniteField + Send + Sync>(
    modulus: u64,
    measured: bool,
    measure_work: bool,
    discovery: bool,
    mode: RunMode<'_>,
    problem: &str,
) {
    let RunMode {
        workers,
        dynamic,
        backward,
    } = mode;
    let order = MonomialOrder::GradedReverseLexicographic;
    let input = corpus::instance(problem, modulus, order).expect("published corpus problem");
    let entry = corpus::ladder()
        .into_iter()
        .find(|e| e.name == input.name)
        .unwrap();
    assert_eq!(entry.digest_at(modulus), Some(input.digest().as_str()));
    assert_eq!(input.variables.len(), N);
    let names: [&str; N] = std::array::from_fn(|i| input.variables[i].as_str());
    let system: Vec<MultivariatePolynomial<N, F>> = input
        .system
        .iter()
        .map(|s| MultivariatePolynomial::parse(s, names).unwrap())
        .collect();
    let options = F4Options {
        measure_stages: measured,
        ..F4Options::default()
    };
    let started = Instant::now();
    #[cfg(feature = "research-work")]
    let mut observer = workers.map(|workers| ConcurrentObserver {
        backward,
        config: zeebra::linalg::concurrent::Config {
            workers,
            schedule: if dynamic {
                zeebra::linalg::concurrent::Schedule::Dynamic
            } else {
                zeebra::linalg::concurrent::Schedule::Static
            },
            measure_work,
            ..Default::default()
        },
        batches: Vec::new(),
        fallbacks: 0,
    });
    #[cfg(feature = "research-work")]
    let mut selective =
        backward
            .filter(|_| workers.is_none())
            .map(|mode| selective_backward::Observer {
                mode,
                detailed: measure_work,
                batches: Vec::new(),
            });
    let solve = || {
        #[cfg(feature = "research-work")]
        if let Some(observer) = selective.as_mut() {
            return zeebra::grobner::f4::f4_observed(&system, order, &options, observer)
                .expect("selective backward corpus computation failed");
        }
        #[cfg(feature = "research-work")]
        if let Some(observer) = observer.as_mut() {
            return zeebra::grobner::f4::f4_observed(&system, order, &options, observer)
                .expect("bounded concurrent corpus computation failed");
        }
        f4_with_options(&system, order, &options).expect("corpus computation failed")
    };
    #[cfg(feature = "research-work")]
    let ((basis, stats), work) = if measure_work {
        let (result, report) = if discovery {
            zeebra::linalg::work::measure_discovery(solve)
        } else {
            zeebra::linalg::work::measure(solve)
        };
        (result, Some(report))
    } else {
        (execute(solve), None)
    };
    #[cfg(not(feature = "research-work"))]
    let (basis, stats) = {
        assert!(
            backward.is_none(),
            "--backward requires --features research-work"
        );
        assert!(!discovery, "--discovery requires --features research-work");
        assert!(
            workers.is_none(),
            "--workers requires --features research-work"
        );
        assert!(!measure_work, "--work requires --features research-work");
        execute(solve)
    };
    let elapsed = started.elapsed();
    #[cfg(feature = "research-work")]
    let work = work.map_or(Json::Null, |report| report.json());
    #[cfg(not(feature = "research-work"))]
    let work = Json::Null;
    #[cfg(feature = "research-work")]
    let parallel = observer.map_or(Json::Null, |observer| {
        Json::object([
            ("workers", Json::size(observer.config.workers)),
            (
                "backward_mode",
                Json::string(observer.backward.unwrap_or("full")),
            ),
            ("dynamic", Json::Bool(dynamic)),
            ("fallbacks", Json::size(observer.fallbacks)),
            ("batches", Json::Array(observer.batches)),
        ])
    });
    #[cfg(not(feature = "research-work"))]
    let parallel = {
        let _ = dynamic;
        Json::Null
    };
    #[cfg(feature = "research-work")]
    let backward_report = selective.map_or(Json::Null, |o| {
        Json::object([
            ("mode", Json::string(o.mode)),
            ("batches", Json::Array(o.batches)),
        ])
    });
    #[cfg(not(feature = "research-work"))]
    let backward_report = Json::Null;
    let mut basis: Vec<_> = basis
        .iter()
        .map(|p| polynomial_to_string(p, &names, order))
        .collect();
    basis.sort();
    println!(
        "{}",
        Json::object([
            ("modulus", Json::int(modulus)),
            ("problem", Json::string(problem)),
            ("digest", Json::string(input.digest())),
            ("measured", Json::Bool(measured)),
            ("work", work),
            ("parallel", parallel),
            ("backward", backward_report),
            ("field_type", Json::string(std::any::type_name::<F>())),
            ("options", Json::string(format!("{options:?}"))),
            ("f4_call_ns", Json::nanos(elapsed)),
            (
                "peak_rss_bytes",
                zeebra::util::peak_resident_bytes()
                    .map(Json::int)
                    .unwrap_or(Json::Null)
            ),
            (
                "input",
                Json::object([
                    (
                        "variables",
                        Json::Array(input.variables.iter().cloned().map(Json::string).collect())
                    ),
                    (
                        "generators",
                        Json::Array(input.system.iter().cloned().map(Json::string).collect())
                    ),
                ])
            ),
            ("statistics", statistics(&stats, measured)),
            (
                "basis",
                Json::Array(basis.into_iter().map(Json::string).collect())
            ),
        ])
        .to_json()
    );
}

fn main() {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if args.first().is_some_and(|arg| arg == "dispatch") {
        assert_eq!(args.len(), 2, "usage: mq10_profile dispatch WORKERS");
        let workers: usize = args[1].parse().unwrap();
        assert!((1..=64).contains(&workers));
        let samples = (0..16)
            .map(|_| {
                let started = Instant::now();
                std::thread::scope(|scope| {
                    for _ in 0..workers {
                        scope.spawn(|| std::hint::black_box(()));
                    }
                });
                Json::nanos(started.elapsed())
            })
            .collect();
        println!(
            "{}",
            Json::object([
                ("workers", Json::size(workers)),
                ("samples_ns", Json::Array(samples))
            ])
            .to_json()
        );
        return;
    }
    let modulus: u64 = args
        .first()
        .expect("usage: mq10_profile MODULUS [--stages] [--work | --discovery] [--workers=P] [--schedule=dynamic|static] [--backward=full|dense-all|dense-selected]")
        .parse()
        .unwrap();
    assert!(
        args[1..].iter().all(|s| s == "--stages"
            || s == "--work"
            || s == "--discovery"
            || s.starts_with("--workers=")
            || s.starts_with("--problem=")
            || s.starts_with("--backward=")
            || s == "--schedule=dynamic"
            || s == "--schedule=static")
            && args[1..]
                .iter()
                .collect::<std::collections::HashSet<_>>()
                .len()
                == args.len() - 1,
        "unexpected argument"
    );
    let measured = args.iter().any(|s| s == "--stages");
    let discovery = args.iter().any(|s| s == "--discovery");
    assert!(
        !(discovery && args.iter().any(|s| s == "--work")),
        "choose --work or --discovery"
    );
    let measure_work = discovery || args.iter().any(|s| s == "--work");
    let worker_args: Vec<_> = args
        .iter()
        .filter_map(|s| s.strip_prefix("--workers="))
        .collect();
    assert!(worker_args.len() <= 1, "one worker count required");
    let workers = worker_args
        .first()
        .map(|s| s.parse::<usize>().expect("integer workers"));
    assert!(workers != Some(0), "workers must be positive");
    let schedules: Vec<_> = args
        .iter()
        .filter(|s| s.starts_with("--schedule="))
        .collect();
    assert!(
        schedules.len() <= 1 && (schedules.is_empty() || workers.is_some()),
        "one schedule requires workers"
    );
    assert!(
        !discovery || workers.is_none(),
        "discovery observes the serial control only"
    );
    let dynamic = !args.iter().any(|s| s == "--schedule=static");
    let problems: Vec<_> = args
        .iter()
        .filter_map(|s| s.strip_prefix("--problem="))
        .collect();
    assert!(problems.len() <= 1, "one problem required");
    let problem = problems.first().copied().unwrap_or("mq-random-10");
    let backwards: Vec<_> = args
        .iter()
        .filter_map(|s| s.strip_prefix("--backward="))
        .collect();
    assert!(backwards.len() <= 1, "one backward policy required");
    let backward = backwards.first().copied();
    assert!(
        backward.is_none_or(|p| matches!(p, "full" | "dense-all" | "dense-selected")),
        "unknown backward policy"
    );
    assert!(
        backward.is_none() || (!discovery && (workers.is_none() || backward != Some("dense-all"))),
        "dense-all requires serial forward; backward policies exclude discovery"
    );
    let mode = RunMode {
        workers,
        dynamic,
        backward,
    };
    macro_rules! run_field {
        ($field:ty) => {
            match problem {
                "mq-random-10" => {
                    run::<10, $field>(modulus, measured, measure_work, discovery, mode, problem)
                }
                "mq-random-14" => {
                    run::<14, $field>(modulus, measured, measure_work, discovery, mode, problem)
                }
                "katsura-6" => {
                    run::<6, $field>(modulus, measured, measure_work, discovery, mode, problem)
                }
                "cyclic-5" => {
                    run::<5, $field>(modulus, measured, measure_work, discovery, mode, problem)
                }
                _ => panic!("supported problems: mq-random-10, mq-random-14, katsura-6, cyclic-5"),
            }
        };
    }
    match modulus {
        32003 => run_field!(Zp32003),
        2147483647 => run_field!(Zp2147483647),
        _ => panic!("supported moduli: 32003, 2147483647"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    // Selective and all-target research policies return the exact ordinary basis and pair schedule.
    #[cfg(feature = "research-work")]
    #[test]
    fn backward_policies_preserve_complete_solves() {
        use zeebra::grobner::{
            benchmark_systems::{cyclic, katsura},
            f4::f4_observed,
        };
        for system in [cyclic::<4, Zp32003>(), katsura::<4, Zp32003>()] {
            for order in [
                MonomialOrder::GradedReverseLexicographic,
                MonomialOrder::Lexicographic,
            ] {
                let options = F4Options::default();
                let (expected, original) = f4_with_options(&system, order, &options).unwrap();
                for mode in ["full", "dense-all", "dense-selected"] {
                    let mut observer = selective_backward::Observer {
                        mode,
                        detailed: true,
                        batches: Vec::new(),
                    };
                    let (basis, actual) =
                        f4_observed(&system, order, &options, &mut observer).unwrap();
                    assert_eq!(basis, expected, "{mode}");
                    assert_eq!(actual.batches, original.batches);
                    assert_eq!(actual.step_degrees, original.step_degrees);
                    assert!(!observer.batches.is_empty());
                }
            }
        }
    }

    // Concurrent forward pivots compose with candidate-only backward reduction without changing a basis.
    #[cfg(feature = "research-work")]
    #[test]
    fn concurrent_forward_accepts_selective_backward() {
        use zeebra::grobner::{
            benchmark_systems::{cyclic, katsura},
            f4::f4_observed,
        };
        for system in [cyclic::<4, Zp32003>(), katsura::<4, Zp32003>()] {
            let options = F4Options::default();
            let order = MonomialOrder::GradedReverseLexicographic;
            let expected = f4_with_options(&system, order, &options).unwrap().0;
            for workers in [1, 4] {
                let mut observer = ConcurrentObserver {
                    config: zeebra::linalg::concurrent::Config {
                        workers,
                        ..Default::default()
                    },
                    backward: Some("dense-selected"),
                    batches: Vec::new(),
                    fallbacks: 0,
                };
                let actual = f4_observed(&system, order, &options, &mut observer)
                    .unwrap()
                    .0;
                assert_eq!(actual, expected);
                assert_eq!(observer.fallbacks, 0);
            }
        }
    }

    // Refining timers are excluded from the partition, so stage shares never double count them.
    #[test]
    fn stage_partition_excludes_refinements() {
        let mut s = F4Statistics {
            total: Duration::from_millis(20),
            ..Default::default()
        };
        s.stages.symbolic = Duration::from_millis(3);
        s.stages.construction = Duration::from_millis(4);
        s.stages.construction_split.scatter = Duration::from_millis(4);
        s.stages.elimination = Duration::from_millis(8);
        s.stages.extraction = Duration::from_millis(1);
        s.stages.interreduction = Duration::from_millis(2);
        s.stages.interreduction_reduce = Duration::from_millis(2);
        let report = statistics(&s, true);
        assert_eq!(
            report.get("other_ns").and_then(Json::as_int),
            Some(2_000_000)
        );
        assert_eq!(
            report.get("total_ns").and_then(Json::as_int),
            Some(20_000_000)
        );
    }

    // Disabled clocks remain absent rather than publishing zero as a measured stage duration.
    #[test]
    fn disabled_clocks_are_absent() {
        assert_eq!(
            statistics(&F4Statistics::default(), false).get("total_ns"),
            Some(&Json::Null)
        );
    }
}
