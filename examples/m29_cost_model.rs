//! One fresh-process F4 run of a frozen M29 target (#834) on the shipping defaults; only the
//! forward-worker cap, the pair-multiple policy and the opt-in stage clocks are varied. Process wall
//! belongs to the caller: stage clocks cost MQ10 3.8–11.5%, so timed and clocked runs are separate.
//!
//! cargo run --release --features external-runners --example m29_cost_model -- \
//!     --target mq10-32003 --workers 16 [--stages] [--pair-multiples every|distinct]
//!     [--batch-order forward|fl] [--hilbert off|observe|limited+N|deferred+N] [--wall-s 180]
//!
//! With `--features research-work`, `--work` adds the serial thread-local entry-operation census
//! and `--discovery` splits forward products into inherited-pivot and newly-discovered-pivot work.
use std::time::{Duration, Instant};
use zeebra::{
    fields::{PrimeFieldElement64, Zp2147483647, Zp32003},
    grobner::{
        differential::polynomial_to_string, external::corpus, f4_reported, BatchOrder, F4Options,
        F4Statistics, HilbertSelection, PairMultiples, ParallelForward,
    },
    util::{peak_resident_bytes, sha256_hex, Json},
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

type Goldilocks = PrimeFieldElement64<18446744069414584321>;
type Wide = PrimeFieldElement64<18446744073709551263>;
const ORDER: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

/// The four M29 targets — MQ10 at both #820 primes, #821's preferred wide-field rows — and
/// #859's Katsura-11 / 2^31-1, the instance #827 priced level-parallel symbolic on.
const TARGETS: &[&str] = &[
    "mq10-32003",
    "mq10-m31",
    "eco12-wide64",
    "mq11-goldilocks",
    "katsura11-m31",
];

#[derive(Debug, PartialEq)]
struct Args {
    target: String,
    workers: usize,
    stages: bool,
    pair_multiples: PairMultiples,
    batch_order: BatchOrder,
    wall: Duration,
    work: bool,
    discovery: bool,
    hilbert: HilbertSelection,
}

fn parse_args(args: &[String]) -> Result<Args, String> {
    let mut parsed = Args {
        target: String::new(),
        workers: 0,
        stages: false,
        pair_multiples: F4Options::default().pair_multiples,
        batch_order: F4Options::default().batch_order,
        wall: Duration::from_secs(180),
        work: false,
        discovery: false,
        hilbert: HilbertSelection::Off,
    };
    let mut it = args.iter();
    while let Some(arg) = it.next() {
        let mut value = || it.next().cloned().ok_or(format!("{arg} needs a value"));
        match arg.as_str() {
            "--target" => parsed.target = value()?,
            "--workers" => {
                parsed.workers = value()?
                    .parse()
                    .ok()
                    .filter(|&w| w > 0)
                    .ok_or("--workers takes a positive integer")?
            }
            "--stages" => parsed.stages = true,
            "--pair-multiples" => {
                parsed.pair_multiples = match value()?.as_str() {
                    "every" => PairMultiples::Every,
                    "distinct" => PairMultiples::Distinct,
                    other => return Err(format!("unknown pair-multiple policy {other}")),
                }
            }
            "--batch-order" => {
                parsed.batch_order = match value()?.as_str() {
                    "forward" => BatchOrder::Forward,
                    "fl" => BatchOrder::FaugereLachartre,
                    other => return Err(format!("unknown batch order {other}")),
                }
            }
            "--hilbert" => {
                let mode = value()?;
                let slack = |prefix: &str| {
                    mode[prefix.len()..]
                        .parse()
                        .map_err(|_| format!("{prefix}N takes a whole slack"))
                };
                parsed.hilbert = match mode.as_str() {
                    "off" => HilbertSelection::Off,
                    "observe" => HilbertSelection::Observe,
                    m if m.starts_with("limited+") => HilbertSelection::CertifiedLimited {
                        slack: slack("limited+")?,
                    },
                    m if m.starts_with("deferred+") => HilbertSelection::Deferred {
                        slack: slack("deferred+")?,
                    },
                    other => return Err(format!("unknown Hilbert selection {other}")),
                }
            }
            "--wall-s" => {
                parsed.wall = Duration::from_secs(
                    value()?
                        .parse()
                        .map_err(|_| "--wall-s takes whole seconds")?,
                )
            }
            "--work" => parsed.work = true,
            "--discovery" => parsed.discovery = true,
            other => return Err(format!("unexpected argument {other}")),
        }
    }
    if !TARGETS.contains(&parsed.target.as_str()) {
        return Err(format!("--target must be one of {TARGETS:?}"));
    }
    if parsed.workers == 0 {
        return Err("--workers is required".into());
    }
    if (parsed.work || parsed.discovery) && parsed.workers != 1 {
        // The census is thread-local: worker threads' arithmetic would go uncounted.
        return Err("--work and --discovery observe the serial route only".into());
    }
    if parsed.work && parsed.discovery {
        return Err("choose --work or --discovery".into());
    }
    Ok(parsed)
}

/// Shipping defaults with forward elimination serial at one worker and capped at `workers` above.
fn options(args: &Args) -> F4Options {
    F4Options {
        measure_stages: args.stages,
        max_wall_time: Some(args.wall),
        pair_multiples: args.pair_multiples,
        batch_order: args.batch_order,
        hilbert: args.hilbert,
        parallel_forward: if args.workers == 1 {
            ParallelForward::Serial
        } else {
            ParallelForward::Auto {
                max_workers: args.workers,
            }
        },
        ..F4Options::default()
    }
}

struct Input {
    modulus: String,
    digest: String,
    variables: Vec<String>,
    generators: Vec<String>,
}

fn ladder(problem: &str, modulus: u64) -> Input {
    let input = corpus::instance(problem, modulus, ORDER).expect("published ladder row");
    let entry = corpus::ladder()
        .into_iter()
        .find(|e| e.name == input.name)
        .expect("ladder entry");
    assert_eq!(entry.digest_at(modulus), Some(input.digest().as_str()));
    Input {
        modulus: modulus.to_string(),
        digest: input.digest(),
        variables: input.variables.clone(),
        generators: input.system.clone(),
    }
}

/// Read a frozen #738 row and refuse it unless its canonical text still hashes to its digest.
fn wide(field: &str, name: &str) -> Input {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/research/wide-corpus/cases.json"
    );
    let cases = Json::parse(&std::fs::read_to_string(path).expect("frozen wide catalog")).unwrap();
    let case = cases
        .items()
        .iter()
        .find(|c| {
            c.get("field").and_then(Json::as_str) == Some(field)
                && c.get("name").and_then(Json::as_str) == Some(name)
        })
        .expect("frozen wide row");
    let text = |key| case.get(key).and_then(Json::as_str).unwrap().to_string();
    let strings = |key| -> Vec<String> {
        case.get(key)
            .unwrap()
            .items()
            .iter()
            .map(|s| s.as_str().unwrap().to_string())
            .collect()
    };
    let digest = text("digest");
    assert_eq!(sha256_hex(text("canonical").as_bytes()), digest);
    Input {
        modulus: text("modulus"),
        digest,
        variables: strings("variables"),
        generators: strings("generators"),
    }
}

fn statistics(s: &F4Statistics, stages: bool) -> Json {
    let time = |d: Duration| if stages { Json::nanos(d) } else { Json::Null };
    let t = s.stages;
    let c = t.construction_split;
    let pf = s.parallel_forward;
    let cr = s.candidate_reduction;
    Json::object([
        ("total_ns", time(s.total)),
        ("symbolic_ns", time(t.symbolic)),
        ("construction_ns", time(t.construction)),
        ("elimination_ns", time(t.elimination)),
        ("forward_ns", time(t.forward)),
        ("backward_ns", time(t.backward)),
        ("extraction_ns", time(t.extraction)),
        ("interreduction_ns", time(t.interreduction)),
        ("interreduction_reduce_ns", time(t.interreduction_reduce)),
        ("other_ns", time(s.total.saturating_sub(t.sum()))),
        ("construction_collect_ns", time(c.collect)),
        ("construction_sort_ns", time(c.sort)),
        ("construction_map_ns", time(c.map)),
        ("construction_scatter_ns", time(c.scatter)),
        ("batches", Json::size(s.batches)),
        ("structured_batches", Json::size(s.structured_batches)),
        ("pairs_considered", Json::size(s.pairs_considered)),
        ("pairs_reduced", Json::size(s.pairs_reduced)),
        (
            "pair_multiples_removed",
            Json::size(s.pair_multiples_removed),
        ),
        ("elements_added", Json::size(s.elements_added)),
        ("reducer_rows", Json::size(s.reducer_rows)),
        ("reducer_rows_reused", Json::size(s.reducer_rows_reused)),
        ("max_matrix_rows", Json::size(s.max_matrix_rows)),
        ("max_matrix_columns", Json::size(s.max_matrix_columns)),
        (
            "total_initial_nonzeros",
            Json::size(s.total_initial_nonzeros),
        ),
        ("total_final_nonzeros", Json::size(s.total_final_nonzeros)),
        ("max_live_nonzeros", Json::size(s.max_live_nonzeros)),
        (
            "max_live_nonzeros_as_built",
            Json::size(s.max_live_nonzeros_as_built),
        ),
        (
            "live_entry_requirement",
            Json::size(s.live_entry_requirement()),
        ),
        ("bytes_per_entry", Json::size(s.bytes_per_entry)),
        (
            "max_dense_buffer_bytes",
            Json::size(s.max_dense_buffer_bytes),
        ),
        ("max_estimated_bytes", Json::size(s.max_estimated_bytes)),
        ("row_operations", Json::size(s.row_operations)),
        ("pivot_inversions", Json::size(s.pivot_inversions)),
        ("zero_rows", Json::size(s.zero_rows)),
        ("free_pivots", Json::size(s.free_pivots)),
        (
            "candidate_rank_contribution",
            Json::size(s.candidate_rank_contribution),
        ),
        (
            "dependent_candidate_rows",
            Json::size(s.dependent_candidate_rows),
        ),
        (
            "interreduction_elements",
            Json::size(s.interreduction_elements),
        ),
        ("peak_basis_elements", Json::size(s.peak_basis_elements)),
        ("peak_basis_terms", Json::size(s.peak_basis_terms)),
        ("monomials_enqueued", Json::size(s.monomials_enqueued)),
        ("divisor_queries", Json::size(s.divisor_queries)),
        (
            "parallel_forward",
            Json::object([
                ("batches", Json::size(pf.batches)),
                ("fallback_batches", Json::size(pf.fallback_batches)),
                ("max_workers", Json::size(pf.max_workers)),
                ("lost_publications", Json::size(pf.lost_publications)),
                ("reserved_entries", Json::size(pf.reserved_entries)),
                ("workspace_bytes", Json::size(pf.workspace_bytes)),
            ]),
        ),
        (
            "candidate_reduction",
            Json::object([
                ("batches", Json::size(cr.batches)),
                ("targets", Json::size(cr.targets)),
                ("coefficient_products", Json::size(cr.coefficient_products)),
                ("workspace_bytes", Json::size(cr.workspace_bytes)),
                ("reserved_entries", Json::size(cr.reserved_entries)),
                (
                    "peak_sparse_capacity_entries",
                    Json::size(cr.peak_sparse_capacity_entries),
                ),
                ("fallback_batches", Json::size(cr.fallback_batches)),
                ("parallel_batches", Json::size(cr.parallel_batches)),
                ("max_workers", Json::size(cr.max_workers)),
            ]),
        ),
        (
            "degree_sequence",
            Json::Array(s.step_degrees.iter().map(|d| Json::int(*d)).collect()),
        ),
        ("full_statistics", Json::string(format!("{s:#?}"))),
    ])
}

/// Per-batch census rows plus totals; per-row discovery records are summed, not printed.
#[cfg(feature = "research-work")]
fn census(report: &zeebra::linalg::work::WorkReport) -> Json {
    use zeebra::linalg::work::PhaseWork;
    let mut forward = PhaseWork::default();
    let mut backward = PhaseWork::default();
    let (mut inherited, mut discovered) = (0usize, 0usize);
    let batches: Vec<Json> = report
        .batches
        .iter()
        .map(|b| {
            forward.accumulate(&b.forward);
            backward.accumulate(&b.backward);
            let i: usize = b.discovery.iter().map(|r| r.inherited_products).sum();
            let d: usize = b.discovery.iter().map(|r| r.discovered_products).sum();
            inherited += i;
            discovered += d;
            // Rows that end zero: work a criterion that predicted the dependency would not pay.
            let zero =
                |r: &&zeebra::linalg::work::DiscoveryRow| r.completed && r.pivot_column.is_none();
            let zero_rows = b.discovery.iter().filter(zero).count();
            let zero_products: usize = b
                .discovery
                .iter()
                .filter(zero)
                .map(|r| r.inherited_products + r.discovered_products)
                .sum();
            let zero_ns: u64 = b.discovery.iter().filter(zero).map(|r| r.elapsed_ns).sum();
            let row_ns: u64 = b.discovery.iter().map(|r| r.elapsed_ns).sum();
            Json::object([
                ("zero_rows", Json::size(zero_rows)),
                ("zero_row_products", Json::size(zero_products)),
                ("zero_row_ns", Json::int(zero_ns)),
                ("row_ns", Json::int(row_ns)),
                ("degree", Json::int(b.degree)),
                ("pairs", Json::size(b.pairs)),
                ("rows", Json::size(b.rows)),
                ("reducer_rows", Json::size(b.reducer_rows)),
                ("columns", Json::size(b.columns)),
                ("initial_entries", Json::size(b.initial_entries)),
                ("rank", Json::size(b.rank)),
                ("final_entries", Json::size(b.final_entries)),
                (
                    "peak_mathematical_entries",
                    Json::size(b.peak_mathematical_entries),
                ),
                (
                    "forward_products",
                    Json::size(b.forward.coefficient_products),
                ),
                (
                    "forward_applications",
                    Json::size(b.forward.pivot_applications),
                ),
                (
                    "backward_products",
                    Json::size(b.backward.coefficient_products),
                ),
                ("inherited_products", Json::size(i)),
                ("discovered_products", Json::size(d)),
            ])
        })
        .collect();
    Json::object([
        ("forward", forward.json()),
        ("backward", backward.json()),
        ("outside_batch", report.outside_batch.forward.json()),
        ("inherited_products", Json::size(inherited)),
        ("discovered_products", Json::size(discovered)),
        ("batches", Json::Array(batches)),
    ])
}

fn run<const N: usize, F: FiniteField>(input: Input, args: &Args) -> Json {
    let names: [&str; N] = std::array::from_fn(|i| input.variables[i].as_str());
    let system: Vec<MultivariatePolynomial<N, F>> = input
        .generators
        .iter()
        .map(|s| MultivariatePolynomial::parse(s, names).expect("generator parses"))
        .collect();
    let options = options(args);
    let solve = || f4_reported(&system, ORDER, &options);
    let started = Instant::now();
    #[cfg(feature = "research-work")]
    let ((result, stats), work) = if args.discovery {
        let (r, w) = zeebra::linalg::work::measure_discovery(solve);
        (r, census(&w))
    } else if args.work {
        let (r, w) = zeebra::linalg::work::measure(solve);
        (r, census(&w))
    } else {
        (solve(), Json::Null)
    };
    #[cfg(not(feature = "research-work"))]
    let ((result, stats), work) = {
        assert!(
            !args.work && !args.discovery,
            "--work and --discovery require --features research-work"
        );
        (solve(), Json::Null)
    };
    let elapsed = started.elapsed();
    let (status, basis) = match &result {
        Ok(basis) => {
            let mut text: Vec<_> = basis
                .iter()
                .map(|p| polynomial_to_string(p, &names, ORDER))
                .collect();
            text.sort();
            ("complete".to_string(), Some(text))
        }
        Err(error) => (format!("stopped: {error}"), None),
    };
    Json::object([
        ("target", Json::string(&args.target)),
        ("modulus", Json::string(&input.modulus)),
        ("digest", Json::string(&input.digest)),
        ("field_type", Json::string(std::any::type_name::<F>())),
        ("workers", Json::size(args.workers)),
        ("stages", Json::Bool(args.stages)),
        (
            "pair_multiples",
            Json::string(format!("{:?}", args.pair_multiples)),
        ),
        (
            "batch_order",
            Json::string(format!("{:?}", args.batch_order)),
        ),
        ("options", Json::string(format!("{options:?}"))),
        ("status", Json::string(status)),
        ("f4_call_ns", Json::nanos(elapsed)),
        (
            "peak_rss_bytes",
            peak_resident_bytes().map(Json::int).unwrap_or(Json::Null),
        ),
        (
            "basis_elements",
            basis.as_ref().map_or(Json::Null, |b| Json::size(b.len())),
        ),
        (
            "basis_sha256",
            basis.as_ref().map_or(Json::Null, |b| {
                Json::string(sha256_hex(b.join("\n").as_bytes()))
            }),
        ),
        ("statistics", statistics(&stats, args.stages)),
        ("work", work),
    ])
}

fn main() {
    let raw: Vec<String> = std::env::args().skip(1).collect();
    let args = parse_args(&raw).unwrap_or_else(|e| panic!("{e}"));
    let report = match args.target.as_str() {
        "mq10-32003" => run::<10, Zp32003>(ladder("mq-random-10", 32003), &args),
        "mq10-m31" => run::<10, Zp2147483647>(ladder("mq-random-10", 2147483647), &args),
        "katsura11-m31" => run::<11, Zp2147483647>(ladder("katsura-11", 2147483647), &args),
        "eco12-wide64" => run::<12, Wide>(wide("wide64", "eco-12"), &args),
        "mq11-goldilocks" => run::<11, Goldilocks>(wide("goldilocks", "mq-random-11"), &args),
        _ => unreachable!(),
    };
    println!("{}", report.to_json().replace('\n', ""));
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(list: &[&str]) -> Result<Args, String> {
        parse_args(&list.iter().map(|s| s.to_string()).collect::<Vec<_>>())
    }

    // One worker is serial forward elimination and more caps the adaptive default; nothing else moves.
    #[test]
    fn workers_map_to_the_forward_policy_and_keep_defaults() {
        let one = options(&args(&["--target", "mq10-32003", "--workers", "1"]).unwrap());
        assert_eq!(one.parallel_forward, ParallelForward::Serial);
        let sixteen = options(&args(&["--target", "mq10-m31", "--workers", "16"]).unwrap());
        assert_eq!(
            sixteen.parallel_forward,
            ParallelForward::Auto { max_workers: 16 }
        );
        let default = F4Options::default();
        assert_eq!(sixteen.pair_multiples, default.pair_multiples);
        assert_eq!(sixteen.reduction, default.reduction);
        assert_eq!(sixteen.elimination, default.elimination);
        assert_eq!(sixteen.max_live_bytes, default.max_live_bytes);
        assert!(!sixteen.measure_stages);
    }

    // The pre-#831 arm is selectable, and an unknown policy, target or worker count is refused.
    #[test]
    fn arguments_are_validated() {
        let every = args(&[
            "--target",
            "eco12-wide64",
            "--workers",
            "4",
            "--pair-multiples",
            "every",
            "--stages",
        ])
        .unwrap();
        assert_eq!(options(&every).pair_multiples, PairMultiples::Every);
        assert!(options(&every).measure_stages);
        assert!(args(&["--target", "katsura-11", "--workers", "1"]).is_err());
        assert!(args(&["--target", "katsura11-m31", "--workers", "1"]).is_ok());
        assert!(args(&["--target", "mq10-32003", "--workers", "0"]).is_err());
        assert!(args(&["--target", "mq10-32003"]).is_err());
        assert!(args(&[
            "--target",
            "mq10-32003",
            "--workers",
            "1",
            "--pair-multiples",
            "x"
        ])
        .is_err());
    }

    // Each Hilbert selection mode parses to its policy with its slack, and off is the default.
    #[test]
    fn hilbert_selection_is_selectable() {
        let base = ["--target", "mq11-goldilocks", "--workers", "1"];
        let with = |mode: &str| args(&[&base[..], &["--hilbert", mode]].concat());
        assert_eq!(
            options(&args(&base).unwrap()).hilbert,
            HilbertSelection::Off
        );
        assert_eq!(
            options(&with("observe").unwrap()).hilbert,
            HilbertSelection::Observe
        );
        assert_eq!(
            options(&with("limited+100").unwrap()).hilbert,
            HilbertSelection::CertifiedLimited { slack: 100 }
        );
        assert_eq!(
            options(&with("deferred+0").unwrap()).hilbert,
            HilbertSelection::Deferred { slack: 0 }
        );
        assert!(with("limited+x").is_err());
        assert!(with("sometimes").is_err());
    }

    // The opt-in Faugère–Lachartre order is selectable for #828's cross-check; forward is the default.
    #[test]
    fn batch_order_is_selectable() {
        let base = ["--target", "eco12-wide64", "--workers", "16"];
        assert_eq!(
            options(&args(&base).unwrap()).batch_order,
            F4Options::default().batch_order
        );
        let fl = args(&[&base[..], &["--batch-order", "fl"]].concat()).unwrap();
        assert_eq!(options(&fl).batch_order, BatchOrder::FaugereLachartre);
        let fwd = args(&[&base[..], &["--batch-order", "forward"]].concat()).unwrap();
        assert_eq!(options(&fwd).batch_order, BatchOrder::Forward);
        assert!(args(&[&base[..], &["--batch-order", "x"]].concat()).is_err());
    }

    // The thread-local census would miss worker threads, so it is refused above one worker.
    #[test]
    fn census_is_serial_only() {
        assert!(args(&["--target", "mq10-32003", "--workers", "4", "--work"]).is_err());
        assert!(args(&[
            "--target",
            "mq10-32003",
            "--workers",
            "1",
            "--work",
            "--discovery"
        ])
        .is_err());
        assert!(args(&["--target", "mq10-32003", "--workers", "1", "--discovery"]).is_ok());
    }

    // Both wide rows are read from the frozen #738 catalog and still hash to their pinned digests.
    #[test]
    fn wide_targets_match_their_frozen_digests() {
        let eco = wide("wide64", "eco-12");
        assert_eq!(
            eco.digest,
            "e9ef0fecf3906d9283e1ce003c4489d6921fb8718f2956c39c4aaa79e52a93cb"
        );
        assert_eq!(eco.variables.len(), 12);
        let mq = wide("goldilocks", "mq-random-11");
        assert_eq!(
            mq.digest,
            "ee76de455c5ea571d6e8286152a4b4380b9d1ea323ee63dc8f889ffa11a92af5"
        );
        assert_eq!(mq.generators.len(), 11);
    }

    // #859's Katsura-11 row is the published ladder row at 2^31-1, checked against its digest.
    #[test]
    fn katsura_target_matches_its_ladder_digest() {
        let k = ladder("katsura-11", 2147483647);
        assert_eq!(k.variables.len(), 11);
        assert_eq!(k.modulus, "2147483647");
    }
}
