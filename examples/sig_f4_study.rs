//! One fresh-process run of the #857 signature engine or the shipping F4 on a frozen wide-corpus
//! row; process wall belongs to the caller (`research/m30-sigf4/run.py`).
//!
//! cargo run --release --features research-sigf4 --example sig_f4_study -- \
//!     --field wide64 --name eco-12 --engine sigf4|f4 [--workers 16] [--wall-s 600] [--certify]
//!
//! `--basis` prints the reduced basis's SHA-256 (sorted rendered text), which is how two engines'
//! outputs are compared coefficient for coefficient without holding both in one process. With
//! `--features research-work`, `--discovery` adds the shipping F4's serial census: forward and
//! backward coefficient products and those on rows that end zero (#835's instrument).
//!
//! With `--features research-sigf4-replay`, `--replay` (sigf4, `--workers ≥ 2`) runs design 1
//! twice, without and with recording, then design 2 recorded, and prints #902's cascade records
//! and schedule ceilings instead of a timing row; it refuses if recording moved any algebraic
//! quantity (`docs/research/m31-parallel-signature-elimination.md`).
use std::time::{Duration, Instant};
use zeebra::{
    fields::PrimeFieldElement64,
    grobner::{
        certify_f4_output,
        differential::polynomial_to_string,
        f4_reported,
        sigf4::{sig_f4_reported, SigF4Options, SigF4Statistics},
        F4Options, ParallelForward, ParallelSymbolic,
    },
    util::{peak_resident_bytes, sha256_hex, Json},
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

type Goldilocks = PrimeFieldElement64<18446744069414584321>;
type Wide = PrimeFieldElement64<18446744073709551263>;
const ORDER: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

#[derive(Debug, PartialEq)]
struct Args {
    field: String,
    name: String,
    engine: String,
    workers: usize,
    wall: Duration,
    certify: bool,
    discovery: bool,
    replay: bool,
}

fn parse_args(args: &[String]) -> Result<Args, String> {
    let mut parsed = Args {
        field: String::new(),
        name: String::new(),
        engine: String::new(),
        workers: 1,
        wall: Duration::from_secs(600),
        certify: false,
        discovery: false,
        replay: false,
    };
    let mut it = args.iter();
    while let Some(arg) = it.next() {
        let mut value = || it.next().cloned().ok_or(format!("{arg} needs a value"));
        match arg.as_str() {
            "--field" => parsed.field = value()?,
            "--name" => parsed.name = value()?,
            "--engine" => parsed.engine = value()?,
            "--workers" => {
                parsed.workers = value()?
                    .parse()
                    .ok()
                    .filter(|&w| w > 0)
                    .ok_or("--workers takes a positive integer")?
            }
            "--wall-s" => {
                parsed.wall = Duration::from_secs(value()?.parse().map_err(|_| "--wall-s")?)
            }
            "--certify" => parsed.certify = true,
            "--discovery" => parsed.discovery = true,
            "--replay" => parsed.replay = true,
            other => return Err(format!("unexpected argument {other}")),
        }
    }
    if !["goldilocks", "wide64"].contains(&parsed.field.as_str()) {
        return Err("--field must be goldilocks or wide64".into());
    }
    if !["sigf4", "f4"].contains(&parsed.engine.as_str()) {
        return Err("--engine must be sigf4 or f4".into());
    }
    if parsed.discovery && (parsed.engine != "f4" || parsed.workers != 1) {
        return Err("--discovery observes the serial shipping F4 only".into());
    }
    if parsed.replay && (parsed.engine != "sigf4" || parsed.workers < 2) {
        return Err("--replay runs design 1 and design 2: --engine sigf4 --workers ≥ 2".into());
    }
    Ok(parsed)
}

/// Shipping defaults; only the forward and symbolic worker caps vary, as in `m29_cost_model`.
fn f4_options(args: &Args) -> F4Options {
    F4Options {
        max_wall_time: Some(args.wall),
        parallel_forward: if args.workers == 1 {
            ParallelForward::Serial
        } else {
            ParallelForward::Auto {
                max_workers: args.workers,
            }
        },
        parallel_symbolic: if args.workers == 1 {
            ParallelSymbolic::Serial
        } else {
            ParallelSymbolic::Auto {
                max_workers: args.workers,
            }
        },
        ..F4Options::default()
    }
}

struct Input {
    digest: String,
    variables: Vec<String>,
    generators: Vec<String>,
}

/// A frozen #738 row, refused unless its canonical text still hashes to its digest.
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
        .unwrap_or_else(|| panic!("no frozen row {field}/{name}"));
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
        digest,
        variables: strings("variables"),
        generators: strings("generators"),
    }
}

fn sig_statistics(s: &SigF4Statistics) -> Json {
    let size = |v: usize| Json::size(v);
    Json::object([
        ("batches", size(s.batches)),
        ("pairs_created", size(s.pairs_created)),
        ("pairs_singular", size(s.pairs_singular)),
        ("rejected_product", size(s.rejected_product)),
        ("rejected_koszul", size(s.rejected_koszul)),
        ("rejected_zero_row", size(s.rejected_zero_row)),
        ("rejected_rewrite", size(s.rejected_rewrite)),
        ("rejected_duplicate", size(s.rejected_duplicate)),
        ("targets", size(s.targets)),
        ("reducer_rows", size(s.reducer_rows)),
        ("reductions_to_zero", size(s.reductions_to_zero)),
        ("zero_rows", size(s.zero_rows)),
        ("singular_rows", size(s.singular_rows)),
        ("rows_adding_no_rank", size(s.rows_adding_no_rank)),
        ("coefficient_products", Json::int(s.coefficient_products)),
        ("products_on_zero_rows", Json::int(s.products_on_zero_rows)),
        (
            "products_on_singular_rows",
            Json::int(s.products_on_singular_rows),
        ),
        ("max_matrix_rows", size(s.max_matrix_rows)),
        ("max_matrix_columns", size(s.max_matrix_columns)),
        ("elements_added", size(s.elements_added)),
        ("signature_basis_elements", size(s.signature_basis_elements)),
        ("reduced_basis_elements", size(s.reduced_basis_elements)),
        ("interreduction_columns", size(s.interreduction_columns)),
        ("interreduction_nonzeros", size(s.interreduction_nonzeros)),
        (
            "interreduction_peak_nonzeros",
            size(s.interreduction_peak_nonzeros),
        ),
        ("syzygy_signatures", size(s.syzygy_signatures)),
        ("peak_pending", size(s.peak_pending)),
        ("signature_metadata_bytes", size(s.signature_metadata_bytes)),
        ("bookkeeping_ns", Json::nanos(s.bookkeeping)),
        ("symbolic_ns", Json::nanos(s.symbolic)),
        ("elimination_ns", Json::nanos(s.elimination)),
        ("interreduction_ns", Json::nanos(s.interreduction)),
        ("total_ns", Json::nanos(s.total)),
        #[cfg(feature = "research-sigf4-split")]
        ("split", split(&s.split)),
    ])
}

/// #901: per-batch reducer-block / cascade split and the engine's glue clocks.
#[cfg(feature = "research-sigf4-split")]
fn split(log: &zeebra::grobner::sigf4::SplitLog) -> Json {
    let batches = log.batches.iter().map(|b| {
        Json::object([
            ("targets", Json::size(b.targets)),
            ("reducers", Json::size(b.reducers)),
            ("columns", Json::size(b.columns)),
            ("setup_ns", Json::nanos(b.setup)),
            ("parallel_pass_ns", Json::nanos(b.parallel_pass)),
            ("serial_pass_ns", Json::nanos(b.serial_pass)),
            ("parallel_products", Json::int(b.parallel_products)),
            (
                "serial_reducer_products",
                Json::int(b.serial_reducer_products),
            ),
            ("cascade_products", Json::int(b.cascade_products)),
            ("cascading_targets", Json::size(b.cascading_targets)),
        ])
    });
    Json::object([
        ("inputs_ns", Json::nanos(log.inputs)),
        ("materialize_ns", Json::nanos(log.materialize)),
        ("drop_ns", Json::nanos(log.drop)),
        ("batches", Json::Array(batches.collect())),
    ])
}

#[cfg(feature = "research-work")]
fn discovery(report: &zeebra::linalg::work::WorkReport) -> Json {
    let (mut forward, mut backward, mut zero_rows, mut zero_products) = (0u64, 0u64, 0u64, 0u64);
    for b in &report.batches {
        forward += b.forward.coefficient_products as u64;
        backward += b.backward.coefficient_products as u64;
        for r in &b.discovery {
            if r.completed && r.pivot_column.is_none() {
                zero_rows += 1;
                zero_products += (r.inherited_products + r.discovered_products) as u64;
            }
        }
    }
    Json::object([
        ("forward_products", Json::int(forward)),
        ("backward_products", Json::int(backward)),
        ("zero_rows", Json::int(zero_rows)),
        ("products_on_zero_rows", Json::int(zero_products)),
    ])
}

#[cfg(feature = "research-sigf4-replay")]
fn basis_sha256<const N: usize, F: FiniteField>(
    basis: &[MultivariatePolynomial<N, F>],
    names: &[&str; N],
) -> String {
    let mut text: Vec<_> = basis
        .iter()
        .map(|p| polynomial_to_string(p, names, ORDER))
        .collect();
    text.sort();
    sha256_hex(text.join("\n").as_bytes())
}

#[cfg(feature = "research-sigf4-replay")]
mod cascade {
    use super::*;
    use zeebra::grobner::sigf4::replay::{ceiling, record, BatchRecord, SCHEDULES};

    /// Every count the plan's validation names; timings excluded.
    fn algebraic(s: &SigF4Statistics) -> Vec<u64> {
        let counts = [
            s.batches,
            s.pairs_created,
            s.pairs_singular,
            s.rejected_product,
            s.rejected_koszul,
            s.rejected_zero_row,
            s.rejected_rewrite,
            s.rejected_duplicate,
            s.targets,
            s.reducer_rows,
            s.reductions_to_zero,
            s.singular_rows,
            s.elements_added,
            s.signature_basis_elements,
            s.reduced_basis_elements,
            s.syzygy_signatures,
        ];
        counts
            .iter()
            .map(|&v| v as u64)
            .chain([
                s.coefficient_products,
                s.products_on_zero_rows,
                s.products_on_singular_rows,
            ])
            .collect()
    }

    fn batch(r: &BatchRecord) -> Json {
        let int = |v: u64| Json::int(v);
        let size = |v: usize| Json::size(v);
        Json::object([
            ("columns", size(r.columns)),
            ("targets", size(r.targets)),
            ("zero_targets", size(r.zero_targets)),
            ("reducer_steps", int(r.reducer_steps)),
            ("target_steps", int(r.target_steps)),
            ("surviving", int(r.surviving)),
            ("shadowed", int(r.shadowed)),
            ("phase_a", int(r.phase_a)),
            ("max_phase_a", int(r.max_phase_a)),
            ("cascade", int(r.cascade)),
            ("max_target", int(r.max_target)),
            ("dependent_targets", size(r.dependent_targets)),
            ("edges", size(r.edges)),
            ("depth", size(r.depth)),
            ("width", size(r.width)),
            ("cp_dag", int(r.critical[0])),
            ("cp_frontier", int(r.critical[1])),
            ("cp_claim", int(r.critical[2])),
            ("would_displace", int(r.would_displace)),
            ("displaced_suffix", int(r.displaced_suffix)),
        ])
    }

    fn ratio(x: f64) -> Json {
        Json::string(format!("{x:.3}"))
    }

    /// Ceilings at 4/8/16 workers against design 1's products, per arm and schedule.
    fn ceilings(d1: &[BatchRecord], d2: &[BatchRecord]) -> Json {
        let base: u64 = d1.iter().map(BatchRecord::work).sum();
        let d2_work: u64 = d2.iter().map(BatchRecord::work).sum();
        let mut rows = Vec::new();
        for workers in [4, 8, 16] {
            let mut row = |arm: &str, schedule: &str, records: &[BatchRecord], s, work: u64| {
                let (bound, greedy) = ceiling(records, base, s, workers);
                rows.push(Json::object([
                    ("workers", Json::size(workers)),
                    ("arm", Json::string(arm)),
                    ("schedule", Json::string(schedule)),
                    ("ceiling", ratio(bound)),
                    ("greedy", ratio(greedy)),
                    ("products_ratio", ratio(work as f64 / base as f64)),
                ]));
            };
            for s in SCHEDULES {
                row("exact", s.name(), d1, Some(s), base);
                row("prereduce", s.name(), d2, Some(s), d2_work);
            }
            row("prereduce", "serial-cascade", d2, None, d2_work);
        }
        Json::Array(rows)
    }

    pub(super) fn report<const N: usize, F: FiniteField>(
        system: &[MultivariatePolynomial<N, F>],
        names: &[&str; N],
        digest: &str,
        args: &Args,
    ) -> Json {
        let options = |workers| SigF4Options {
            max_wall_time: Some(args.wall),
            workers,
            ..SigF4Options::default()
        };
        let (plain, plain_stats) = sig_f4_reported(system, ORDER, &options(1));
        let ((d1, d1_stats), d1_records) = record(|| sig_f4_reported(system, ORDER, &options(1)));
        let ((d2, d2_stats), d2_records) =
            record(|| sig_f4_reported(system, ORDER, &options(args.workers)));
        let (plain, d1, d2) = (
            plain.expect("design 1 finishes"),
            d1.expect("recorded design 1 finishes"),
            d2.expect("recorded design 2 finishes"),
        );
        let digest_of = |b: &[MultivariatePolynomial<N, F>]| basis_sha256(b, names);
        assert_eq!(
            algebraic(&d1_stats),
            algebraic(&plain_stats),
            "recording moved an algebraic quantity"
        );
        assert_eq!(
            digest_of(&d1),
            digest_of(&plain),
            "recording moved the basis"
        );
        assert_eq!(
            digest_of(&d2),
            digest_of(&plain),
            "design 2 moved the basis"
        );
        let all = |records: &[BatchRecord]| Json::Array(records.iter().map(batch).collect());
        Json::object([
            ("field", Json::string(&args.field)),
            ("name", Json::string(&args.name)),
            ("digest", Json::string(digest)),
            ("design2_workers", Json::size(args.workers)),
            ("basis_sha256", Json::string(digest_of(&plain))),
            ("replay_invariant", Json::Bool(true)),
            ("design1_statistics", sig_statistics(&plain_stats)),
            ("design2_statistics", sig_statistics(&d2_stats)),
            ("ceilings", ceilings(&d1_records, &d2_records)),
            ("design1_batches", all(&d1_records)),
            ("design2_batches", all(&d2_records)),
        ])
    }
}

fn run<const N: usize, F: FiniteField>(input: Input, args: &Args) -> Json {
    let names: [&str; N] = std::array::from_fn(|i| input.variables[i].as_str());
    let system: Vec<MultivariatePolynomial<N, F>> = input
        .generators
        .iter()
        .map(|s| MultivariatePolynomial::parse(s, names).expect("generator parses"))
        .collect();
    if args.replay {
        #[cfg(feature = "research-sigf4-replay")]
        return cascade::report(&system, &names, &input.digest, args);
        #[cfg(not(feature = "research-sigf4-replay"))]
        panic!("--replay requires --features research-sigf4-replay");
    }
    let started = Instant::now();
    let (result, statistics, work) = if args.engine == "sigf4" {
        let options = SigF4Options {
            max_wall_time: Some(args.wall),
            workers: args.workers,
            ..SigF4Options::default()
        };
        let (result, stats) = sig_f4_reported(&system, ORDER, &options);
        (
            result.map_err(|e| e.to_string()),
            sig_statistics(&stats),
            Json::Null,
        )
    } else {
        let options = f4_options(args);
        let solve = || f4_reported(&system, ORDER, &options);
        #[cfg(feature = "research-work")]
        let ((result, stats), work) = if args.discovery {
            let (r, w) = zeebra::linalg::work::measure_discovery(solve);
            (r, discovery(&w))
        } else {
            (solve(), Json::Null)
        };
        #[cfg(not(feature = "research-work"))]
        let ((result, stats), work) = {
            assert!(!args.discovery, "--discovery requires research-work");
            (solve(), Json::Null)
        };
        let summary = Json::object([
            ("batches", Json::size(stats.batches)),
            ("pairs_reduced", Json::size(stats.pairs_reduced)),
            ("zero_rows", Json::size(stats.zero_rows)),
            ("elements_added", Json::size(stats.elements_added)),
            ("max_matrix_rows", Json::size(stats.max_matrix_rows)),
            ("max_matrix_columns", Json::size(stats.max_matrix_columns)),
        ]);
        (result.map_err(|e| e.to_string()), summary, work)
    };
    let elapsed = started.elapsed();
    let render = Instant::now();
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
    let render = render.elapsed();
    let certification = match (&result, args.certify) {
        (Ok(basis), true) => {
            let clock = Instant::now();
            let report = certify_f4_output(&system, basis, ORDER);
            Json::object([
                ("checks_passed", Json::Bool(report.checks_passed())),
                ("ns", Json::nanos(clock.elapsed())),
            ])
        }
        _ => Json::Null,
    };
    Json::object([
        ("field", Json::string(&args.field)),
        ("name", Json::string(&args.name)),
        ("digest", Json::string(&input.digest)),
        ("engine", Json::string(&args.engine)),
        ("workers", Json::size(args.workers)),
        ("status", Json::string(status)),
        ("call_ns", Json::nanos(elapsed)),
        ("render_ns", Json::nanos(render)),
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
        ("statistics", statistics),
        ("work", work),
        ("certification", certification),
    ])
}

fn main() {
    let started = Instant::now();
    let raw: Vec<String> = std::env::args().skip(1).collect();
    let args = parse_args(&raw).unwrap_or_else(|e| panic!("{e}"));
    let input = wide(&args.field, &args.name);
    let n = input.variables.len();
    let mut report = match (args.field.as_str(), n) {
        ("goldilocks", 4) => run::<4, Goldilocks>(input, &args),
        ("goldilocks", 7) => run::<7, Goldilocks>(input, &args),
        ("goldilocks", 11) => run::<11, Goldilocks>(input, &args),
        ("goldilocks", 12) => run::<12, Goldilocks>(input, &args),
        ("wide64", 8) => run::<8, Wide>(input, &args),
        ("wide64", 9) => run::<9, Wide>(input, &args),
        ("wide64", 14) => run::<14, Wide>(input, &args),
        ("wide64", 4) => run::<4, Wide>(input, &args),
        ("wide64", 7) => run::<7, Wide>(input, &args),
        ("wide64", 11) => run::<11, Wide>(input, &args),
        ("wide64", 12) => run::<12, Wide>(input, &args),
        (field, n) => panic!("no instantiation for {field} with {n} variables"),
    };
    // In-process time before and after the solve: with `call_ns` and `render_ns` this leaves only
    // exec and exit to the caller's process wall.
    if let Json::Object(fields) = &mut report {
        fields.push(("main_ns".into(), Json::nanos(started.elapsed())));
    }
    println!("{}", report.to_json().replace('\n', ""));
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(list: &[&str]) -> Result<Args, String> {
        parse_args(&list.iter().map(|s| s.to_string()).collect::<Vec<_>>())
    }

    // Both engines take workers, the census is serial-F4-only, and unknown fields or engines fail.
    #[test]
    fn arguments_are_validated() {
        let base = ["--field", "wide64", "--name", "eco-12", "--engine"];
        assert!(args(&[&base[..], &["sigf4"]].concat()).is_ok());
        assert!(args(&[&base[..], &["sigf4", "--workers", "16"]].concat()).is_ok());
        assert!(args(&[&base[..], &["f4", "--workers", "16"]].concat()).is_ok());
        assert!(args(&[&base[..], &["f4", "--workers", "16", "--discovery"]].concat()).is_err());
        assert!(args(&[&base[..], &["magma"]].concat()).is_err());
        assert!(args(&["--field", "bn254", "--name", "eco-12", "--engine", "f4"]).is_err());
    }

    // The replay runs both signature designs, so it needs the signature engine and two workers.
    #[test]
    fn replay_needs_the_signature_engine_and_two_workers() {
        let base = [
            "--field", "wide64", "--name", "eco-12", "--replay", "--engine",
        ];
        assert!(args(&[&base[..], &["sigf4", "--workers", "2"]].concat()).is_ok());
        assert!(args(&[&base[..], &["sigf4"]].concat()).is_err());
        assert!(args(&[&base[..], &["f4", "--workers", "2"]].concat()).is_err());
    }

    // The shipping F4 arm caps the symbolic team at the worker count, as forward is (#883).
    #[test]
    fn f4_arm_caps_the_symbolic_team() {
        use zeebra::grobner::ParallelSymbolic;
        let base = ["--field", "wide64", "--name", "eco-12", "--engine", "f4"];
        let one = f4_options(&args(&base).unwrap());
        assert_eq!(one.parallel_symbolic, ParallelSymbolic::Serial);
        let four = f4_options(&args(&[&base[..], &["--workers", "4"]].concat()).unwrap());
        assert_eq!(
            four.parallel_symbolic,
            ParallelSymbolic::Auto { max_workers: 4 }
        );
    }

    // The two engines agree on a small frozen row, which is what the basis digest relies on.
    #[test]
    fn engines_agree_on_katsura_4() {
        let run_engine = |engine: &str| {
            let a = args(&[
                "--field",
                "goldilocks",
                "--name",
                "katsura-4",
                "--engine",
                engine,
            ])
            .unwrap();
            run::<4, Goldilocks>(wide("goldilocks", "katsura-4"), &a)
                .get("basis_sha256")
                .and_then(Json::as_str)
                .map(str::to_string)
        };
        assert!(run_engine("sigf4").is_some());
        assert_eq!(run_engine("sigf4"), run_engine("f4"));
    }
}
