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
use std::time::{Duration, Instant};
use zeebra::{
    fields::PrimeFieldElement64,
    grobner::{
        certify_f4_output,
        differential::polynomial_to_string,
        f4_reported,
        sigf4::{sig_f4_reported, SigF4Options, SigF4Statistics},
        F4Options, ParallelForward,
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
    Ok(parsed)
}

/// Shipping defaults; only the forward-worker cap varies, as in `m29_cost_model`.
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
        ("syzygy_signatures", size(s.syzygy_signatures)),
        ("peak_pending", size(s.peak_pending)),
        ("signature_metadata_bytes", size(s.signature_metadata_bytes)),
        ("bookkeeping_ns", Json::nanos(s.bookkeeping)),
        ("symbolic_ns", Json::nanos(s.symbolic)),
        ("elimination_ns", Json::nanos(s.elimination)),
        ("interreduction_ns", Json::nanos(s.interreduction)),
        ("total_ns", Json::nanos(s.total)),
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

fn run<const N: usize, F: FiniteField>(input: Input, args: &Args) -> Json {
    let names: [&str; N] = std::array::from_fn(|i| input.variables[i].as_str());
    let system: Vec<MultivariatePolynomial<N, F>> = input
        .generators
        .iter()
        .map(|s| MultivariatePolynomial::parse(s, names).expect("generator parses"))
        .collect();
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
    let raw: Vec<String> = std::env::args().skip(1).collect();
    let args = parse_args(&raw).unwrap_or_else(|e| panic!("{e}"));
    let input = wide(&args.field, &args.name);
    let n = input.variables.len();
    let report = match (args.field.as_str(), n) {
        ("goldilocks", 4) => run::<4, Goldilocks>(input, &args),
        ("goldilocks", 7) => run::<7, Goldilocks>(input, &args),
        ("goldilocks", 11) => run::<11, Goldilocks>(input, &args),
        ("goldilocks", 12) => run::<12, Goldilocks>(input, &args),
        ("wide64", 4) => run::<4, Wide>(input, &args),
        ("wide64", 7) => run::<7, Wide>(input, &args),
        ("wide64", 11) => run::<11, Wide>(input, &args),
        ("wide64", 12) => run::<12, Wide>(input, &args),
        (field, n) => panic!("no instantiation for {field} with {n} variables"),
    };
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
