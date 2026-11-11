use std::{env, fs, time::Instant};

use zeebra::{
    fields::Zp65537 as F,
    grobner::fglm::{fglm_to_lex_with_options, ConversionStrategy, FglmOptions},
    util::{peak_resident_bytes, sha256_hex},
    MonomialOrder, MultivariatePolynomial,
};

#[derive(Debug)]
struct Args {
    variables: usize,
    degree: u32,
    repeats: usize,
    input: Option<String>,
    msolve: Option<String>,
    route: String,
    max_dimension: usize,
    span_cells: usize,
    span_bytes: usize,
    operator_entries: usize,
    operator_bytes: usize,
    border_entries: usize,
}

impl Args {
    fn parse() -> Self {
        let mut args = Self {
            variables: 4,
            degree: 5,
            repeats: 3,
            input: None,
            msolve: None,
            route: "compare".into(),
            max_dimension: 4096,
            span_cells: 20_000_000,
            span_bytes: 320_000_000,
            operator_entries: 20_000_000,
            operator_bytes: 320_000_000,
            border_entries: 20_000_000,
        };
        let mut input = env::args().skip(1);
        while let Some(flag) = input.next() {
            if flag == "--help" {
                println!("wiedemann_conversion [--variables N] [--degree D] [--repeats N] [--route compare|classical|adaptive|wiedemann] [--input FILE] [--msolve PATH] [--max-dimension N] [--span-cells N] [--span-bytes N] [--operator-entries N] [--operator-bytes N] [--border-entries N]");
                println!("Input: variable names, characteristic 65537, then comma-separated polynomials forming a grevlex Groebner basis. Without a file, generate x_i^d-x_(i+1), last^d-x_0-1.");
                std::process::exit(0);
            }
            let value = input.next().expect("every flag takes a value");
            match flag.as_str() {
                "--variables" => args.variables = value.parse().expect("variable count"),
                "--degree" => args.degree = value.parse().expect("positive degree"),
                "--repeats" => args.repeats = value.parse().expect("positive repeat count"),
                "--input" => args.input = Some(value),
                "--msolve" => args.msolve = Some(value),
                "--route" => args.route = value,
                "--max-dimension" => args.max_dimension = value.parse().expect("dimension budget"),
                "--span-cells" => args.span_cells = value.parse().expect("cell budget"),
                "--span-bytes" => args.span_bytes = value.parse().expect("byte budget"),
                "--operator-entries" => {
                    args.operator_entries = value.parse().expect("operator entry budget")
                }
                "--border-entries" => {
                    args.border_entries = value.parse().expect("border entry budget")
                }
                "--operator-bytes" => {
                    args.operator_bytes = value.parse().expect("operator byte budget")
                }
                _ => panic!("unknown argument {flag}"),
            }
        }
        assert!(args.degree > 1 && args.repeats > 0);
        assert!(["compare", "classical", "adaptive", "wiedemann"].contains(&args.route.as_str()));
        args
    }
}

fn run<const N: usize>(args: &Args, input: Option<&str>) {
    let names: [String; N] = std::array::from_fn(|i| format!("x{i}"));
    let names_ref: [&str; N] = std::array::from_fn(|i| names[i].as_str());
    let source: Vec<MultivariatePolynomial<N, F>> = if let Some(text) = input {
        let mut lines = text.lines();
        let header = lines.next().expect("variable header");
        let fields: Vec<_> = header.split(',').map(str::trim).collect();
        let names: [&str; N] = fields.try_into().expect("declared variable count");
        assert_eq!(lines.next().expect("characteristic").trim(), "65537");
        lines
            .collect::<Vec<_>>()
            .join(" ")
            .trim()
            .trim_end_matches(',')
            .split(',')
            .map(|p| MultivariatePolynomial::parse(p.trim(), names).expect("a source polynomial"))
            .collect()
    } else {
        (0..N)
            .map(|i| {
                let tail = if i + 1 < N {
                    format!("x{}", i + 1)
                } else {
                    "x0-1".into()
                };
                MultivariatePolynomial::parse(&format!("x{i}^{}-{tail}", args.degree), names_ref)
                    .unwrap()
            })
            .collect()
    };
    let source_text = source
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join("\n");
    println!(
        "source-sha256={} variables={N} characteristic=65537; source must be a grevlex basis",
        sha256_hex(source_text.as_bytes())
    );
    println!(
        "machine={} affinity={} ISA={}",
        env::var("ZEEBRA_MACHINE").unwrap_or_else(|_| "unspecified".into()),
        env::var("ZEEBRA_AFFINITY").unwrap_or_else(|_| "unspecified".into()),
        zeebra::util::isa_floor()
    );
    println!("repeat strategy selected attempts fallback D operators wall-ms operator-ms dependence-ms workspace-cells basis-sha256");
    let mut reference = None;
    for repeat in 0..args.repeats {
        let strategies = if args.route == "compare" {
            if repeat % 2 == 0 {
                vec![ConversionStrategy::Classical, ConversionStrategy::Adaptive]
            } else {
                vec![ConversionStrategy::Adaptive, ConversionStrategy::Classical]
            }
        } else {
            vec![match args.route.as_str() {
                "classical" => ConversionStrategy::Classical,
                "adaptive" => ConversionStrategy::Adaptive,
                _ => ConversionStrategy::Wiedemann,
            }]
        };
        for strategy in strategies {
            let options = FglmOptions {
                conversion_strategy: strategy,
                max_quotient_dimension: args.max_dimension,
                max_span_entries: args.span_cells,
                max_span_bytes: args.span_bytes,
                max_operator_entries: args.operator_entries,
                max_operator_bytes: args.operator_bytes,
                border_batch: zeebra::grobner::fglm::BorderBatch {
                    max_nonzeros: args.border_entries,
                    ..zeebra::grobner::fglm::BorderBatch::recommended()
                },
                measure_stages: true,
                ..FglmOptions::recommended()
            };
            let start = Instant::now();
            let (basis, stats) = fglm_to_lex_with_options(
                &source,
                MonomialOrder::GradedReverseLexicographic,
                &options,
            )
            .expect("conversion within the explicit budgets");
            let elapsed = start.elapsed();
            match &reference {
                Some(previous) => assert_eq!(&basis, previous, "routes/repeats disagree"),
                None => reference = Some(basis.clone()),
            }
            let text = basis
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join("\n");
            println!(
                "{} {:?} {:?} {} {:?} {} {} {:.6} {:.6} {:.6} {} {}",
                repeat + 1,
                strategy,
                stats.conversion_route,
                stats.wiedemann_attempts,
                stats.wiedemann_fallback,
                stats.quotient_dimension,
                stats.operator_entries,
                elapsed.as_secs_f64() * 1000.,
                stats.timings.operator_construction().as_secs_f64() * 1000.,
                stats.timings.dependence.as_secs_f64() * 1000.,
                stats.memory.krylov_workspace_cells,
                sha256_hex(text.as_bytes())
            );
        }
    }
    if let Some(binary) = &args.msolve {
        compare_msolve(
            binary,
            &source,
            reference.as_ref().expect("converted basis"),
        );
    }
    println!("process-peak-rss-bytes={:?}; combined high-water mark across all repeats/routes; output bases asserted equal",peak_resident_bytes());
}

#[cfg(feature = "external-runners")]
fn compare_msolve<const N: usize>(
    binary: &str,
    source: &[MultivariatePolynomial<N, F>],
    lex: &[MultivariatePolynomial<N, F>],
) {
    use zeebra::grobner::external::{
        ExternalSolver, FieldSpec, Instance, Limits, MsolveSolver, RunStatus, Task,
    };
    let names: Vec<String> = (0..N).map(|i| format!("x_{i}")).collect();
    let instance = Instance::new(
        "prepared-basis",
        "shape",
        FieldSpec::prime(65537),
        names.clone(),
        source.iter().map(ToString::to_string).collect(),
        MonomialOrder::GradedReverseLexicographic,
    );
    let scratch = std::env::temp_dir().join(format!("wiedemann-msolve-{}", std::process::id()));
    let mut solver = MsolveSolver::new(binary, &scratch);
    let version = solver.probe_version().expect("available msolve");
    let report = solver.run(
        &instance,
        Task::UnivariateEliminant,
        &Limits::wall(std::time::Duration::from_secs(600)).with_max_rss_bytes(16 << 30),
    );
    println!("msolve version={version:?} objective=univariate-eliminant process-wall={:?} stages={:?} log={:?}",report.measurement.wall,report.measurement.stages,report.log_path);
    println!(
        "msolve peak-rss-bytes={:?}, workers=1",
        report.measurement.peak_rss_bytes
    );
    match report.status {
        RunStatus::Complete(answer) => {
            let names: [&str; N] = std::array::from_fn(|i| names[i].as_str());
            let found: MultivariatePolynomial<N, F> = MultivariatePolynomial::parse(
                answer.eliminant.as_deref().expect("eliminant"),
                names,
            )
            .expect("parse eliminant");
            let expected = lex
                .iter()
                .find(|p| {
                    p.terms()
                        .keys()
                        .all(|m| m.exponents()[..N - 1].iter().all(|e| *e == 0))
                })
                .expect("lex eliminant");
            assert_eq!(&found, expected, "external eliminant differs");
            println!("msolve eliminant exactly equal; this is no startup-floor-qualified ratio");
        }
        status => panic!("msolve supplied no comparable eliminant: {status:?}"),
    }
}

#[cfg(not(feature = "external-runners"))]
fn compare_msolve<const N: usize>(
    _: &str,
    _: &[MultivariatePolynomial<N, F>],
    _: &[MultivariatePolynomial<N, F>],
) {
    panic!("--msolve requires the external-runners feature");
}

fn main() {
    let mut args = Args::parse();
    let input = args
        .input
        .as_ref()
        .map(|p| fs::read_to_string(p).expect("readable basis input"));
    if let Some(text) = &input {
        args.variables = text.lines().next().expect("header").split(',').count();
    }
    macro_rules! dispatch { ($($n:literal),*) => { match args.variables { $($n=>run::<$n>(&args,input.as_deref()),)* _=>panic!("supported variable counts: 1 through 8, 10, 12") } }; }
    dispatch!(1, 2, 3, 4, 5, 6, 7, 8, 10, 12);
}
