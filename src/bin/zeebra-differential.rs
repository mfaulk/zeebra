//! Differential testing of Zeebra's zero-dimensional pipeline against Singular.
//!
//! Generates deterministic polynomial systems, asks Singular about each one, and compares every
//! intermediate result: the grevlex Gröbner basis, the quotient dimension, the standard monomials,
//! the normal form of each border monomial, each multiplication-operator column, and the lex
//! basis.
//!
//! ```text
//! cargo run --release --bin zeebra-differential -- --systems 500
//! cargo run --release --bin zeebra-differential -- --help
//! ```
//!
//! Exits non-zero if anything disagreed *or* if the oracle failed to answer about any system. A
//! sweep that could not consult its oracle has validated nothing, and must not look like a pass.

use std::{
    io::Write,
    path::PathBuf,
    process::ExitCode,
    time::{Duration, Instant},
};

use zeebra::grobner::fglm::{FglmOptions, OperatorConstruction, OperatorStorage};
use zeebra::grobner::F4Options;

use zeebra::grobner::differential::{
    check::{SUPPORTED_CHARACTERISTICS, SUPPORTED_VARIABLES},
    emit_failure, emit_fixture_module, run_sweep, Failure, SingularOracle, SweepOptions,
    SweepReport, SystemOutcome,
};

/// What the command was asked to do.
struct Arguments {
    sweep: SweepOptions,
    singular: String,
    timeout: Duration,
    work_dir: PathBuf,
    keep_files: bool,
    fixtures: Option<PathBuf>,
    failures: PathBuf,
    quiet: bool,
}

const USAGE: &str = "\
zeebra-differential — compare Zeebra's zero-dimensional pipeline against Singular

USAGE
    cargo run --release --bin zeebra-differential -- [OPTIONS]

OPTIONS
    --oracle <name>          Oracle to compare against. Only `singular` is implemented.
    --singular <path>        Singular executable. Default: Singular
    --seed <n>               Base seed; system i is generated from seed + i. Default: 12345
    --systems <n>            Systems to check. Default: 48
    --min-variables <n>      Smallest variable count. Default: 2
    --max-variables <n>      Largest variable count. Default: 5
    --characteristics <csv>  Primes to sweep. Default: every supported one
    --max-degree <d>         Largest total degree of a generated term. Default: 3
    --max-terms <t>          Largest number of terms in a generated polynomial. Default: 4
    --timeout <seconds>      Per-system Singular time limit. Default: 30
    --operator-construction <s>
                             per-column | deduplicated-border | batched-border.
                             Default: batched-border, the `FglmOptions` default
    --operator-storage <s>   sparse | adaptive | dense.
                             Default: adaptive, the `FglmOptions` default
    --minimize-attempts <n>  Shrink candidates per failing system, 0 to disable. Default: 40
    --minimize-seconds <s>   Wall-clock for shrinking one failing system. Default: 20
    --fixtures <path>        Write the agreeing cases as a Rust fixture module.
    --failures <dir>         Where to write failing cases. Default: target/differential-failures
    --work-dir <dir>         Scratch directory for Singular scripts. Default: a temporary one
    --keep-files             Keep every Singular script and its output, not only failures'.
    --quiet                  Only print the summary.
    -h, --help               This.

EXIT STATUS
    0  every system agreed, or was explicitly skipped as an unsupported shape
    1  something disagreed, Zeebra could not finish, or the oracle did not answer
    2  the arguments were not understood
";

fn main() -> ExitCode {
    let arguments = match parse_arguments() {
        Ok(Some(arguments)) => arguments,
        Ok(None) => {
            print!("{}", USAGE);
            return ExitCode::SUCCESS;
        }
        Err(message) => {
            eprintln!("{}\n\n{}", message, USAGE);
            return ExitCode::from(2);
        }
    };

    match run(arguments) {
        Ok(report) if report.clean() => ExitCode::SUCCESS,
        Ok(_) => ExitCode::FAILURE,
        Err(message) => {
            eprintln!("{}", message);
            ExitCode::FAILURE
        }
    }
}

fn run(arguments: Arguments) -> Result<SweepReport, String> {
    let mut oracle = SingularOracle::new(
        &arguments.singular,
        &arguments.work_dir,
        arguments.timeout,
        arguments.keep_files,
    )
    .map_err(|e| format!("cannot prepare the oracle: {}", e))?;

    // Before the sweep rather than per system: the alternative is discovering that Singular is
    // absent once for each of five hundred systems.
    let version = oracle
        .version()
        .map_err(|e| format!("cannot run Singular: {}", e))?;

    println!(
        "# Zeebra against Singular build {}, seed {}, {} systems",
        version, arguments.sweep.seed, arguments.sweep.systems
    );
    println!(
        "# variables {:?}, characteristics {:?}, degree <= {}, terms <= {}",
        arguments.sweep.variables,
        arguments.sweep.characteristics,
        arguments.sweep.max_degree,
        arguments.sweep.max_terms
    );
    println!(
        "# operator construction: {:?}, storage: {:?}",
        arguments.sweep.fglm.operator_construction, arguments.sweep.fglm.operator_storage
    );
    println!("# scratch in {}", oracle.work_dir().display());
    println!();

    let started = Instant::now();
    let quiet = arguments.quiet;
    let mut report = run_sweep(
        &arguments.sweep,
        &mut oracle,
        &mut |index, system, outcome| {
            if quiet && outcome.agreed() {
                return;
            }
            let prefix = match outcome {
                SystemOutcome::Agreed { .. } => "ok  ",
                SystemOutcome::Disagreed { .. } => "FAIL",
                SystemOutcome::OracleFailed { .. } => "ERR ",
                SystemOutcome::ZeebraFailed { .. } => "ERR ",
                SystemOutcome::Unsupported { .. } => "skip",
            };
            println!(
                "{} [{:>4}] {:<22} {}",
                prefix,
                index,
                system.name(),
                outcome.summary()
            );
            std::io::stdout().flush().expect("stdout");
        },
    );
    let elapsed = started.elapsed();

    for failure in &report.failures {
        match save_failure(&arguments.failures, failure) {
            Ok(path) => println!("\nsaved {} to {}", failure.original.name(), path.display()),
            Err(e) => println!("\ncould not save {}: {}", failure.original.name(), e),
        }
    }

    if let Some(path) = &arguments.fixtures {
        // Sorted so that regenerating with the same arguments gives the same file, byte for byte,
        // rather than a diff that depends on the order the sweep happened to finish in.
        report.agreed_cases.sort_by(|a, b| a.name.cmp(&b.name));
        let module = emit_fixture_module(&report.agreed_cases, &version, &sweep_flags(&arguments));
        std::fs::write(path, module)
            .map_err(|e| format!("cannot write {}: {}", path.display(), e))?;
        println!(
            "\nwrote {} fixtures to {}; run `cargo fmt` over it",
            report.agreed_cases.len(),
            path.display()
        );
    }

    summarize(&report, elapsed);
    Ok(report)
}

/// The flags that reproduce this sweep, for the generated fixture module's header.
///
/// Spelled out rather than taken from `std::env::args`, so that a table regenerated through a
/// wrapper script still records flags the tool itself accepts. Only the ones that change which
/// systems are generated: the oracle's path and the scratch directory do not.
fn sweep_flags(arguments: &Arguments) -> String {
    let sweep = &arguments.sweep;
    let characteristics: Vec<String> = sweep
        .characteristics
        .iter()
        .map(|p| p.to_string())
        .collect();
    format!(
        "--seed {} --systems {} --min-variables {} --max-variables {} --max-degree {} \
         --max-terms {} --characteristics {}",
        sweep.seed,
        sweep.systems,
        sweep.variables.iter().min().copied().unwrap_or(0),
        sweep.variables.iter().max().copied().unwrap_or(0),
        sweep.max_degree,
        sweep.max_terms,
        characteristics.join(","),
    )
}

fn summarize(report: &SweepReport, elapsed: Duration) {
    println!();
    println!("## Summary");
    println!();
    println!("| outcome                  | systems |");
    println!("|--------------------------|---------|");
    println!("| agreed                   | {:>7} |", report.agreed);
    println!(
        "|   of which zero-dim      | {:>7} |",
        report.zero_dimensional
    );
    println!("|   of which unit ideal    | {:>7} |", report.unit_ideals);
    println!(
        "|   of which positive-dim  | {:>7} |",
        report.positive_dimensional
    );
    println!(
        "| disagreed                | {:>7} |",
        report.failures.len()
    );
    println!(
        "| oracle did not answer    | {:>7} |",
        report.oracle_failures.len()
    );
    println!(
        "| Zeebra could not finish  | {:>7} |",
        report.zeebra_failures.len()
    );
    println!(
        "| skipped, unsupported     | {:>7} |",
        report.unsupported.len()
    );
    println!("| attempted                | {:>7} |", report.attempted);
    println!();
    println!("Took {:.1}s.", elapsed.as_secs_f64());

    for (name, reason) in &report.oracle_failures {
        println!("oracle failure: {}: {}", name, reason);
    }
    for (name, reason) in &report.zeebra_failures {
        println!("Zeebra failure: {}: {}", name, reason);
    }

    if report.clean() {
        println!("\nEverything compared agreed.");
    } else {
        println!("\nNot clean. An oracle that did not answer is not agreement.");
    }
}

/// Write a failing case where it can be reproduced and committed.
fn save_failure(directory: &PathBuf, failure: &Failure) -> std::io::Result<PathBuf> {
    std::fs::create_dir_all(directory)?;
    let path = directory.join(format!(
        "{}-{}.rs",
        failure.original.name(),
        failure.disagreement.check.name()
    ));
    std::fs::write(
        &path,
        emit_failure(
            &failure.case,
            &failure.disagreement.to_string(),
            &provenance(failure),
        ),
    )?;
    Ok(path)
}

/// How to get back to a failure: the seed, the original system, and what the shrinking did.
fn provenance(failure: &Failure) -> String {
    let mut out = String::new();
    out.push_str(&format!(
        "seed {}, GF({}), {} variables\n",
        failure.original.seed,
        failure.original.characteristic,
        failure.original.variables.len()
    ));
    out.push_str(&format!(
        "as generated: {}\n",
        failure.original.render().join(", ")
    ));
    out.push_str(&format!(
        "minimized to: {}\n",
        failure.minimized.render().join(", ")
    ));
    out.push_str(&format!(
        "{} shrinks accepted of {} candidates tried\n",
        failure.shrinks, failure.attempts
    ));
    out
}

fn parse_arguments() -> Result<Option<Arguments>, String> {
    let mut sweep = SweepOptions {
        seed: 12_345,
        systems: 48,
        variables: SUPPORTED_VARIABLES.to_vec(),
        characteristics: SUPPORTED_CHARACTERISTICS.to_vec(),
        max_degree: 3,
        max_terms: 4,
        minimize_attempts: 40,
        minimize_budget: Duration::from_secs(20),
        fglm: FglmOptions::default(),
        f4: F4Options::default(),
    };
    let mut singular = "Singular".to_string();
    let mut timeout = Duration::from_secs(30);
    let mut work_dir = default_work_dir();
    let mut keep_files = false;
    let mut fixtures: Option<PathBuf> = None;
    let mut failures = PathBuf::from("target/differential-failures");
    let mut quiet = false;
    let mut min_variables = *SUPPORTED_VARIABLES.first().expect("a supported count");
    let mut max_variables = *SUPPORTED_VARIABLES.last().expect("a supported count");

    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let mut index = 0;
    while index < arguments.len() {
        let flag = arguments[index].as_str();
        let mut value = || -> Result<String, String> {
            index += 1;
            arguments
                .get(index)
                .cloned()
                .ok_or_else(|| format!("{} needs a value", flag))
        };

        match flag {
            "-h" | "--help" => return Ok(None),
            "--quiet" => quiet = false_to(&mut quiet),
            "--keep-files" => keep_files = false_to(&mut keep_files),
            "--oracle" => {
                let name = value()?;
                if name != "singular" {
                    return Err(format!(
                        "{:?} is not an implemented oracle; only `singular` is",
                        name
                    ));
                }
            }
            "--singular" => singular = value()?,
            "--seed" => sweep.seed = number(&value()?, flag)?,
            "--systems" => sweep.systems = number(&value()?, flag)?,
            "--min-variables" => min_variables = number(&value()?, flag)?,
            "--max-variables" => max_variables = number(&value()?, flag)?,
            "--max-degree" => sweep.max_degree = number(&value()?, flag)?,
            "--max-terms" => sweep.max_terms = number(&value()?, flag)?,
            "--timeout" => timeout = Duration::from_secs(number(&value()?, flag)?),
            "--operator-storage" => {
                let name = value()?;
                sweep.fglm.operator_storage = match name.as_str() {
                    "sparse" => OperatorStorage::Sparse,
                    "adaptive" => OperatorStorage::Adaptive,
                    "dense" => OperatorStorage::Dense,
                    other => {
                        return Err(format!(
                            "{:?} is not an operator-storage strategy; use sparse, adaptive or \
                             dense",
                            other
                        ))
                    }
                };
            }
            "--operator-construction" => {
                let name = value()?;
                sweep.fglm.operator_construction = match name.as_str() {
                    "per-column" => OperatorConstruction::PerColumn,
                    "deduplicated-border" => OperatorConstruction::DeduplicatedBorder,
                    "batched-border" => OperatorConstruction::BatchedBorder,
                    other => {
                        return Err(format!(
                            "{:?} is not an operator-construction strategy; use per-column, \
                             deduplicated-border or batched-border",
                            other
                        ))
                    }
                };
            }
            "--minimize-attempts" => sweep.minimize_attempts = number(&value()?, flag)?,
            "--minimize-seconds" => {
                sweep.minimize_budget = Duration::from_secs(number(&value()?, flag)?)
            }
            "--characteristics" => {
                let list = value()?;
                sweep.characteristics = list
                    .split(',')
                    .map(|p| number(p.trim(), "--characteristics"))
                    .collect::<Result<Vec<u64>, String>>()?;
            }
            "--fixtures" => fixtures = Some(PathBuf::from(value()?)),
            "--failures" => failures = PathBuf::from(value()?),
            "--work-dir" => work_dir = PathBuf::from(value()?),
            other => return Err(format!("{:?} is not an option", other)),
        }
        index += 1;
    }

    sweep.variables = SUPPORTED_VARIABLES
        .iter()
        .copied()
        .filter(|count| *count >= min_variables && *count <= max_variables)
        .collect();
    if sweep.variables.is_empty() {
        return Err(format!(
            "no supported variable count is between {} and {}; the supported counts are {:?}",
            min_variables, max_variables, SUPPORTED_VARIABLES
        ));
    }
    if sweep.characteristics.is_empty() {
        return Err("--characteristics was empty".to_string());
    }
    for characteristic in &sweep.characteristics {
        if !SUPPORTED_CHARACTERISTICS.contains(characteristic) {
            return Err(format!(
                "GF({}) is not instantiated; the supported characteristics are {:?}",
                characteristic, SUPPORTED_CHARACTERISTICS
            ));
        }
    }
    if sweep.max_terms == 0 {
        return Err("--max-terms must be at least one".to_string());
    }

    Ok(Some(Arguments {
        sweep,
        singular,
        timeout,
        work_dir,
        keep_files,
        fixtures,
        failures,
        quiet,
    }))
}

/// Set a flag, returning the new value. Exists only so the match arms above stay one line each.
fn false_to(flag: &mut bool) -> bool {
    *flag = true;
    true
}

fn number<T: std::str::FromStr>(value: &str, flag: &str) -> Result<T, String> {
    value
        .parse()
        .map_err(|_| format!("{} does not take {:?}", flag, value))
}

/// A scratch directory unique to this process, under the system temporary directory.
fn default_work_dir() -> PathBuf {
    std::env::temp_dir().join(format!("zeebra-differential-{}", std::process::id()))
}
