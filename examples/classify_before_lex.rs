// Run one case and policy per process so peak RSS belongs to that measurement.
use std::time::Instant;

use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    fields::{Zp2, Zp2147483647},
    grobner::{
        benchmark_systems::{cyclic, katsura, planted},
        record::{Environment, ExperimentRecord},
        solve_one_planned, PlannedSolveOptions, SolveOutcome, SolvePolicy, SolveStrategy,
    },
    util::{peak_resident_bytes, Json},
    FiniteField, KnownOrder, MultivariatePolynomial,
};

fn measure<const N: usize, F: KnownOrder>(
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
    policy: SolvePolicy,
) {
    let mut options = PlannedSolveOptions::with_policy(policy);
    // Bound the direct-lex refusal as well as the preclassification on the same inputs.
    options.attempt.f4.max_matrix_rows = 1000;
    options.attempt.f4.max_matrix_columns = 1000;
    let at = Instant::now();
    let (outcome, plan) = solve_one_planned(system, &mut StdRng::seed_from_u64(417), &options);
    let elapsed = at.elapsed();
    let verified = match &outcome {
        Ok(SolveOutcome::Point(point)) => {
            assert!(system.iter().all(|p| p.eval(point).is_zero()));
            Some(true)
        }
        _ => None,
    };
    let mut record = ExperimentRecord::new(name, format!("{policy:?}")).with_plan(&plan);
    record.elapsed = elapsed;
    record.verified = verified;
    record.verification = "points evaluated against every original generator".into();
    record.peak_resident_bytes = peak_resident_bytes();
    record.reproduce = format!(
        "cargo run --release --example classify_before_lex -- {name} {}",
        if policy == SolvePolicy::ClassifyThenDirectLex {
            "classify"
        } else {
            "direct"
        }
    );
    let environment = Environment {
        machine: std::env::var("ZEEBRA_MACHINE").unwrap_or_else(|_| "unrecorded".into()),
        cpu: std::env::var("ZEEBRA_AFFINITY").unwrap_or_else(|_| "unrecorded".into()),
        concurrency: 1,
        build: "release; target-cpu=x86-64-v3; fat LTO; codegen-units=1".into(),
        policy: "1000 rows, 1000 columns; other F4 limits default".into(),
        ..Environment::from_git()
    };
    println!(
        "{}",
        Json::object([
            ("environment", environment.to_json()),
            ("record", record.to_json()),
            ("plan", Json::string(plan.to_string())),
        ])
        .to_json()
    );
}

fn main() {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if args.len() != 2 {
        eprintln!("usage: classify_before_lex <planted-8|katsura-5|katsura-6-minus-one|cyclic-4-gf2> <direct|classify>");
        std::process::exit(2);
    }
    let policy = match args[1].as_str() {
        "direct" => SolvePolicy::Explicit(SolveStrategy::DirectLexF4),
        "classify" => SolvePolicy::ClassifyThenDirectLex,
        _ => {
            eprintln!("unknown policy: {}", args[1]);
            std::process::exit(2);
        }
    };
    match args[0].as_str() {
        "planted-8" => measure(
            &args[0],
            &planted::<8, Zp2147483647>(
                &(0..8)
                    .map(|i| Zp2147483647::new(2 * i + 3))
                    .collect::<Vec<_>>(),
            ),
            policy,
        ),
        "katsura-5" => measure(&args[0], &katsura::<5, Zp2147483647>(), policy),
        "katsura-6-minus-one" => {
            let mut system = katsura::<6, Zp2147483647>();
            system.pop();
            measure(&args[0], &system, policy);
        }
        "cyclic-4-gf2" => measure(&args[0], &cyclic::<4, Zp2>(), policy),
        _ => {
            eprintln!("unknown system: {}", args[0]);
            std::process::exit(2);
        }
    }
}
