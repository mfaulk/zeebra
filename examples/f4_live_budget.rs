// Each invocation measures one F4 computation so process peak RSS belongs to that row.
use std::time::{Duration, Instant};
use zeebra::{
    fields::PrimeFieldElement64,
    grobner::{
        benchmark_systems::{cyclic, katsura},
        differential::{CaseField, GeneratedSystem, SystemShape},
        f4_reported,
        record::Environment,
        F4Options,
    },
    util::{peak_resident_bytes, sha256_hex, Json},
    KnownOrder, MonomialOrder, MultivariatePolynomial,
};

fn input<const N: usize, F: KnownOrder>(system: &[MultivariatePolynomial<N, F>]) -> String {
    let names: Vec<_> = (0..N).map(|i| format!("x_{i}")).collect();
    format!(
        "{}\n{}\n{}",
        names.join(","),
        F::order_limbs()[0],
        system
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(",\n")
    )
}

fn run<const N: usize, F: KnownOrder>(name: &str, text: &str, entries: &str, reduced: bool) {
    let mut lines = text.lines();
    let names: Vec<_> = lines.next().expect("variable header").split(',').collect();
    assert_eq!(names.len(), N);
    let variables: [&str; N] = names.try_into().expect("matching arity");
    assert_eq!(
        lines.next().expect("prime header").parse::<u64>().unwrap(),
        F::order_limbs()[0]
    );
    let polynomials = lines.collect::<Vec<_>>().join("\n");
    let system: Vec<MultivariatePolynomial<N, F>> = polynomials
        .split(',')
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(|p| MultivariatePolynomial::parse(p, variables).expect("polynomial parses"))
        .collect();
    let mut options = F4Options::default();
    if entries != "default" {
        options = options.with_live_entries::<F>(entries.parse().expect("entry count"));
    }
    options.reduce_batch_rows = reduced;
    options.max_wall_time = Some(Duration::from_secs(
        std::env::var("ZEEBRA_WALL_SECONDS")
            .unwrap_or_else(|_| "120".into())
            .parse()
            .expect("wall seconds"),
    ));
    options.measure_stages = true;
    let at = Instant::now();
    let (result, statistics) =
        f4_reported(&system, MonomialOrder::GradedReverseLexicographic, &options);
    let elapsed = at.elapsed();
    let (outcome, error, basis_elements, basis_digest) = match result {
        Ok(basis) => {
            let mut polynomials: Vec<_> = basis.iter().map(ToString::to_string).collect();
            polynomials.sort();
            (
                "complete",
                Json::Null,
                basis.len(),
                Json::string(sha256_hex(polynomials.join("\n").as_bytes())),
            )
        }
        Err(error) => ("stopped", Json::string(error.to_string()), 0, Json::Null),
    };
    let environment = Environment {
        machine: std::env::var("ZEEBRA_MACHINE").unwrap_or_else(|_| "unrecorded".into()),
        cpu: std::env::var("ZEEBRA_AFFINITY").unwrap_or_else(|_| "unrecorded".into()),
        concurrency: 1,
        build: if cfg!(debug_assertions) {
            "debug".into()
        } else {
            "release; x86-64-v3; fat LTO; codegen-units=1".into()
        },
        policy: format!(
            "{}; reduced batch rows={reduced}; wall={:?}",
            options.live_budget_policy::<F>(),
            options.max_wall_time
        ),
        ..Environment::from_git()
    };
    println!(
        "{}",
        Json::object([
            ("environment", environment.to_json()),
            ("input", Json::string(name)),
            ("input_sha256", Json::string(sha256_hex(text.as_bytes()))),
            ("variables", Json::size(N)),
            ("equations", Json::size(system.len())),
            ("outcome", Json::string(outcome)),
            ("error", error),
            ("elapsed_nanos", Json::nanos(elapsed)),
            (
                "peak_resident_bytes",
                peak_resident_bytes().map_or(Json::Null, |bytes| Json::int(bytes as i128))
            ),
            ("basis_elements", Json::size(basis_elements)),
            ("basis_sha256", basis_digest),
            ("completed_batches", Json::size(statistics.batches)),
            (
                "completed_peak_live_entries",
                Json::size(statistics.max_live_nonzeros)
            ),
            (
                "interreduction_peak_entries",
                statistics
                    .interreduction_matrix
                    .as_ref()
                    .map_or(Json::Null, |s| Json::size(s.peak_nonzeros))
            ),
            (
                "interreduction_fell_back",
                statistics
                    .interreduction_matrix
                    .as_ref()
                    .map_or(Json::Null, |s| Json::Bool(s.fell_back))
            ),
            ("max_rows", Json::size(statistics.max_matrix_rows)),
            ("max_columns", Json::size(statistics.max_matrix_columns)),
            (
                "max_pair_degree",
                Json::int(statistics.max_pair_degree as i128)
            ),
        ])
        .to_json()
    );
}

fn builtin_input(name: &str) -> Option<String> {
    Some(match name {
        "katsura-11" => input(&katsura::<11, PrimeFieldElement64<2147483647>>()),
        "cyclic-9" => input(&cyclic::<9, PrimeFieldElement64<2147483647>>()),
        "mq-random-10" => {
            let generated = GeneratedSystem::generate(
                10,
                SystemShape {
                    variables: 10,
                    max_degree: 2,
                    max_terms: 40,
                },
                CaseField::prime(2147483647),
            );
            format!(
                "{}\n2147483647\n{}",
                generated.variables.join(","),
                generated.render().join(",\n")
            )
        }
        _ => return None,
    })
}

fn main() {
    let args: Vec<_> = std::env::args().skip(1).collect();
    assert_eq!(args.len(), 3, "usage: f4_live_budget <mq-random-10|katsura-11|cyclic-9|input.system> <entries|default> <reduced|echelon>");
    let reduced = match args[2].as_str() {
        "reduced" => true,
        "echelon" => false,
        _ => panic!("unknown row form"),
    };
    let text = builtin_input(&args[0])
        .unwrap_or_else(|| std::fs::read_to_string(&args[0]).expect("input readable"));
    let mut lines = text.lines();
    let n = lines.next().unwrap().split(',').count();
    let prime: u64 = lines.next().unwrap().parse().expect("prime header");
    macro_rules! call {
        ($n:literal, $p:literal) => {
            run::<$n, PrimeFieldElement64<$p>>(&args[0], &text, &args[1], reduced)
        };
    }
    match (n, prime) {
        (5, 65537) => call!(5, 65537),
        (6, 65537) => call!(6, 65537),
        (7, 65537) => call!(7, 65537),
        (8, 65537) => call!(8, 65537),
        (10, 65537) => call!(10, 65537),
        (80, 2130706433) => call!(80, 2130706433),
        (9, 2147483647) => call!(9, 2147483647),
        (10, 2147483647) => call!(10, 2147483647),
        (11, 2147483647) => call!(11, 2147483647),
        _ => panic!("uncompiled field/arity {prime}/{n}"),
    }
}

#[cfg(test)]
mod tests {
    use super::builtin_input;

    // Built-in controls use the corpus variable counts and reference characteristic.
    #[test]
    fn test_builtin_controls_match_corpus_dimensions() {
        for (name, arity) in [("katsura-11", 11), ("cyclic-9", 9), ("mq-random-10", 10)] {
            let text = builtin_input(name).unwrap();
            let mut lines = text.lines();
            assert_eq!(lines.next().unwrap().split(',').count(), arity);
            assert_eq!(lines.next(), Some("2147483647"));
        }
        assert!(builtin_input("unknown").is_none());
    }

    // The seeded MQ control matches the canonical competitive-corpus generators exactly.
    #[test]
    #[cfg(feature = "external-runners")]
    fn test_mq_control_matches_competitive_corpus() {
        let corpus = zeebra::grobner::external::corpus::instance(
            "mq-random-10",
            2147483647,
            zeebra::MonomialOrder::GradedReverseLexicographic,
        )
        .unwrap();
        assert_eq!(
            builtin_input("mq-random-10").unwrap(),
            format!(
                "{}\n2147483647\n{}",
                corpus.variables.join(","),
                corpus.system.join(",\n")
            )
        );
    }
}
