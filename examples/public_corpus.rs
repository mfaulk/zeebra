//! One public input per process; full-basis references remain separate from measured F4 work.
use std::{
    path::PathBuf,
    time::{Duration, Instant},
};
use zeebra::{
    fields::Zp32003,
    grobner::{
        differential::polynomial_to_string,
        external::{
            public_corpus::{self, PublicCase, CASES},
            ExternalSolver, GrobxSolver, Instance, Limits, SingularSolver, SylvesterSolver, Task,
        },
        f4_reported, F4Options,
    },
    util::{peak_resident_bytes, Json},
    FiniteField, MultivariatePolynomial,
};

fn shape<const N: usize>(input: &Instance) -> Json {
    let names: [&str; N] = std::array::from_fn(|i| input.variables[i].as_str());
    let system: Vec<MultivariatePolynomial<N, Zp32003>> = input
        .system
        .iter()
        .map(|s| MultivariatePolynomial::parse(s, names).unwrap())
        .collect();
    Json::object([
        (
            "degrees",
            Json::Array(system.iter().map(|p| Json::int(p.degree())).collect()),
        ),
        (
            "term_counts",
            Json::Array(system.iter().map(|p| Json::size(p.terms().len())).collect()),
        ),
    ])
}

fn metadata(c: &PublicCase, input: &Instance) -> Vec<(&'static str, Json)> {
    let shape = match c.variables {
        3 => shape::<3>(input),
        4 => shape::<4>(input),
        5 => shape::<5>(input),
        6 => shape::<6>(input),
        8 => shape::<8>(input),
        _ => unreachable!(),
    };
    vec![
        ("shape", shape),
        ("name", Json::string(c.name)),
        ("family", Json::string(c.family)),
        ("tier", Json::string(format!("{:?}", c.tier))),
        ("modulus", Json::int(input.field.characteristic)),
        ("digest", Json::string(input.digest())),
        (
            "variables",
            Json::Array(input.variables.iter().map(Json::string).collect()),
        ),
        (
            "generators",
            Json::Array(input.system.iter().map(Json::string).collect()),
        ),
        ("canonical", Json::string(input.canonical())),
    ]
}

fn run<const N: usize>(c: &PublicCase, input: &Instance) -> Vec<(&'static str, Json)> {
    let names: [&str; N] = std::array::from_fn(|i| input.variables[i].as_str());
    let generators: Vec<MultivariatePolynomial<N, Zp32003>> = input
        .system
        .iter()
        .map(|s| MultivariatePolynomial::parse(s, names).unwrap())
        .collect();
    let options = F4Options {
        measure_stages: true,
        max_wall_time: Some(Duration::from_secs(60)),
        ..F4Options::default()
    };
    let started = Instant::now();
    let (answer, stats) = f4_reported(&generators, input.order, &options);
    let elapsed = started.elapsed();
    let mut fields = vec![
        ("wall_ns", Json::nanos(elapsed)),
        ("options", Json::string(format!("{options:?}"))),
        ("statistics", Json::string(format!("{stats:#?}"))),
        (
            "peak_rss_bytes",
            peak_resident_bytes().map(Json::int).unwrap_or(Json::Null),
        ),
    ];
    match answer {
        Ok(basis) => {
            let canonical = |polys: &[MultivariatePolynomial<N, Zp32003>]| {
                let mut text: Vec<_> = polys
                    .iter()
                    .map(|p| polynomial_to_string(p, &names, input.order))
                    .collect();
                text.sort();
                text
            };
            let reference: Vec<_> = c
                .reference_for(input)
                .expect("recorded input and reference")
                .iter()
                .map(|s| {
                    let p = MultivariatePolynomial::<N, Zp32003>::parse(s, names).unwrap();
                    p.scale(&p.leading_coefficient(input.order).inverse())
                })
                .collect();
            let basis = canonical(&basis);
            assert_eq!(basis, canonical(&reference), "full reference basis differs");
            fields.extend([
                ("status", Json::string("verified")),
                (
                    "basis",
                    Json::Array(basis.into_iter().map(Json::string).collect()),
                ),
            ]);
        }
        Err(error) => fields.extend([
            ("status", Json::string("stopped-by-limit")),
            ("error", Json::string(error.to_string())),
        ]),
    }
    fields
}

fn reference_matches(c: &PublicCase, input: &Instance, basis: &[String]) -> bool {
    let Ok(reference) = c.reference_for(input) else {
        return false;
    };
    let canonical = |text: &str| {
        zeebra::grobner::external::contract::canonical_generator(text, input.field.characteristic)
    };
    let mut expected: Vec<_> = reference.iter().map(|s| canonical(s)).collect();
    let mut actual: Vec<_> = basis.iter().map(|s| canonical(s)).collect();
    expected.sort();
    actual.sort();
    actual == expected
}

fn main() {
    let args: Vec<_> = std::env::args().collect();
    if args.iter().any(|s| s == "--list") {
        println!(
            "{}",
            Json::Array(
                CASES
                    .iter()
                    .map(|c| Json::object(metadata(
                        c,
                        &public_corpus::instance(
                            c.name,
                            32003,
                            zeebra::MonomialOrder::GradedReverseLexicographic
                        )
                        .unwrap()
                    )))
                    .collect()
            )
            .to_json()
        );
        return;
    }
    let value = |key| {
        args.iter()
            .position(|s| s == key)
            .and_then(|i| args.get(i + 1))
            .map(String::as_str)
    };
    let name = value("--row").expect("--row public-eco-4 (or --list)");
    let c = CASES
        .iter()
        .find(|c| c.name == name)
        .expect("registered public case");
    let input = public_corpus::instance(
        name,
        32003,
        zeebra::MonomialOrder::GradedReverseLexicographic,
    )
    .unwrap();
    let engine = value("--engine").unwrap_or("zeebra");
    let mut fields = metadata(c, &input);
    fields.push(("engine", Json::string(engine)));
    if engine == "zeebra" {
        fields.extend(match c.variables {
            3 => run::<3>(c, &input),
            4 => run::<4>(c, &input),
            5 => run::<5>(c, &input),
            6 => run::<6>(c, &input),
            8 => run::<8>(c, &input),
            _ => unreachable!(),
        });
    } else {
        let scratch = PathBuf::from(std::env::var("TMPDIR").expect("set TMPDIR under /buildcache"))
            .join(format!("public-corpus-{}", std::process::id()));
        let mut solver: Box<dyn ExternalSolver> = match engine {
            "singular" => Box::new(
                SingularSolver::with_binary("Singular", scratch, Duration::from_secs(60)).unwrap(),
            ),
            "grobx" => Box::new(
                GrobxSolver::from_env(&scratch, zeebra::grobner::external::grobx::Mode::Raw)
                    .unwrap(),
            ),
            "sylvester" => Box::new(
                SylvesterSolver::from_env(
                    &scratch,
                    zeebra::grobner::external::sylvester::Mode::Raw,
                )
                .unwrap(),
            ),
            _ => panic!("engines: zeebra, singular, grobx, sylvester"),
        };
        let version = solver
            .probe_version()
            .expect("provision the requested engine");
        let report = solver.run(
            &input,
            Task::ReducedGrobnerBasis,
            &Limits::wall(Duration::from_secs(60))
                .with_workers(1)
                .with_max_rss_bytes(2 * 1024 * 1024 * 1024),
        );
        fields.extend([
            ("version", Json::string(version.to_string())),
            ("status", Json::string(report.status.tag())),
            ("wall_ns", Json::nanos(report.measurement.wall)),
            (
                "peak_rss_bytes",
                report
                    .measurement
                    .peak_rss_bytes
                    .map(Json::int)
                    .unwrap_or(Json::Null),
            ),
        ]);
        if let Some(answer) = report.status.answer() {
            let generating = args.iter().any(|s| s == "--reference-generation");
            assert!(
                !generating || engine == "singular",
                "only Singular generates references"
            );
            let basis = answer.basis.as_ref().expect("complete basis");
            if !generating {
                assert!(
                    reference_matches(c, &input, basis),
                    "full external basis differs from the recorded reference"
                );
            }
            fields.push(("reference_verified", Json::Bool(!generating)));
            fields.push((
                "basis",
                Json::Array(
                    answer
                        .basis
                        .as_ref()
                        .expect("complete basis")
                        .iter()
                        .map(Json::string)
                        .collect(),
                ),
            ));
            fields.push((
                "quotient_dimension",
                answer
                    .invariants
                    .quotient_dimension
                    .map(Json::size)
                    .unwrap_or(Json::Null),
            ));
        } else {
            fields.push(("error", Json::string(format!("{:?}", report.status))));
        }
    }
    println!("{}", Json::object(fields).to_json());
}

#[cfg(test)]
mod tests {
    use super::*;

    // External answers must match every coefficient of the recorded basis, not only its leaders.
    #[test]
    fn external_reference_check_rejects_a_changed_tail() {
        let c = &CASES[0];
        let input = public_corpus::instance(
            c.name,
            32003,
            zeebra::MonomialOrder::GradedReverseLexicographic,
        )
        .unwrap();
        let mut basis: Vec<String> = c
            .reference_for(&input)
            .unwrap()
            .into_iter()
            .map(String::from)
            .collect();
        assert!(reference_matches(c, &input, &basis));
        basis[0].push_str("+1");
        assert!(!reference_matches(c, &input, &basis));
    }
}
