//! Decimal characteristics keep BN254 capability records outside the u64 external contract.
use rand::{rngs::StdRng, SeedableRng};
use std::{
    path::PathBuf,
    time::{Duration, Instant},
};
use zeebra::{
    fields::{Bn254Fr, PrimeFieldElement64, BN254_FR_MODULUS_DECIMAL},
    grobner::{
        benchmark_systems::{cyclic, eco, katsura, noon},
        differential::polynomial_to_string,
        external::{
            ExternalSolver, FieldSpec, GrobxSolver, GroebnerJlSolver, GroebnerRsSolver, Instance,
            Limits, Task,
        },
        f4_reported, F4Options,
    },
    util::{peak_resident_bytes, sha256_hex, Json},
    FiniteField, MonomialOrder, MultivariatePolynomial,
};
type Goldilocks = PrimeFieldElement64<18446744069414584321>;
type Wide = PrimeFieldElement64<18446744073709551263>;
const ORDER: MonomialOrder = MonomialOrder::GradedReverseLexicographic;
const ROWS: &[&str] = &[
    "katsura-4",
    "katsura-9",
    "katsura-11",
    "katsura-14",
    "cyclic-7",
    "cyclic-11",
    "mq-random-10",
    "mq-random-11",
    "mq-random-12",
    "mq-random-14",
    "mq-random-16",
    "eco-12",
    "eco-14",
    "eco-18",
    "noon-7",
    "noon-8",
    "noon-11",
];
const FIELDS: &[(&str, &str)] = &[
    ("wide64", "18446744073709551263"),
    ("goldilocks", "18446744069414584321"),
    ("bn254", BN254_FR_MODULUS_DECIMAL),
];

fn published(field: &str, row: &str) -> bool {
    field != "bn254" || ["katsura-9", "cyclic-7", "mq-random-10", "eco-12", "noon-7"].contains(&row)
}

fn dense_mq<const N: usize, F: FiniteField>() -> Vec<MultivariatePolynomial<N, F>> {
    let names: Vec<_> = (1..=N).map(|i| format!("x{i}")).collect();
    let refs: [&str; N] = std::array::from_fn(|i| names[i].as_str());
    let mut rng = StdRng::seed_from_u64(0x73800000 + N as u64);
    let mut coefficient = || loop {
        let c = F::random(&mut rng);
        if !c.is_zero() {
            break c;
        }
    };
    (0..N)
        .map(|_| {
            let mut terms = vec![coefficient().to_string()];
            for i in 0..N {
                terms.push(format!("{}*x{}", coefficient(), i + 1));
                for j in i..N {
                    terms.push(format!("{}*x{}*x{}", coefficient(), i + 1, j + 1));
                }
            }
            MultivariatePolynomial::parse(&terms.join("+"), refs).expect("dense polynomial")
        })
        .collect()
}

struct WideInput<const N: usize, F: FiniteField> {
    system: Vec<MultivariatePolynomial<N, F>>,
    variables: Vec<String>,
    text: Vec<String>,
    transformation: String,
    fields: Vec<(&'static str, Json)>,
}

fn build<const N: usize, F: FiniteField>(field: &str, modulus: &str, row: &str) -> WideInput<N, F> {
    let family = row.rsplit_once('-').unwrap().0;
    let system = match family {
        "katsura" => katsura::<N, F>(),
        "cyclic" => cyclic::<N, F>(),
        "eco" => eco::<N, F>(),
        "noon" => noon::<N, F>(),
        "mq-random" => dense_mq::<N, F>(),
        _ => unreachable!(),
    };
    let variables: Vec<_> = (1..=N).map(|i| format!("x{i}")).collect();
    let names: [&str; N] = std::array::from_fn(|i| variables[i].as_str());
    let text: Vec<_> = system
        .iter()
        .map(|p| polynomial_to_string(p, &names, ORDER))
        .collect();
    let transformation = if family == "mq-random" {
        format!(
            "dense MQ; StdRng seed {}; all degree <=2 coefficients nonzero; no planting",
            0x73800000 + N as u64
        )
    } else if family == "noon" {
        "Noonburg 11/10; equations multiplied by 10".into()
    } else {
        "independent benchmark_systems definition".into()
    };
    let canonical = format!("wide-corpus-v1\nprime {modulus}\norder grevlex\nvariables {}\ntransformation {transformation}\n{}", variables.join(","), text.iter().map(|s| format!("generator {s}\n")).collect::<String>());
    let fields = vec![
        ("field", Json::string(field)),
        ("modulus", Json::string(modulus)),
        ("name", Json::string(row)),
        ("family", Json::string(family)),
        (
            "variables",
            Json::Array(variables.iter().map(Json::string).collect()),
        ),
        ("canonical", Json::string(&canonical)),
        ("digest", Json::string(sha256_hex(canonical.as_bytes()))),
        (
            "generators",
            Json::Array(text.iter().map(Json::string).collect()),
        ),
    ];
    WideInput {
        system,
        variables,
        text,
        transformation,
        fields,
    }
}

fn run<const N: usize, F: FiniteField>(
    field: &str,
    modulus: &str,
    row: &str,
    engine: &str,
    list: bool,
) -> Json {
    let WideInput {
        system,
        variables,
        text,
        transformation,
        mut fields,
    } = build::<N, F>(field, modulus, row);
    if list {
        return Json::object(fields);
    }
    let family = row.rsplit_once('-').unwrap().0;
    let names: [&str; N] = std::array::from_fn(|i| variables[i].as_str());
    fields.push(("engine", Json::string(engine)));
    if engine == "zeebra" {
        let options = F4Options {
            max_wall_time: Some(Duration::from_secs(60)),
            max_live_bytes: 2 * 1024 * 1024 * 1024,
            measure_stages: true,
            ..F4Options::default()
        };
        fields.push(("options", Json::string(format!("{options:?}"))));
        let started = Instant::now();
        let (result, stats) = f4_reported(&system, ORDER, &options);
        fields.push(("engine_wall_ns", Json::nanos(started.elapsed())));
        fields.push(("statistics", Json::string(format!("{stats:#?}"))));
        fields.push((
            "peak_rss_bytes",
            peak_resident_bytes().map(Json::int).unwrap_or(Json::Null),
        ));
        match result {
            Ok(basis) => {
                let mut basis: Vec<_> = basis
                    .iter()
                    .map(|p| polynomial_to_string(p, &names, ORDER))
                    .collect();
                basis.sort();
                fields.push(("status", Json::string("complete")));
                fields.push((
                    "basis",
                    Json::Array(basis.into_iter().map(Json::string).collect()),
                ));
            }
            Err(error) => {
                fields.push(("status", Json::string("stopped-by-limit")));
                fields.push(("detail", Json::string(error.to_string())));
            }
        }
    } else if field == "bn254" {
        fields.push(("status", Json::string("unsupported")));
        fields.push((
            "detail",
            Json::string("254-bit characteristic exceeds all current external adapter contracts"),
        ));
    } else {
        let input = Instance::new(
            row,
            family,
            FieldSpec::prime(modulus.parse().unwrap()),
            variables.clone(),
            text,
            ORDER,
        )
        .transformed(transformation);
        let scratch = PathBuf::from(std::env::var("TMPDIR").expect("set TMPDIR on /buildcache"))
            .join(format!("wide-{}", std::process::id()));
        let mut solver: Box<dyn ExternalSolver> = match engine {
            "groebner.jl" => Box::new(GroebnerJlSolver::from_env(&scratch).expect("Julia")),
            "groebner-rs" => Box::new(GroebnerRsSolver::from_env(&scratch).expect("groebner-rs")),
            "grobx" => Box::new(
                GrobxSolver::from_env(&scratch, zeebra::grobner::external::grobx::Mode::Raw)
                    .expect("grobx"),
            ),
            _ => panic!("unsupported engine"),
        };
        let version = solver.probe_version().expect("provision engine");
        let mut limits = Limits::wall(Duration::from_secs(60)).with_workers(1);
        // Native controls can exit before the adapter's first RSS sample; the campaign's
        // process-tree watchdog enforces their ceiling, as in the planted-wide verification.
        if engine == "groebner.jl" {
            limits = limits.with_max_rss_bytes(2 * 1024 * 1024 * 1024);
        }
        let report = solver.run(&input, Task::ReducedGrobnerBasis, &limits);
        fields.push(("version", Json::string(version.to_string())));
        fields.push(("status", Json::string(report.status.tag())));
        if report.status.answer().is_none() {
            fields.push(("detail", Json::string(format!("{:?}", report.status))));
        }
        fields.push(("engine_wall_ns", Json::nanos(report.measurement.wall)));
        let process_wall = report
            .measurement
            .stages
            .iter()
            .find(|(name, _)| name == "process-wall")
            .map(|(_, duration)| *duration)
            .unwrap_or(report.measurement.wall);
        fields.push(("solver_process_wall_ns", Json::nanos(process_wall)));
        fields.push((
            "stages",
            Json::object(
                report
                    .measurement
                    .stages
                    .iter()
                    .map(|(name, duration)| (name.as_str(), Json::nanos(*duration))),
            ),
        ));
        if let Some(answer) = report.status.answer() {
            let mut basis: Vec<_> = answer
                .basis
                .as_ref()
                .expect("complete basis")
                .iter()
                .map(|s| {
                    let p = MultivariatePolynomial::<N, F>::parse(s, names)
                        .expect("external basis parses");
                    polynomial_to_string(
                        &p.scale(&p.leading_coefficient(ORDER).inverse()),
                        &names,
                        ORDER,
                    )
                })
                .collect();
            basis.sort();
            fields.push((
                "basis",
                Json::Array(basis.into_iter().map(Json::string).collect()),
            ));
        }
        std::fs::remove_dir_all(scratch).expect("remove private scratch");
    }
    Json::object(fields)
}

fn dispatch<F: FiniteField>(
    field: &str,
    modulus: &str,
    row: &str,
    engine: &str,
    list: bool,
) -> Json {
    macro_rules! go { ($($n:literal),*) => { match row.rsplit_once('-').unwrap().1 { $(stringify!($n) => run::<$n,F>(field,modulus,row,engine,list),)* _ => panic!("unregistered width") } }; }
    go!(4, 7, 8, 9, 10, 11, 12, 14, 16, 18)
}
fn main() {
    let args: Vec<_> = std::env::args().collect();
    let value = |key| {
        args.iter()
            .position(|s| s == key)
            .and_then(|i| args.get(i + 1))
            .map(String::as_str)
    };
    let list = args.iter().any(|s| s == "--list");
    let mut rows = Vec::new();
    for &(field, modulus) in FIELDS {
        if value("--field").is_some_and(|s| s != field) {
            continue;
        }
        for &row in ROWS {
            if !published(field, row) {
                continue;
            }
            if value("--row").is_some_and(|s| s != row) {
                continue;
            }
            if !list && (value("--row").is_none() || value("--field").is_none()) {
                panic!("--field and --row required");
            }
            let engine = value("--engine").unwrap_or("zeebra");
            rows.push(match field {
                "wide64" => dispatch::<Wide>(field, modulus, row, engine, list),
                "goldilocks" => dispatch::<Goldilocks>(field, modulus, row, engine, list),
                "bn254" => dispatch::<Bn254Fr>(field, modulus, row, engine, list),
                _ => unreachable!(),
            });
        }
    }
    assert!(!rows.is_empty(), "unknown field or row");
    println!(
        "{}",
        if list {
            Json::Array(rows).to_json()
        } else {
            assert_eq!(rows.len(), 1);
            rows.remove(0).to_json()
        }
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use zeebra::Zero;

    // Every field, variable order, generator and transformation reproduces its frozen SHA-256 pin.
    #[test]
    fn catalog_reproduces_every_frozen_identity() {
        fn generated<F: FiniteField>(field: &str, modulus: &str, row: &str) -> Json {
            macro_rules! metadata { ($($n:literal),*) => { match row.rsplit_once('-').unwrap().1 { $(stringify!($n) => Json::object(build::<$n,F>(field,modulus,row).fields),)* _ => unreachable!() } }; }
            metadata!(4, 7, 8, 9, 10, 11, 12, 14, 16, 18)
        }
        let mut actual = Vec::new();
        for &(field, modulus) in FIELDS {
            for &row in ROWS {
                if !published(field, row) {
                    continue;
                }
                actual.push(match field {
                    "wide64" => generated::<Wide>(field, modulus, row),
                    "goldilocks" => generated::<Goldilocks>(field, modulus, row),
                    "bn254" => generated::<Bn254Fr>(field, modulus, row),
                    _ => unreachable!(),
                });
            }
        }
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("research/wide-corpus/cases.json");
        let expected =
            Json::parse(&std::fs::read_to_string(path).expect("frozen catalog")).unwrap();
        assert_eq!(Json::Array(actual), expected);
    }

    // Dense random MQ has every quadratic, linear and constant coefficient and is reproducible.
    #[test]
    fn dense_random_mq_has_full_support_and_no_planted_origin() {
        let names = ["x1", "x2", "x3"];
        let system = dense_mq::<3, Goldilocks>();
        assert_eq!(system.len(), 3);
        assert_eq!(system, dense_mq::<3, Goldilocks>());
        for p in system {
            assert_eq!(p.terms().len(), 10);
            assert!(!p.eval(&[Goldilocks::zero(); 3]).is_zero());
            assert!(MultivariatePolynomial::<3, Goldilocks>::parse(
                &polynomial_to_string(&p, &names, ORDER),
                names
            )
            .is_ok());
        }
    }
}
