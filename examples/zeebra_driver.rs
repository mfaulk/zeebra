//! Fresh-process Zeebra for `tools/external/comparand-scaling.py` (#820): reads the request JSON the
//! native comparand drivers read and prints one result object, so Zeebra's process wall is taken on
//! the same boundary as theirs. F4 never uses more forward or symbolic workers than the
//! request's `workers`.
//!
//! cargo run --release --example zeebra_driver -- REQUEST.json
use std::time::{Duration, Instant};
use zeebra::{
    fields::PrimeFieldElement64,
    grobner::{
        external::{ExternalSolver, FieldSpec, Instance, Limits, Task, ZeebraSolver},
        F4Options,
    },
    util::{peak_resident_bytes, Json},
    MonomialOrder,
};

type Goldilocks = PrimeFieldElement64<18446744069414584321>;
type Wide = PrimeFieldElement64<18446744073709551263>;

#[derive(Debug)]
struct Request {
    variables: Vec<String>,
    modulus: u64,
    generators: Vec<String>,
    workers: usize,
    wall: Duration,
}

fn parse_request(text: &str) -> Result<Request, String> {
    let json = Json::parse(text).map_err(|e| format!("request is not JSON: {e:?}"))?;
    let strings = |key: &str| -> Result<Vec<String>, String> {
        json.get(key)
            .ok_or(format!("missing {key}"))?
            .items()
            .iter()
            .map(|s| {
                s.as_str()
                    .map(str::to_string)
                    .ok_or(format!("{key} holds a non-string"))
            })
            .collect()
    };
    let int = |key: &str| json.get(key).and_then(Json::as_int);
    if json.get("order").and_then(Json::as_str) != Some("grevlex") {
        return Err("only grevlex requests are supported".into());
    }
    let modulus = int("modulus")
        .and_then(|m| u64::try_from(m).ok())
        .ok_or("modulus must be a u64")?;
    let workers = int("workers")
        .and_then(|w| usize::try_from(w).ok())
        .filter(|&w| w > 0)
        .ok_or("workers must be a positive integer")?;
    let wall = match int("wall_ns") {
        None => Duration::from_secs(60),
        Some(ns) => Duration::from_nanos(u64::try_from(ns).map_err(|_| "wall_ns out of range")?),
    };
    Ok(Request {
        variables: strings("variables")?,
        modulus,
        generators: strings("generators")?,
        workers,
        wall,
    })
}

/// The adapter plus the grid's widths it does not compile itself: Goldilocks at every width the
/// #739 grid uses, and the wide prime at the two the competitive ladder lacks.
fn solver(wall: Duration) -> ZeebraSolver {
    let registered = ZeebraSolver::new()
        .measuring_one_row()
        .with_f4_options(F4Options {
            max_wall_time: Some(wall),
            ..F4Options::default()
        })
        .with_instantiation::<4, Goldilocks>()
        .and_then(|s| s.with_instantiation::<7, Goldilocks>())
        .and_then(|s| s.with_instantiation::<9, Goldilocks>())
        .and_then(|s| s.with_instantiation::<10, Goldilocks>())
        .and_then(|s| s.with_instantiation::<7, Wide>())
        .and_then(|s| s.with_instantiation::<9, Wide>());
    registered.expect("prime fields and nonzero widths register")
}

fn run(request: &Request) -> Json {
    let instance = Instance::new(
        "comparand-request",
        "comparand-request",
        FieldSpec::prime(request.modulus),
        request.variables.clone(),
        request.generators.clone(),
        MonomialOrder::GradedReverseLexicographic,
    );
    let limits = Limits::wall(request.wall).with_workers(request.workers);
    let started = Instant::now();
    let report = solver(request.wall).run(&instance, Task::ReducedGrobnerBasis, &limits);
    let run_ns = started.elapsed();
    let basis = report
        .status
        .answer()
        .and_then(|answer| answer.basis.clone())
        .map(|basis| Json::Array(basis.into_iter().map(Json::string).collect()))
        .unwrap_or(Json::Null);
    let detail = if report.status.answered() {
        Json::Null
    } else {
        Json::string(format!("{:?}", report.status))
    };
    Json::object([
        ("contract", Json::int(1)),
        ("engine", Json::string("zeebra")),
        (
            "variables",
            Json::Array(request.variables.iter().map(Json::string).collect()),
        ),
        // A string: the wide moduli do not fit every JSON reader's integers.
        ("modulus", Json::string(request.modulus.to_string())),
        ("order", Json::string("grevlex")),
        ("workers", Json::int(request.workers as i128)),
        ("status", Json::string(report.status.tag())),
        ("detail", detail),
        ("basis", basis),
        ("solve_ns", Json::nanos(report.measurement.wall)),
        ("run_ns", Json::nanos(run_ns)),
        (
            "kernel_peak_rss_bytes",
            peak_resident_bytes().map(Json::int).unwrap_or(Json::Null),
        ),
    ])
}

fn main() {
    let path = std::env::args()
        .nth(1)
        .expect("usage: zeebra_driver REQUEST.json");
    let text = std::fs::read_to_string(&path).expect("readable request");
    let request = parse_request(&text).unwrap_or_else(|error| panic!("{error}"));
    println!("{}", run(&request).to_json());
}

#[cfg(test)]
mod tests {
    use super::*;

    fn request(modulus: &str, workers: usize, order: &str) -> String {
        format!(
            r#"{{"variables":["x","y"],"modulus":{modulus},"order":"{order}","generators":["x^2 - 1","y - x"],"workers":{workers}}}"#
        )
    }

    // A comparand request parses into its ring, generators, workers and the default 60 s wall.
    #[test]
    fn parses_a_comparand_request() {
        let parsed = parse_request(&request("18446744069414584321", 4, "grevlex")).unwrap();
        assert_eq!(parsed.variables, ["x", "y"]);
        assert_eq!(parsed.modulus, 18446744069414584321);
        assert_eq!(parsed.generators, ["x^2 - 1", "y - x"]);
        assert_eq!(parsed.workers, 4);
        assert_eq!(parsed.wall, Duration::from_secs(60));
    }

    // Orders other than grevlex and a zero worker count are refused rather than reinterpreted.
    #[test]
    fn refuses_other_orders_and_zero_workers() {
        assert!(parse_request(&request("32003", 1, "lex")).is_err());
        assert!(parse_request(&request("32003", 0, "grevlex")).is_err());
    }

    // Every comparand field and width the #739 grid uses solves, and the result echoes its ring.
    #[test]
    fn solves_every_grid_field_and_echoes_the_request() {
        for modulus in [
            32003u64,
            2147483647,
            18446744073709551263,
            18446744069414584321,
        ] {
            for width in [4usize, 7, 9, 10] {
                let variables: Vec<String> = (1..=width).map(|i| format!("x{i}")).collect();
                let mut generators: Vec<String> =
                    variables.iter().map(|v| format!("{v}^2 - 1")).collect();
                generators.push(format!("{} - {}", variables[0], variables[1]));
                let parsed = Request {
                    variables: variables.clone(),
                    modulus,
                    generators,
                    workers: 2,
                    wall: Duration::from_secs(60),
                };
                let result = run(&parsed);
                assert_eq!(
                    result.get("status").and_then(Json::as_str),
                    Some("complete"),
                    "{modulus} {width}: {}",
                    result.to_json()
                );
                assert_eq!(result.get("workers").and_then(Json::as_int), Some(2));
                assert_eq!(
                    result.get("modulus").and_then(Json::as_str),
                    Some(modulus.to_string().as_str())
                );
                assert_eq!(
                    result.get("basis").map(|b| b.items().len()),
                    Some(width),
                    "{modulus} {width}"
                );
            }
        }
    }
}
