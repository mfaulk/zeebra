//! #1009: what each inexpensive input feature costs on one `corpus-instance-v1` record, beside the
//! cheapest shipping arm's solve of the same record, in one fresh process.
//!
//! cargo run --release --example feature_costs -- --catalog research/m34-public-corpus/catalog.json
//!     --id sd-caprasse@p31 [--wall-s 60] [--batches 7] [--min-batch-ms 2] [--solve-repeat 5]
//!     [--skip-solve]
//!
//! A feature's cost is the median per-call time over `--batches` batches, each batch long enough
//! (at least `--min-batch-ms`) for the clock to resolve it; the first, cold call is reported beside
//! it. The arms are `entry` (`f4_signature_reported`, the dispatch every caller reaches) and `f4`
//! (`f4_reported`), both on `F4Options::default()` with `max_wall_time`, interleaved; the
//! cheapest arm is the faster median of the two. Ratios are left to
//! `research/1009-feature-costs/summarize.py`: `Json` holds no floats.

use std::{
    hint::black_box,
    time::{Duration, Instant},
};
use zeebra::{
    fields::{Zp18446744073709551557, Zp2147483647},
    grobner::{
        f4_reported, f4_signature_reported, is_homogeneous,
        planning::{
            analyze, incidence, leading_profile, linear_subsystem, scalar_substitutions,
            support_profile, DEFAULT_OVERLAP_WORK, DEFAULT_PAIR_SAMPLE, DEFAULT_WIDTH_WORK,
        },
        F4Options,
    },
    util::Json,
    FiniteField, Monomial, MonomialOrder, MultivariatePolynomial,
};

const ORDER: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

#[derive(Debug, PartialEq)]
struct Args {
    catalog: String,
    id: String,
    wall: Duration,
    batches: usize,
    min_batch: Duration,
    solve_repeat: usize,
    skip_solve: bool,
}

fn parse_args(raw: &[String]) -> Result<Args, String> {
    let mut a = Args {
        catalog: String::new(),
        id: String::new(),
        wall: Duration::from_secs(60),
        batches: 7,
        min_batch: Duration::from_millis(2),
        solve_repeat: 5,
        skip_solve: false,
    };
    let mut it = raw.iter();
    while let Some(arg) = it.next() {
        let mut value = || it.next().cloned().ok_or(format!("{arg} needs a value"));
        let number = |v: String| v.parse::<u64>().map_err(|e| format!("{arg}: {e}"));
        match arg.as_str() {
            "--catalog" => a.catalog = value()?,
            "--id" => a.id = value()?,
            "--wall-s" => a.wall = Duration::from_secs(number(value()?)?),
            "--batches" => a.batches = number(value()?)? as usize,
            "--min-batch-ms" => a.min_batch = Duration::from_millis(number(value()?)?),
            "--solve-repeat" => a.solve_repeat = number(value()?)? as usize,
            "--skip-solve" => a.skip_solve = true,
            other => return Err(format!("unknown argument {other}")),
        }
    }
    if a.catalog.is_empty() || a.id.is_empty() {
        return Err("--catalog and --id are required".into());
    }
    if a.batches == 0 || a.solve_repeat == 0 {
        return Err("--batches and --solve-repeat must be positive".into());
    }
    Ok(a)
}

/// One catalog record: its ring and its equations as `(coefficient, exponents)` terms.
#[derive(Debug)]
struct Record {
    id: String,
    digest: String,
    characteristic: u64,
    variables: Vec<String>,
    equations: Vec<Vec<(u64, Vec<u32>)>>,
}

fn find_record(catalog: &str, id: &str) -> Result<Record, String> {
    let records = Json::parse(catalog).map_err(|e| format!("catalog is not JSON: {e:?}"))?;
    let record = records
        .items()
        .iter()
        .find(|r| r.get("id").and_then(Json::as_str) == Some(id))
        .ok_or(format!("no record {id}"))?;
    let text = |j: Option<&Json>, what: &str| {
        j.and_then(Json::as_str)
            .map(str::to_string)
            .ok_or(format!("{id}: missing {what}"))
    };
    if text(record.get("schema"), "schema")? != "corpus-instance-v1" {
        return Err(format!("{id}: not a corpus-instance-v1 record"));
    }
    if text(record.get("order"), "order")? != "grevlex" {
        return Err(format!("{id}: only grevlex records are supported"));
    }
    let field = record.get("field").ok_or(format!("{id}: missing field"))?;
    if field.get("extension_degree").and_then(Json::as_int) != Some(1) {
        return Err(format!("{id}: only prime fields are supported"));
    }
    let characteristic = text(field.get("characteristic"), "characteristic")?
        .parse::<u64>()
        .map_err(|e| format!("{id}: characteristic: {e}"))?;
    let variables = record
        .get("variables")
        .map_or(&[][..], Json::items)
        .iter()
        .map(|v| v.as_str().map(str::to_string).ok_or("non-string variable"))
        .collect::<Result<Vec<_>, _>>()?;
    let mut equations = Vec::new();
    for equation in record.get("equations").map_or(&[][..], Json::items) {
        let mut terms = Vec::new();
        for term in equation.items() {
            let coefficient = match term.get("coefficient").map(Json::items) {
                Some([c]) => text(Some(c), "coefficient")?
                    .parse::<u64>()
                    .map_err(|e| format!("{id}: coefficient: {e}"))?,
                _ => return Err(format!("{id}: a prime-field coefficient is one integer")),
            };
            let exponents = term
                .get("exponents")
                .map_or(&[][..], Json::items)
                .iter()
                .map(|e| e.as_int().and_then(|e| u32::try_from(e).ok()))
                .collect::<Option<Vec<u32>>>()
                .ok_or(format!("{id}: bad exponent"))?;
            if exponents.len() != variables.len() {
                return Err(format!("{id}: exponent vector of the wrong length"));
            }
            terms.push((coefficient, exponents));
        }
        equations.push(terms);
    }
    Ok(Record {
        id: id.to_string(),
        digest: text(
            record.get("normalized_input_digest"),
            "normalized_input_digest",
        )?,
        characteristic,
        variables,
        equations,
    })
}

fn polynomials<const N: usize, F: FiniteField>(
    record: &Record,
) -> Vec<MultivariatePolynomial<N, F>> {
    record
        .equations
        .iter()
        .map(|terms| {
            let terms: Vec<(F, Monomial<N>)> = terms
                .iter()
                .map(|(c, e)| (F::new(*c), Monomial::new(e)))
                .collect();
            MultivariatePolynomial::new(&terms)
        })
        .collect()
}

/// A feature's cost: the first call alone, then the median per-call time over `batches` batches of
/// `calls` calls each, `calls` doubled until one batch takes at least `min_batch`.
#[derive(Debug)]
struct Cost {
    cold: Duration,
    median: Duration,
    calls: u64,
}

fn cost<R>(mut f: impl FnMut() -> R, batches: usize, min_batch: Duration) -> Cost {
    let clock = Instant::now();
    black_box(f());
    let cold = clock.elapsed();
    let batch = |f: &mut dyn FnMut() -> R, calls: u64| {
        let clock = Instant::now();
        for _ in 0..calls {
            black_box(f());
        }
        clock.elapsed()
    };
    let mut calls = 1u64;
    while batch(&mut f, calls) < min_batch && calls < 1 << 24 {
        calls *= 2;
    }
    let mut per_call: Vec<Duration> = (0..batches)
        .map(|_| batch(&mut f, calls) / calls as u32)
        .collect();
    per_call.sort();
    Cost {
        cold,
        median: per_call[per_call.len() / 2],
        calls,
    }
}

fn cost_json(c: &Cost) -> Json {
    Json::object([
        ("cold_ns", Json::nanos(c.cold)),
        ("median_ns", Json::nanos(c.median)),
        ("calls_per_batch", Json::int(c.calls)),
    ])
}

/// Every extractor's cost, and the values the coverage summary reads.
fn features<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    args: &Args,
) -> (Json, Json) {
    let (b, mb) = (args.batches, args.min_batch);
    let costs = Json::object([
        ("system_shape", cost_json(&cost(|| analyze(system), b, mb))),
        (
            "is_homogeneous",
            cost_json(&cost(|| is_homogeneous(system), b, mb)),
        ),
        (
            "incidence",
            cost_json(&cost(|| incidence(system, DEFAULT_WIDTH_WORK), b, mb)),
        ),
        (
            "linear_subsystem",
            cost_json(&cost(|| linear_subsystem(system), b, mb)),
        ),
        (
            "scalar_substitutions",
            cost_json(&cost(|| scalar_substitutions(system), b, mb)),
        ),
        (
            "support_profile",
            cost_json(&cost(
                || support_profile(system, DEFAULT_OVERLAP_WORK),
                b,
                mb,
            )),
        ),
        (
            "leading_profile",
            cost_json(&cost(
                || leading_profile(system, ORDER, DEFAULT_PAIR_SAMPLE),
                b,
                mb,
            )),
        ),
    ]);

    let shape = analyze(system);
    let structure = incidence(system, DEFAULT_WIDTH_WORK);
    let linear = linear_subsystem(system);
    let substitutions = scalar_substitutions(system);
    let support = support_profile(system, DEFAULT_OVERLAP_WORK);
    let leading = leading_profile(system, ORDER, DEFAULT_PAIR_SAMPLE);
    let histogram = |h: &[(u64, usize)]| {
        Json::Array(
            h.iter()
                .map(|&(k, n)| Json::Array(vec![Json::int(k), Json::size(n)]))
                .collect(),
        )
    };
    let optional = |v: Option<u64>| v.map_or(Json::Null, Json::int);
    let values = Json::object([
        ("variables", Json::size(N)),
        ("generators", Json::size(shape.generators)),
        ("zero_generators", Json::size(shape.zero_generators)),
        ("terms", Json::size(shape.terms)),
        ("max_degree", Json::int(shape.max_degree)),
        ("degree_histogram", histogram(&shape.degree_histogram)),
        ("linear_generators", Json::size(shape.linear_generators)),
        (
            "quadratic_generators",
            Json::size(shape.quadratic_generators),
        ),
        (
            "univariate_generators",
            Json::size(shape.univariate_generators),
        ),
        ("interaction_pairs", Json::size(shape.interaction_pairs)),
        ("homogeneous", Json::Bool(is_homogeneous(system))),
        ("components", Json::size(structure.components.len())),
        (
            "largest_component_variables",
            Json::size(structure.largest_component_variables()),
        ),
        (
            "unused_variables",
            Json::size(structure.unused_variables.len()),
        ),
        (
            "constant_generators",
            Json::size(structure.constant_generators),
        ),
        (
            "max_arity",
            Json::size(structure.arity_histogram.last().map_or(0, |&(a, _)| a)),
        ),
        (
            "elimination_width",
            optional(structure.elimination_width.map(|w| w as u64)),
        ),
        (
            "linear_subsystem_generators",
            Json::size(linear.generators.len()),
        ),
        ("linear_rank", Json::size(linear.rank)),
        ("linear_consistent", Json::Bool(linear.consistent)),
        ("scalar_substitutions", Json::size(substitutions.len())),
        (
            "max_fill_bound",
            optional(substitutions.iter().map(|s| s.fill_bound).max()),
        ),
        ("nonzero_generators", Json::size(support.nonzero_generators)),
        ("top_degree_terms", Json::size(support.top_degree_terms)),
        (
            "homogeneous_capacity",
            Json::int(support.homogeneous_capacity),
        ),
        ("affine_capacity", Json::int(support.affine_capacity)),
        (
            "homogeneous_generators",
            Json::size(support.homogeneous_generators),
        ),
        ("distinct_monomials", Json::size(support.distinct_monomials)),
        ("shared_monomials", Json::size(support.shared_monomials)),
        ("overlapping_pairs", optional(support.overlapping_pairs)),
        (
            "monomial_generators",
            Json::size(support.monomial_generators),
        ),
        (
            "binomial_generators",
            Json::size(support.binomial_generators),
        ),
        (
            "duplicate_generators",
            Json::size(support.duplicate_generators),
        ),
        ("divisible_leading", Json::size(leading.divisible_leading)),
        ("total_pairs", Json::int(leading.total_pairs)),
        ("sampled_pairs", Json::int(leading.sampled_pairs)),
        ("coprime_pairs", Json::int(leading.coprime_pairs)),
        (
            "max_lcm_degree",
            optional(leading.lcm_degree_histogram.last().map(|&(d, _)| d)),
        ),
    ]);
    (costs, values)
}

/// One arm's calls: up to `solve_repeat`, stopping after the first that does not complete or once
/// the arm has spent ten seconds.
#[derive(Debug, Default)]
struct Arm {
    calls: Vec<Duration>,
    status: &'static str,
    error: Option<String>,
    basis_elements: Option<usize>,
    route: Option<String>,
}

impl Arm {
    fn median(&self) -> Option<Duration> {
        let mut sorted = self.calls.clone();
        sorted.sort();
        (self.status == "complete").then(|| sorted[sorted.len() / 2])
    }

    fn json(&self) -> Json {
        Json::object([
            ("status", Json::string(self.status)),
            (
                "error",
                self.error.as_ref().map_or(Json::Null, Json::string),
            ),
            (
                "basis_elements",
                self.basis_elements.map_or(Json::Null, Json::size),
            ),
            (
                "route",
                self.route.as_ref().map_or(Json::Null, Json::string),
            ),
            (
                "calls_ns",
                Json::Array(self.calls.iter().map(|&d| Json::nanos(d)).collect()),
            ),
            ("median_ns", self.median().map_or(Json::Null, Json::nanos)),
        ])
    }
}

fn solve<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    args: &Args,
) -> (Arm, Arm) {
    let options = F4Options {
        max_wall_time: Some(args.wall),
        ..F4Options::default()
    };
    let spent = Duration::from_secs(10);
    let (mut entry, mut f4) = (Arm::default(), Arm::default());
    let open = |arm: &Arm| {
        arm.calls.len() < args.solve_repeat
            && (arm.calls.is_empty() || arm.status == "complete")
            && arm.calls.iter().sum::<Duration>() < spent
    };
    // Interleaved, so both arms see the same box.
    while open(&entry) || open(&f4) {
        if open(&entry) {
            let clock = Instant::now();
            let (result, report) = f4_signature_reported(system, ORDER, &options);
            entry.calls.push(clock.elapsed());
            entry.route = Some(format!("{:?}", report.route));
            record(
                &mut entry,
                result.map(|b| b.len()).map_err(|e| format!("{e:?}")),
            );
        }
        if open(&f4) {
            let clock = Instant::now();
            let (result, _) = f4_reported(system, ORDER, &options);
            f4.calls.push(clock.elapsed());
            record(
                &mut f4,
                result.map(|b| b.len()).map_err(|e| format!("{e:?}")),
            );
        }
    }
    (entry, f4)
}

fn record(arm: &mut Arm, result: Result<usize, String>) {
    match result {
        Ok(n) => {
            arm.status = "complete";
            arm.basis_elements = Some(n);
        }
        Err(e) => {
            arm.status = if e.contains("Unsupported") {
                "refused"
            } else {
                "stopped"
            };
            arm.error = Some(e);
        }
    }
}

fn measure<const N: usize, F: FiniteField>(
    record: &Record,
    args: &Args,
) -> Vec<(&'static str, Json)> {
    let system = polynomials::<N, F>(record);
    let (costs, values) = features(&system, args);
    let mut out = vec![("feature_costs", costs), ("features", values)];
    if !args.skip_solve {
        let (entry, f4) = solve(&system, args);
        let cheapest = match (entry.median(), f4.median()) {
            (Some(a), Some(b)) if b < a => ("f4", Json::nanos(b)),
            (Some(a), _) => ("entry", Json::nanos(a)),
            (None, Some(b)) => ("f4", Json::nanos(b)),
            (None, None) => ("none", Json::Null),
        };
        out.push(("entry", entry.json()));
        out.push(("f4", f4.json()));
        out.push(("cheapest_arm", Json::string(cheapest.0)));
        out.push(("cheapest_ns", cheapest.1));
    }
    out
}

fn run(record: &Record, args: &Args) -> Result<Json, String> {
    macro_rules! dispatch {
        ($($p:literal => $f:ty),*) => {
            match (record.characteristic, record.variables.len()) {
                $(($p, 2) => measure::<2, $f>(record, args), ($p, 3) => measure::<3, $f>(record, args),
                  ($p, 4) => measure::<4, $f>(record, args), ($p, 5) => measure::<5, $f>(record, args),
                  ($p, 6) => measure::<6, $f>(record, args), ($p, 7) => measure::<7, $f>(record, args),
                  ($p, 8) => measure::<8, $f>(record, args), ($p, 9) => measure::<9, $f>(record, args),
                  ($p, 10) => measure::<10, $f>(record, args), ($p, 11) => measure::<11, $f>(record, args),
                  ($p, 12) => measure::<12, $f>(record, args), ($p, 13) => measure::<13, $f>(record, args),
                  ($p, 14) => measure::<14, $f>(record, args), ($p, 15) => measure::<15, $f>(record, args),
                  ($p, 16) => measure::<16, $f>(record, args), ($p, 34) => measure::<34, $f>(record, args),)*
                (p, n) => return Err(format!("no instantiation for p = {p} with {n} variables")),
            }
        };
    }
    let mut fields = vec![
        ("id", Json::string(&record.id)),
        ("digest", Json::string(&record.digest)),
        (
            "characteristic",
            Json::string(record.characteristic.to_string()),
        ),
        ("wall_s", Json::int(args.wall.as_secs())),
    ];
    fields.extend(dispatch!(
        2147483647 => Zp2147483647, 18446744073709551557 => Zp18446744073709551557
    ));
    Ok(Json::object(fields))
}

fn main() {
    let raw: Vec<String> = std::env::args().skip(1).collect();
    let args = parse_args(&raw).unwrap_or_else(|e| panic!("{e}"));
    let catalog = std::fs::read_to_string(&args.catalog).expect("readable catalog");
    let record = find_record(&catalog, &args.id).unwrap_or_else(|e| panic!("{e}"));
    let line = run(&record, &args).unwrap_or_else(|e| panic!("{e}"));
    println!("{}", line.to_json().replace('\n', ""));
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `x² + y² − 1` and `x − y` at 2³¹−1, as the catalog writes them.
    const CIRCLE: &str = r#"[{"equations":[[{"coefficient":["2147483646"],"exponents":[0,0]},{"coefficient":["1"],"exponents":[0,2]},{"coefficient":["1"],"exponents":[2,0]}],[{"coefficient":["1"],"exponents":[1,0]},{"coefficient":["2147483646"],"exponents":[0,1]}]],"field":{"characteristic":"2147483647","defining_polynomial":[],"extension_degree":1},"id":"circle@p31","normalized_input_digest":"00","order":"grevlex","schema":"corpus-instance-v1","task":"T-GB","variables":["x","y"]}]"#;

    fn args(extra: &[&str]) -> Args {
        let mut raw = vec!["--catalog", "c.json", "--id", "circle@p31"];
        raw.extend_from_slice(extra);
        parse_args(&raw.iter().map(|s| s.to_string()).collect::<Vec<_>>()).unwrap()
    }

    // A record's exponent vectors and reduced coefficients build exactly the polynomials its text names.
    #[test]
    fn record_builds_the_polynomials_it_names() {
        let record = find_record(CIRCLE, "circle@p31").unwrap();
        assert_eq!(record.characteristic, 2147483647);
        let system = polynomials::<2, Zp2147483647>(&record);
        let expected = ["x^2 + y^2 - 1", "x - y"]
            .map(|s| MultivariatePolynomial::<2, Zp2147483647>::parse(s, ["x", "y"]).unwrap());
        assert_eq!(system, expected);
    }

    // Unknown ids, other orders and extension fields are refused rather than reinterpreted.
    #[test]
    fn refuses_what_it_cannot_measure() {
        assert!(find_record(CIRCLE, "absent").is_err());
        assert!(find_record(&CIRCLE.replace("grevlex", "lex"), "circle@p31").is_err());
        assert!(find_record(
            &CIRCLE.replace("\"extension_degree\":1", "\"extension_degree\":2"),
            "circle@p31"
        )
        .is_err());
    }

    // Defaults are a 60 s wall and seven batches; a missing id or a zero repeat is refused.
    #[test]
    fn parses_arguments() {
        let a = args(&[]);
        assert_eq!(a.wall, Duration::from_secs(60));
        assert_eq!(a.batches, 7);
        assert!(!a.skip_solve);
        assert_eq!(
            args(&["--wall-s", "5", "--skip-solve"]).wall,
            Duration::from_secs(5)
        );
        assert!(parse_args(&["--catalog".into(), "c".into()]).is_err());
        let zero: Vec<String> = ["--catalog", "c", "--id", "i", "--solve-repeat", "0"]
            .iter()
            .map(|s| s.to_string())
            .collect();
        assert!(parse_args(&zero).is_err());
    }

    // The cost of a feature counts every call it batches and never reports a zero-call median.
    #[test]
    fn cost_batches_until_the_clock_resolves() {
        let mut calls = 0u64;
        let c = cost(
            || {
                calls += 1;
                calls
            },
            3,
            Duration::from_micros(200),
        );
        assert!(c.calls >= 1);
        assert!(c.median * c.calls as u32 <= Duration::from_secs(1));
        assert!(calls >= 1 + 3 * c.calls);
    }

    // One measured record carries every extractor's cost, the incidence the circle has, and both arms.
    #[test]
    fn measures_a_record_end_to_end() {
        let record = find_record(CIRCLE, "circle@p31").unwrap();
        let a = args(&[
            "--batches",
            "1",
            "--min-batch-ms",
            "0",
            "--solve-repeat",
            "1",
        ]);
        let line = run(&record, &a).unwrap();
        let costs = line.get("feature_costs").unwrap();
        for name in [
            "system_shape",
            "is_homogeneous",
            "incidence",
            "linear_subsystem",
            "scalar_substitutions",
            "support_profile",
            "leading_profile",
        ] {
            assert!(
                costs.get(name).and_then(|c| c.get("median_ns")).is_some(),
                "{name}"
            );
        }
        let values = line.get("features").unwrap();
        assert_eq!(values.get("components").and_then(Json::as_int), Some(1));
        assert_eq!(
            values.get("interaction_pairs").and_then(Json::as_int),
            Some(0)
        );
        assert_eq!(values.get("linear_rank").and_then(Json::as_int), Some(1));
        for arm in ["entry", "f4"] {
            assert_eq!(
                line.get(arm)
                    .and_then(|a| a.get("status"))
                    .and_then(Json::as_str),
                Some("complete"),
                "{arm}"
            );
        }
        assert!(line.get("cheapest_ns").and_then(Json::as_int).is_some());
    }
}
