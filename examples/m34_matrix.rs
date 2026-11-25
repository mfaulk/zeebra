//! #1012 Gate H: one fresh-process solve of one `corpus-instance-v1` record by one portfolio arm,
//! for the development-panel performance matrix (`research/m34-gate-h/`).
//!
//! cargo run --release --features research-sigf4 --example m34_matrix -- --catalog FILE --id ID
//!     [--engine f4|cap16|adaptive|sig] [--workers N] [--wall-s S]
//!
//! The engines set exactly the options `examples/m33_qualify.rs` gives the #1011 arms on Z0, so a
//! cell here is the arm #1011 qualified. A typed refusal or budget stop is a normal exit with
//! `status` "refused" or "stopped" and the error's `Debug` text, the shape `tools/bench-job`'s
//! selection-outcome classifier reads. `basis_sha256` is the corpus's `reduced-basis-v1` digest
//! (`tools/m34_public_corpus.py basis_digest`), so it compares directly with the panel's
//! `references.json`.

use std::time::{Duration, Instant};
use zeebra::{
    fields::{Zp18446744073709551557, Zp2147483647},
    grobner::{f4_reported, F4Options, GradedEngine, ParallelForward, ParallelSymbolic},
    util::{peak_resident_bytes, sha256_hex, Json},
    FiniteField, Monomial, MonomialOrder, MultivariatePolynomial,
};

const ORDER: MonomialOrder = MonomialOrder::GradedReverseLexicographic;
const ENGINES: [&str; 4] = ["f4", "cap16", "adaptive", "sig"];

#[derive(Debug, PartialEq)]
struct Args {
    catalog: String,
    id: String,
    engine: String,
    workers: usize,
    wall: Duration,
}

fn parse_args(raw: &[String]) -> Result<Args, String> {
    let mut a = Args {
        catalog: String::new(),
        id: String::new(),
        engine: "f4".into(),
        workers: 1,
        wall: Duration::from_secs(300),
    };
    let mut it = raw.iter();
    while let Some(arg) = it.next() {
        let mut value = || it.next().cloned().ok_or(format!("{arg} needs a value"));
        match arg.as_str() {
            "--catalog" => a.catalog = value()?,
            "--id" => a.id = value()?,
            "--engine" => a.engine = value()?,
            "--workers" => a.workers = value()?.parse().map_err(|_| "--workers")?,
            "--wall-s" => a.wall = Duration::from_secs(value()?.parse().map_err(|_| "--wall-s")?),
            other => return Err(format!("unknown argument {other}")),
        }
    }
    if a.catalog.is_empty() || a.id.is_empty() {
        return Err("--catalog and --id are required".into());
    }
    if !ENGINES.contains(&a.engine.as_str()) {
        return Err(format!("unknown engine {}", a.engine));
    }
    if a.workers == 0 {
        return Err("--workers must be positive".into());
    }
    Ok(a)
}

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

/// JSON string as Python's `json.dumps(..., ensure_ascii=True)` writes it.
fn json_string(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 || (c as u32) > 0x7e => {
                let mut buf = [0u16; 2];
                for unit in c.encode_utf16(&mut buf) {
                    out.push_str(&format!("\\u{unit:04x}"));
                }
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// `reduced-basis-v1`: the compact, sorted-key JSON of `{basis, field, format, order, variables}`,
/// each element monic at its grevlex leading term with its terms sorted by exponent tuple, and the
/// elements sorted by their encoded bytes; exactly `tools/m34_public_corpus.py basis_digest`.
fn reduced_basis_digest<const N: usize, F: FiniteField>(
    basis: &[MultivariatePolynomial<N, F>],
    record: &Record,
) -> String {
    let mut elements: Vec<String> = basis
        .iter()
        .filter(|p| !p.is_zero())
        .map(|p| {
            let mut terms: Vec<_> = p.terms().iter().collect();
            let lead = terms.iter().max_by(|a, b| ORDER.cmp(a.0, b.0)).unwrap();
            let scale = lead.1.inverse();
            terms.sort_unstable_by(|a, b| a.0.exponents().cmp(b.0.exponents()));
            let body: Vec<String> = terms
                .iter()
                .map(|(m, c)| {
                    let e: Vec<String> = m.exponents().iter().map(u32::to_string).collect();
                    format!("[[{}],[\"{}\"]]", e.join(","), **c * scale)
                })
                .collect();
            format!("[{}]", body.join(","))
        })
        .collect();
    elements.sort_unstable();
    let variables: Vec<String> = record.variables.iter().map(|v| json_string(v)).collect();
    let text = format!(
        "{{\"basis\":[{}],\"field\":{{\"characteristic\":\"{}\",\"defining_polynomial\":[],\"extension_degree\":1}},\"format\":\"reduced-basis-v1\",\"order\":\"grevlex\",\"variables\":[{}]}}",
        elements.join(","),
        record.characteristic,
        variables.join(",")
    );
    sha256_hex(text.as_bytes())
}

/// The options #1011's `m33_qualify` gives every engine: the wall budget and `workers` as both
/// teams' cap, then the one option an arm changes.
fn options(args: &Args) -> F4Options {
    let w = args.workers;
    let shared = F4Options {
        max_wall_time: Some(args.wall),
        parallel_forward: if w == 1 {
            ParallelForward::Serial
        } else {
            ParallelForward::Auto { max_workers: w }
        },
        parallel_symbolic: if w == 1 {
            ParallelSymbolic::Serial
        } else {
            ParallelSymbolic::Auto { max_workers: w }
        },
        ..F4Options::default()
    };
    match args.engine.as_str() {
        "cap16" => F4Options {
            max_pairs_per_batch: Some(16),
            ..shared
        },
        "adaptive" => F4Options {
            graded_engine: GradedEngine::Adaptive,
            ..shared
        },
        _ => shared,
    }
}

#[cfg(feature = "research-sigf4")]
fn sig_options(args: &Args) -> zeebra::grobner::sigf4::SigF4Options {
    zeebra::grobner::sigf4::SigF4Options {
        max_wall_time: Some(args.wall),
        workers: args.workers,
        parallel_cascade: args.workers > 1,
        ..zeebra::grobner::sigf4::SigF4Options::default()
    }
}

fn run<const N: usize, F: FiniteField>(record: &Record, args: &Args) -> Vec<(&'static str, Json)> {
    let system = polynomials::<N, F>(record);
    let clock = Instant::now();
    let (result, route) = match args.engine.as_str() {
        #[cfg(feature = "research-sigf4")]
        "sig" => {
            let (result, _) =
                zeebra::grobner::sigf4::sig_f4_reported(&system, ORDER, &sig_options(args));
            (
                result.map_err(|e| format!("{e:?}")),
                Some(("Forced".to_string(), args.workers)),
            )
        }
        #[cfg(not(feature = "research-sigf4"))]
        "sig" => (
            Err("Unsupported: built without research-sigf4".to_string()),
            None,
        ),
        _ => {
            let (result, statistics) = f4_reported(&system, ORDER, &options(args));
            let route = statistics
                .graded_route
                .map(|d| (format!("{:?}", d.route), d.workers));
            (result.map_err(|e| format!("{e:?}")), route)
        }
    };
    let call = clock.elapsed();
    let status = match &result {
        Ok(_) => "complete",
        Err(e) if e.contains("Unsupported") => "refused",
        Err(_) => "stopped",
    };
    vec![
        ("status", Json::string(status)),
        (
            "error",
            result.as_ref().err().map_or(Json::Null, Json::string),
        ),
        (
            "route",
            route.as_ref().map_or(Json::Null, |r| Json::string(&r.0)),
        ),
        (
            "team",
            route.as_ref().map_or(Json::Null, |r| Json::size(r.1)),
        ),
        (
            "basis_sha256",
            result.as_ref().map_or(Json::Null, |b| {
                Json::string(reduced_basis_digest(b, record))
            }),
        ),
        (
            "basis_elements",
            result.as_ref().map_or(Json::Null, |b| Json::size(b.len())),
        ),
        ("call_ns", Json::nanos(call)),
    ]
}

fn solve(record: &Record, args: &Args) -> Result<Vec<(&'static str, Json)>, String> {
    macro_rules! dispatch {
        ($($p:literal => $f:ty),*) => {
            match (record.characteristic, record.variables.len()) {
                $(($p, 2) => run::<2, $f>(record, args), ($p, 3) => run::<3, $f>(record, args),
                  ($p, 4) => run::<4, $f>(record, args), ($p, 5) => run::<5, $f>(record, args),
                  ($p, 6) => run::<6, $f>(record, args), ($p, 7) => run::<7, $f>(record, args),
                  ($p, 8) => run::<8, $f>(record, args), ($p, 9) => run::<9, $f>(record, args),
                  ($p, 10) => run::<10, $f>(record, args), ($p, 11) => run::<11, $f>(record, args),
                  ($p, 12) => run::<12, $f>(record, args), ($p, 13) => run::<13, $f>(record, args),
                  ($p, 14) => run::<14, $f>(record, args), ($p, 15) => run::<15, $f>(record, args),
                  ($p, 16) => run::<16, $f>(record, args), ($p, 18) => run::<18, $f>(record, args),
                  ($p, 20) => run::<20, $f>(record, args), ($p, 21) => run::<21, $f>(record, args),
                  ($p, 22) => run::<22, $f>(record, args), ($p, 24) => run::<24, $f>(record, args),
                  ($p, 25) => run::<25, $f>(record, args), ($p, 34) => run::<34, $f>(record, args),)*
                (p, n) => return Err(format!("no instantiation for p = {p} with {n} variables")),
            }
        };
    }
    Ok(dispatch!(
        2147483647 => Zp2147483647, 18446744073709551557 => Zp18446744073709551557
    ))
}

fn main() {
    let started = Instant::now();
    let raw: Vec<String> = std::env::args().skip(1).collect();
    let args = parse_args(&raw).unwrap_or_else(|e| panic!("{e}"));
    let catalog = std::fs::read_to_string(&args.catalog).unwrap_or_else(|e| panic!("{e}"));
    let record = find_record(&catalog, &args.id).unwrap_or_else(|e| panic!("{e}"));
    let mut fields = vec![
        ("id", Json::string(&record.id)),
        ("digest", Json::string(&record.digest)),
        (
            "characteristic",
            Json::string(record.characteristic.to_string()),
        ),
        ("engine", Json::string(&args.engine)),
        ("workers", Json::size(args.workers)),
    ];
    match solve(&record, &args) {
        Ok(solved) => fields.extend(solved),
        Err(e) => {
            fields.push(("status", Json::string("refused")));
            fields.push(("error", Json::string(format!("Unsupported: {e}"))));
        }
    }
    fields.push((
        "peak_rss_bytes",
        peak_resident_bytes().map(Json::int).unwrap_or(Json::Null),
    ));
    fields.push(("main_ns", Json::nanos(started.elapsed())));
    println!("{}", Json::object(fields).to_json().replace('\n', ""));
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(extra: &[&str]) -> Result<Args, String> {
        let mut raw: Vec<String> = ["--catalog", "c.json", "--id", "x@p31"]
            .iter()
            .map(|s| s.to_string())
            .collect();
        raw.extend(extra.iter().map(|s| s.to_string()));
        parse_args(&raw)
    }

    const CATALOG: &str = r#"[{"schema":"corpus-instance-v1","id":"x@p31","order":"grevlex",
        "field":{"characteristic":"2147483647","extension_degree":1,"defining_polynomial":[]},
        "variables":["x1","x2"],"normalized_input_digest":"d",
        "equations":[[{"exponents":[2,0],"coefficient":["3"]},{"exponents":[0,1],"coefficient":["1"]}],
                     [{"exponents":[0,2],"coefficient":["1"]},{"exponents":[0,0],"coefficient":["2147483646"]}]]}]"#;

    /// Arguments are validated: unknown engines, zero workers and missing inputs are refused.
    #[test]
    fn arguments_are_validated() {
        assert_eq!(
            args(&["--engine", "sig", "--workers", "8"])
                .unwrap()
                .workers,
            8
        );
        assert!(args(&["--engine", "entry"]).is_err());
        assert!(args(&["--workers", "0"]).is_err());
        assert!(parse_args(&["--id".into(), "x".into()]).is_err());
    }

    /// The reduced-basis digest equals `basis_digest` in `tools/m34_public_corpus.py` on a fixed basis.
    #[test]
    fn digest_matches_the_python_reference() {
        let record = find_record(CATALOG, "x@p31").unwrap();
        let basis = polynomials::<2, Zp2147483647>(&record);
        // python3 -c 'import sys; sys.path.insert(0,"tools"); import m34_public_corpus as m, json;
        //   r=json.loads(open("c.json").read())[0];
        //   print(m.basis_digest(r,[{(2,0):3,(0,1):1},{(0,2):1,(0,0):-1}]))'
        assert_eq!(
            reduced_basis_digest(&basis, &record),
            "57758064fdf86dbe294d5d2209357d19fbaa82d4d6833a546e0156d72eff0bb2"
        );
    }

    /// Every engine on a small record returns the same reduced basis.
    #[test]
    fn engines_agree_on_a_small_record() {
        let record = find_record(CATALOG, "x@p31").unwrap();
        let digests: Vec<String> = ["f4", "cap16", "adaptive"]
            .iter()
            .map(|engine| {
                let a = Args {
                    catalog: String::new(),
                    id: record.id.clone(),
                    engine: engine.to_string(),
                    workers: 1,
                    wall: Duration::from_secs(10),
                };
                let out = solve(&record, &a).unwrap();
                let get = |k| out.iter().find(|(key, _)| *key == k).unwrap().1.to_json();
                assert_eq!(get("status"), "\"complete\"");
                get("basis_sha256")
            })
            .collect();
        assert!(digests.windows(2).all(|w| w[0] == w[1]));
    }
}
