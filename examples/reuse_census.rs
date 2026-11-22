//! #1031's reduced-multiple reuse census: one fresh-process run of the conventional F4 defaults or
//! the signature engine, at one worker, on a pinned M29 row or a generated dense quadratic system.
//!
//! cargo run --release --features research-reuse --example reuse_census -- \
//!     --row eco12-wide64|katsura11-m31|mq10-32003|mq10-m31|mq11-goldilocks|dmq-n<N>-m<M>-<field>-s<S>[-u]
//!     --engine f4|sigf4 [--census] [--stages] [--wall-s 180]
//!
//! Without `--census` the run is the timed arm: the engine as it ships at one worker (`--stages` adds
//! the conventional engine's stage clocks, which cost it a few percent). With `--census`
//! (`--features research-reuse`) every batch is replayed by `grobner::reuse_census`; that run is
//! untimed. Both report `basis_sha256`, which must agree.
//!
//! `dmq-n<N>-m<M>-<field>-s<S>` is #1030's dense quadratic cohort: `M` equations in `N` variables
//! over `gf31`, `gf32003`, `m31` (2^31-1) or `p64` (2^64-59), each of the 1 + N + N(N+1)/2 monomials
//! of degree at most two present with probability one half under support seed `S`, coefficients
//! uniform and nonzero, and a planted point; `-u` drops the plant.
#![cfg_attr(not(feature = "research-reuse"), allow(unused))]

use std::time::{Duration, Instant};
use zeebra::{
    fields::{PrimeFieldElement64, Zp18446744073709551557, Zp2147483647, Zp31, Zp32003},
    grobner::{
        differential::polynomial_to_string,
        external::corpus,
        f4_reported,
        sigf4::{sig_f4_reported, SigF4Options},
        F4Options, ParallelForward, ParallelSymbolic,
    },
    util::{peak_resident_bytes, sha256_hex, Json},
    FiniteField, Monomial, MonomialOrder, MultivariatePolynomial,
};

type Goldilocks = PrimeFieldElement64<18446744069414584321>;
type Wide = PrimeFieldElement64<18446744073709551263>;
const ORDER: MonomialOrder = MonomialOrder::GradedReverseLexicographic;
const PINNED: &[&str] = &[
    "eco12-wide64",
    "katsura11-m31",
    "mq10-32003",
    "mq10-m31",
    "mq11-goldilocks",
];
/// The variable counts a generated row may have; each is a separate monomorphization.
const SIZES: &[usize] = &[6, 7, 8, 9, 10, 11, 12, 13, 14];
const FIELDS: &[&str] = &["gf31", "gf32003", "m31", "p64"];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Engine {
    F4,
    SigF4,
}

#[derive(Debug, PartialEq)]
struct Args {
    row: String,
    engine: Engine,
    census: bool,
    stages: bool,
    wall: Duration,
}

/// A generated row's shape: `m` equations in `n` variables over `field`, support seed `seed`.
#[derive(Debug, PartialEq, Eq)]
struct Dense {
    n: usize,
    m: usize,
    field: String,
    seed: u64,
    planted: bool,
}

fn parse_dense(name: &str) -> Option<Dense> {
    let rest = name.strip_prefix("dmq-")?;
    let (rest, planted) = match rest.strip_suffix("-u") {
        Some(r) => (r, false),
        None => (rest, true),
    };
    let parts: Vec<&str> = rest.split('-').collect();
    let [n, m, field, seed] = parts[..] else {
        return None;
    };
    let dense = Dense {
        n: n.strip_prefix('n')?.parse().ok()?,
        m: m.strip_prefix('m')?.parse().ok()?,
        field: field.to_string(),
        seed: seed.strip_prefix('s')?.parse().ok()?,
        planted,
    };
    (SIZES.contains(&dense.n) && FIELDS.contains(&field) && dense.m >= dense.n).then_some(dense)
}

fn parse_args(args: &[String]) -> Result<Args, String> {
    let mut parsed = Args {
        row: String::new(),
        engine: Engine::F4,
        census: false,
        stages: false,
        wall: Duration::from_secs(180),
    };
    let mut engine = None;
    let mut it = args.iter();
    while let Some(arg) = it.next() {
        let mut value = || it.next().cloned().ok_or(format!("{arg} needs a value"));
        match arg.as_str() {
            "--row" => parsed.row = value()?,
            "--engine" => {
                engine = Some(match value()?.as_str() {
                    "f4" => Engine::F4,
                    "sigf4" => Engine::SigF4,
                    other => return Err(format!("unknown engine {other}")),
                })
            }
            "--census" => parsed.census = true,
            "--stages" => parsed.stages = true,
            "--wall-s" => {
                parsed.wall = Duration::from_secs(
                    value()?
                        .parse()
                        .map_err(|_| "--wall-s takes whole seconds")?,
                )
            }
            other => return Err(format!("unexpected argument {other}")),
        }
    }
    parsed.engine = engine.ok_or("--engine is required")?;
    if !PINNED.contains(&parsed.row.as_str()) && parse_dense(&parsed.row).is_none() {
        return Err(format!(
            "--row must be one of {PINNED:?} or dmq-n<N>-m<M>-<field>-s<S>[-u] with N in {SIZES:?}"
        ));
    }
    if parsed.census && !cfg!(feature = "research-reuse") {
        return Err("--census needs --features research-reuse".into());
    }
    if parsed.census && parsed.stages {
        return Err("--stages times a run; --census runs are untimed".into());
    }
    Ok(parsed)
}

struct Input {
    modulus: String,
    digest: String,
    variables: Vec<String>,
    generators: Vec<String>,
}

/// A published ladder entry, refused unless its digest at `modulus` is the pinned one.
fn ladder(name: &str, modulus: u64) -> Input {
    let input = corpus::instance(name, modulus, ORDER).expect("published ladder entry");
    let entry = corpus::ladder()
        .into_iter()
        .find(|e| e.name == input.name)
        .expect("ladder entry");
    assert_eq!(entry.digest_at(modulus), Some(input.digest().as_str()));
    Input {
        modulus: modulus.to_string(),
        digest: input.digest(),
        variables: input.variables.clone(),
        generators: input.system.clone(),
    }
}

const WIDE_CATALOG: &str = include_str!("../research/wide-corpus/cases.json");

/// A frozen #738 row, refused unless its canonical text still hashes to its digest.
fn wide(field: &str, name: &str) -> Input {
    let cases = Json::parse(WIDE_CATALOG).unwrap();
    let case = cases
        .items()
        .iter()
        .find(|c| {
            c.get("field").and_then(Json::as_str) == Some(field)
                && c.get("name").and_then(Json::as_str) == Some(name)
        })
        .expect("frozen wide row");
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
        modulus: text("modulus"),
        digest,
        variables: strings("variables"),
        generators: strings("generators"),
    }
}

fn splitmix(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// #1030's dense quadratic row, rendered as text so its digest is that of the text solved.
fn dense<const N: usize, F: FiniteField>(shape: &Dense, characteristic: u64) -> Input {
    let names: Vec<String> = (0..N).map(|i| format!("x{i}")).collect();
    let refs: [&str; N] = std::array::from_fn(|i| names[i].as_str());
    let mut monomials: Vec<Monomial<N>> = vec![Monomial::one()];
    for i in 0..N {
        monomials.push(Monomial::univariate(i, 1));
    }
    for i in 0..N {
        for j in i..N {
            let mut e = [0u32; N];
            e[i] += 1;
            e[j] += 1;
            monomials.push(Monomial::new(&e));
        }
    }
    let mut state =
        shape.seed ^ ((shape.n as u64) << 32) ^ ((shape.m as u64) << 48) ^ characteristic;
    let mut uniform = |bound: u64| splitmix(&mut state) % bound;
    let point: Vec<F> = (0..N).map(|_| F::new(uniform(characteristic))).collect();
    let mut generators = Vec::with_capacity(shape.m);
    for _ in 0..shape.m {
        let mut terms: Vec<(Monomial<N>, F)> = Vec::new();
        for (k, monomial) in monomials.iter().enumerate() {
            // Every equation keeps one quadratic term, so none degenerates to a linear one.
            let forced = k == monomials.len() - 1;
            if (forced || uniform(2) == 1) && !(shape.planted && k == 0) {
                terms.push((*monomial, F::new(1 + uniform(characteristic - 1))));
            }
        }
        if shape.planted {
            let mut value = F::zero();
            for (monomial, c) in &terms {
                let mut v = *c;
                for (i, &e) in monomial.exponents().iter().enumerate() {
                    for _ in 0..e {
                        v *= point[i];
                    }
                }
                value += v;
            }
            if !value.is_zero() {
                terms.push((Monomial::one(), -value));
            }
        }
        let p = MultivariatePolynomial::new(&terms);
        generators.push(polynomial_to_string(&p, &refs, ORDER));
    }
    let canonical = format!(
        "{} {}\n{}\n{}",
        characteristic,
        names.join(","),
        shape.m,
        generators.join("\n")
    );
    Input {
        modulus: characteristic.to_string(),
        digest: sha256_hex(canonical.as_bytes()),
        variables: names,
        generators,
    }
}

fn f4_options(args: &Args) -> F4Options {
    F4Options {
        measure_stages: args.stages,
        max_wall_time: Some(args.wall),
        parallel_forward: ParallelForward::Serial,
        parallel_symbolic: ParallelSymbolic::Serial,
        #[cfg(feature = "research-reuse")]
        reducer_cache: if args.census {
            zeebra::grobner::CacheMode::Count
        } else {
            zeebra::grobner::CacheMode::Off
        },
        ..F4Options::default()
    }
}

fn sig_options(args: &Args) -> SigF4Options {
    SigF4Options {
        max_wall_time: Some(args.wall),
        #[cfg(feature = "research-reuse")]
        reuse_census: args.census,
        ..SigF4Options::default()
    }
}

#[cfg(feature = "research-reuse")]
fn ledger_json(work: &zeebra::linalg::work::WorkReport) -> Json {
    let phase = |backward: bool| -> (usize, usize, usize) {
        work.batches.iter().fold((0, 0, 0), |(a, p, r), b| {
            let w = if backward { &b.backward } else { &b.forward };
            (
                a + w.pivot_applications,
                p + w.coefficient_products,
                r + w.reducer_target_operations,
            )
        })
    };
    let (fa, fp, fr) = phase(false);
    let (ba, bp, br) = phase(true);
    Json::object([
        ("forward_applications", Json::size(fa)),
        ("forward_products", Json::size(fp)),
        ("forward_reducer_target_operations", Json::size(fr)),
        ("backward_applications", Json::size(ba)),
        ("backward_products", Json::size(bp)),
        ("backward_reducer_target_operations", Json::size(br)),
        (
            "batch_forward_products",
            Json::Array(
                work.batches
                    .iter()
                    .map(|b| Json::size(b.forward.coefficient_products))
                    .collect(),
            ),
        ),
    ])
}

type Outcome<const N: usize, F> = (
    Result<Vec<MultivariatePolynomial<N, F>>, String>,
    Json,
    Json,
    Json,
);

/// The conventional census run: the batch observer inside the serial work ledger.
#[cfg(feature = "research-reuse")]
fn f4_census<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    options: &F4Options,
    bytes_per_term: usize,
) -> Outcome<N, F> {
    let mut observer = zeebra::grobner::reuse_census::F4Census::<N>::new();
    let (result, work) = zeebra::linalg::work::measure(|| {
        zeebra::grobner::f4_observed(system, ORDER, options, &mut observer)
    });
    let (result, stats) = match result {
        Ok((basis, stats)) => (Ok(basis), Some(stats)),
        Err(e) => (Err(e.to_string()), None),
    };
    let reused = stats.as_ref().map(|s| s.reducer_rows_reused);
    let census = &observer.census;
    (
        result,
        f4_json(stats.as_ref(), reused),
        Json::object([
            ("summary", census.summary_json(bytes_per_term)),
            ("batches", census.batches_json()),
        ]),
        ledger_json(&work),
    )
}

#[cfg(not(feature = "research-reuse"))]
fn f4_census<const N: usize, F: FiniteField>(
    _: &[MultivariatePolynomial<N, F>],
    _: &F4Options,
    _: usize,
) -> Outcome<N, F> {
    unreachable!("parse_args refuses --census without research-reuse")
}

fn run<const N: usize, F: FiniteField>(input: Input, args: &Args) -> Json {
    let names: [&str; N] = std::array::from_fn(|i| input.variables[i].as_str());
    let system: Vec<MultivariatePolynomial<N, F>> = input
        .generators
        .iter()
        .map(|s| MultivariatePolynomial::parse(s, names).expect("generator parses"))
        .collect();
    let bytes_per_term = size_of::<Monomial<N>>() + size_of::<F>();
    let started = Instant::now();
    let (result, statistics, census, ledger) = match args.engine {
        Engine::F4 => {
            let options = f4_options(args);
            if args.census {
                f4_census(&system, &options, bytes_per_term)
            } else {
                let (result, stats) = f4_reported(&system, ORDER, &options);
                (
                    result.map_err(|e| e.to_string()),
                    f4_json(Some(&stats), None),
                    Json::Null,
                    Json::Null,
                )
            }
        }
        Engine::SigF4 => {
            let (result, stats) = sig_f4_reported(&system, ORDER, &sig_options(args));
            #[cfg(feature = "research-reuse")]
            let census = stats
                .reuse
                .clone()
                .map_or(Json::Null, |(summary, batches)| {
                    Json::object([("summary", summary), ("batches", batches)])
                });
            #[cfg(not(feature = "research-reuse"))]
            let census = Json::Null;
            (
                result.map_err(|e| e.to_string()),
                sig_json(&stats),
                census,
                Json::Null,
            )
        }
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
    Json::object([
        ("row", Json::string(&args.row)),
        (
            "engine",
            Json::string(match args.engine {
                Engine::F4 => "f4",
                Engine::SigF4 => "sigf4",
            }),
        ),
        ("census", Json::Bool(args.census)),
        ("stages", Json::Bool(args.stages)),
        ("modulus", Json::string(&input.modulus)),
        ("variables", Json::size(N)),
        ("equations", Json::size(system.len())),
        ("input_digest", Json::string(&input.digest)),
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
        ("ledger", ledger),
        ("reuse", census),
    ])
}

fn f4_json(s: Option<&zeebra::grobner::F4Statistics>, reused: Option<usize>) -> Json {
    let Some(s) = s else {
        return Json::Null;
    };
    let t = s.stages;
    Json::object([
        ("total_ns", Json::nanos(s.total)),
        ("symbolic_ns", Json::nanos(t.symbolic)),
        ("construction_ns", Json::nanos(t.construction)),
        ("elimination_ns", Json::nanos(t.elimination)),
        ("interreduction_ns", Json::nanos(t.interreduction)),
        ("batches", Json::size(s.batches)),
        ("pairs_reduced", Json::size(s.pairs_reduced)),
        ("reducer_rows", Json::size(s.reducer_rows)),
        ("reducer_rows_reused", reused.map_or(Json::Null, Json::size)),
        ("zero_rows", Json::size(s.zero_rows)),
        ("max_matrix_rows", Json::size(s.max_matrix_rows)),
        ("max_matrix_columns", Json::size(s.max_matrix_columns)),
        ("peak_basis_terms", Json::size(s.peak_basis_terms)),
    ])
}

fn sig_json(s: &zeebra::grobner::sigf4::SigF4Statistics) -> Json {
    Json::object([
        ("total_ns", Json::nanos(s.total)),
        ("symbolic_ns", Json::nanos(s.symbolic)),
        ("elimination_ns", Json::nanos(s.elimination)),
        ("interreduction_ns", Json::nanos(s.interreduction)),
        ("bookkeeping_ns", Json::nanos(s.bookkeeping)),
        ("batches", Json::size(s.batches)),
        ("targets", Json::size(s.targets)),
        ("reducer_rows", Json::size(s.reducer_rows)),
        ("zero_rows", Json::size(s.zero_rows)),
        ("singular_rows", Json::size(s.singular_rows)),
        ("coefficient_products", Json::int(s.coefficient_products)),
        ("products_on_zero_rows", Json::int(s.products_on_zero_rows)),
        ("rejected_koszul", Json::size(s.rejected_koszul)),
        ("rejected_zero_row", Json::size(s.rejected_zero_row)),
        ("rejected_rewrite", Json::size(s.rejected_rewrite)),
        ("max_matrix_rows", Json::size(s.max_matrix_rows)),
        ("max_matrix_columns", Json::size(s.max_matrix_columns)),
        (
            "signature_basis_elements",
            Json::size(s.signature_basis_elements),
        ),
    ])
}

macro_rules! dense_dispatch {
    ($shape:expr, $args:expr, $($n:literal),*) => {
        match $shape.n {
            $($n => dense_field::<$n>(&$shape, $args),)*
            _ => unreachable!("parse_dense admits only SIZES"),
        }
    };
}

fn dense_field<const N: usize>(shape: &Dense, args: &Args) -> Json {
    match shape.field.as_str() {
        "gf31" => run::<N, Zp31>(dense::<N, Zp31>(shape, 31), args),
        "gf32003" => run::<N, Zp32003>(dense::<N, Zp32003>(shape, 32003), args),
        "m31" => run::<N, Zp2147483647>(dense::<N, Zp2147483647>(shape, 2147483647), args),
        "p64" => run::<N, Zp18446744073709551557>(
            dense::<N, Zp18446744073709551557>(shape, 18446744073709551557),
            args,
        ),
        _ => unreachable!("parse_dense admits only FIELDS"),
    }
}

fn main() {
    let raw: Vec<String> = std::env::args().skip(1).collect();
    let args = parse_args(&raw).unwrap_or_else(|e| panic!("{e}"));
    let report = match args.row.as_str() {
        "mq10-32003" => run::<10, Zp32003>(ladder("mq-random-10", 32003), &args),
        "mq10-m31" => run::<10, Zp2147483647>(ladder("mq-random-10", 2147483647), &args),
        "katsura11-m31" => run::<11, Zp2147483647>(ladder("katsura-11", 2147483647), &args),
        "eco12-wide64" => run::<12, Wide>(wide("wide64", "eco-12"), &args),
        "mq11-goldilocks" => run::<11, Goldilocks>(wide("goldilocks", "mq-random-11"), &args),
        name => {
            let shape = parse_dense(name).expect("validated");
            dense_dispatch!(shape, &args, 6, 7, 8, 9, 10, 11, 12, 13, 14)
        }
    };
    println!("{}", report.to_json().replace('\n', ""));
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(list: &[&str]) -> Result<Args, String> {
        parse_args(&list.iter().map(|s| s.to_string()).collect::<Vec<_>>())
    }

    // A generated row name parses to its shape, and a malformed or out-of-range one is refused.
    #[test]
    fn dense_rows_parse() {
        assert_eq!(
            parse_dense("dmq-n10-m20-gf31-s2"),
            Some(Dense {
                n: 10,
                m: 20,
                field: "gf31".into(),
                seed: 2,
                planted: true
            })
        );
        assert!(!parse_dense("dmq-n10-m20-p64-s0-u").unwrap().planted);
        assert!(parse_dense("dmq-n99-m20-gf31-s0").is_none());
        assert!(parse_dense("dmq-n10-m5-gf31-s0").is_none());
        assert!(parse_dense("dmq-n10-m20-gf7-s0").is_none());
    }

    // The engine is required, stage clocks and the census are exclusive, and rows are validated.
    #[test]
    fn arguments_are_validated() {
        assert!(args(&["--row", "mq10-32003"]).is_err());
        assert!(args(&["--row", "mq10-32003", "--engine", "f4"]).is_ok());
        assert!(args(&["--row", "katsura-11", "--engine", "f4"]).is_err());
        assert!(args(&["--row", "mq10-m31", "--engine", "sigf4", "--census", "--stages"]).is_err());
        assert_eq!(
            args(&["--row", "mq10-m31", "--engine", "sigf4", "--census"]).is_ok(),
            cfg!(feature = "research-reuse")
        );
    }

    // A generated row is deterministic, has its stated shape, and vanishes at its planted point.
    #[test]
    fn dense_rows_are_reproducible_and_planted() {
        let shape = parse_dense("dmq-n6-m12-gf32003-s1").unwrap();
        let a = dense::<6, Zp32003>(&shape, 32003);
        let b = dense::<6, Zp32003>(&shape, 32003);
        assert_eq!(a.digest, b.digest);
        assert_eq!(a.generators.len(), 12);
        let other = dense::<6, Zp32003>(&parse_dense("dmq-n6-m12-gf32003-s2").unwrap(), 32003);
        assert_ne!(a.digest, other.digest);
        // Planted, so consistent: the reduced basis is not {1}.
        let report = run::<6, Zp32003>(
            a,
            &args(&["--row", "dmq-n6-m12-gf32003-s1", "--engine", "f4"]).unwrap(),
        );
        assert_eq!(
            report.get("status").and_then(Json::as_str),
            Some("complete")
        );
        assert!(report.get("basis_elements").and_then(Json::as_int).unwrap() > 1);
    }

    // Both engines return the same reduced basis, and the census changes neither.
    #[test]
    fn engines_and_census_agree_on_the_basis() {
        let row = "dmq-n6-m12-m31-s0";
        let digest = |list: &[&str]| {
            let shape = parse_dense(row).unwrap();
            let input = dense::<6, Zp2147483647>(&shape, 2147483647);
            run::<6, Zp2147483647>(input, &args(list).unwrap())
                .get("basis_sha256")
                .and_then(Json::as_str)
                .unwrap()
                .to_string()
        };
        let reference = digest(&["--row", row, "--engine", "f4"]);
        assert_eq!(digest(&["--row", row, "--engine", "sigf4"]), reference);
        if cfg!(feature = "research-reuse") {
            assert_eq!(
                digest(&["--row", row, "--engine", "f4", "--census"]),
                reference
            );
            assert_eq!(
                digest(&["--row", row, "--engine", "sigf4", "--census"]),
                reference
            );
        }
    }
}
