//! #1039: one fresh-process complete lex-basis computation, for the cross-engine table against the
//! pinned grobx's lex route (`research/1039-wiedemann-lex/`).
//!
//! cargo run --release --example lex_pipeline -- (--family NAME [--modulus P] | --input FILE)
//!     [--input-only] [--arm ARM] [--workers N] [--wall-s S] [--budget shipping|lifted]
//!
//! Arms: `adaptive`, `wiedemann` and `classical` are grevlex F4 (the signature dispatch) followed by
//! `fglm_to_lex_with_options` under that `ConversionStrategy`; `shape` is grevlex F4 then
//! `shape_lex_basis`; `direct-lex` is F4 under lex; `probe` reports the quotient algebra's operator
//! shape without converting. Every stage of the complete task is inside `call_ns`; the
//! `m33-basis-v1` digest is computed after it, as the grobx driver's is.
//!
//! `--input FILE` takes the grobx driver's request JSON (`variables`, `modulus`, `generators`), so
//! both engines read the same text. `--input-only` prints that request for a `--family`.

use std::time::{Duration, Instant};

use rand::{rngs::StdRng, SeedableRng};
use zeebra::{
    fields::{Zp2147483647, Zp32003, Zp65537},
    grobner::{
        benchmark_systems::{cyclic, katsura},
        differential::polynomial_to_string,
        f4_reported, f4_signature_reported,
        fglm::{
            fglm_to_lex_with_options, shape_lex_basis, ConversionRoute, ConversionStrategy,
            FglmError, FglmOptions, FglmStatistics, QuotientAlgebra,
        },
        F4Options, ParallelForward, ParallelSymbolic,
    },
    util::{peak_resident_bytes, sha256_hex, Json},
    FiniteField, Monomial, MonomialOrder, MultivariatePolynomial,
};

const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;
const LEX: MonomialOrder = MonomialOrder::Lexicographic;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Arm {
    Adaptive,
    Wiedemann,
    Classical,
    Shape,
    DirectLex,
    Probe,
}

impl Arm {
    fn parse(s: &str) -> Option<Self> {
        Some(match s {
            "adaptive" => Self::Adaptive,
            "wiedemann" => Self::Wiedemann,
            "classical" => Self::Classical,
            "shape" => Self::Shape,
            "direct-lex" => Self::DirectLex,
            "probe" => Self::Probe,
            _ => return None,
        })
    }

    fn strategy(self) -> Option<ConversionStrategy> {
        match self {
            Self::Adaptive => Some(ConversionStrategy::Adaptive),
            Self::Wiedemann => Some(ConversionStrategy::Wiedemann),
            Self::Classical => Some(ConversionStrategy::Classical),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Budget {
    /// `FglmOptions::recommended()`: the library's default conversion limits (D <= 4096).
    Shipping,
    /// Limits lifted to the issue's 16 GiB budget, leaving 4 GiB for the F4 stage and the process.
    Lifted,
}

fn fglm_options(budget: Budget, strategy: ConversionStrategy) -> FglmOptions {
    let mut options = FglmOptions::recommended();
    if budget == Budget::Lifted {
        const BYTES: usize = 12 << 30;
        options.max_quotient_dimension = 1 << 21;
        options.max_span_bytes = BYTES;
        options.max_span_entries = BYTES / 8;
        options.max_operator_bytes = BYTES;
        options.max_operator_entries = BYTES / 16;
    }
    options.conversion_strategy = strategy;
    options.measure_stages = true;
    options
}

fn f4_options(workers: usize, wall: Duration) -> F4Options {
    F4Options {
        max_wall_time: Some(wall),
        parallel_forward: if workers == 1 {
            ParallelForward::Serial
        } else {
            ParallelForward::Auto {
                max_workers: workers,
            }
        },
        parallel_symbolic: if workers == 1 {
            ParallelSymbolic::Serial
        } else {
            ParallelSymbolic::Auto {
                max_workers: workers,
            }
        },
        ..F4Options::default()
    }
}

/// A request in the grobx driver's vocabulary.
#[derive(Clone, Debug)]
struct Request {
    name: String,
    variables: Vec<String>,
    modulus: u64,
    generators: Vec<String>,
}

impl Request {
    fn digest(&self) -> String {
        let text = format!(
            "{}\n{}\n{}\n",
            self.variables.join(","),
            self.modulus,
            self.generators.join(",\n")
        );
        sha256_hex(text.as_bytes())
    }

    fn to_json(&self) -> Json {
        let strings = |v: &[String]| Json::Array(v.iter().map(Json::string).collect());
        Json::object([
            ("name", Json::string(&self.name)),
            ("digest", Json::string(self.digest())),
            ("variables", strings(&self.variables)),
            ("modulus", Json::int(self.modulus)),
            ("generators", strings(&self.generators)),
        ])
    }

    fn from_json(text: &str) -> Result<Self, String> {
        let json = Json::parse(text).map_err(|e| format!("{e:?}"))?;
        let strings = |key: &str| -> Result<Vec<String>, String> {
            json.get(key)
                .ok_or(format!("missing {key}"))?
                .items()
                .iter()
                .map(|s| {
                    s.as_str()
                        .map(str::to_string)
                        .ok_or(format!("{key}: not a string"))
                })
                .collect()
        };
        Ok(Self {
            name: json
                .get("name")
                .and_then(Json::as_str)
                .unwrap_or("input")
                .to_string(),
            variables: strings("variables")?,
            modulus: json
                .get("modulus")
                .and_then(Json::as_int)
                .ok_or("missing modulus")?
                .try_into()
                .map_err(|_| "modulus out of range")?,
            generators: strings("generators")?,
        })
    }
}

fn names(n: usize, extra: bool) -> Vec<String> {
    extra
        .then(|| "y".to_string())
        .into_iter()
        .chain((0..n).map(|i| format!("x{i}")))
        .collect()
}

/// The `wiedemann_conversion` chain `x_i^d - x_{i+1}`, `x_{n-1}^d - x_0 - 1` and its controls.
///
/// - `wd-N-d`: radical, shape position, D = d^N, and already a grevlex basis.
/// - `wdns-N-d`: adds `y^2 - 1` with `y` first, so `x_{N-1}` does not separate: non-shape, D = 2 d^N.
/// - `wdnr-N-d`: adds `y^2` instead: nonradical and non-shape, D = 2 d^N.
/// - `wdsq-N-d`: squares the last generator: nonradical, D = 2 d^N.
fn chain(kind: &str, n: usize, d: u32) -> (Vec<String>, Vec<String>) {
    let last = n - 1;
    let mut generators: Vec<String> = (0..last).map(|i| format!("x{i}^{d}-x{}", i + 1)).collect();
    if kind == "wdsq" {
        generators.push(format!(
            "x{last}^{}-2*x{last}^{d}*x0-2*x{last}^{d}+x0^2+2*x0+1",
            2 * d
        ));
    } else {
        generators.push(format!("x{last}^{d}-x0-1"));
    }
    match kind {
        "wdns" => generators.insert(0, "y^2-1".into()),
        "wdnr" => generators.insert(0, "y^2".into()),
        _ => {}
    }
    (names(n, matches!(kind, "wdns" | "wdnr")), generators)
}

fn render<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    variables: &[String],
) -> Vec<String> {
    let refs: Vec<&str> = variables.iter().map(String::as_str).collect();
    system
        .iter()
        .map(|p| polynomial_to_string(p, &refs, GREVLEX))
        .collect()
}

/// `n` dense quadratics in `n` variables with a planted point: D = 2^n and, generically, shape
/// position. Seeded, so the same name is the same input.
fn planted_quadratics<const N: usize, F: FiniteField>(
    seed: u64,
) -> Vec<MultivariatePolynomial<N, F>> {
    let mut rng = StdRng::seed_from_u64(seed);
    let point: Vec<F> = (0..N).map(|_| F::random(&mut rng)).collect();
    let mut monomials = vec![];
    for i in 0..N {
        monomials.push(Monomial::univariate(i, 1));
        for j in i..N {
            monomials.push(Monomial::univariate(i, 1) * Monomial::univariate(j, 1));
        }
    }
    (0..N)
        .map(|_| {
            let mut terms: Vec<(Monomial<N>, F)> = monomials
                .iter()
                .map(|m| (*m, F::random(&mut rng)))
                .filter(|(_, c)| !c.is_zero())
                .collect();
            let value = terms
                .iter()
                .map(|(m, c)| {
                    let mut v = *c;
                    for (i, &e) in m.exponents().iter().enumerate() {
                        for _ in 0..e {
                            v *= point[i];
                        }
                    }
                    v
                })
                .fold(F::zero(), |a, b| a + b);
            terms.push((Monomial::one(), F::zero() - value));
            MultivariatePolynomial::new(&terms)
        })
        .collect()
}

fn generated<const N: usize, F: FiniteField>(family: &str, seed: u64) -> Option<Vec<String>> {
    let system: Vec<MultivariatePolynomial<N, F>> = match family {
        "katsura" => katsura(),
        "cyclic" => cyclic(),
        "pquad" => planted_quadratics(seed),
        _ => return None,
    };
    Some(render(&system, &names(N, false)))
}

/// A named input: `wd|wdns|wdnr|wdsq-N-d`, `katsura-N`, `cyclic-N` or `pquad-N-seed`.
fn family(name: &str, modulus: u64) -> Result<Request, String> {
    let parts: Vec<&str> = name.split('-').collect();
    let number = |i: usize| -> Result<u64, String> {
        parts
            .get(i)
            .and_then(|s| s.parse().ok())
            .ok_or(format!("{name}: expected a number in position {i}"))
    };
    let (variables, generators) = match parts[0] {
        kind @ ("wd" | "wdns" | "wdnr" | "wdsq") => {
            chain(kind, number(1)? as usize, number(2)? as u32)
        }
        kind @ ("katsura" | "cyclic" | "pquad") => {
            let n = number(1)? as usize;
            let seed = if kind == "pquad" { number(2)? } else { 0 };
            macro_rules! by_n {
                ($($k:literal),*) => {
                    match (modulus, n) {
                        $((65537, $k) => generated::<$k, Zp65537>(kind, seed),
                          (32003, $k) => generated::<$k, Zp32003>(kind, seed),
                          (2147483647, $k) => generated::<$k, Zp2147483647>(kind, seed),)*
                        _ => None,
                    }
                };
            }
            let generators = by_n!(3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16)
                .ok_or(format!("{name}: no instantiation for p = {modulus}"))?;
            (names(n, false), generators)
        }
        _ => return Err(format!("unknown family {name}")),
    };
    Ok(Request {
        name: name.to_string(),
        variables,
        modulus,
        generators,
    })
}

/// What one arm did, stage by stage.
#[derive(Debug, Default)]
struct Outcome<const N: usize, F: FiniteField> {
    status: &'static str,
    error: Option<String>,
    basis: Option<Vec<MultivariatePolynomial<N, F>>>,
    f4_ns: Duration,
    f4_route: Option<String>,
    f4_workers: usize,
    conversion_ns: Duration,
    fglm: Option<FglmStatistics>,
    probe: Vec<(&'static str, Json)>,
    call_ns: Duration,
}

fn pipeline<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    arm: Arm,
    workers: usize,
    wall: Duration,
    budget: Budget,
) -> Outcome<N, F> {
    let started = Instant::now();
    let mut outcome = Outcome {
        status: "complete",
        f4_workers: workers,
        ..Outcome::default()
    };
    let order = if arm == Arm::DirectLex { LEX } else { GREVLEX };
    let options = f4_options(workers, wall);
    // The signature dispatch is graded-only (#986), so lex runs conventional F4, as the
    // eligibility matrix (`docs/research/adaptive-selection-contracts.md` §5) records.
    let result = if order == LEX {
        outcome.f4_route = Some("ConventionalLex".into());
        f4_reported(system, order, &options)
            .0
            .map_err(|e| format!("{e:?}"))
    } else {
        let (result, dispatch) = f4_signature_reported(system, order, &options);
        outcome.f4_route = Some(format!("{:?}", dispatch.route));
        outcome.f4_workers = dispatch.workers;
        result.map_err(|e| format!("{e:?}"))
    };
    outcome.f4_ns = started.elapsed();
    let source = match result {
        Ok(basis) => basis,
        Err(e) => {
            outcome.status = "stopped";
            outcome.error = Some(format!("f4: {e:?}"));
            outcome.call_ns = started.elapsed();
            return outcome;
        }
    };
    let converting = Instant::now();
    let budget_options = fglm_options(budget, ConversionStrategy::Classical);
    let converted: Result<Option<Vec<_>>, String> = match arm {
        Arm::DirectLex => Ok(Some(source)),
        Arm::Adaptive | Arm::Wiedemann | Arm::Classical => {
            let options = fglm_options(budget, arm.strategy().expect("a converting arm"));
            fglm_to_lex_with_options(&source, GREVLEX, &options)
                .map(|(basis, stats)| {
                    outcome.fglm = Some(stats);
                    Some(basis)
                })
                .map_err(|e| fglm_error(&e))
        }
        Arm::Shape => QuotientAlgebra::new(&source, GREVLEX, &budget_options)
            .map_err(|e| fglm_error(&e))
            .and_then(|algebra| {
                // The Krylov sweep keeps D vectors of length D; refuse past the span budget.
                let d = algebra.dimension();
                let cells = d.saturating_mul(d);
                if cells > budget_options.max_span_entries {
                    return Err(format!(
                        "refused: SpanStorageExceeded {{ entries: {cells} }}"
                    ));
                }
                shape_lex_basis(&algebra)
                    .map(Some)
                    .map_err(|e| format!("unsupported: shape {e:?}"))
            }),
        Arm::Probe => QuotientAlgebra::new(&source, GREVLEX, &budget_options)
            .map(|algebra| {
                let last = algebra.operator(N - 1);
                outcome.probe = vec![
                    ("dimension", Json::size(algebra.dimension())),
                    ("operator_entries", Json::size(algebra.operator_entries())),
                    ("dense_columns", Json::size(algebra.dense_columns())),
                    ("last_stored_entries", Json::size(last.stored_entries())),
                    ("last_stored_cells", Json::size(last.stored_cells())),
                    ("last_standard_columns", Json::size(last.standard_columns())),
                    ("last_dense_columns", Json::size(last.dense_columns())),
                    ("last_stored_bytes", Json::size(last.stored_bytes())),
                ];
                None
            })
            .map_err(|e| fglm_error(&e)),
    };
    outcome.conversion_ns = converting.elapsed();
    match converted {
        Ok(basis) => outcome.basis = basis,
        Err(e) => {
            outcome.status = if e.starts_with("refused") {
                "refused"
            } else if e.starts_with("unsupported") {
                "unsupported"
            } else {
                "error"
            };
            outcome.error = Some(e);
        }
    }
    outcome.call_ns = started.elapsed();
    outcome
}

/// A budget refusal is typed and distinct from an unsupported input (#1008).
fn fglm_error(e: &FglmError) -> String {
    let kind = match e {
        FglmError::PositiveDimensional => "unsupported",
        FglmError::NotAGrobnerBasis => "error",
        _ => "refused",
    };
    format!("{kind}: {e:?}")
}

/// The `selection-outcome-v1` keys (`docs/research/benchmark-schema.md` §8.2) with the costs the
/// complete task charges: a failed projection is discarded work and the classical walk after it is
/// the fallback.
fn selection<const N: usize, F: FiniteField>(outcome: &Outcome<N, F>) -> Vec<(&'static str, Json)> {
    let error = outcome.error.as_deref().unwrap_or("");
    let status = match outcome.status {
        "complete" => "complete",
        "refused" => "memory-refusal",
        "unsupported" => "unsupported",
        "stopped" if error.contains("Time") || error.contains("Wall") => "time-stop",
        "stopped" if error.contains("Unsupported") => "unsupported",
        "stopped" => "memory-refusal",
        _ => "incorrect-output",
    };
    let (mut acceptance, mut verified) = ("deterministic", false);
    let mut costs = vec![("conversion", Json::nanos(outcome.conversion_ns))];
    if let Some(s) = &outcome.fglm {
        let t = &s.timings;
        let scalar = t.scalar_sequence + t.scalar_reconstruction + t.scalar_certificate;
        if s.wiedemann_attempts > 0 {
            acceptance = "certified-randomized";
        }
        if s.conversion_route == ConversionRoute::Wiedemann {
            verified = true;
            costs.push(("verification", Json::nanos(t.scalar_certificate)));
        } else {
            costs.push(("discarded", Json::nanos(scalar)));
            costs.push(("fallback", Json::nanos(t.dependence.saturating_sub(scalar))));
        }
    }
    vec![
        ("selection_outcome", Json::string(status)),
        (
            "reason",
            outcome.error.as_ref().map_or(Json::Null, Json::string),
        ),
        ("acceptance", Json::string(acceptance)),
        ("verified", Json::Bool(verified)),
        ("costs_ns", Json::object(costs)),
    ]
}

/// `m33-basis-v1` over elements made monic at their grevlex leading term (`basis_digest.py`), so a
/// lex basis digests like any other engine's text of it.
fn basis_m33<const N: usize, F: FiniteField>(
    basis: &[MultivariatePolynomial<N, F>],
    modulus: u64,
) -> String {
    let mut elements: Vec<Vec<u8>> = basis
        .iter()
        .filter(|p| !p.is_zero())
        .map(|p| {
            let mut terms: Vec<_> = p.terms().iter().collect();
            let lead = terms.iter().max_by(|a, b| GREVLEX.cmp(a.0, b.0)).unwrap();
            let scale = lead.1.inverse();
            terms.sort_unstable_by(|a, b| a.0.exponents().cmp(b.0.exponents()));
            let mut bytes = Vec::new();
            for (monomial, coefficient) in terms {
                for &e in monomial.exponents() {
                    let mut e = e;
                    while e >= 0x80 {
                        bytes.push((e as u8 & 0x7f) | 0x80);
                        e >>= 7;
                    }
                    bytes.push(e as u8);
                }
                bytes.extend(format!("{};", *coefficient * scale).bytes());
            }
            bytes
        })
        .collect();
    elements.sort_unstable();
    let mut data = format!("m33-basis-v1 {modulus} {N}\n").into_bytes();
    for element in &elements {
        data.extend_from_slice(&(element.len() as u32).to_le_bytes());
        data.extend_from_slice(element);
    }
    sha256_hex(&data)
}

fn report<const N: usize, F: FiniteField>(
    request: &Request,
    arm: Arm,
    workers: usize,
    wall: Duration,
    budget: Budget,
) -> Vec<(&'static str, Json)> {
    let names: [&str; N] = std::array::from_fn(|i| request.variables[i].as_str());
    let system: Vec<MultivariatePolynomial<N, F>> = request
        .generators
        .iter()
        .map(|g| MultivariatePolynomial::parse(g, names).expect("a generator"))
        .collect();
    let outcome = pipeline(&system, arm, workers, wall, budget);
    let hashing = Instant::now();
    let digest = outcome
        .basis
        .as_ref()
        .map_or(Json::Null, |b| Json::string(basis_m33(b, request.modulus)));
    let digest_ns = hashing.elapsed();
    let ns = |d: Duration| Json::nanos(d);
    let mut fields = vec![
        ("status", Json::string(outcome.status)),
        (
            "error",
            outcome.error.as_ref().map_or(Json::Null, Json::string),
        ),
        ("call_ns", ns(outcome.call_ns)),
        ("f4_ns", ns(outcome.f4_ns)),
        (
            "f4_route",
            outcome.f4_route.as_ref().map_or(Json::Null, Json::string),
        ),
        ("f4_team", Json::size(outcome.f4_workers)),
        ("conversion_ns", ns(outcome.conversion_ns)),
        ("basis_m33", digest),
        ("digest_ns", ns(digest_ns)),
        (
            "lex_elements",
            outcome
                .basis
                .as_ref()
                .map_or(Json::Null, |b| Json::size(b.len())),
        ),
        (
            "lex_terms",
            outcome.basis.as_ref().map_or(Json::Null, |b| {
                Json::size(b.iter().map(|p| p.terms().len()).sum())
            }),
        ),
    ];
    if let Some(s) = &outcome.fglm {
        let t = &s.timings;
        // On a fallback the failed projections' stages are the retry cost and the rest of the
        // walk clock is the classical conversion; on the Wiedemann route the walk is all scalar.
        let scalar = t.scalar_sequence + t.scalar_reconstruction + t.scalar_certificate;
        fields.extend([
            ("dimension", Json::size(s.quotient_dimension)),
            ("route", Json::string(format!("{:?}", s.conversion_route))),
            (
                "fallback",
                s.wiedemann_fallback
                    .map_or(Json::Null, |f| Json::string(format!("{f:?}"))),
            ),
            ("attempts", Json::size(s.wiedemann_attempts)),
            ("operator_entries", Json::size(s.operator_entries)),
            ("operators_built", Json::size(s.operators_built)),
            ("normal_form_calls", Json::size(s.border.normal_form_calls)),
            ("read_off_columns", Json::size(s.border.read_off_columns)),
            ("operator_cells", Json::size(s.memory.operator_cells)),
            ("dense_columns", Json::size(s.memory.dense_columns)),
            ("quotient_basis_ns", ns(t.quotient_basis)),
            ("operator_ns", ns(t.operator_construction())),
            ("sequence_ns", ns(t.scalar_sequence)),
            ("reconstruction_ns", ns(t.scalar_reconstruction)),
            ("certificate_ns", ns(t.scalar_certificate)),
            ("walk_ns", ns(t.dependence)),
            ("classical_walk_ns", ns(t.dependence.saturating_sub(scalar))),
            ("estimated_bytes", Json::size(s.estimated_bytes())),
        ]);
    }
    fields.extend(selection(&outcome));
    fields.extend(outcome.probe);
    fields
}

fn main() {
    let started = Instant::now();
    let args: Vec<String> = std::env::args().skip(1).collect();
    let value = |flag: &str| {
        args.iter()
            .position(|a| a == flag)
            .and_then(|i| args.get(i + 1))
            .cloned()
    };
    let modulus: u64 = value("--modulus").map_or(65537, |m| m.parse().expect("--modulus"));
    let request = match (value("--family"), value("--input")) {
        (Some(name), None) => family(&name, modulus).unwrap_or_else(|e| panic!("{e}")),
        (None, Some(path)) => Request::from_json(&std::fs::read_to_string(path).expect("input"))
            .unwrap_or_else(|e| panic!("{e}")),
        _ => panic!("give exactly one of --family NAME and --input FILE"),
    };
    if args.iter().any(|a| a == "--input-only") {
        println!("{}", request.to_json().to_json().replace('\n', ""));
        return;
    }
    let arm_name = value("--arm").unwrap_or_else(|| "adaptive".into());
    let arm =
        Arm::parse(&arm_name).expect("--arm adaptive|wiedemann|classical|shape|direct-lex|probe");
    let workers: usize = value("--workers").map_or(1, |w| w.parse().expect("--workers"));
    let wall = Duration::from_secs(value("--wall-s").map_or(600, |s| s.parse().expect("--wall-s")));
    let budget = match value("--budget").as_deref() {
        None | Some("lifted") => Budget::Lifted,
        Some("shipping") => Budget::Shipping,
        Some(other) => panic!("--budget shipping|lifted, not {other}"),
    };
    let mut fields = vec![
        ("name", Json::string(&request.name)),
        ("digest", Json::string(request.digest())),
        ("modulus", Json::int(request.modulus)),
        ("variables", Json::size(request.variables.len())),
        ("arm", Json::string(&arm_name)),
        ("workers", Json::size(workers)),
        ("budget", Json::string(format!("{budget:?}").to_lowercase())),
    ];
    macro_rules! dispatch {
        ($($n:literal),*) => {
            match (request.modulus, request.variables.len()) {
                $((65537, $n) => report::<$n, Zp65537>(&request, arm, workers, wall, budget),
                  (32003, $n) => report::<$n, Zp32003>(&request, arm, workers, wall, budget),
                  (2147483647, $n) => report::<$n, Zp2147483647>(&request, arm, workers, wall, budget),)*
                (p, n) => panic!("no instantiation for p = {p} with {n} variables"),
            }
        };
    }
    fields.extend(dispatch!(
        2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16
    ));
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
    use zeebra::grobner::fglm::{ConversionRoute, WiedemannFallback};

    type F = Zp65537;

    fn parse<const N: usize>(request: &Request) -> Vec<MultivariatePolynomial<N, F>> {
        let names: [&str; N] = std::array::from_fn(|i| request.variables[i].as_str());
        request
            .generators
            .iter()
            .map(|g| MultivariatePolynomial::parse(g, names).unwrap())
            .collect()
    }

    fn run<const N: usize>(name: &str, arm: Arm, budget: Budget) -> Outcome<N, F> {
        let request = family(name, 65537).unwrap();
        pipeline(
            &parse::<N>(&request),
            arm,
            1,
            Duration::from_secs(60),
            budget,
        )
    }

    const CONVERTING: [Arm; 4] = [Arm::Adaptive, Arm::Wiedemann, Arm::Classical, Arm::Shape];

    /// Every grevlex-then-convert arm returns direct lex F4's basis on a shape-position chain.
    #[test]
    fn every_arm_agrees_with_direct_lex_in_shape_position() {
        let reference = run::<3>("wd-3-6", Arm::DirectLex, Budget::Lifted)
            .basis
            .unwrap();
        for arm in CONVERTING {
            let outcome = run::<3>("wd-3-6", arm, Budget::Lifted);
            assert_eq!(outcome.status, "complete", "{arm:?}");
            assert_eq!(outcome.basis.as_ref(), Some(&reference), "{arm:?}");
        }
    }

    /// The adaptive rule takes Wiedemann at D = 216 and classical below 128.
    #[test]
    fn adaptive_routes_by_quotient_dimension() {
        let large = run::<3>("wd-3-6", Arm::Adaptive, Budget::Lifted)
            .fglm
            .unwrap();
        assert_eq!(large.quotient_dimension, 216);
        assert_eq!(large.conversion_route, ConversionRoute::Wiedemann);
        let small = run::<3>("wd-3-5", Arm::Adaptive, Budget::Lifted)
            .fglm
            .unwrap();
        assert_eq!(small.quotient_dimension, 125);
        assert_eq!(
            small.wiedemann_fallback,
            Some(WiedemannFallback::SmallQuotient)
        );
    }

    /// A non-shape control spends three projections, falls back, and still returns the lex basis.
    #[test]
    fn non_shape_control_falls_back_with_the_retries_counted() {
        let reference = run::<4>("wdns-3-6", Arm::DirectLex, Budget::Lifted)
            .basis
            .unwrap();
        let outcome = run::<4>("wdns-3-6", Arm::Adaptive, Budget::Lifted);
        let stats = outcome.fglm.as_ref().unwrap();
        assert_eq!(stats.quotient_dimension, 432);
        assert_eq!(stats.wiedemann_attempts, 3);
        assert_eq!(stats.conversion_route, ConversionRoute::Classical);
        assert_eq!(
            stats.wiedemann_fallback,
            Some(WiedemannFallback::NonCyclicProjection)
        );
        assert_eq!(outcome.basis, Some(reference));
        assert_eq!(
            run::<4>("wdns-3-6", Arm::Shape, Budget::Lifted).status,
            "unsupported"
        );
    }

    /// Nonradical controls keep their multiplicities: D counts them and every arm agrees.
    #[test]
    fn nonradical_controls_preserve_multiplicity() {
        let reference = run::<3>("wdsq-3-6", Arm::DirectLex, Budget::Lifted)
            .basis
            .unwrap();
        for arm in [Arm::Adaptive, Arm::Wiedemann, Arm::Classical] {
            let outcome = run::<3>("wdsq-3-6", arm, Budget::Lifted);
            assert_eq!(outcome.fglm.as_ref().unwrap().quotient_dimension, 432);
            assert_eq!(outcome.basis.as_ref(), Some(&reference), "{arm:?}");
        }
        let reference = run::<4>("wdnr-3-6", Arm::DirectLex, Budget::Lifted)
            .basis
            .unwrap();
        let outcome = run::<4>("wdnr-3-6", Arm::Adaptive, Budget::Lifted);
        assert_eq!(outcome.fglm.as_ref().unwrap().quotient_dimension, 432);
        assert_eq!(outcome.basis, Some(reference));
    }

    /// The shipping budget refuses D above 4096 with a typed error instead of converting.
    #[test]
    fn shipping_budget_refuses_large_quotients() {
        let outcome = run::<2>("wd-2-70", Arm::Adaptive, Budget::Shipping);
        assert_eq!(outcome.status, "refused");
        assert!(outcome.error.unwrap().contains("QuotientDimensionExceeded"));
        let lifted = run::<2>("wd-2-70", Arm::Adaptive, Budget::Lifted);
        assert_eq!(lifted.status, "complete");
        assert_eq!(
            lifted.fglm.unwrap().conversion_route,
            ConversionRoute::Wiedemann
        );
    }

    /// Katsura, Cyclic and the planted quadratics convert to direct lex F4's basis; cyclic-4 is refused.
    #[test]
    fn named_families_convert_to_the_direct_lex_basis() {
        for name in ["katsura-4", "pquad-4-1"] {
            let reference = run::<4>(name, Arm::DirectLex, Budget::Lifted)
                .basis
                .unwrap();
            let outcome = run::<4>(name, Arm::Adaptive, Budget::Lifted);
            assert_eq!(outcome.basis, Some(reference), "{name}");
        }
        // Cyclic-4 is positive-dimensional; cyclic-5 (D = 70) is the smallest zero-dimensional one.
        assert_eq!(
            run::<4>("cyclic-4", Arm::Adaptive, Budget::Lifted).status,
            "unsupported"
        );
        let reference = run::<5>("cyclic-5", Arm::DirectLex, Budget::Lifted)
            .basis
            .unwrap();
        let outcome = run::<5>("cyclic-5", Arm::Classical, Budget::Lifted);
        assert_eq!(outcome.basis, Some(reference));
        let planted = run::<4>("pquad-4-1", Arm::Adaptive, Budget::Lifted);
        assert_eq!(planted.fglm.unwrap().quotient_dimension, 16);
    }

    /// The probe arm reports the last operator's density without converting.
    #[test]
    fn probe_reports_operator_shape() {
        let outcome = run::<3>("wd-3-6", Arm::Probe, Budget::Lifted);
        assert_eq!(outcome.status, "complete");
        assert!(outcome.basis.is_none());
        let get = |k: &str| {
            outcome
                .probe
                .iter()
                .find(|(n, _)| *n == k)
                .map(|(_, v)| v.clone())
        };
        assert_eq!(get("dimension"), Some(Json::size(216)));
        assert!(get("last_stored_entries").is_some());
    }

    fn key<const N: usize>(outcome: &Outcome<N, F>, name: &str) -> Option<Json> {
        selection(outcome)
            .into_iter()
            .find(|(n, _)| *n == name)
            .map(|(_, v)| v)
    }

    /// The #1008 selection keys: typed budget refusals, unsupported inputs and acceptance modes.
    #[test]
    fn selection_outcome_names_refusals_and_acceptance() {
        let outcome = |o: &str| Some(Json::string(o));
        let refused = run::<2>("wd-2-70", Arm::Adaptive, Budget::Shipping);
        assert_eq!(
            key(&refused, "selection_outcome"),
            outcome("memory-refusal")
        );
        let wiedemann = run::<2>("wd-2-70", Arm::Adaptive, Budget::Lifted);
        assert_eq!(
            key(&wiedemann, "acceptance"),
            outcome("certified-randomized")
        );
        assert_eq!(key(&wiedemann, "verified"), Some(Json::Bool(true)));
        let classical = run::<2>("wd-2-70", Arm::Classical, Budget::Lifted);
        assert_eq!(key(&classical, "selection_outcome"), outcome("complete"));
        assert_eq!(key(&classical, "acceptance"), outcome("deterministic"));
        let positive = run::<4>("cyclic-4", Arm::Adaptive, Budget::Lifted);
        assert_eq!(key(&positive, "selection_outcome"), outcome("unsupported"));
        let shape = run::<4>("wdns-3-6", Arm::Shape, Budget::Lifted);
        assert_eq!(key(&shape, "selection_outcome"), outcome("unsupported"));
    }

    /// A request survives the JSON round trip the grobx driver also reads.
    #[test]
    fn request_round_trips_through_json() {
        let request = family("wdsq-3-4", 65537).unwrap();
        let back = Request::from_json(&request.to_json().to_json()).unwrap();
        assert_eq!(back.generators, request.generators);
        assert_eq!(back.variables, request.variables);
        assert_eq!(back.digest(), request.digest());
    }

    /// The digest normalizes at the grevlex lead, so it matches `basis_digest.py` on a scaled basis.
    #[test]
    fn digest_matches_the_python_reference() {
        let basis: Vec<MultivariatePolynomial<2, Zp32003>> =
            ["2*x2^2+32001", "x1*x2+2", "x1^2+3*x2"]
                .iter()
                .map(|s| MultivariatePolynomial::parse(s, ["x1", "x2"]).unwrap())
                .collect();
        assert_eq!(
            basis_m33(&basis, 32003),
            "8fb196a0f7de4f7d36d2d8c6b34fb80eebd5f04658fcc799e1f2583781e5fefc"
        );
    }
}
