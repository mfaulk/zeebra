//! #1192: hit rate of the weight-vector detector, and weighted-vs-grevlex matrix counts.
//!
//! cargo run --release --example weight_detector_study -- --panel research/m34-public-corpus/catalog.json [--solve]
//! cargo run --release --example weight_detector_study -- --families
//!
//! `--panel` reads the #1006 public panel and prints one JSON line per `p31` record: the
//! detector's outcome and work under grevlex tie-breaks, and the weighted-homogeneity weights.
//! `--families` runs two parameterised families (see `chain` and `power_map`) and, on each row,
//! conventional F4 under grevlex and, where the detector hits, under its weighted order, then FGLM
//! to lex from each basis. Every reported figure is a count except the `_ns` fields, which are
//! unpinned and for scale only.

use std::time::Instant;
use zeebra::{
    fields::Zp2147483647 as F,
    grobner::{
        f4_with_options, fglm_to_lex_with_options,
        weight_detector::{
            detect_free_basis, weighted_homogeneous_weights, Detection, DetectorLimits,
        },
        F4Options, F4Statistics, FglmOptions, FglmStatistics,
    },
    util::Json,
    FiniteField, Monomial, MonomialOrder, MultivariatePolynomial, WeightedTieBreak,
};

const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;
const TIE_BREAK: WeightedTieBreak = WeightedTieBreak::ReverseLexicographic;

fn detection<const N: usize>(d: &Detection<N>, ns: u128) -> Json {
    let s = &d.statistics;
    let mut fields = vec![
        (
            "outcome",
            Json::string(match &d.outcome {
                Ok(hit) if hit.weights.iter().all(|&w| w == 1) => "hit-graded".to_string(),
                Ok(_) => "hit-weighted".to_string(),
                Err(miss) => format!("{miss:?}"),
            }),
        ),
        ("fast_path", Json::Bool(s.fast_path)),
        ("screen_nodes", Json::size(s.screen_nodes)),
        ("candidates", Json::size(s.candidates)),
        ("nodes", Json::size(s.nodes)),
        ("lp_solves", Json::size(s.lp_solves)),
        ("lp_pivots", Json::size(s.lp_pivots)),
        ("detect_ns", Json::int(ns as i128)),
    ];
    if let Ok(hit) = &d.outcome {
        fields.push((
            "weights",
            Json::Array(hit.weights.iter().map(|&w| Json::int(w)).collect()),
        ));
    }
    Json::object(fields)
}

fn detect<const N: usize>(system: &[MultivariatePolynomial<N, F>]) -> (Detection<N>, Json) {
    let started = Instant::now();
    let d = detect_free_basis(system, TIE_BREAK, &DetectorLimits::default());
    let ns = started.elapsed().as_nanos();
    let json = detection(&d, ns);
    (d, json)
}

// ---------------------------------------------------------------------------------------------
// The public panel.

fn panel_row<const N: usize>(record: &Json, solve: bool) -> Json {
    let mut system = Vec::new();
    for equation in record.get("equations").map_or(&[][..], Json::items) {
        let terms: Vec<(Monomial<N>, F)> = equation
            .items()
            .iter()
            .map(|term| {
                let exponents: Vec<u32> = term
                    .get("exponents")
                    .map_or(&[][..], Json::items)
                    .iter()
                    .map(|e| e.as_int().expect("exponent") as u32)
                    .collect();
                let c = term
                    .get("coefficient")
                    .and_then(|c| c.items().first())
                    .and_then(Json::as_str)
                    .expect("coefficient");
                (
                    Monomial::new(&exponents),
                    F::from_str(c).expect("coefficient"),
                )
            })
            .collect();
        system.push(MultivariatePolynomial::new(&terms));
    }
    let (d, json) = detect(&system);
    let homogeneous_result = weighted_homogeneous_weights(&system);
    let homogeneous = match &homogeneous_result {
        Ok(Some(w)) => Json::Array(w.iter().map(|&w| Json::int(w)).collect()),
        Ok(None) => Json::Null,
        Err(e) => Json::string(format!("{e:?}")),
    };
    let homogeneous_weights = homogeneous_result.ok().flatten();
    let mut fields = vec![
        (
            "id",
            Json::string(record.get("id").and_then(Json::as_str).unwrap_or("")),
        ),
        ("variables", Json::size(N)),
        ("generators", Json::size(system.len())),
        ("detector", json),
        ("weighted_homogeneous", homogeneous),
    ];
    // Priced only where detection did LP work or found weights: elsewhere it is microseconds.
    let weights: Vec<Vec<u32>> = d
        .outcome
        .as_ref()
        .ok()
        .map(|hit| hit.weights.clone())
        .into_iter()
        .chain(homogeneous_weights.filter(|w| w.iter().any(|&w| w != 1)))
        .collect();
    if solve && (d.statistics.lp_solves > 0 || !weights.is_empty()) {
        let run = |order| {
            let started = Instant::now();
            match f4_with_options(&system, order, &F4Options::default()) {
                Ok((_, f4)) => f4_counts(&f4, started.elapsed().as_nanos()),
                Err(e) => Json::object([("error", Json::string(format!("{e:?}")))]),
            }
        };
        fields.push(("grevlex_f4", run(GREVLEX)));
        let weighted: Vec<Json> = weights
            .iter()
            .map(|w| {
                let order = MonomialOrder::weighted(w, TIE_BREAK).expect("positive weights");
                Json::object([
                    (
                        "weights",
                        Json::Array(w.iter().map(|&w| Json::int(w)).collect()),
                    ),
                    ("f4", run(order)),
                ])
            })
            .collect();
        fields.push(("weighted_f4", Json::Array(weighted)));
    }
    Json::object(fields)
}

/// `--solve` also runs grevlex F4, the solve the detector is priced against, and F4 under each
/// weight vector the row has (a detector hit, non-trivial weighted homogeneity).
fn panel(path: &str, solve: bool) {
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{path}: {e}"));
    let records = Json::parse(&text).expect("catalog JSON");
    for record in records.items() {
        let characteristic = record
            .get("field")
            .and_then(|f| f.get("characteristic"))
            .and_then(Json::as_str);
        if characteristic != Some("2147483647") {
            continue;
        }
        let n = record.get("variables").map_or(0, |v| v.items().len());
        macro_rules! dispatch {
            ($($n:literal),*) => {
                match n {
                    $($n => panel_row::<$n>(record, solve),)*
                    _ => panic!("no instantiation for {n} variables"),
                }
            };
        }
        let row = dispatch!(2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 21, 22, 24, 34);
        println!("{}", row.to_json().replace('\n', ""));
    }
}

// ---------------------------------------------------------------------------------------------
// Families.

fn names<const N: usize>() -> [String; N] {
    std::array::from_fn(|i| format!("x{i}"))
}

fn parse<const N: usize>(text: &[String]) -> Vec<MultivariatePolynomial<N, F>> {
    let names = names::<N>();
    let vars: [&str; N] = std::array::from_fn(|i| names[i].as_str());
    text.iter()
        .map(|s| MultivariatePolynomial::parse(s, vars).expect("generator"))
        .collect()
}

/// `x_i^d + x_{i+1}^{d+1} + x_i·x_{i+1} + (i+2)` for `i < n-1`, closed by `x_{n-1}^d + x_0 + 1`.
///
/// Synthetic, not an application model. Under grevlex the leading monomials `x_{i+1}^{d+1}` and
/// `x_{n-1}^d` share `x_{n-1}`, so F4 runs; a weight vector that orients the cycle the other way
/// at one link makes them coprime.
fn chain<const N: usize>(d: u32) -> Vec<MultivariatePolynomial<N, F>> {
    let mut text: Vec<String> = (0..N - 1)
        .map(|i| {
            format!(
                "x{i}^{d} + x{j}^{e} + x{i}*x{j} + {c}",
                j = i + 1,
                e = d + 1,
                c = i + 2
            )
        })
        .collect();
    text.push(format!("x{}^{d} + x0 + 1", N - 1));
    parse(&text)
}

/// A textbook iterated power map with `N` rounds: `(x_i + c_i)^3 − x_{i+1}`, closed by
/// `(x_{N-1} + c)^3 − 5`. Each new state is the cube of the previous one, MiMC-style; no
/// cryptanalytic structure is modelled.
fn power_map<const N: usize>() -> Vec<MultivariatePolynomial<N, F>> {
    let cube = |i: usize, c: u64| {
        format!(
            "x{i}^3 + {a}*x{i}^2 + {b}*x{i} + {k}",
            a = 3 * c,
            b = 3 * c * c,
            k = c * c * c
        )
    };
    let mut text: Vec<String> = (0..N - 1)
        .map(|i| format!("{} - x{}", cube(i, i as u64 + 2), i + 1))
        .collect();
    text.push(format!("{} - 5", cube(N - 1, 7)));
    parse(&text)
}

fn f4_counts(s: &F4Statistics, ns: u128) -> Json {
    Json::object([
        ("batches", Json::size(s.batches)),
        ("pairs_reduced", Json::size(s.pairs_reduced)),
        (
            "pairs_product_criterion",
            Json::size(s.pairs_eliminated_by_product_criterion),
        ),
        ("max_pair_degree", Json::int(s.max_pair_degree)),
        ("max_rows", Json::size(s.max_matrix_rows)),
        ("max_columns", Json::size(s.max_matrix_columns)),
        ("max_live_nonzeros", Json::size(s.max_live_nonzeros)),
        ("call_ns", Json::int(ns as i128)),
    ])
}

fn fglm_counts(s: &FglmStatistics, ns: u128) -> Json {
    Json::object([
        ("quotient_dimension", Json::size(s.quotient_dimension)),
        ("operator_entries", Json::size(s.operator_entries)),
        ("normal_form_calls", Json::size(s.border.normal_form_calls)),
        ("border_columns", Json::size(s.border.border_columns)),
        ("candidates_considered", Json::size(s.candidates_considered)),
        ("span_row_operations", Json::size(s.span_row_operations)),
        ("call_ns", Json::int(ns as i128)),
    ])
}

/// F4 under `order`, then FGLM to lex from its basis.
fn solve<const N: usize>(
    system: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
) -> (Json, Json, Vec<MultivariatePolynomial<N, F>>) {
    let started = Instant::now();
    let (basis, f4) = f4_with_options(system, order, &F4Options::default()).expect("F4");
    let f4_ns = started.elapsed().as_nanos();
    let started = Instant::now();
    let (lex, fglm) =
        fglm_to_lex_with_options(&basis, order, &FglmOptions::default()).expect("FGLM");
    let fglm_ns = started.elapsed().as_nanos();
    (f4_counts(&f4, f4_ns), fglm_counts(&fglm, fglm_ns), lex)
}

fn family_row<const N: usize>(name: &str, system: Vec<MultivariatePolynomial<N, F>>) -> Json {
    let (d, detector) = detect(&system);
    let (f4, fglm, lex) = solve(&system, GREVLEX);
    let mut fields = vec![
        ("name", Json::string(name)),
        ("variables", Json::size(N)),
        ("detector", detector),
        ("grevlex_f4", f4),
        ("grevlex_fglm", fglm),
    ];
    if let Ok(hit) = &d.outcome {
        let (f4, fglm, weighted_lex) = solve(&system, hit.order);
        // The lex basis is a property of the ideal: both routes must agree exactly.
        assert_eq!(weighted_lex, lex, "{name}: lex bases differ");
        fields.push(("weighted_f4", f4));
        fields.push(("weighted_fglm", fglm));
    }
    Json::object(fields)
}

fn families() {
    let mut rows = Vec::new();
    macro_rules! chain_rows {
        ($(($d:literal, $n:literal)),*) => {
            $(rows.push(family_row::<$n>(&format!("chain-d{}-n{}", $d, $n), chain::<$n>($d)));)*
        };
    }
    chain_rows!(
        (2, 2),
        (2, 3),
        (3, 3),
        (3, 4),
        (3, 5),
        (4, 3),
        (4, 4),
        (4, 5),
        (5, 3),
        (5, 4)
    );
    macro_rules! power_rows {
        ($($n:literal),*) => {
            $(rows.push(family_row::<$n>(&format!("power-map-{}", $n), power_map::<$n>()));)*
        };
    }
    power_rows!(3, 4, 5, 6);
    for row in rows {
        println!("{}", row.to_json().replace('\n', ""));
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("--panel") => panel(
            args.get(1).expect("--panel FILE"),
            args.get(2).map(String::as_str) == Some("--solve"),
        ),
        Some("--families") => families(),
        _ => panic!("usage: --panel FILE | --families"),
    }
}
