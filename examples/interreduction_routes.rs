//! Both final-interreduction routes over the corpus ladder, with the matrix route's own verdict.
//!
//! ```text
//! cargo run --release --example interreduction_routes              # every reference-field rung
//! cargo run --release --example interreduction_routes -- katsura-6 # one rung
//! cargo run --release --example interreduction_routes -- --orders  # grevlex, grlex and lex
//! ```
//!
//! # Why this exists and the competitive board does not answer it
//!
//! `competitive_sweep --interreduce-by-matrix on|off` produces two board rows and therefore two
//! wall times. A row that does not move between them is ambiguous in a way that matters for
//! deciding the default (#507): the matrix route is subject to the same row, column and entry
//! budgets as any batch's, and **falls back to the division route** when one would be crossed. So
//! an unchanged row may mean interreduction was already negligible, or it may mean the matrix was
//! never built — and `F4Statistics::interreduction_matrix` is the only place that difference is
//! recorded. The external adapter does not carry it out, so this example calls F4 directly.
//!
//! The two routes are run **interleaved on one build in one process**, and the bases are asserted
//! **equal** rather than both valid. A reduced Gröbner basis is unique up to its leading
//! monomials, so exact equality is the right failure mode for a route substitution.
//!
//! # Scope: the reference characteristic only
//!
//! Rungs whose registry pins their own field — the Poseidon and Anemoi CICO rungs, whose round
//! constants are derived from the prime — are skipped and say so. Covering them would mean
//! monomorphizing F4 over three more fields for rungs whose interreduction stage is under a
//! millisecond, and the board sweep already carries their timings. What is reported here is the
//! classical ladder, which is where `#507`'s unmeasured question lives.

use std::time::Duration;

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        external::{
            corpus::{instance, ladder},
            Instance,
        },
        f4_reported, F4Options, MatrixRefusal,
    },
    MonomialOrder, MultivariatePolynomial,
};

type F = Zp2147483647;

const REFERENCE: u64 = zeebra::grobner::external::REFERENCE_CHARACTERISTIC;

/// One rung's outcome under one order, as the table prints it.
struct Row {
    rung: String,
    order: &'static str,
    division_total: Duration,
    division_stage: Duration,
    matrix_total: Duration,
    matrix_stage: Duration,
    /// `None` when the matrix route recorded nothing, which is what a basis too small to have an
    /// interreduction matrix looks like.
    shape: Option<(usize, usize, usize)>,
    fell_back: Option<MatrixRefusal>,
    basis: usize,
}

fn millis(d: Duration) -> f64 {
    d.as_secs_f64() * 1e3
}

/// Run one instance through both routes and compare, or explain why it was not run.
///
/// A budget stop is reported rather than skipped: `f4_reported` returns its statistics whatever
/// the outcome, and a rung that stops under both routes is still evidence about the stage.
macro_rules! compare {
    ($instance:expr, $order_name:expr, $order:expr, $($n:literal),+ $(,)?) => {{
        let built: &Instance = $instance;
        let names: Vec<&str> = built.variables.iter().map(String::as_str).collect();
        match built.variables.len() {
            $(
                $n => {
                    let mut compiled = [""; $n];
                    compiled.copy_from_slice(&names[..$n]);
                    let mut system: Vec<MultivariatePolynomial<$n, F>> = Vec::new();
                    for text in &built.system {
                        system.push(
                            MultivariatePolynomial::parse(text, compiled)
                                .expect("this crate rendered this text"),
                        );
                    }
                    run_both(&built.name, $order_name, &system, $order)
                }
            )+
            other => {
                eprintln!("- {} has {} variables, which this example does not compile",
                          built.name, other);
                None
            }
        }
    }};
}

/// The two routes, interleaved, with the bases asserted equal.
fn run_both<const N: usize>(
    rung: &str,
    order_name: &'static str,
    system: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
) -> Option<Row> {
    let division = F4Options {
        measure_stages: true,
        interreduce_by_matrix: false,
        ..F4Options::default()
    };
    let matrix = F4Options {
        measure_stages: true,
        interreduce_by_matrix: true,
        ..F4Options::default()
    };

    let (division_basis, division_statistics) = f4_reported(system, order, &division);
    let (matrix_basis, matrix_statistics) = f4_reported(system, order, &matrix);

    match (&division_basis, &matrix_basis) {
        (Ok(expected), Ok(actual)) => assert_eq!(
            actual, expected,
            "{rung} under {order_name}: the matrix route returned a different basis. A reduced \
             Grobner basis is unique, so this is a correctness failure and not a tolerance."
        ),
        // Both stopped, which is a fact about the rung and not about the route. Reported with the
        // timings it did take, because a stage share under a budget stop is still a stage share.
        (Err(_), Err(_)) => eprintln!("- {rung} under {order_name}: both routes stopped short"),
        // One finished and one did not. Never silently averaged: the two sides are no longer the
        // same computation, so the row would be a ratio between different amounts of work.
        _ => {
            eprintln!(
                "- {rung} under {order_name}: one route stopped and the other did not, so there \
                 is no comparison to report"
            );
            return None;
        }
    }

    let shape = matrix_statistics
        .interreduction_matrix
        .as_ref()
        .map(|m| (m.rows, m.columns, m.nonzeros));
    let fell_back = matrix_statistics
        .interreduction_matrix
        .as_ref()
        .and_then(|m| m.refused_by);

    Some(Row {
        rung: rung.to_string(),
        order: order_name,
        division_total: division_statistics.total,
        division_stage: division_statistics.stages.interreduction,
        matrix_total: matrix_statistics.total,
        matrix_stage: matrix_statistics.stages.interreduction,
        shape,
        fell_back,
        basis: division_basis.map(|b| b.len()).unwrap_or(0),
    })
}

fn refusal(reason: &MatrixRefusal) -> String {
    match reason {
        MatrixRefusal::Rows { limit } => format!("rows > {}", limit),
        MatrixRefusal::Columns { limit } => format!("columns > {}", limit),
        MatrixRefusal::Nonzeros { nonzeros } => format!("{} live nonzeros", nonzeros),
    }
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let all_orders = arguments.iter().any(|a| a == "--orders");
    let wanted: Vec<&str> = arguments
        .iter()
        .filter(|a| !a.starts_with("--"))
        .map(String::as_str)
        .collect();

    let orders: &[(&'static str, MonomialOrder)] = if all_orders {
        &[
            ("grevlex", MonomialOrder::GradedReverseLexicographic),
            ("grlex", MonomialOrder::GradedLexicographic),
            ("lex", MonomialOrder::Lexicographic),
        ]
    } else {
        &[("grevlex", MonomialOrder::GradedReverseLexicographic)]
    };

    println!(
        "# #507: both interreduction routes over the corpus ladder, GF({})",
        REFERENCE
    );
    println!();

    let mut rows: Vec<Row> = Vec::new();
    for entry in ladder() {
        if !wanted.is_empty() && !wanted.contains(&entry.name) {
            continue;
        }
        for (order_name, order) in orders {
            let built = match instance(entry.name, REFERENCE, *order) {
                Some(built) => built,
                None => {
                    eprintln!("- {} is not in the corpus at this field", entry.name);
                    continue;
                }
            };
            // A rung that keeps its registry field is a different problem from the one asked for,
            // and this example compiles F4 over the reference field only.
            if built.field.characteristic != REFERENCE {
                eprintln!(
                    "- {} keeps its registry field GF({}), which this example does not compile",
                    built.name, built.field.characteristic
                );
                continue;
            }
            if let Some(row) = compare!(&built, order_name, *order, 4, 5, 6, 7, 8, 9, 10, 11, 14) {
                rows.push(row);
            }
        }
    }

    println!(
        "{:<30} {:<8} {:>11} {:>11} {:>8} {:>11} {:>11} {:>8} {:>7} {:>6}",
        "rung",
        "order",
        "div/ms",
        "div stage",
        "stage %",
        "matrix/ms",
        "mtx stage",
        "stage %",
        "e2e",
        "basis"
    );
    for row in &rows {
        let share = |stage: Duration, total: Duration| {
            if total.is_zero() {
                0.0
            } else {
                100.0 * stage.as_secs_f64() / total.as_secs_f64()
            }
        };
        println!(
            "{:<30} {:<8} {:>11.3} {:>11.3} {:>7.2}% {:>11.3} {:>11.3} {:>7.2}% {:>6.2}x {:>6}",
            row.rung,
            row.order,
            millis(row.division_total),
            millis(row.division_stage),
            share(row.division_stage, row.division_total),
            millis(row.matrix_total),
            millis(row.matrix_stage),
            share(row.matrix_stage, row.matrix_total),
            millis(row.division_total) / millis(row.matrix_total).max(f64::MIN_POSITIVE),
            row.basis
        );
    }

    println!();
    println!("## What the matrix route did on each rung");
    println!();
    for row in &rows {
        let verdict = match (&row.shape, &row.fell_back) {
            (Some((r, c, nz)), None) => format!(
                "built {} x {}, {} nonzeros ({:.2}% dense)",
                r,
                c,
                nz,
                100.0 * *nz as f64 / (*r as f64 * *c as f64).max(f64::MIN_POSITIVE)
            ),
            (Some((r, c, nz)), Some(reason)) => format!(
                "FELL BACK to division, refused on {}; would have been {} x {}, {} nonzeros",
                refusal(reason),
                r,
                c,
                nz
            ),
            (None, _) => {
                "no interreduction matrix recorded — nothing reducible to close over".to_string()
            }
        };
        println!("- `{}` {}: {}", row.rung, row.order, verdict);
    }

    println!();
    println!(
        "A `FELL BACK` row's matrix column is the division route's timing under another name,"
    );
    println!("so its end-to-end ratio is noise and not an effect. An unchanged row with a built");
    println!("matrix is an honest null: the route ran and the stage was not where the time went.");
}
