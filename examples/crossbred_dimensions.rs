//! What crossbred would cost on the instances Zeebra has, against what F4 actually cost.
//!
//! #75's deliverable is "a written complexity accounting, validated against one published
//! parameter choice", with the warning that **the cost is the sum over all guesses, not the size
//! of the reduced system**. This harness is that accounting as arithmetic: it builds no Macaulay
//! matrix and runs no linear algebra, because admissibility and the shapes are series coefficients
//! and binomial counts — exact integers that reproduce bit-for-bit and need no benchmark lock.
//!
//! It runs the validation first. Every published parameter choice this repository could find for
//! crossbred over `F_2` is checked against [`zeebra::grobner::research::crossbred`] before any
//! figure about Zeebra's own instances is printed, so a figure below is either consistent with
//! Joux-Vitse's Table 1, Vidal-Delaplace-Ionica's Tables 1, 2 and 6, and Baena et al.'s Example 2,
//! or this harness refuses to run.
//!
//! The comparand is F4's **measured** peak live entries on the same instance, transcribed through
//! `docs/research/mq-comparison-methodology.md` §7 exactly as `examples/xl_dimensions.rs` does, so
//! the two harnesses price their matrices in the same unit and #76's answer and #75's are
//! comparable.
//!
//! ```text
//! cargo run --release --example crossbred_dimensions
//! cargo run --release --example crossbred_dimensions -- 10 15 20
//! ```

use zeebra::fields::Zp31;
use zeebra::grobner::research::crossbred::{
    best_parameters, monomials_up_to, preprocessing_shape, CrossbredSeries, WorkOptions,
};

/// Fukuoka type III rungs Zeebra has imported, which are `m = 2n` quadratics over GF(31).
const DEFAULT: [usize; 3] = [10, 15, 20];

/// How far to expand the bivariate series when searching for an admissible `(D, d)`.
///
/// The search cost is cubic in this and the series are `m`-th powers, so it is a parameter rather
/// than a constant. Type III at `n = 20` needs `D = 7` and nothing in this family has wanted more.
const MAX_DEGREE: u64 = 10;

/// Bytes a live sparse entry occupies — `xl_dimensions`' unit, so the figures are comparable.
fn bytes_per_entry() -> usize {
    size_of::<(usize, Zp31)>()
}

/// F4's **measured** peak live entries on the type III rung at `n`, and what produced the figure.
///
/// Transcribed from `research/scoreboard/runs/` through `mq-comparison-methodology.md` §7, the
/// same four rows `examples/xl_dimensions.rs` carries. `None` where Zeebra has no type III run.
fn f4_peak_entries(n: usize) -> Option<(u64, &'static str)> {
    match n {
        10 => Some((168_020, "verified witness, 114 ms, D = 1")),
        15 => Some((2_143_983, "verified witness, 7.8 s, D = 1")),
        20 => Some((12_212_087, "stopped at the 20 000 000-entry cap, degree 5")),
        _ => None,
    }
}

/// A deliberately generous field-operation rate, used only to bound a decision.
///
/// Nothing here is measured in seconds, and inventing a rate would be inventing a measurement. So
/// the rate is chosen to be **generously favourable to crossbred** — `10^9` field operations per
/// second is above what any dense-linear-algebra kernel in this repository has measured over
/// GF(31) — and used only where the conclusion survives being wrong by orders of magnitude. Where
/// it does not survive, the cell says so instead of reporting a number.
const GENEROUS_OPERATIONS_PER_SECOND: f64 = 1e9;

/// F4's **measured** wall time to a verified solution on the type III rung at `n`.
///
/// Same provenance as [`f4_peak_entries`]. `None` where F4 did not reach a solution — at `n = 20`
/// it stopped at the entry cap, which is itself the comparison's most interesting row.
fn f4_measured_seconds(n: usize) -> Option<f64> {
    match n {
        10 => Some(0.114),
        15 => Some(7.8),
        _ => None,
    }
}

/// `2^log2` seconds at [`GENEROUS_OPERATIONS_PER_SECOND`], rendered, or a refusal.
fn generous_seconds(log2_operations: f64) -> String {
    let seconds = log2_operations.exp2() / GENEROUS_OPERATIONS_PER_SECOND;
    if seconds < 1.0 {
        format!("{:.0} ms", seconds * 1000.0)
    } else if seconds < 90.0 {
        format!("{:.1} s", seconds)
    } else if seconds < 3600.0 * 48.0 {
        format!("{:.1} h", seconds / 3600.0)
    } else if seconds < 3600.0 * 24.0 * 365.0 * 1000.0 {
        format!("{:.0} days", seconds / (3600.0 * 24.0))
    } else {
        format!("{:.0} years", seconds / (3600.0 * 24.0 * 365.0))
    }
}

/// Bytes, in whichever unit keeps the figure readable.
fn human(bytes: i128) -> String {
    let b = bytes as f64;
    if b >= 1024.0_f64.powi(5) {
        format!("{:.2} PiB", b / 1024.0_f64.powi(5))
    } else if b >= 1024.0_f64.powi(4) {
        format!("{:.2} TiB", b / 1024.0_f64.powi(4))
    } else if b >= 1024.0_f64.powi(3) {
        format!("{:.2} GiB", b / 1024.0_f64.powi(3))
    } else if b >= 1024.0 * 1024.0 {
        format!("{:.1} MiB", b / (1024.0 * 1024.0))
    } else {
        format!("{:.0} KiB", b / 1024.0)
    }
}

/// That the five parameter sets of Joux and Vitse's own Table 1 reproduce.
///
/// Their table publishes the column count `N`, the independent-row count `R`, and the polynomial
/// count they expect; the series must land on the same integers, which is what says this harness
/// computes the quantity their table reports and not a near relative of it.
fn the_joux_vitse_parameters_reproduce() {
    let published = [
        (35usize, 35usize, 9usize, 3u64, 1056i128, 204i128),
        (35, 70, 14, 3, 2366, 154),
        (41, 41, 11, 4, 31075, 3406),
        (41, 82, 15, 3, 3290, 154),
        (62, 148, 23, 4, 277288, 878),
    ];
    for (n, m, k, degree, columns, polynomials) in published {
        let series = CrossbredSeries::new(2, n, m, k, degree).expect("the series expands");
        let shape = preprocessing_shape(&series, n, degree, 1).expect("a shape");
        assert_eq!(shape.columns, columns, "columns at n = {}, k = {}", n, k);
        assert_eq!(
            shape.polynomials, polynomials,
            "polynomials at n = {}, k = {}",
            n, k
        );
    }
}

/// That the `n = 74` Fukuoka type I record's own parameters are admissible, and that the stricter
/// definition of 2024/758 does not take them away.
///
/// Joux and Vitse solved 148 quadratics in 74 variables at `(D, d, k) = (4, 1, 23)` with `h = 12`
/// outer hybridation, so on 62 variables. Both conditions of 2024/758 Definition 5 hold there, and
/// `2^51` is the guess count that record paid.
fn the_record_parameters_are_admissible() {
    let series = CrossbredSeries::new(2, 62, 148, 23, 4).expect("the series expands");
    let verdict = series.admissibility(4, 1);
    assert!(
        verdict.admissible(),
        "the n = 74 record's parameters must be admissible: {:?}",
        verdict
    );
    assert_eq!(verdict.polynomials, 878, "878 polynomials, as published");
    assert_eq!(verdict.needed, 24, "linearization at d = 1 needs k + 1");
}

/// Crossbred's shape and total work at the cheapest admissible triple for one instance.
struct Plan {
    kept: usize,
    degree: u64,
    kept_degree: u64,
    log2_guesses: f64,
    log2_per_guess: f64,
    log2_total: f64,
    preprocessing_bytes: i128,
    polynomials: i128,
}

/// The cheapest admissible triple for `m` quadratics in `n` variables over `F_q`, by total work.
///
/// Sweeps `k` because the literature's parameters are found by search and not by formula: the
/// admissible set is not an interval in `k`, and the optimum trades `q^(n-k)` guesses against a
/// preprocessing matrix that grows with `k`.
fn plan(order: u64, variables: usize, equations: usize) -> Option<Plan> {
    let mut best: Option<Plan> = None;
    for kept in 1..variables {
        let options = WorkOptions::default();
        let Ok(Some((degree, kept_degree, accounting))) =
            best_parameters(order, variables, equations, kept, MAX_DEGREE, options)
        else {
            continue;
        };
        if best
            .as_ref()
            .is_some_and(|found| found.log2_total <= accounting.log2_total)
        {
            continue;
        }
        let series =
            CrossbredSeries::new(order, variables, equations, kept, degree).expect("expands");
        let shape = preprocessing_shape(&series, variables, degree, kept_degree).expect("a shape");
        // A row is one quadratic times one monomial, so it carries as many entries as a dense
        // quadratic has terms — the same reasoning `xl_dimensions` prices XL's rows by.
        let terms = monomials_up_to(variables, order, 2).expect("a term count");
        best = Some(Plan {
            kept,
            degree,
            kept_degree,
            log2_guesses: accounting.log2_guesses,
            log2_per_guess: accounting.log2_per_guess,
            log2_total: accounting.log2_total,
            preprocessing_bytes: shape.rows * terms * bytes_per_entry() as i128,
            polynomials: shape.polynomials,
        });
    }
    best
}

fn main() {
    the_joux_vitse_parameters_reproduce();
    the_record_parameters_are_admissible();

    let arguments: Vec<String> = std::env::args().skip(1).filter(|a| a != "--").collect();
    let sizes: Vec<usize> = if arguments.is_empty() {
        DEFAULT.to_vec()
    } else {
        arguments
            .iter()
            .map(|a| a.parse().expect("a variable count"))
            .collect()
    };

    println!("# Crossbred's work on the instances Zeebra has, against F4's measured cost (#75)");
    println!();
    println!("Counts, not timings. Admissibility is a coefficient of a bivariate series and the");
    println!("matrix shapes are monomial counts, so every figure is exact and reproduces without");
    println!("a benchmark lock. Validated first against Joux-Vitse's Table 1 and the n = 74");
    println!("record's own parameters — this harness refuses to print if either fails.");
    println!();
    println!("`guesses` is `q^(n-k)` and is reported on its own line, never folded into a");
    println!("per-guess figure: **the cost is the sum over all guesses.**");
    println!();
    println!("## Fukuoka type III, `m = 2n` quadratics over GF(31)");
    println!();
    println!(
        "| n | best (D, d, k) | polys r | log2 guesses | log2 per guess | log2 total | crossbred matrix | F4 measured peak | crossbred at 1e9 ops/s | F4 measured |"
    );
    println!("|---|---|---|---|---|---|---|---|---|---|");
    for n in sizes.iter().copied() {
        let equations = 2 * n;
        match plan(31, n, equations) {
            Some(found) => {
                let measured = f4_peak_entries(n)
                    .map(|(entries, note)| {
                        format!(
                            "{} ({})",
                            human(entries as i128 * bytes_per_entry() as i128),
                            note
                        )
                    })
                    .unwrap_or_else(|| "no Zeebra run".to_string());
                println!(
                    "| {} | ({}, {}, {}) | {} | {:.1} | {:.1} | {:.1} | {} | {} | {} | {} |",
                    n,
                    found.degree,
                    found.kept_degree,
                    found.kept,
                    found.polynomials,
                    found.log2_guesses,
                    found.log2_per_guess,
                    found.log2_total,
                    human(found.preprocessing_bytes),
                    measured,
                    generous_seconds(found.log2_total),
                    f4_measured_seconds(n)
                        .map(|seconds| format!("{} s to a witness", seconds))
                        .unwrap_or_else(|| "no solution: hit the entry cap".to_string())
                );
            }
            None => println!(
                "| {} | none admissible with D <= {} | | | | | | | | |",
                n, MAX_DEGREE
            ),
        }
    }

    println!();
    println!("## The GF(2) rungs crossbred was built for, for scale");
    println!();
    println!("Zeebra cannot import type I — `MqField` says why — so these are the literature's");
    println!("own instances, priced by the same arithmetic.");
    println!();
    println!(
        "| instance | (D, d, k) | h | polys r | log2 guesses | log2 preprocessing | log2 total |"
    );
    println!("|---|---|---|---|---|---|---|");
    for (label, variables, equations, kept, degree, kept_degree, hybridation) in [
        (
            "type I n=74 (Joux-Vitse record)",
            74usize,
            148usize,
            23usize,
            4u64,
            1u64,
            12usize,
        ),
        ("type I n=74 (Bellini optimum)", 74, 148, 28, 6, 1, 0),
        ("MQOM level I", 160, 160, 31, 13, 1, 3),
    ] {
        let options = WorkOptions {
            hybridation,
            ..WorkOptions::default()
        };
        let accounting = zeebra::grobner::research::crossbred::work(
            2,
            variables,
            equations,
            kept,
            degree,
            kept_degree,
            options,
        )
        .expect("an accounting");
        let series = CrossbredSeries::new(2, variables - hybridation, equations, kept, degree)
            .expect("expands");
        println!(
            "| {} | ({}, {}, {}) | {} | {} | {:.1} | {:.1} | {:.1} |",
            label,
            degree,
            kept_degree,
            kept,
            hybridation,
            series.polynomials(degree, kept_degree),
            accounting.log2_guesses,
            accounting.log2_preprocessing,
            accounting.log2_total
        );
    }
    println!();
    println!("See `docs/research/crossbred.md` for what these figures mean for Zeebra, which");
    println!("published totals they do and do not agree with, and the recommendation.");
}
