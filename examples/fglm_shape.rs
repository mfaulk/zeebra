//! Which benchmark systems are in shape position, and what the shape route would save.
//!
//! M18-4's research spike, measured. Classical FGLM walks the monomials in lex order and keeps
//! every accepted quotient vector so a candidate's class costs one operator application. If a
//! single variable generates the quotient algebra — **shape position** — none of that is needed:
//! the lex basis is `p(t)` together with `x_i - h_i(t)`, and each of those is one solve against the
//! echelon form of `1, t, ..., t^{D-1}`.
//!
//! Three questions, three tables:
//!
//! * **Which variables generate the algebra**, per system. The answer is not "all" or "none", and
//!   the shape *lex* basis needs the last one specifically.
//! * **What it costs**, two ways: the two conversion routes against each other from a prepared
//!   quotient algebra, and end to end from the source basis. Only the second is what a caller pays,
//!   and the two do not agree — the operators dominate end to end, so a route that is 2.7x slower
//!   disappears into a wash.
//! * **What it saves**, in dense cells. The shape route holds the echelon form and one vector; the
//!   classical route holds the echelon form and every accepted vector.
//!
//! **Not sparse FGLM.** Faugère and Mou replace the dense dependence test with a scalar Krylov
//! sequence and Berlekamp–Massey, which is where the asymptotic win is. This prototype keeps the
//! dense echelon form. §8 of `docs/MILESTONE-FGLM-SCALABILITY.md` is the go/no-go that follows.
//!
//! ```text
//! cargo run --release --example fglm_shape
//! cargo run --release --example fglm_shape -- katsura-7
//! ```

use std::{
    io::Write,
    time::{Duration, Instant},
};

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura, planted},
        f4,
        fglm::{
            fglm_to_lex, fglm_to_lex_with_options, separating_variables, shape_lex_basis,
            shape_report, FglmOptions, IncrementalSpan, QuotientAlgebra, ShapeError,
        },
    },
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

type F = Zp2147483647;

const SOURCE: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

fn millis(d: Duration) -> f64 {
    d.as_secs_f64() * 1e3
}

/// The fastest of three runs: interference can only make a run slower.
fn fastest(mut run: impl FnMut() -> Duration) -> Duration {
    (0..3).map(|_| run()).min().expect("a round")
}

fn algebra_of<const N: usize>(source: &[MultivariatePolynomial<N, F>]) -> QuotientAlgebra<N, F> {
    QuotientAlgebra::new(source, SOURCE, &FglmOptions::unbounded()).expect("finite")
}

fn position_header() {
    println!(
        "| {:<11} | {:>2} | {:>5} | {:>10} | {:>22} | {:>12} |",
        "system", "N", "D", "deg of x_N-1", "separating variables", "shape basis",
    );
    println!(
        "|{}|{}|{}|{}|{}|{}|",
        "-".repeat(13),
        "-".repeat(4),
        "-".repeat(7),
        "-".repeat(12),
        "-".repeat(24),
        "-".repeat(14),
    );
}

fn position_row<const N: usize>(name: &str, system: &[MultivariatePolynomial<N, F>]) {
    let source = f4(system, SOURCE).expect("within limits");
    let algebra = algebra_of(&source);
    let report = shape_report(&algebra, N - 1);
    let separating = separating_variables(&algebra);

    let outcome = match shape_lex_basis(&algebra) {
        Ok(basis) => {
            // Asserted before it is reported: the reduced lex basis is unique, so a shape basis
            // that differs from the classical one is simply wrong.
            assert_eq!(
                basis,
                fglm_to_lex(&source, SOURCE).expect("convertible"),
                "{}: the shape basis disagrees with classical FGLM",
                name
            );
            "yes".to_string()
        }
        Err(ShapeError::NotSeparating { .. }) => "no".to_string(),
        Err(e) => panic!("{}: {}", name, e),
    };

    println!(
        "| {:<11} | {:>2} | {:>5} | {:>10} | {:>22} | {:>12} |",
        name,
        N,
        algebra.dimension(),
        report.minimal_polynomial_degree,
        format!("{:?}", separating),
        outcome,
    );
    std::io::stdout().flush().expect("stdout");
}

fn cost_header() {
    println!(
        "| {:<11} | {:>5} | {:>10} | {:>10} | {:>8} | {:>10} | {:>10} | {:>8} | {:>10} | {:>10} | {:>8} |",
        "system",
        "D",
        "lex walk",
        "shape",
        "route won",
        "classical",
        "shape all",
        "end won",
        "classical",
        "shape cells",
        "cells won",
    );
    println!(
        "|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|",
        "-".repeat(13),
        "-".repeat(7),
        "-".repeat(12),
        "-".repeat(12),
        "-".repeat(10),
        "-".repeat(12),
        "-".repeat(12),
        "-".repeat(10),
        "-".repeat(12),
        "-".repeat(13),
        "-".repeat(10),
    );
}

fn cost_row<const N: usize>(name: &str, system: &[MultivariatePolynomial<N, F>]) {
    let source = f4(system, SOURCE).expect("within limits");
    let algebra = algebra_of(&source);
    if shape_lex_basis(&algebra).is_err() {
        return;
    }
    let d = algebra.dimension();

    // Two comparisons, because they answer different questions and only one of them is the one a
    // caller cares about.
    //
    // The *route*: the classical lex walk against the shape route, both starting from a prepared
    // quotient algebra. The walk's own figure comes from the stage breakdown rather than from a
    // separate timing, since there is no entry point that runs the walk alone.
    let mut measured = FglmOptions::unbounded();
    measured.measure_stages = true;
    let walk = (0..3)
        .map(|_| {
            fglm_to_lex_with_options(&source, SOURCE, &measured)
                .expect("convertible")
                .1
                .timings
                .dependence
        })
        .min()
        .expect("a round");
    let route = fastest(|| {
        let at = Instant::now();
        let _ = shape_lex_basis(&algebra).expect("in shape position");
        at.elapsed()
    });

    // **End to end**, which is what a caller pays: both from the same source basis, both including
    // the quotient algebra, which neither route can do without.
    let classical = fastest(|| {
        let at = Instant::now();
        let _ = fglm_to_lex(&source, SOURCE).expect("convertible");
        at.elapsed()
    });
    let shape_all = fastest(|| {
        let at = Instant::now();
        let built = algebra_of(&source);
        let _ = shape_lex_basis(&built).expect("in shape position");
        at.elapsed()
    });

    // The span at full rank, plus the block each route carries beside it: every accepted vector for
    // the classical walk, and one Krylov vector for the shape route.
    let span = IncrementalSpan::<F>::cells_at_full_rank(d).expect("representable");
    let classical_cells = span + d * d;
    let shape_cells = span + d;

    println!(
        "| {:<11} | {:>5} | {:>10.3} | {:>10.3} | {:>7.2}x | {:>10.2} | {:>10.2} | {:>7.2}x | {:>10} | {:>11} | {:>7.2}x |",
        name,
        d,
        millis(walk),
        millis(route),
        millis(walk) / millis(route).max(f64::MIN_POSITIVE),
        millis(classical),
        millis(shape_all),
        millis(classical) / millis(shape_all).max(f64::MIN_POSITIVE),
        classical_cells,
        shape_cells,
        classical_cells as f64 / shape_cells as f64,
    );
    std::io::stdout().flush().expect("stdout");
}

fn planted_point<const N: usize>() -> Vec<F> {
    (0..N).map(|i| F::new(2 * i as u64 + 3)).collect()
}

/// Every system the example reports on, applied to a function generic in `N`.
macro_rules! corpus {
    ($f:ident, $wanted:expr) => {{
        if $wanted("katsura-3") {
            $f("katsura-3", &katsura::<3, F>());
        }
        if $wanted("katsura-4") {
            $f("katsura-4", &katsura::<4, F>());
        }
        if $wanted("katsura-5") {
            $f("katsura-5", &katsura::<5, F>());
        }
        if $wanted("katsura-6") {
            $f("katsura-6", &katsura::<6, F>());
        }
        if $wanted("katsura-7") {
            $f("katsura-7", &katsura::<7, F>());
        }
        if $wanted("cyclic-3") {
            $f("cyclic-3", &cyclic::<3, F>());
        }
        if $wanted("cyclic-5") {
            $f("cyclic-5", &cyclic::<5, F>());
        }
        if $wanted("cyclic-6") {
            $f("cyclic-6", &cyclic::<6, F>());
        }
        if $wanted("planted-4") {
            $f("planted-4", &planted::<4, F>(&planted_point::<4>()));
        }
        if $wanted("planted-6") {
            $f("planted-6", &planted::<6, F>(&planted_point::<6>()));
        }
        if $wanted("planted-8") {
            $f("planted-8", &planted::<8, F>(&planted_point::<8>()));
        }
    }};
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let wanted = |name: &str| args.is_empty() || args.iter().any(|a| a == name);

    println!("# Shape position over the benchmark corpus, GF(2^31 - 1), grevlex source");
    println!();
    position_header();
    corpus!(position_row, wanted);
    println!();
    println!("`deg of x_N-1` is the degree of the last variable's minimal polynomial in R/I. It");
    println!(
        "equals `D` exactly when that variable generates the algebra, which is what the shape"
    );
    println!(
        "*lex* basis needs — lex eliminates the earlier variables, so `x_i - h_i(t)` is a lex"
    );
    println!("basis element only for `t` last. `separating variables` lists every variable that");
    println!("generates the algebra, which is a different and larger question.");

    println!();
    println!("# Cost of the shape route against classical FGLM, fastest of three");
    println!();
    cost_header();
    corpus!(cost_row, wanted);
    println!();
    println!("Systems not in shape position are absent rather than dashed.");
    println!();
    println!("`lex walk` and `shape` both start from a prepared quotient algebra, so `route won`");
    println!("is the two conversion routes against each other with the shared operators excluded.");
    println!("`classical` and `shape all` are **end to end** from the source basis and both");
    println!("include building those operators, which neither route can do without — so `end won`");
    println!("is what a caller would see, and it is the number to quote.");
    println!();
    println!(
        "`cells` is the dense field-element blocks each route needs at full rank: the echelon"
    );
    println!(
        "form's `D^2 + D(D+1)/2` for both, plus `D^2` accepted vectors for the classical walk"
    );
    println!("against one `D`-vector for the shape route. That block is what the shape route does");
    println!("not need, and it is the whole of the difference.");
}
