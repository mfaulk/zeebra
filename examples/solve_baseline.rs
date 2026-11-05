//! M21-0's baseline: both solving routes on every corpus system, with resources and outcome class.
//!
//! The measurement M21's strategy planning has to be built on. `examples/solve_one.rs` already
//! times the two routes; this one answers the questions a planner needs instead — what each route
//! *cost*, which stage stopped it when it stopped, and which of the four mathematically distinct
//! outcomes it reached.
//!
//! The pipeline is re-run here rather than read out of [`SolveStatistics`], because
//! `solve_zero_dimensional.rs`'s `lex_basis` discards the `F4Statistics` of both routes and the
//! `FglmStatistics` of the one that converts is all a caller gets. Surfacing those is M21-C; this
//! duplication is the evidence for why.
//!
//! ```text
//! cargo run --release --example solve_baseline
//! ```

use std::time::{Duration, Instant};

use rand::{prelude::StdRng, SeedableRng};

use zeebra::{
    fields::{Bn254Fr, Zp2147483647},
    grobner::{
        benchmark_systems::{cyclic, katsura, planted},
        f4_with_options,
        fglm::{classify_ideal, fglm_to_lex_with_options},
        solve_one_with_options, F4Options, FglmOptions, SolveOptions, SolveStrategy,
    },
    util::peak_resident_bytes,
    FiniteField, KnownOrder, MonomialOrder, MultivariatePolynomial,
};

type F = Zp2147483647;

fn millis(d: Duration) -> f64 {
    d.as_secs_f64() * 1e3
}

/// The mathematically distinct things a solve attempt can establish.
///
/// The distinction M21-D must not lose. Only the first two are answers; the third is a statement
/// about the ideal and the fourth is a statement about this machine.
enum Outcome {
    /// A point, verified against the original system here and not only inside the solver.
    Verified,
    /// The ideal is zero-dimensional and has no point over the base field. An answer.
    NoBaseFieldPoint,
    /// `1` is in the ideal. **Also reported as no solution today**, which is the defect: the two
    /// are different mathematical facts and `solve_one` returns `Ok(None)` for both.
    Inconsistent,
    /// Not zero-dimensional, so this route does not apply. Not a resource failure.
    PositiveDimensional,
    /// A budget was crossed. Says nothing about whether a solution exists.
    Exhausted(String),
}

impl Outcome {
    fn label(&self) -> String {
        match self {
            Self::Verified => "verified point".to_string(),
            Self::NoBaseFieldPoint => "no F-point".to_string(),
            Self::Inconsistent => "inconsistent".to_string(),
            Self::PositiveDimensional => "positive-dim".to_string(),
            Self::Exhausted(why) => why.clone(),
        }
    }
}

/// One route's cost and outcome on one system.
struct Row {
    route: &'static str,
    /// Gröbner basis: `Ok((ms, rows, columns, peak entries, peak bytes, worst fill-in))`.
    grobner: Result<(f64, usize, usize, usize, usize, f64), String>,
    /// Conversion: `None` for the direct route, else `Ok((D, estimated bytes))`.
    conversion: Option<Result<(usize, usize), String>>,
    solve_ms: f64,
    outcome: Outcome,
}

/// Run one route over one system, measuring the Gröbner stage and the conversion separately.
fn measure<const N: usize, FF: KnownOrder>(
    system: &[MultivariatePolynomial<N, FF>],
    route: SolveStrategy,
    seed: u64,
) -> Row {
    let f4 = F4Options::default();
    let fglm = FglmOptions::default();
    let order = match route {
        SolveStrategy::DirectLexF4 => MonomialOrder::Lexicographic,
        SolveStrategy::GrevlexF4ThenFglm => MonomialOrder::GradedReverseLexicographic,
    };

    let at = Instant::now();
    let basis = f4_with_options(system, order, &f4);
    let grobner_ms = millis(at.elapsed());

    let (grobner, conversion) = match &basis {
        Err(e) => (Err(e.to_string()), None),
        Ok((_, s)) => {
            let measured = Ok((
                grobner_ms,
                s.max_matrix_rows,
                s.max_matrix_columns,
                s.max_live_nonzeros,
                s.peak_live_bytes(),
                s.worst_fill_in(),
            ));
            let converted = match route {
                SolveStrategy::DirectLexF4 => None,
                SolveStrategy::GrevlexF4ThenFglm => {
                    let source = &basis.as_ref().expect("checked above").0;
                    // Classified first, so a positive-dimensional ideal is reported as one rather
                    // than as whatever the conversion would have said about it.
                    if classify_ideal(source, order).is_finite_dimensional() {
                        Some(
                            fglm_to_lex_with_options(source, order, &fglm)
                                .map(|(_, c)| (c.quotient_dimension, c.estimated_bytes()))
                                .map_err(|e| e.to_string()),
                        )
                    } else {
                        None
                    }
                }
            };
            (measured, converted)
        }
    };

    // The solve itself, for the outcome class and the end-to-end clock. Re-runs the stages above,
    // which is the cost of their diagnostics not being reachable through the solver.
    let options = SolveOptions {
        strategy: route,
        ..SolveOptions::default()
    };
    let mut rng = StdRng::seed_from_u64(seed);
    let at = Instant::now();
    let solved = solve_one_with_options(system, &mut rng, &options);
    let solve_ms = millis(at.elapsed());

    let outcome = match solved {
        Ok((Some(point), _)) => {
            for p in system {
                assert!(p.eval(&point).is_zero(), "the point does not satisfy {}", p);
            }
            Outcome::Verified
        }
        // The solver cannot tell these apart, so the harness asks the basis directly. Exactly the
        // conflation M21-D's §9.4 forbids, present today.
        Ok((None, _)) => match basis.as_ref() {
            Ok((b, _)) if b.iter().any(|p| p.is_constant() && !p.is_zero()) => {
                Outcome::Inconsistent
            }
            _ => Outcome::NoBaseFieldPoint,
        },
        Err(zeebra::grobner::SolveError::PositiveDimensional) => Outcome::PositiveDimensional,
        Err(e) => Outcome::Exhausted(e.to_string()),
    };

    Row {
        route: match route {
            SolveStrategy::DirectLexF4 => "direct",
            SolveStrategy::GrevlexF4ThenFglm => "fglm",
        },
        grobner,
        conversion,
        solve_ms,
        outcome,
    }
}

fn print_row(name: &str, row: &Row) {
    let (gb, shape, entries, bytes, fill) = match &row.grobner {
        Ok((ms, rows, columns, nz, by, fill)) => (
            format!("{:.1}", ms),
            format!("{}x{}", rows, columns),
            format!("{}", nz),
            format!("{:.1}", *by as f64 / 1e6),
            format!("{:.2}", fill),
        ),
        Err(_) => ("—".into(), "—".into(), "—".into(), "—".into(), "—".into()),
    };
    let conversion = match &row.conversion {
        None => "—".to_string(),
        Some(Ok((d, bytes))) => format!("D={} {:.1} MB", d, *bytes as f64 / 1e6),
        Some(Err(e)) => truncate(e, 22),
    };
    println!(
        "| {:<11} | {:<6} | {:>8} | {:>11} | {:>9} | {:>7} | {:>5} | {:<22} | {:>8} | {:<42} |",
        name,
        row.route,
        gb,
        shape,
        entries,
        bytes,
        fill,
        conversion,
        format!("{:.1}", row.solve_ms),
        truncate(&row.outcome.label(), 42),
    );
}

fn truncate(s: &str, width: usize) -> String {
    if s.chars().count() <= width {
        s.to_string()
    } else {
        format!("{}…", s.chars().take(width - 1).collect::<String>())
    }
}

fn report<const N: usize, FF: KnownOrder>(
    name: &str,
    system: &[MultivariatePolynomial<N, FF>],
    seed: u64,
) {
    for route in [SolveStrategy::DirectLexF4, SolveStrategy::GrevlexF4ThenFglm] {
        print_row(name, &measure(system, route, seed));
    }
}

fn header() {
    println!(
        "| {:<11} | {:<6} | {:>8} | {:>11} | {:>9} | {:>7} | {:>5} | {:<22} | {:>8} | {:<42} |",
        "system",
        "route",
        "f4 ms",
        "max matrix",
        "peak nz",
        "peak MB",
        "fill",
        "conversion",
        "solve ms",
        "outcome"
    );
    println!(
        "|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|",
        "-".repeat(13),
        "-".repeat(8),
        "-".repeat(10),
        "-".repeat(13),
        "-".repeat(11),
        "-".repeat(9),
        "-".repeat(7),
        "-".repeat(24),
        "-".repeat(10),
        "-".repeat(44)
    );
}

fn point<FF: FiniteField>(n: usize) -> Vec<FF> {
    (0..n).map(|i| FF::new(2 * i as u64 + 3)).collect()
}

/// `{x^2 - c, y}` for the smallest `c` that is not a square in `FF`.
///
/// Zero-dimensional with quotient dimension two and no point over the base field. The non-square
/// is **found rather than assumed**: whether a given small integer is a square differs between
/// fields, and `x^2 + 1` — the obvious choice over GF(2^31 - 1), which is 3 mod 4 — is solvable
/// over BN254 `Fr`, which is 1 mod 4. A corpus entry that silently changes outcome class with the
/// field is worse than no entry.
fn without_a_base_field_point<FF: KnownOrder>() -> Vec<MultivariatePolynomial<2, FF>> {
    let vars = ["x", "y"];
    for c in 2u64..200 {
        let system: Vec<MultivariatePolynomial<2, FF>> =
            parse(&[&format!("x^2 - {}", c), "y"], vars);
        let mut rng = StdRng::seed_from_u64(0);
        if let Ok((None, _)) = solve_one_with_options(&system, &mut rng, &SolveOptions::default()) {
            return system;
        }
    }
    panic!("no small integer below 200 is a non-square in this field");
}

fn parse<const N: usize, FF: FiniteField>(
    strings: &[&str],
    vars: [&str; N],
) -> Vec<MultivariatePolynomial<N, FF>> {
    strings
        .iter()
        .map(|s| MultivariatePolynomial::parse(s, vars).expect("parses"))
        .collect()
}

fn main() {
    println!("# M21-0 baseline: both routes, with resources and outcome class");
    println!();
    println!("Field GF(2^31 - 1), `F4Options::default()` and `FglmOptions::default()` throughout.");
    println!();
    header();

    report("katsura-6", &katsura::<6, F>(), 1);
    report("katsura-7", &katsura::<7, F>(), 2);
    report("cyclic-5", &cyclic::<5, F>(), 3);
    report("cyclic-6", &cyclic::<6, F>(), 4);
    report("planted-8", &planted::<8, F>(&point(8)), 5);
    report("planted-10", &planted::<10, F>(&point(10)), 6);
    report("planted-12", &planted::<12, F>(&point(12)), 7);

    // The three outcomes that are not "a point". cyclic-4 is the positive-dimensional case the
    // zero-dimensional route must refuse rather than mis-answer.
    report("cyclic-4", &cyclic::<4, F>(), 8);
    report(
        "inconsistent",
        &parse::<2, F>(&["x - 1", "x - 2"], ["x", "y"]),
        9,
    );
    report("no-F-point", &without_a_base_field_point::<F>(), 10);

    println!();
    println!("## The same systems over BN254 `Fr`, where they are tractable");
    println!();
    header();
    report("katsura-5", &katsura::<5, Bn254Fr>(), 11);
    report("katsura-6", &katsura::<6, Bn254Fr>(), 12);
    report("planted-8", &planted::<8, Bn254Fr>(&point(8)), 13);
    report("no-F-point", &without_a_base_field_point::<Bn254Fr>(), 14);

    println!();
    println!("`peak nz` is live matrix entries and `peak MB` is those entries in megabytes — 16");
    println!("bytes each over GF(2^31 - 1) and 40 over BN254, which is the ratio M20-C's byte");
    println!("budget exists for. `fill` is the worst fill-in ratio over all batches.");
    println!();
    println!("`conversion` is the FGLM stage: the quotient dimension D and the operators plus");
    println!("dense blocks it estimated, or the limit it crossed. The direct route has none.");
    println!();
    println!("`solve ms` is the whole of `solve_one_with_options`, which recomputes the Gröbner");
    println!("stage — so it is not `f4 ms` plus a search, and the two columns are not additive.");
    println!();
    match peak_resident_bytes() {
        Some(bytes) => println!(
            "Process peak RSS for the whole run: {:.0} MB. A high-water mark over every row, not\n\
             attributable to any one of them, and the only figure here that is measured rather\n\
             than estimated.",
            bytes as f64 / 1e6
        ),
        None => println!("Process peak RSS unavailable on this platform."),
    }
    println!();
    println!("Outcome classes: `verified point` and `no F-point` are answers; `inconsistent` is a");
    println!("third answer that the solver does **not** distinguish from the second — both are");
    println!("`Ok(None)`, and the class above was recovered by inspecting the basis here.");
    println!("`positive-dim` says the route does not apply. Anything else is a budget, which says");
    println!("nothing about whether a solution exists.");
}
