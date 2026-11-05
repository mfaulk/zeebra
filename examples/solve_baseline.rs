//! Both solving routes on every corpus system, with resources and outcome class.
//!
//! M21-0's baseline. `examples/solve_one.rs` times the two routes; this one answers the questions
//! a planner needs instead — what each route *cost*, which stage stopped it when it stopped, and
//! which of the mathematically distinct outcomes it reached.
//!
//! Every figure comes from one call to `solve_one_with_outcome`. The first version of this example
//! had to re-run F4 and the conversion alongside the solver to get them, because `lex_basis`
//! discarded both routes' `F4Statistics`; M21-C surfaced them and this is what that bought.
//!
//! ```text
//! cargo run --release --example solve_baseline
//! ```

use std::time::{Duration, Instant};

use rand::{prelude::StdRng, SeedableRng};

use zeebra::{
    fields::{Bn254Fr, Zp2147483647},
    grobner::{
        analyze,
        benchmark_systems::{cyclic, katsura, planted},
        solve_one_reported, solve_one_with_outcome, SolveError, SolveOptions, SolveOutcome,
        SolveStrategy,
    },
    util::peak_resident_bytes,
    FiniteField, KnownOrder, MultivariatePolynomial,
};

type F = Zp2147483647;

fn millis(d: Duration) -> f64 {
    d.as_secs_f64() * 1e3
}

/// One route's cost and outcome on one system.
struct Row {
    route: &'static str,
    /// `Ok` only if the Gröbner stage completed: rows, columns, peak entries, peak bytes, fill-in.
    grobner: Option<(usize, usize, usize, usize, f64)>,
    /// The conversion's quotient dimension and estimated bytes, if it ran and completed.
    conversion: Option<(usize, usize)>,
    /// Estimated peak bytes across the stages that ran.
    estimated_bytes: usize,
    elapsed: f64,
    /// What was established, or why nothing was.
    verdict: String,
}

/// Run one route over one system and read its diagnostics off the result.
fn measure<const N: usize, FF: KnownOrder>(
    system: &[MultivariatePolynomial<N, FF>],
    route: SolveStrategy,
    seed: u64,
) -> Row {
    let options = SolveOptions::with_strategy(route);
    let mut rng = StdRng::seed_from_u64(seed);

    let at = Instant::now();
    // The *reported* entry point, so that a failed route still says what it spent — a
    // positive-dimensional refusal and a crossed span budget both sit behind a Gröbner basis that
    // really was computed, and the `—` those rows used to print made them look free.
    let (outcome, statistics) = solve_one_reported(system, &mut rng, &options);
    let elapsed = millis(at.elapsed());

    let verdict = match outcome {
        Ok(SolveOutcome::Point(point)) => {
            // Checked here as well as inside the solver: the demonstration's whole claim is that
            // the point satisfies the equations as *given*.
            for p in system {
                assert!(p.eval(&point).is_zero(), "the point does not satisfy {}", p);
            }
            "verified point".to_string()
        }
        Ok(SolveOutcome::NoBaseFieldPoint) => "no F-point".to_string(),
        Ok(SolveOutcome::Inconsistent) => "inconsistent".to_string(),
        // Not a resource failure: the route does not apply to this ideal at all.
        Err(SolveError::PositiveDimensional) => "positive-dim".to_string(),
        Err(e) => e.to_string(),
    };

    let grobner = statistics.f4.as_ref().map(|f| {
        (
            f.max_matrix_rows,
            f.max_matrix_columns,
            f.max_live_nonzeros,
            f.peak_live_bytes(),
            f.worst_fill_in(),
        )
    });
    let conversion = statistics
        .fglm
        .as_ref()
        .map(|c| (c.quotient_dimension, c.estimated_bytes()));

    Row {
        route: match route {
            SolveStrategy::DirectLexF4 => "direct",
            SolveStrategy::GrevlexF4ThenFglm => "fglm",
        },
        grobner,
        conversion,
        estimated_bytes: statistics.estimated_peak_bytes(),
        elapsed,
        verdict,
    }
}

fn truncate(s: &str, width: usize) -> String {
    if s.chars().count() <= width {
        s.to_string()
    } else {
        format!("{}…", s.chars().take(width - 1).collect::<String>())
    }
}

fn print_row(name: &str, row: &Row) {
    let (shape, entries, bytes, fill) = match row.grobner {
        Some((rows, columns, nz, by, fill)) => (
            format!("{}x{}", rows, columns),
            format!("{}", nz),
            format!("{:.1}", by as f64 / 1e6),
            format!("{:.2}", fill),
        ),
        None => ("—".into(), "—".into(), "—".into(), "—".into()),
    };
    let conversion = match row.conversion {
        Some((d, bytes)) => format!("D={} {:.1} MB", d, bytes as f64 / 1e6),
        None => "—".to_string(),
    };
    println!(
        "| {:<12} | {:<6} | {:>11} | {:>9} | {:>7} | {:>5} | {:<16} | {:>7} | {:>9} | {:<42} |",
        name,
        row.route,
        shape,
        entries,
        bytes,
        fill,
        conversion,
        format!("{:.1}", row.estimated_bytes as f64 / 1e6),
        format!("{:.1}", row.elapsed),
        truncate(&row.verdict, 42),
    );
}

fn header() {
    println!(
        "| {:<12} | {:<6} | {:>11} | {:>9} | {:>7} | {:>5} | {:<16} | {:>7} | {:>9} | {:<42} |",
        "system",
        "route",
        "max matrix",
        "peak nz",
        "peak MB",
        "fill",
        "conversion",
        "est MB",
        "solve ms",
        "outcome"
    );
    println!(
        "|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|",
        "-".repeat(14),
        "-".repeat(8),
        "-".repeat(13),
        "-".repeat(11),
        "-".repeat(9),
        "-".repeat(7),
        "-".repeat(18),
        "-".repeat(9),
        "-".repeat(11),
        "-".repeat(44)
    );
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

fn point<FF: FiniteField>(n: usize) -> Vec<FF> {
    (0..n).map(|i| FF::new(2 * i as u64 + 3)).collect()
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
        let outcome = solve_one_with_outcome(&system, &mut rng, &SolveOptions::default());
        if matches!(outcome, Ok((SolveOutcome::NoBaseFieldPoint, _))) {
            return system;
        }
    }
    panic!("no small integer below 200 is a non-square in this field");
}

/// The structural figures, for the systems where they differ interestingly.
fn shapes() {
    println!(
        "| {:<12} | {:>4} | {:>4} | {:>5} | {:>6} | {:>5} | {:>9} | {:>7} | {:<24} |",
        "system",
        "vars",
        "gens",
        "terms",
        "degree",
        "quad",
        "pairs/all",
        "univar",
        "dimension (needs a basis)"
    );
    println!(
        "|{}|{}|{}|{}|{}|{}|{}|{}|{}|",
        "-".repeat(14),
        "-".repeat(6),
        "-".repeat(6),
        "-".repeat(7),
        "-".repeat(8),
        "-".repeat(7),
        "-".repeat(11),
        "-".repeat(9),
        "-".repeat(26)
    );

    fn row<const N: usize>(name: &str, system: &[MultivariatePolynomial<N, F>], dimension: &str) {
        let s = analyze(system);
        println!(
            "| {:<12} | {:>4} | {:>4} | {:>5} | {:>6} | {:>5} | {:>9} | {:>7} | {:<24} |",
            name,
            s.variables,
            s.generators,
            s.terms,
            s.max_degree,
            s.quadratic_generators,
            format!("{:.2}", s.interaction_density()),
            s.univariate_generators,
            dimension
        );
    }

    row("cyclic-4", &cyclic::<4, F>(), "positive — measured");
    row("katsura-4", &katsura::<4, F>(), "zero — measured");
    row("katsura-7", &katsura::<7, F>(), "zero — measured");
    row(
        "planted-12",
        &planted::<12, F>(&point(12)),
        "zero — measured",
    );
    row(
        "inconsistent",
        &parse::<2, F>(&["x - 1", "x - 2"], ["x", "y"]),
        "unit ideal",
    );
}

fn main() {
    println!("# M21-0 baseline: both routes, with resources and outcome class");
    println!();
    println!("Field GF(2^31 - 1), `SolveOptions::default()` budgets throughout.");
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
    println!("## Structural analysis, which decides none of the above");
    println!();
    shapes();
    println!();
    println!("cyclic-4 and katsura-4 agree on every column and differ in dimension. Nothing");
    println!("`analyze` reports bounds the quotient dimension or the solving degree; the last");
    println!("column needs a Gröbner basis, which is the point.");

    println!();
    println!("`peak nz` is live matrix entries and `peak MB` is those entries estimated in");
    println!("megabytes — 16 bytes each over GF(2^31 - 1) and 40 over BN254, which is the ratio");
    println!("M20-C's byte budget exists for. `fill` is the worst fill-in ratio over all batches.");
    println!("`est MB` is the larger of the Gröbner stage's and the conversion's estimates.");
    println!();
    println!("`conversion` is the FGLM stage: quotient dimension D and the operators plus dense");
    println!("blocks it estimated. The direct route has none.");
    println!();
    println!("A **failed** route still reports what it spent: katsura-7's direct attempt built a");
    println!("7320x33792 matrix and 18.1M entries before crossing its budget, and planted-12's");
    println!("conversion has a complete source basis behind it. `peak nz` is the peak of the last");
    println!("elimination that *finished*, so it is below the count named in the error.");
    println!();
    match peak_resident_bytes() {
        Some(bytes) => println!(
            "Process peak RSS for the whole run: {:.0} MB. A high-water mark over every row, not\n\
             attributable to any one of them, and the only figure here that is measured rather\n\
             than estimated. katsura-7 under lex dominates it: that row reports 290 MB of\n\
             entries against a 320 MB budget and this much resident, so a budget on the\n\
             representation is a cooperative limit and not a ceiling on the process.",
            bytes as f64 / 1e6
        ),
        None => println!("Process peak RSS unavailable on this platform."),
    }
    println!();
    println!("Outcome classes: `verified point`, `no F-point` and `inconsistent` are all answers,");
    println!("and the last two are distinguished by `SolveOutcome` — `solve_one` returns");
    println!("`Ok(None)` for both. `positive-dim` says the route does not apply. Anything else is");
    println!("a budget, which says nothing about whether a solution exists.");
}
