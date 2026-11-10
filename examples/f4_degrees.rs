//! Where F4's work goes, degree by degree.
//!
//! The whole-run counters in `F4Statistics` say a computation was expensive; they cannot say at
//! which degree the matrices became unaffordable, nor how much of the work at that degree carried
//! new algebraic information. This prints both, for Katsura, Cyclic and a planted quadratic system.
//!
//! ```text
//! cargo run --release --example f4_degrees
//! ```
//!
//! Every table states its exact configuration, because a degree profile taken under different
//! options is a different measurement.
//!
//! # What the columns mean
//!
//! `pairs` is pairs taken off the queue at that degree and `cut` those a selection-time criterion
//! discarded. `rows` splits into reducer scaffolding and pair halves. **`rank+` is the rank the
//! pair rows added on top of the reducer block** — the useful-work column — and `dep` the pair rows
//! that added nothing. `new` is basis elements extracted, `<d` how many of those have degree below
//! the degree they were found at.

use std::time::Instant;

use zeebra::{
    fields::PrimeFieldElement64,
    grobner::{
        benchmark_systems::{cyclic, katsura, planted},
        classify_ideal,
        f4::f4_reported,
        DegreeProfile, F4Options, F4Statistics, IdealClass,
    },
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

type P = PrimeFieldElement64<2_147_483_647>;

/// The one configuration every table in this program uses.
///
/// `recommended()` plus degree profiling, so the numbers describe what F4 does by default rather
/// than what a research mode does. The column budget is explicit so that a failure is reproducible:
/// F4 has no cooperative time check, and "it took too long on this machine" is not a result.
fn options() -> F4Options {
    F4Options {
        profile_degrees: true,
        measure_stages: true,
        max_matrix_columns: 60_000,
        max_live_bytes: 400_000_000,
        ..F4Options::default()
    }
}

/// What one run of F4 established, whether or not it finished.
struct Run {
    label: String,
    variables: usize,
    equations: usize,
    statistics: F4Statistics,
    outcome: String,
    basis: Option<usize>,
    dimension: Option<IdealClass>,
}

/// Run F4 under [`options`], keeping the degree profile whether it finished or not.
fn run<const N: usize, F: FiniteField>(
    label: &str,
    system: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
) -> Run {
    let at = Instant::now();
    let (result, statistics) = f4_reported(system, order, &options());
    let elapsed = at.elapsed();

    let (outcome, basis, dimension) = match &result {
        Ok(basis) => (
            format!("complete in {:.1} ms", elapsed.as_secs_f64() * 1e3),
            Some(basis.len()),
            Some(classify_ideal(basis, order)),
        ),
        // The limiting stage, named. This is what M21's `f4_reported` is for: the counters below
        // describe real completed work even though there is no basis.
        Err(e) => (
            format!("{} after {:.1} ms", e, elapsed.as_secs_f64() * 1e3),
            None,
            None,
        ),
    };

    Run {
        label: label.to_string(),
        variables: N,
        equations: system.len(),
        statistics,
        outcome,
        basis,
        dimension,
    }
}

fn degree_table(profile: &DegreeProfile) {
    println!(
        "| {:>3} | {:>5} | {:>4} | {:>6} | {:>6} | {:>6} | {:>5} | {:>5} | {:>7} | {:>3} | {:>3} | {:>9} |",
        "deg", "pairs", "cut", "batch", "reduce", "pair", "rank+", "dep", "cols", "new", "<d", "peak MB"
    );
    println!(
        "|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|",
        "-".repeat(5),
        "-".repeat(7),
        "-".repeat(6),
        "-".repeat(8),
        "-".repeat(8),
        "-".repeat(8),
        "-".repeat(7),
        "-".repeat(7),
        "-".repeat(9),
        "-".repeat(5),
        "-".repeat(5),
        "-".repeat(11),
    );
    for degree in profile.iter() {
        println!(
            "| {:>3} | {:>5} | {:>4} | {:>6} | {:>6} | {:>6} | {:>5} | {:>5} | {:>7} | {:>3} | {:>3} | {:>9} |",
            degree.degree,
            degree.pairs_considered,
            degree.pairs_rejected_by_criteria,
            degree.batches,
            degree.reducer_rows,
            degree.candidate_rows,
            degree.candidate_rank_contribution,
            degree.dependent_candidate_rows,
            degree.max_matrix_columns,
            degree.new_basis_elements,
            degree.new_elements_below_degree,
            format!("{:.1}", degree.peak_estimated_bytes as f64 / 1e6),
        );
    }
}

fn summarize(run: &Run) {
    let s = &run.statistics;
    println!(
        "**{}** — {} variables, {} equations.",
        run.label, run.variables, run.equations
    );
    println!();
    println!("- outcome: {}", run.outcome);
    if let Some(elements) = run.basis {
        println!(
            "- basis: {} elements; the ideal is {}",
            elements,
            match run.dimension {
                Some(IdealClass::ZeroDimensional) => "zero-dimensional",
                Some(IdealClass::PositiveDimensional) => "positive-dimensional",
                Some(IdealClass::Unit) => "the whole ring — the system is inconsistent",
                None => "of undetermined dimension",
            }
        );
    }
    println!(
        "- degrees reached: {}, highest selection degree {}, highest matrix monomial degree {}",
        s.degrees.len(),
        s.max_pair_degree,
        s.max_monomial_degree
    );
    if let Some((degree, peak)) = s.degrees.peak_degree() {
        println!(
            "- largest matrices at **degree {}**: {} live entries ({:.1} MB)",
            degree,
            peak,
            (peak * s.bytes_per_entry) as f64 / 1e6
        );
    }
    println!(
        "- pair rows that added no rank: **{:.1}%** ({} of {})",
        100.0 * s.dependent_row_fraction(),
        s.dependent_candidate_rows,
        s.dependent_candidate_rows + s.candidate_rank_contribution
    );
    println!(
        "- reducer scaffolding: {:.1}% of rows",
        100.0 * s.reducer_row_fraction()
    );
    println!(
        "- mutants: {} elements over {} of {} batches, largest degree gap {}",
        s.mutant_elements, s.batches_with_mutants, s.batches, s.max_mutant_degree_gap
    );
    println!(
        "- degree regressions: {} ({} right after a batch with a mutant), largest drop {}",
        s.degree_regressions, s.regressions_after_mutants, s.max_degree_drop
    );
    println!();
    degree_table(&s.degrees);
    println!();
}

/// Generic systems of increasing size, all over GF(2^31 - 1) under grevlex.
fn generic_systems() -> Vec<Run> {
    let order = MonomialOrder::GradedReverseLexicographic;
    let point: Vec<P> = (0..8).map(|i| P::new(3 + 2 * i)).collect();
    vec![
        run("katsura-6", &katsura::<6, P>(), order),
        run("cyclic-5", &cyclic::<5, P>(), order),
        run("cyclic-6", &cyclic::<6, P>(), order),
        run("planted-8", &planted::<8, P>(&point), order),
    ]
}

fn comparison_row(run: &Run) {
    let s = &run.statistics;
    println!(
        "| {:<54} | {:>4} | {:>3} | {:>3} | {:>4} | {:>8} | {:>6} | {:<34} |",
        truncate(&run.label, 54),
        run.variables,
        run.equations,
        s.max_pair_degree,
        s.max_monomial_degree,
        s.max_matrix_columns,
        format!("{:.0}", s.max_estimated_bytes as f64 / 1e6),
        truncate(&run.outcome, 34),
    );
}

fn comparison_header() {
    println!(
        "| {:<54} | {:>4} | {:>3} | {:>3} | {:>4} | {:>8} | {:>6} | {:<34} |",
        "instance", "vars", "eqs", "deg", "mono", "cols", "MB", "outcome"
    );
    println!(
        "|{}|{}|{}|{}|{}|{}|{}|{}|",
        "-".repeat(56),
        "-".repeat(6),
        "-".repeat(5),
        "-".repeat(5),
        "-".repeat(6),
        "-".repeat(10),
        "-".repeat(8),
        "-".repeat(36),
    );
}

fn truncate(s: &str, width: usize) -> String {
    if s.chars().count() <= width {
        s.to_string()
    } else {
        format!("{}…", s.chars().take(width - 1).collect::<String>())
    }
}

fn main() {
    println!("# F4 degree by degree");
    println!();
    // The live budget is reported as the one that *binds*, not as whichever of the pair is
    // assigned: the effective limit is the `min` of the two (#322), and this program sets
    // `max_live_bytes` to 400 MB while leaving `max_live_nonzeros` at its default, so over the
    // 16-byte entry every row here uses the cap is 320 MB and the 400 MB never applies (#469).
    println!(
        "Configuration: `F4Options::recommended()` with `profile_degrees` and `measure_stages` \
         set, `max_matrix_columns = {}`, {}. Order: grevlex throughout. \
         Reproduce with `cargo run --release --example f4_degrees`.",
        options().max_matrix_columns,
        options().live_budget_policy::<P>()
    );
    println!();
    println!(
        "The rank attribution is exact: reducer rows have distinct leading monomials and so span a \
         space of dimension exactly `reducer_rows`, which makes `rank - reducer_rows` the rank the \
         pair rows contributed. It does not depend on the order elimination took the rows in."
    );
    println!();

    // A classical system first, so the table can be read against something whose behaviour is
    // already documented.
    println!("## katsura-5 over GF(2^31 - 1), for calibration");
    println!();
    summarize(&run(
        "katsura-5",
        &katsura::<5, P>(),
        MonomialOrder::GradedReverseLexicographic,
    ));

    println!("## Generic systems");
    println!();
    let generic = generic_systems();
    comparison_header();
    for row in &generic {
        comparison_row(row);
    }
    println!();
    for row in &generic {
        summarize(row);
    }
}
