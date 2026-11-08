//! Where F4's work goes, degree by degree, on the systems M22 is about.
//!
//! M22-0. The whole-run counters in `F4Statistics` say a computation was expensive; they cannot say
//! at which degree the matrices became unaffordable, nor how much of the work at that degree
//! carried new algebraic information. This prints both, for one Fukuoka MQ instance and for the
//! controlled Poseidon family, and it is the baseline every later M22 workstream is measured
//! against.
//!
//! ```text
//! tools/fetch-mq-challenge.sh         # for the MQ sections; the rest runs without it
//! cargo run --release --example f4_degrees
//! ```
//!
//! Set `ZEEBRA_MQ_DIR` to read the instances from elsewhere. Every table states its exact
//! configuration, because a degree profile taken under different options is a different
//! measurement.
//!
//! # What the columns mean
//!
//! `pairs` is pairs taken off the queue at that degree and `cut` those a selection-time criterion
//! discarded. `rows` splits into reducer scaffolding and pair halves. **`rank+` is the rank the
//! pair rows added on top of the reducer block** — the useful-work column — and `dep` the pair rows
//! that added nothing. `new` is basis elements extracted, `<d` how many of those have degree below
//! the degree they were found at.

use std::{path::PathBuf, time::Instant};

use zeebra::{
    fields::PrimeFieldElement64,
    grobner::{
        benchmark_systems::katsura,
        classify_ideal,
        f4::f4_reported,
        research::{
            CicoInstance, MqInstance, Poseidon, PoseidonParameters, Specialization, KOALABEAR_PRIME,
        },
        DegreeProfile, F4Options, F4Statistics, IdealClass,
    },
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

/// GF(31), the Fukuoka type III and VI coefficient field.
type Q = PrimeFieldElement64<31>;

/// KoalaBear, the field the 2026 Poseidon initiative's challenges are over.
type K = PrimeFieldElement64<KOALABEAR_PRIME>;

/// The bounty's first input constant, reused so the reduced instances share it.
const C1: u64 = 0xC0_9DE4;

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

fn directory() -> PathBuf {
    std::env::var("ZEEBRA_MQ_DIR")
        .unwrap_or_else(|_| "research/instances/mq".to_string())
        .into()
}

/// Read an instance, or `None` if the data is not present.
fn load(stem: &str) -> Option<MqInstance> {
    let text = std::fs::read_to_string(directory().join(stem)).ok()?;
    MqInstance::parse(&text).ok()
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

/// A planted reduced CICO instance at the given parameters.
fn cico(t: usize, r_f: usize, r_p: usize) -> (CicoInstance<K>, Vec<K>) {
    let poseidon = Poseidon::<K>::new(PoseidonParameters {
        prime: KOALABEAR_PRIME,
        alpha: 3,
        t,
        r_f,
        r_p,
    })
    .expect("R_F is even");
    let free: Vec<K> = (0..t - 1).map(|i| K::new(1_000 + i as u64)).collect();
    let instance = CicoInstance::planted(
        poseidon,
        1,
        &[K::new(C1)],
        &free,
        Some(PoseidonParameters::bounty_cico()),
    )
    .expect("the right widths");
    assert!(
        instance.is_solution(&free).expect("the right width"),
        "the plant does not solve its own instance"
    );
    (instance, free)
}

/// The `t = 3` system, and the same system with one free input fixed to its planted value.
///
/// §5.5 of the plan: the two nine-variable Poseidon benchmarks M21 measured **do not have the same
/// algebraic dimension**, so comparing them as though the difference were state width alone would
/// be wrong. `N - E = t - 2k`, which is 1 at `t = 3, k = 1` and 0 at `t = 2, k = 1`.
fn controlled_poseidon() -> Vec<Run> {
    let order = MonomialOrder::GradedReverseLexicographic;
    let mut runs = Vec::new();

    // t = 3, R_F = 2, R_P = 1: 9 variables, 8 equations. Planted, so consistent, and with one more
    // variable than equations — positive-dimensional unless something unexpected happens.
    let (instance, free) = cico(3, 2, 1);
    let system = instance.system::<9>().expect("nine variables");
    runs.push(run("t=3 R_F=2 R_P=1, as generated", &system, order));

    // The same system with free input 0 fixed to the planted value. `Specialization::apply`
    // substitutes *and* appends the pinning equation, so the fixed coordinate is part of the answer
    // rather than a free one that happens not to appear. Nine variables still, nine equations now.
    //
    // Fixing one variable does **not** prove the result zero-dimensional, which is why the run
    // reports `classify_ideal` of the basis it computed rather than asserting a dimension here.
    let fixed = Specialization::<9, K>::new(&[(0, free[0])]).expect("one assignment");
    let sliced = fixed.apply(&system);
    runs.push(run(
        "t=3 R_F=2 R_P=1, free input 0 pinned to its planted value",
        &sliced,
        order,
    ));

    // t = 2, R_F = 4: nine variables, nine equations — the square instance M21 solved in 401 ms.
    let (instance, _) = cico(2, 4, 0);
    let system = instance.system::<9>().expect("nine variables");
    runs.push(run("t=2 R_F=4 R_P=0", &system, order));

    runs
}

/// Round count varying with the state width held fixed at `t = 2`.
fn poseidon_rounds() -> Vec<Run> {
    let order = MonomialOrder::GradedReverseLexicographic;
    let mut runs = Vec::new();

    let (instance, _) = cico(2, 2, 0);
    runs.push(run(
        "t=2 R_F=2 R_P=0",
        &instance.system::<5>().expect("five variables"),
        order,
    ));

    let (instance, _) = cico(2, 2, 2);
    runs.push(run(
        "t=2 R_F=2 R_P=2",
        &instance.system::<7>().expect("seven variables"),
        order,
    ));

    let (instance, _) = cico(2, 4, 0);
    runs.push(run(
        "t=2 R_F=4 R_P=0",
        &instance.system::<9>().expect("nine variables"),
        order,
    ));

    runs
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

/// The Fukuoka sections, or a note that the data is absent.
fn fukuoka() {
    let order = MonomialOrder::GradedReverseLexicographic;

    println!("## Fukuoka MQ Challenge, type III over GF(31)");
    println!();
    let Some(instance) = load("ToyExample-type3-n10-seed0") else {
        println!(
            "`{}` is not present. Run `tools/fetch-mq-challenge.sh` to fetch the toy examples; \
             they are not redistributed here.",
            directory().join("ToyExample-type3-n10-seed0").display()
        );
        println!();
        return;
    };
    println!(
        "{} — overdetermined, `m = 2n`, so the encryption family.",
        instance
    );
    println!();
    let system = instance
        .system::<10, Q>()
        .expect("ten variables over GF(31)");
    summarize(&run("type III n=10 seed 0", &system, order));

    // n = 15 next. It may not finish under the column budget, which is itself the measurement the
    // plan asks for: the first infeasible instance of the family, with the limiting stage named.
    println!("### The next size up");
    println!();
    match load("ToyExample-type3-n15-seed0") {
        Some(instance) => {
            let system = instance.system::<15, Q>().expect("fifteen variables");
            summarize(&run("type III n=15 seed 0", &system, order));
        }
        None => println!("`ToyExample-type3-n15-seed0` is not present.\n"),
    }

    // Type VI is the signature family: n ~ 1.5m, so underdetermined and positive-dimensional as
    // published. Any specialization is recorded explicitly, because a specialized type VI instance
    // is a different mathematical problem from the one the challenge poses.
    println!("## Fukuoka MQ Challenge, type VI over GF(31) — underdetermined");
    println!();
    match load("ToyExample-type6-n10-seed0") {
        Some(instance) => {
            println!(
                "{} — `n - m = {}`, so positive-dimensional as published.",
                instance,
                instance.variables - instance.polynomials
            );
            println!();
            let system = instance.system::<10, Q>().expect("ten variables");
            summarize(&run("type VI n=10 seed 0, as published", &system, order));

            // Specialize n - m variables at seed 1 to reach a square system. The slice is a
            // different problem, and it is labelled as one.
            let count = instance.variables - instance.polynomials;
            let specialization =
                Specialization::<10, Q>::seeded(&(0..count).collect::<Vec<_>>(), 1)
                    .expect("distinct indices");
            let sliced = specialization.apply(&system);
            summarize(&run(
                &format!("type VI n=10 seed 0, specialized: {}", specialization),
                &sliced,
                order,
            ));
        }
        None => println!("`ToyExample-type6-n10-seed0` is not present.\n"),
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
         set, `max_matrix_columns = {}`, {}. Order: grevlex throughout \
         except where stated. Reproduce with `cargo run --release --example f4_degrees`.",
        options().max_matrix_columns,
        options().live_budget_policy::<Q>()
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
        &katsura::<5, PrimeFieldElement64<2_147_483_647>>(),
        MonomialOrder::GradedReverseLexicographic,
    ));

    fukuoka();

    println!("## Controlled Poseidon: dimension, not state width");
    println!();
    println!(
        "`N - E = t - 2k`, so at `k = 1` the `t = 3` instance has one more variable than equation \
         and the `t = 2` instance is square. The two nine-variable benchmarks M21 reported are \
         therefore **not the same kind of system**, and the middle row below is the one that makes \
         the comparison controlled: it is the `t = 3` system with a single free input pinned, so \
         the equation count matches while the round structure does not change."
    );
    println!();
    let controlled = controlled_poseidon();
    comparison_header();
    for row in &controlled {
        comparison_row(row);
    }
    println!();
    for row in &controlled {
        summarize(row);
    }

    println!("## Round count at fixed state width");
    println!();
    println!(
        "`t = 2` throughout, so every row is square and the only thing varying is how many rounds \
         the permutation has — and therefore how many S-box variables."
    );
    println!();
    let rounds = poseidon_rounds();
    comparison_header();
    for row in &rounds {
        comparison_row(row);
    }
    println!();
    for row in &rounds {
        summarize(row);
    }
}
