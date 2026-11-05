//! Controlled experiments on the systems M22 is about, with every transformation inverted.
//!
//! M22-E. Four questions, each with its own table:
//!
//! 1. **The Poseidon ladder**, with algebraic dimension recorded separately from state width —
//!    `N - E = t - 2k`, so two instances with the same variable count need not be the same kind of
//!    system, and M21's nine-variable frontier turns out to be about dimension rather than `t`.
//! 2. **Variable order**, as verified bijective permutations of identical mathematical systems,
//!    with every recovered witness mapped back and re-verified.
//! 3. **Affine preprocessing**: a CICO instance's `k` output constraints determine `k` variables,
//!    and projecting them out of the ring is what shrinks the matrices — substituting alone does
//!    not, because the variable keeps its column.
//! 4. **Fukuoka MQ**, with the published and specialized type VI instances kept apart.
//!
//! Every recovered Poseidon witness is verified by **running the permutation**, not by evaluating
//! the polynomial system, so no bug in the generator or in any transformation here can make a
//! verification pass. Every recovered Fukuoka witness is evaluated against the published
//! coefficient vectors.
//!
//! ```text
//! tools/fetch-mq-challenge.sh                       # for section 4
//! cargo run --release --example cryptanalysis_ladder
//! ```

use std::{path::PathBuf, time::Instant};

use rand::{prelude::StdRng, SeedableRng};

use zeebra::{
    fields::PrimeFieldElement64,
    grobner::{
        classify_ideal, f4_reported,
        research::{
            eliminate_affine, satisfies, CicoInstance, MqInstance, Poseidon, PoseidonParameters,
            RoundLayout, Specialization, VariableOrder, KOALABEAR_PRIME,
        },
        solve_one_planned, F4Options, IdealClass, PlannedSolveOptions, SolveOptions, SolveOutcome,
        SolvePolicy,
    },
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

type Q = PrimeFieldElement64<31>;
type K = PrimeFieldElement64<KOALABEAR_PRIME>;

const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

/// The bounty's first input constant, reused so every reduced instance shares it.
const C1: u64 = 0xC0_9DE4;

/// The resource policy, stated once and applied to every row.
///
/// Column- and byte-bounded rather than time-bounded, so a failure is reproducible: F4 has no
/// cooperative time check, and "it took too long on this machine" is not a result.
fn f4_options() -> F4Options {
    F4Options {
        profile_degrees: true,
        max_matrix_columns: 60_000,
        max_live_bytes: 400_000_000,
        ..F4Options::default()
    }
}

/// `AutoWithFallback`, which is what M21-D's measurements selected.
///
/// Not a bare [`SolveOptions`]: its default strategy is `DirectLexF4`, and that route crosses both
/// the row and the column budget on the Poseidon systems here — M21 measured the same thing and
/// solved them through grevlex plus FGLM. Letting the planner choose and fall back is the
/// configuration M21's figures were taken under, so it is the one a comparison against them has to
/// use.
fn solve_options() -> PlannedSolveOptions {
    PlannedSolveOptions {
        policy: SolvePolicy::AutoWithFallback,
        budget: Default::default(),
        attempt: SolveOptions {
            f4: f4_options(),
            ..SolveOptions::default()
        },
    }
}

/// What one F4 run on one system established.
struct Measured {
    variables: usize,
    equations: usize,
    initial_degrees: Vec<u64>,
    dimension: Option<IdealClass>,

    /// Elements in the reduced basis, zero when the computation did not finish.
    basis: usize,
    max_degree: u64,
    max_columns: usize,
    peak_bytes: usize,
    millis: f64,
    outcome: String,
}

fn measure<const N: usize, F: FiniteField>(system: &[MultivariatePolynomial<N, F>]) -> Measured {
    let mut initial_degrees: Vec<u64> = system.iter().map(|p| p.degree()).collect();
    initial_degrees.sort_unstable();
    initial_degrees.dedup();

    let at = Instant::now();
    let (result, statistics) = f4_reported(system, GREVLEX, &f4_options());
    let millis = at.elapsed().as_secs_f64() * 1e3;

    let (outcome, basis, dimension) = match &result {
        Ok(basis) => (
            "complete".to_string(),
            basis.len(),
            Some(classify_ideal(basis, GREVLEX)),
        ),
        Err(e) => (e.to_string(), 0, None),
    };

    Measured {
        variables: N,
        equations: system.len(),
        initial_degrees,
        dimension,
        basis,
        max_degree: statistics.max_pair_degree,
        max_columns: statistics.max_matrix_columns,
        peak_bytes: statistics.max_estimated_bytes,
        millis,
        outcome,
    }
}

fn dimension_name(class: Option<IdealClass>) -> &'static str {
    match class {
        Some(IdealClass::ZeroDimensional) => "zero",
        Some(IdealClass::PositiveDimensional) => "positive",
        Some(IdealClass::Unit) => "unit",
        None => "undetermined",
    }
}

fn ladder_header() {
    println!(
        "| {:<30} | {:>4} | {:>3} | {:>7} | {:<12} | {:>6} | {:>3} | {:>7} | {:>7} | {:>9} | {:<28} |",
        "instance", "vars", "eqs", "planted", "fixed", "deg in", "deg", "cols", "MB", "ms", "F4 outcome"
    );
    println!(
        "|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|",
        "-".repeat(32),
        "-".repeat(6),
        "-".repeat(5),
        "-".repeat(9),
        "-".repeat(14),
        "-".repeat(8),
        "-".repeat(5),
        "-".repeat(9),
        "-".repeat(9),
        "-".repeat(11),
        "-".repeat(30),
    );
}

#[allow(clippy::too_many_arguments)]
fn ladder_row(label: &str, planted: bool, fixed: &str, measured: &Measured, verification: &str) {
    println!(
        "| {:<30} | {:>4} | {:>3} | {:>7} | {:<12} | {:>6} | {:>3} | {:>7} | {:>7} | {:>9} | {:<28} |",
        truncate(label, 30),
        measured.variables,
        measured.equations,
        if planted { "yes" } else { "no" },
        truncate(fixed, 12),
        format!("{:?}", measured.initial_degrees),
        measured.max_degree,
        measured.max_columns,
        format!("{:.1}", measured.peak_bytes as f64 / 1e6),
        format!("{:.1}", measured.millis),
        truncate(
            &format!(
                "{} ({} elts), dim {}",
                measured.outcome,
                measured.basis,
                dimension_name(measured.dimension),
            ),
            28
        ),
    );
    if !verification.is_empty() {
        VERIFICATIONS
            .lock()
            .expect("no other thread holds it")
            .push((label.to_string(), verification.to_string()));
    }
}

/// Verifications collected while a table is printed, flushed after it.
///
/// A list rather than a table column: a truncated verification is worse than none, and
/// "WITNESS REJECTED" has to be legible in full. Single-threaded, so the mutex is only there to
/// satisfy `static`.
static VERIFICATIONS: std::sync::Mutex<Vec<(String, String)>> = std::sync::Mutex::new(Vec::new());

/// Print and clear the verifications collected for the table just printed.
fn flush_verifications() {
    let mut collected = VERIFICATIONS.lock().expect("no other thread holds it");
    if collected.is_empty() {
        return;
    }
    println!();
    println!("Verification:");
    println!();
    for (label, verdict) in collected.iter() {
        println!("- **{}** — {}", label, verdict);
    }
    collected.clear();
}

fn truncate(s: &str, width: usize) -> String {
    if s.chars().count() <= width {
        s.to_string()
    } else {
        format!("{}…", s.chars().take(width - 1).collect::<String>())
    }
}

/// A planted reduced CICO instance, and the free input that solves it.
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

/// The per-round S-box variable counts of a schedule, for [`RoundLayout`].
///
/// A full round introduces `t` S-box variables and a partial round one, and the schedule is
/// `R_F/2` full rounds, then `R_P` partial, then `R_F/2` full. A single width would mis-group
/// every instance with `R_P > 0`, which is why this is a vector.
fn block_sizes(t: usize, r_f: usize, r_p: usize) -> Vec<usize> {
    let half = r_f / 2;
    let mut sizes = vec![t; half];
    sizes.extend(std::iter::repeat_n(1, r_p));
    sizes.extend(std::iter::repeat_n(t, half));
    sizes
}

/// Solve a CICO system and verify the witness **through the permutation**.
///
/// `recover` maps a solver's point back to the original variable numbering; the free inputs are
/// then the first `t - k` coordinates, and those go through `Poseidon::permutation_plus_linear`.
/// A bug anywhere between the generator and here cannot make this pass.
fn verify_cico<const N: usize>(
    instance: &CicoInstance<K>,
    system: &[MultivariatePolynomial<N, K>],
    recover: impl Fn(&[K; N]) -> [K; N],
    seed: u64,
) -> String {
    let mut rng = StdRng::seed_from_u64(seed);
    match solve_one_planned(system, &mut rng, &solve_options()).0 {
        Ok(SolveOutcome::Point(point)) => {
            let original = recover(&point);
            let free = instance.free_inputs();
            let recovered: Vec<K> = original[..free].to_vec();
            match instance.is_solution(&recovered) {
                Ok(true) => "verified via permutation".to_string(),
                Ok(false) => "WITNESS REJECTED".to_string(),
                Err(e) => format!("verification error: {}", e),
            }
        }
        Ok(other) => format!("{:?}", other),
        Err(e) => format!("solver: {}", e),
    }
}

/// §1: the ladder.
fn ladder() {
    println!("## 1. The Poseidon ladder: dimension apart from state width");
    println!();
    println!(
        "`N - E = t - 2k`. At `k = 1` the `t = 2` instances are square and the `t = 3` instance has \
         one more variable than equation, so the two nine-variable systems M21 compared are **not \
         the same kind of system**. The `deg in` column is the distinct initial generator degrees; \
         `deg` is the highest lcm degree F4 selected at; `dim` is read from `classify_ideal` of the \
         computed basis, not inferred from the counts."
    );
    println!();
    ladder_header();

    // t = 2, varying rounds. Square, so zero-dimensional is expected and checked.
    let (instance, _) = cico(2, 2, 0);
    let system = instance.system::<5>().expect("five variables");
    let measured = measure(&system);
    let verdict = verify_cico(&instance, &system, |p| *p, 1);
    ladder_row("t=2 R_F=2 R_P=0", true, "none", &measured, &verdict);

    let (instance, _) = cico(2, 2, 2);
    let system = instance.system::<7>().expect("seven variables");
    let measured = measure(&system);
    let verdict = verify_cico(&instance, &system, |p| *p, 2);
    ladder_row("t=2 R_F=2 R_P=2", true, "none", &measured, &verdict);

    let (instance, _) = cico(2, 4, 0);
    let system = instance.system::<9>().expect("nine variables");
    let measured = measure(&system);
    let verdict = verify_cico(&instance, &system, |p| *p, 3);
    ladder_row("t=2 R_F=4 R_P=0", true, "none", &measured, &verdict);

    // t = 3, unspecialized: one free coordinate, so positive-dimensional. Included because §10.1
    // asks for at least one such case, and because it is the row M21 reported as a frontier.
    let (instance, free) = cico(3, 2, 1);
    let system = instance.system::<9>().expect("nine variables");
    let measured = measure(&system);
    ladder_row(
        "t=3 R_F=2 R_P=1, as generated",
        true,
        "none",
        &measured,
        "not solved: positive-dim",
    );

    // t = 3, with the one surplus free input pinned to its planted value. Nine equations now, so
    // the equation count matches the t = 2 row without the round structure changing.
    let pinned = Specialization::<9, K>::new(&[(0, free[0])]).expect("one assignment");
    let sliced = pinned.apply(&system);
    let measured = measure(&sliced);
    let verdict = verify_cico(&instance, &sliced, |p| *p, 4);
    ladder_row(
        "t=3 R_F=2 R_P=1, input 0 pinned",
        true,
        &format!("x0={}", free[0]),
        &measured,
        &verdict,
    );

    // And at a value that is *not* the planted one, so the row does not rest on knowing the answer.
    let elsewhere = Specialization::<9, K>::new(&[(0, free[0] + K::new(1))]).expect("one");
    let elsewhere_system = elsewhere.apply(&system);
    let measured = measure(&elsewhere_system);
    let mut rng = StdRng::seed_from_u64(5);
    let verdict = match solve_one_planned(&elsewhere_system, &mut rng, &solve_options()).0 {
        Ok(SolveOutcome::Point(point)) => {
            let recovered: Vec<K> = point[..instance.free_inputs()].to_vec();
            match instance.is_solution(&recovered) {
                Ok(true) => "another preimage, verified".to_string(),
                Ok(false) => "WITNESS REJECTED".to_string(),
                Err(e) => format!("error: {}", e),
            }
        }
        Ok(other) => format!("{:?} — the slice is dead", other),
        Err(e) => format!("solver: {}", e),
    };
    ladder_row(
        "t=3 R_F=2 R_P=1, input 0 off-plant",
        false,
        &format!("x0={}", free[0] + K::new(1)),
        &measured,
        &verdict,
    );

    flush_verifications();
    println!();
    println!(
        "The last two rows are the same mathematical transformation applied at two different \
         values, and they answer different questions. The planted slice is known to contain a \
         solution; the off-plant slice is a genuine search, and a `NoBaseFieldPoint` there is a \
         correct answer about that slice and says nothing about the instance. **Comparing either \
         against an arbitrary-target CICO challenge would be comparing different distributions.**"
    );
    println!();
}

/// §2: variable order, on identical mathematical systems.
fn variable_order() {
    println!("## 2. Variable order");
    println!();
    println!(
        "Three layouts of the same system, as **verified bijective permutations** — the constructor \
         rejects anything that is not a bijection of `0..N`, and every witness is mapped back with \
         the inverse and re-verified through the permutation. A relabelling is a ring isomorphism, \
         so the quotient dimension cannot move; the basis, the matrices and the cost can."
    );
    println!();
    ladder_header();

    for (t, r_f, r_p, dimension) in [(2usize, 2usize, 2usize, 7usize), (2, 4, 0, 9)] {
        let (instance, _) = cico(t, r_f, r_p);
        let sizes = block_sizes(t, r_f, r_p);

        for layout in RoundLayout::ALL {
            // The permutation, built from the per-round block sizes rather than from one width.
            let order = match dimension {
                7 => layout
                    .order::<7>(instance.free_inputs(), &sizes)
                    .map(OrderOf::Seven),
                _ => layout
                    .order::<9>(instance.free_inputs(), &sizes)
                    .map(OrderOf::Nine),
            };
            let label = format!("t={} R_F={} R_P={} / {}", t, r_f, r_p, layout.name());
            match order {
                Err(e) => println!("| {:<30} | {} |", truncate(&label, 30), e),
                Ok(OrderOf::Seven(order)) => {
                    let system = instance.system::<7>().expect("seven variables");
                    let relabelled = order.apply(&system);
                    let measured = measure(&relabelled);
                    let verdict = verify_cico(&instance, &relabelled, |p| order.recover(p), 11);
                    ladder_row(&label, true, order.name(), &measured, &verdict);
                }
                Ok(OrderOf::Nine(order)) => {
                    let system = instance.system::<9>().expect("nine variables");
                    let relabelled = order.apply(&system);
                    let measured = measure(&relabelled);
                    let verdict = verify_cico(&instance, &relabelled, |p| order.recover(p), 12);
                    ladder_row(&label, true, order.name(), &measured, &verdict);
                }
            }
        }
    }
    flush_verifications();
    println!();
}

/// A variable order at one of the two compile-time dimensions this program uses.
///
/// `const N` is not a runtime value, so an order over seven variables and one over nine are
/// different types and cannot share a binding. Two variants rather than boxing, because the two
/// arms do different things with them anyway.
enum OrderOf {
    Seven(VariableOrder<7>),
    Nine(VariableOrder<9>),
}

/// §3: affine preprocessing.
fn affine() {
    println!("## 3. Affine preprocessing");
    println!();
    println!(
        "A CICO instance's `k` output constraints are affine, and nothing else in the system is — \
         the S-box equations are `v - s^alpha`. So `k` variables are determined and the system has \
         more variables than it needs."
    );
    println!();
    println!(
        "**Substituting is not enough.** F4 already reduces by an affine basis element; what it \
         cannot do is make the variable stop existing, so it keeps a column in every Macaulay \
         matrix and a place in the monomial order. Worse, after substitution the variable appears \
         in no generator at all, so it is *unconstrained* and the ideal becomes \
         positive-dimensional — which is why the middle row below is reported as such rather than \
         quietly solved. Projecting to the smaller ring is the step that matters."
    );
    println!();
    ladder_header();

    // t = 2, R_F = 4: nine variables, one affine output constraint, so eight survive.
    let (instance, _) = cico(2, 4, 0);
    let system = instance.system::<9>().expect("nine variables");
    let measured = measure(&system);
    let verdict = verify_cico(&instance, &system, |p| *p, 21);
    ladder_row("t=2 R_F=4, as generated", true, "none", &measured, &verdict);

    let (reduced, record) = eliminate_affine(&system);
    println!(
        "| {:<30} | eliminated x{:?}, {} variables survive |",
        "elimination record",
        record
            .steps()
            .iter()
            .map(|s| s.variable)
            .collect::<Vec<_>>(),
        record.kept().len()
    );

    let measured = measure(&reduced);
    ladder_row(
        "t=2 R_F=4, substituted only",
        true,
        "none",
        &measured,
        "unconstrained variable",
    );

    match record.project::<8>(&reduced) {
        Err(e) => println!("| {:<30} | {} |", "t=2 R_F=4, projected", e),
        Ok(projected) => {
            let measured = measure(&projected);
            // The witness comes back through `lift`, which replaces the projected coordinates and
            // then evaluates the recorded affine expression for the eliminated one — and then
            // through the permutation, as every other row.
            let mut rng = StdRng::seed_from_u64(22);
            let verdict = match solve_one_planned(&projected, &mut rng, &solve_options()).0 {
                Ok(SolveOutcome::Point(point)) => match record.lift::<8>(&point) {
                    Ok(full) => {
                        assert!(
                            satisfies(&system, &full),
                            "the lifted point does not satisfy the unprojected system"
                        );
                        let recovered: Vec<K> = full[..instance.free_inputs()].to_vec();
                        match instance.is_solution(&recovered) {
                            Ok(true) => "lifted, verified via permutation".to_string(),
                            Ok(false) => "WITNESS REJECTED".to_string(),
                            Err(e) => format!("error: {}", e),
                        }
                    }
                    Err(e) => format!("lift: {}", e),
                },
                Ok(other) => format!("{:?}", other),
                Err(e) => format!("solver: {}", e),
            };
            ladder_row(
                "t=2 R_F=4, projected to 8",
                true,
                "x8 eliminated",
                &measured,
                &verdict,
            );
        }
    }
    flush_verifications();
    println!();
}

fn mq_directory() -> PathBuf {
    std::env::var("ZEEBRA_MQ_DIR")
        .unwrap_or_else(|_| "research/instances/mq".to_string())
        .into()
}

fn load_mq(stem: &str) -> Option<(MqInstance, Vec<u64>)> {
    let text = std::fs::read_to_string(mq_directory().join(stem)).ok()?;
    let answer = std::fs::read_to_string(mq_directory().join(format!("{}-answer", stem)))
        .map(|t| MqInstance::parse_answer(&t))
        .unwrap_or_default();
    MqInstance::parse(&text).ok().map(|i| (i, answer))
}

/// §4: Fukuoka MQ, with the published and specialized type VI instances kept apart.
fn fukuoka() {
    println!("## 4. Fukuoka MQ Challenge");
    println!();
    println!(
        "Type III is the overdetermined encryption family and is the main MQ target. Type VI is the \
         signature family — `n ≈ 1.5m`, so **underdetermined and positive-dimensional as \
         published**. A specialized type VI instance is a useful benchmark and is a *different \
         problem*: it is not an overdetermined semiregular system, and nothing about HDF4's \
         justification transfers to it."
    );
    println!();
    ladder_header();

    if let Some((instance, answer)) = load_mq("ToyExample-type3-n10-seed0") {
        let system = instance.system::<10, Q>().expect("ten variables");
        let measured = measure(&system);
        let mut rng = StdRng::seed_from_u64(31);
        // Verification: the recovered point is evaluated against the *published* coefficient
        // vectors, and compared with the published answer.
        let verdict = match solve_one_planned(&system, &mut rng, &solve_options()).0 {
            Ok(SolveOutcome::Point(point)) => {
                let published: Vec<Q> = answer.iter().map(|v| Q::new(*v)).collect();
                let matches_published =
                    published.len() == 10 && (0..10).all(|i| point[i] == published[i]);
                if !satisfies(&system, &point) {
                    "WITNESS REJECTED".to_string()
                } else if matches_published {
                    "the published answer".to_string()
                } else {
                    "a witness, verified".to_string()
                }
            }
            Ok(other) => format!("{:?}", other),
            Err(e) => format!("solver: {}", e),
        };
        ladder_row("type III n=10 seed 0", false, "none", &measured, &verdict);
    } else {
        println!("| {:<30} | instance data absent |", "type III n=10 seed 0");
    }

    if let Some((instance, answer)) = load_mq("ToyExample-type6-n10-seed0") {
        let system = instance.system::<10, Q>().expect("ten variables");
        let measured = measure(&system);
        ladder_row(
            "type VI n=10, as published",
            false,
            "none",
            &measured,
            "underdetermined",
        );

        // One specialization at the published answer's own values, and one at a seeded guess. The
        // first is a planted slice and the second is a genuine search; the distinction is recorded
        // because a dead slice is a fact about the slice and not about the instance.
        let surplus = instance.variables - instance.polynomials;
        if answer.len() >= surplus {
            let assignments: Vec<(usize, Q)> =
                (0..surplus).map(|i| (i, Q::new(answer[i]))).collect();
            let at_answer = Specialization::<10, Q>::new(&assignments).expect("distinct indices");
            let sliced = at_answer.apply(&system);
            let measured = measure(&sliced);
            let mut rng = StdRng::seed_from_u64(32);
            let verdict = match solve_one_planned(&sliced, &mut rng, &solve_options()).0 {
                Ok(SolveOutcome::Point(point)) => {
                    if satisfies(&system, &point) {
                        "verified on the original".to_string()
                    } else {
                        "WITNESS REJECTED".to_string()
                    }
                }
                Ok(other) => format!("{:?}", other),
                Err(e) => format!("solver: {}", e),
            };
            ladder_row(
                "type VI n=10, sliced at answer",
                true,
                &format!("{} fixed", surplus),
                &measured,
                &verdict,
            );
        }

        let seeded = Specialization::<10, Q>::seeded(&(0..surplus).collect::<Vec<_>>(), 1)
            .expect("distinct indices");
        let sliced = seeded.apply(&system);
        let measured = measure(&sliced);
        let mut rng = StdRng::seed_from_u64(33);
        let verdict = match solve_one_planned(&sliced, &mut rng, &solve_options()).0 {
            Ok(SolveOutcome::Point(point)) => {
                if satisfies(&system, &point) {
                    "verified on the original".to_string()
                } else {
                    "WITNESS REJECTED".to_string()
                }
            }
            Ok(other) => format!("{:?} — a dead slice", other),
            Err(e) => format!("solver: {}", e),
        };
        ladder_row(
            "type VI n=10, sliced at seed 1",
            false,
            &format!("{} fixed", surplus),
            &measured,
            &verdict,
        );
    } else {
        println!("| {:<30} | instance data absent |", "type VI n=10 seed 0");
    }

    flush_verifications();
    println!();
}

fn main() {
    println!("# Controlled cryptanalytic experiments");
    println!();
    println!(
        "Configuration: `F4Options::recommended()` with `profile_degrees`, \
         `max_matrix_columns = 60_000`, `max_live_bytes = 400 MB`, grevlex throughout. Reproduce \
         with `cargo run --release --example cryptanalysis_ladder`."
    );
    println!();
    println!(
        "**No full-round claim is made anywhere below.** The 2026 initiative's CICO instance is \
         `t = 16, R_F = 6, R_P = 8` — 104 S-box variables plus fourteen free inputs — and the \
         largest row here has nine variables."
    );
    println!();

    ladder();
    variable_order();
    affine();
    fukuoka();
}
