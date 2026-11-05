//! Seeded slices of an underdetermined system, each one an experiment with a recorded seed.
//!
//! M21-E. The system is six quadratics in nine unknowns, so it is positive-dimensional and the
//! zero-dimensional solvers refuse it outright. Fixing variables makes slices that some of them
//! can solve, and the point of the output is the bookkeeping: which variables, which values, which
//! seed, and **what each result does and does not establish**.
//!
//! The last column is the one that matters. `witness` is a statement about the original system;
//! `empty slice` and `slice inconsistent` are statements about that slice and nothing more. A
//! column of the latter is not a proof of anything, and the table says so rather than leaving it
//! to be inferred.
//!
//! ```text
//! cargo run --release --example specialize_slices
//! ```

use rand::{prelude::StdRng, SeedableRng};

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        analyze,
        research::{solve_slice, SliceOutcome, Specialization},
        solve_one, PlannedSolveOptions, SolveError, SolvePolicy,
    },
    MultivariatePolynomial, Zero,
};

type F = Zp2147483647;
const VARS: [&str; 9] = ["a", "b", "c", "d", "e", "f", "g", "h", "i"];

/// Six quadratics in nine unknowns. Underdetermined by construction.
fn system() -> Vec<MultivariatePolynomial<9, F>> {
    [
        "a*b + c*d - e - 1",
        "b*c + d*e - f - 2",
        "c*d + e*f - g - 3",
        "d*e + f*g - h - 4",
        "e*f + g*h - i - 5",
        "f*g + h*i - a - 6",
    ]
    .iter()
    .map(|s| MultivariatePolynomial::parse(s, VARS).expect("parses"))
    .collect()
}

fn main() {
    let system = system();
    let shape = analyze(&system);

    println!("# Seeded slices of an underdetermined system");
    println!();
    println!(
        "{} quadratics in {} unknowns; interaction density {:.2}.",
        shape.quadratic_generators,
        shape.variables,
        shape.interaction_density()
    );
    println!();

    // Unspecialized: out of scope. Not a budget failure — a property of the ideal.
    let mut rng = StdRng::seed_from_u64(0);
    match solve_one(&system, &mut rng) {
        Err(SolveError::PositiveDimensional) => println!(
            "Unspecialized, the system is positive-dimensional: the zero-dimensional solvers\n\
             refuse it, which is the right answer and not a failure."
        ),
        other => panic!("expected a positive-dimensional refusal, got {:?}", other),
    }
    println!();

    // Which variables to fix, and how many, is this program's decision. The ranking below is a
    // ranking and not a recommendation — every variable here is constrained by several equations,
    // so it has little to say, and the choice is made because three unknowns is a size the
    // solvers handle rather than because anything proved it was right.
    let ranked = shape.specialization_candidates();
    println!(
        "Variables ranked least-constrained first: {:?}. Occurrences: {:?}.",
        ranked, shape.occurrences
    );
    println!("**How many to fix is a choice**, not something inferred from `6 equations, 9");
    println!("unknowns`. Two choices are run below, and they behave completely differently.");
    println!();

    // Three fixed leaves six unknowns against six equations: the square case, generically
    // zero-dimensional.
    let three: Vec<usize> = ranked.iter().copied().take(3).collect();
    println!("## Fixing three, leaving six unknowns against six equations");
    println!();
    let (witnesses, dead, inconclusive) = campaign(&system, &three, 10);

    // Six fixed leaves three unknowns against six equations: over-determined, so a random slice is
    // almost surely inconsistent.
    let six: Vec<usize> = ranked.iter().copied().take(6).collect();
    println!();
    println!("## Fixing six, leaving three unknowns against six equations");
    println!();
    let (over_witnesses, over_dead, _) = campaign(&system, &six, 10);

    println!();
    println!("## What the two tables establish, and what they do not");
    println!();
    println!(
        "Three fixed: {} witnesses, {} dead, {} inconclusive. Six fixed: {} witnesses, {} dead.",
        witnesses, dead, inconclusive, over_witnesses, over_dead
    );
    println!();
    assert!(
        witnesses > 0,
        "the three-fixed campaign must produce a witness for the argument below to hold"
    );
    assert_eq!(
        over_witnesses, 0,
        "the six-fixed campaign is expected to find nothing; the text below says so"
    );
    println!("The second table is a column of dead slices, and **it proves nothing at all**. The");
    println!(
        "first table proves the system satisfiable — those witnesses are verified against the"
    );
    println!("original generators — so the deaths in the second cannot be evidence of");
    println!("unsatisfiability. They are evidence that six random coordinates over-constrain six");
    println!("equations in nine unknowns, which is a fact about the slicing and not about the");
    println!("system.");
    println!();
    println!("That is the whole reason `SliceOutcome` has three variants and a method called");
    println!("`is_evidence_about_the_original_system` that returns true for exactly one of them.");
    println!("Only exhausting all q^|S| slices would be a proof, and q here is 2^31 - 1.");
    println!();
    println!("## One slice in full, so the record is visible rather than described");
    println!();

    let options = PlannedSolveOptions::with_policy(SolvePolicy::AutoWithFallback);
    let mut rng = StdRng::seed_from_u64(SEED);
    let slice = Specialization::<9, F>::seeded(&three, 0).expect("valid indices");
    println!("  {}", slice);
    let (outcome, plan) = solve_slice(&system, &slice, &options, &mut rng);
    println!();
    println!("{}", plan);
    println!();
    match outcome {
        Ok(o) => println!("Outcome: {}", o),
        Err(e) => println!("Outcome: inconclusive about the slice — {}", e),
    }
}

/// The seed the *solver's* RNG starts from. Each slice carries its own, which is what reproduces
/// the slice; this one only makes the search deterministic.
const SEED: u64 = 20_260_104;

/// Run `slices` seeded slices fixing `free`, printing one row each.
///
/// Returns `(witnesses, dead slices, inconclusive)`.
fn campaign(
    system: &[MultivariatePolynomial<9, F>],
    free: &[usize],
    slices: usize,
) -> (usize, usize, usize) {
    println!(
        "| {:>4} | {:>6} | {:<10} | {:>9} | {:<52} |",
        "seed", "fixed", "slice D", "elapsed ms", "what this establishes"
    );
    println!(
        "|{}|{}|{}|{}|{}|",
        "-".repeat(6),
        "-".repeat(8),
        "-".repeat(12),
        "-".repeat(11),
        "-".repeat(54)
    );

    let options = PlannedSolveOptions::with_policy(SolvePolicy::AutoWithFallback);
    // The slices come from their own seeds; this stream is only the solver's.
    let mut rng = StdRng::seed_from_u64(SEED);
    let (mut witnesses, mut dead, mut inconclusive) = (0, 0, 0);

    for seed in 0..slices as u64 {
        let slice = Specialization::<9, F>::seeded(free, seed).expect("valid indices");
        let (outcome, plan) = solve_slice(system, &slice, &options, &mut rng);

        let dimension = plan
            .attempts
            .iter()
            .filter_map(|a| a.statistics.fglm.as_ref())
            .map(|c| format!("D = {}", c.quotient_dimension))
            .next()
            .unwrap_or_else(|| "—".to_string());

        let verdict = match &outcome {
            Ok(o) => {
                if o.is_evidence_about_the_original_system() {
                    witnesses += 1;
                } else {
                    dead += 1;
                }
                o.to_string()
            }
            Err(e) => {
                inconclusive += 1;
                format!("inconclusive about the slice — {}", e)
            }
        };

        println!(
            "| {:>4} | {:>6} | {:<10} | {:>9} | {:<52} |",
            seed,
            slice.len(),
            dimension,
            format!("{:.1}", plan.total_elapsed().as_secs_f64() * 1e3),
            truncate(&verdict, 52),
        );

        // A witness is checked here too, against the original generators. The library already
        // asserts it; a demonstration that claims a witness should show its own working.
        if let Ok(SliceOutcome::Witness(point)) = outcome {
            for p in system {
                assert!(p.eval(&point).is_zero(), "{} is not satisfied", p);
            }
            for (index, value) in slice.fixed() {
                assert_eq!(point[*index], *value, "the slice's own assignment was lost");
            }
        }
    }

    (witnesses, dead, inconclusive)
}

fn truncate(s: &str, width: usize) -> String {
    if s.chars().count() <= width {
        s.to_string()
    } else {
        format!("{}…", s.chars().take(width - 1).collect::<String>())
    }
}
