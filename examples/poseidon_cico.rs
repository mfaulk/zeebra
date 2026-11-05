//! Reduced-round Poseidon CICO: generate the system, solve it, verify through the permutation.
//!
//! M21-B. The parameters are the 2026 initiative's own — KoalaBear, `alpha = 3`, the Grain LFSR
//! constants, the Cauchy MDS — ported from `poseidon-tools` at commit
//! `60075da7c0521d9493749a035b1f30d4eda37138`. What is reduced is the state width and the round
//! counts, and **both reductions are printed with every result**, because a CICO result that did
//! not say what it reduced from would be misleading.
//!
//! The bounty instance is `t = 16`, `R_F = 6`, `R_P = 8`: **104 S-box variables** before the
//! fourteen free inputs. Nothing here is a step toward solving it, and the last table is where the
//! frontier actually is.
//!
//! ```text
//! cargo run --release --example poseidon_cico
//! ```
//! Takes about a minute, most of it the `t = 3` row failing — which is the measurement.

use std::time::{Duration, Instant};

use rand::{prelude::StdRng, SeedableRng};

use zeebra::{
    fields::PrimeFieldElement64,
    grobner::{
        analyze,
        research::{
            verify_against_trace, CicoInstance, Poseidon, PoseidonParameters, KOALABEAR_PRIME,
        },
        solve_one_planned, F4Options, PlannedSolveOptions, SolveOptions, SolveOutcome, SolvePolicy,
    },
    FiniteField, Zero,
};

/// KoalaBear, the field every 2026 initiative challenge is over.
type K = PrimeFieldElement64<KOALABEAR_PRIME>;

/// The bounty's first input constant, reused so the reduced instances share it.
const C1: u64 = 0xC0_9DE4;

fn options() -> PlannedSolveOptions {
    PlannedSolveOptions {
        policy: SolvePolicy::AutoWithFallback,
        budget: Default::default(),
        attempt: SolveOptions {
            // Column-bounded rather than time-bounded, so the failure is reproducible: F4 has no
            // cooperative time check, and "it took too long on this machine" is not a result.
            f4: F4Options {
                max_matrix_columns: 60_000,
                max_live_bytes: 400_000_000,
                ..F4Options::default()
            },
            ..SolveOptions::default()
        },
    }
}

/// One reduced instance, solved and verified.
struct Row {
    label: String,
    variables: usize,
    equations: usize,
    terms: usize,
    elapsed: Duration,
    verdict: String,
}

/// Build a planted reduced CICO instance, solve it, and verify through the permutation.
fn attempt<const N: usize>(t: usize, r_f: usize, r_p: usize) -> Row {
    let poseidon = Poseidon::<K>::new(PoseidonParameters {
        prime: KOALABEAR_PRIME,
        alpha: 3,
        t,
        r_f,
        r_p,
    })
    .expect("R_F is even");

    // One constrained word at each end. The target is *planted*: the permutation is run on a
    // chosen state and its first output word becomes the target, so a solution provably exists.
    // Without that, a CICO instance with an arbitrary target may simply have none, and "found
    // nothing" would be indistinguishable from "is broken".
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

    let system = instance.system::<N>().expect("enough variables");
    let shape = analyze(&system);

    // Faithfulness, before solving: the system vanishes at a real trace of the permutation.
    let mut state = vec![K::new(C1)];
    state.extend_from_slice(&free);
    let trace = instance
        .poseidon
        .run(&state, true)
        .expect("the right width");
    let failures = verify_against_trace(&instance, &system, &trace);
    assert!(
        failures.is_empty(),
        "the generated system does not represent the permutation: equations {:?} do not vanish \
         at a real trace",
        failures
    );

    let at = Instant::now();
    let (outcome, _plan) = solve_one_planned(&system, &mut StdRng::seed_from_u64(1), &options());
    let elapsed = at.elapsed();

    let verdict = match outcome {
        Ok(SolveOutcome::Point(point)) => {
            // The verification that matters: the recovered free input goes back through the
            // permutation, not through the polynomial system. A generator bug cannot make this
            // pass.
            let recovered: Vec<K> = point[..t - 1].to_vec();
            let verified = instance.is_solution(&recovered).expect("the right width");
            assert!(
                verified,
                "the solver's point does not satisfy the CICO condition"
            );
            if recovered == free {
                "solved; the plant itself, verified through the permutation".to_string()
            } else {
                "solved; a different preimage, verified through the permutation".to_string()
            }
        }
        Ok(other) => format!("{:?} — the plant should have been found", other),
        Err(e) => format!("inconclusive — {}", e),
    };

    Row {
        label: format!("t={} R_F={} R_P={}", t, r_f, r_p),
        variables: instance.variables(),
        equations: instance.equations(),
        terms: shape.terms,
        elapsed,
        verdict,
    }
}

fn print_row(row: &Row) {
    println!(
        "| {:<18} | {:>4} | {:>4} | {:>6} | {:>9} | {:<56} |",
        row.label,
        row.variables,
        row.equations,
        row.terms,
        format!("{:.1}", row.elapsed.as_secs_f64() * 1e3),
        truncate(&row.verdict, 56)
    );
}

fn header() {
    println!(
        "| {:<18} | {:>4} | {:>4} | {:>6} | {:>9} | {:<56} |",
        "reduced to", "vars", "eqs", "terms", "ms", "outcome"
    );
    println!(
        "|{}|{}|{}|{}|{}|{}|",
        "-".repeat(20),
        "-".repeat(6),
        "-".repeat(6),
        "-".repeat(8),
        "-".repeat(11),
        "-".repeat(58)
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
    println!("# Reduced-round Poseidon CICO over KoalaBear");
    println!();

    let bounty = PoseidonParameters::bounty_cico();
    println!("The 2026 initiative's CICO instance: {}", bounty);
    println!(
        "That is {} S-box variables plus {} free inputs — {} variables, {} equations.",
        bounty.sboxes(),
        bounty.t - 2,
        bounty.t - 2 + bounty.sboxes(),
        bounty.sboxes() + 2
    );
    println!();

    // The port reproduces the reference's published vector, which is what makes "the real
    // parameters" a checkable claim rather than an assertion.
    let reference = Poseidon::<K>::new(PoseidonParameters {
        prime: KOALABEAR_PRIME,
        alpha: 3,
        t: 16,
        r_f: 8,
        r_p: 20,
    })
    .expect("R_F is even");
    let published = reference
        .permutation(&[K::zero(); 16])
        .expect("the right width")[0];
    println!("poseidon-tools records permutation([0]*16)[0] = 1393439926 at t=16, R_F=8, R_P=20.");
    println!(
        "This port gives {}: {}",
        published,
        if published == K::new(1_393_439_926) {
            "the Grain LFSR, all 448 round constants, the Cauchy MDS and the round\n\
             schedule all agree with the reference."
        } else {
            "DISAGREES — do not trust anything below."
        }
    );
    assert_eq!(published, K::new(1_393_439_926));
    println!();

    println!("## Reduced instances, each with a planted target");
    println!();
    println!(
        "`k = 1` throughout. The target is the permutation's own output on a chosen state, so"
    );
    println!("a solution provably exists — an arbitrary target may simply have none, and then a");
    println!("solver that found nothing would be indistinguishable from one that was broken.");
    println!();
    println!("Every row asserts the generated system vanishes at a real trace *before* solving,");
    println!("and verifies any recovered input by running the permutation on it.");
    println!();
    header();

    print_row(&attempt::<5>(2, 2, 0));
    print_row(&attempt::<7>(2, 2, 2));
    print_row(&attempt::<9>(2, 4, 0));
    print_row(&attempt::<9>(3, 2, 1));

    println!();
    println!("## Where the frontier is");
    println!();
    println!("`t = 2` solves at up to nine variables. `t = 3` fails at the *same* variable count,");
    println!("because the MDS layer couples three words rather than two and every S-box equation");
    println!("is degree 3 — the matrix outgrows its column budget long before the variable count");
    println!("would suggest. **Variable count alone does not predict reach**, which is the same");
    println!("lesson the structural analysis of M21-C refuses to draw conclusions from.");
    println!();
    println!("The bounty is t = 16 with 104 S-box variables. The gap is not incremental, and no");
    println!("result here says anything about the full instance — see the `reduced_from` field,");
    println!("which every instance above carries for exactly that reason.");
    println!();
    println!("The relaxed CICO verifier the bounty also ships is **not** modelled here. Its");
    println!("condition is on the low bits of a field element's canonical integer representative,");
    println!("which is not a polynomial equation over the field; see docs/research/poseidon.md.");
}
