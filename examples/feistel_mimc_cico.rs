//! Feistel-MiMC CICO: the round-count ladder, and the two formulations side by side.
//!
//! #203 (C7). The parameters are the Ethereum Foundation's 2021–2022 ZK Hash bounty instances over
//! `p = 2^64 − 59`, derived — not transcribed — from the reference implementation's own SHAKE128
//! rule, and the permutation reproduces all five of its published test vectors. See
//! `docs/research/mimc-rescue.md`.
//!
//! Two things are measured, and they are different kinds of thing. The **per-round** model is `r`
//! cubics in `r` variables, which is F4's problem. The **univariate** model is one polynomial of
//! degree `3^r` in one variable, which is root-finding's. They have the same solution set, so the
//! comparison is of cost and not of answer.
//!
//! Every row plants its target — the permutation's own trailing output word on a chosen input — so
//! a solution provably exists and "found nothing" is unambiguously a solver outcome. The stated
//! bounty objective is the target **zero**, which need not have a solution at a reduced round
//! count at all; that is reported separately and is a fact about the instance.
//!
//! ```text
//! cargo run --release --example feistel_mimc_cico
//! ```
//!
//! **No row here is a result about a specified instance.** The easiest authoritative rung is
//! `r = 22`; the withdrawn ladder that was broken started at `r = 6`.

use std::time::{Duration, Instant};

use rand::{prelude::StdRng, SeedableRng};

use zeebra::{
    fields::Zp18446744073709551557,
    grobner::{
        analyze,
        research::{
            verify_against_feistel_mimc_trace, FeistelMimc, FeistelMimcCico, FeistelMimcModel,
            FeistelMimcParameters, FEISTEL_MIMC_BOUNTY_ROUNDS, FEISTEL_MIMC_WITHDRAWN_ROUNDS,
        },
        solve_one_planned, F4Options, PlannedSolveOptions, SolveOptions, SolveOutcome, SolvePolicy,
    },
    FiniteField, One, Polynomial, Zero,
};

/// `2^64 - 59`, the bounty field.
type F = Zp18446744073709551557;

/// The input every planted row plants from, so the ladder's rungs are comparable.
const PLANT: u64 = 0x5eed_1234_5678_9abc;

fn options() -> PlannedSolveOptions {
    PlannedSolveOptions {
        policy: SolvePolicy::AutoWithFallback,
        budget: Default::default(),
        attempt: SolveOptions {
            // Column- and memory-bounded rather than time-bounded, so a failure is reproducible:
            // "it took too long on this machine" is not a result.
            f4: F4Options {
                max_matrix_columns: 60_000,
                max_live_bytes: 400_000_000,
                ..F4Options::default()
            },
            ..SolveOptions::default()
        },
    }
}

/// One rung of the per-round ladder.
struct Row {
    rounds: usize,
    variables: usize,
    equations: usize,
    terms: usize,
    elapsed: Duration,
    verdict: String,
}

/// Build the planted per-round system at `r` rounds, solve it, verify through the permutation.
fn attempt<const N: usize>(rounds: usize) -> Row {
    let mimc = FeistelMimc::<F>::new(FeistelMimcParameters::bounty(rounds)).expect("builds");
    let plant = F::new(PLANT);
    let instance = FeistelMimcCico::planted(mimc, FeistelMimcModel::PerRound, plant);
    assert!(
        instance.is_solution(plant),
        "the plant does not solve its own instance"
    );

    let system = instance.system::<N>().expect("enough variables");
    let shape = analyze(&system);

    // Faithfulness, before solving: every generator vanishes at the plant's own trace.
    let failures = verify_against_feistel_mimc_trace(&instance, &system, plant);
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
            // The verification that matters: the recovered input goes back through the
            // permutation, not through the polynomial system. A generator bug cannot make this
            // pass.
            let recovered = point[0];
            assert!(
                instance.is_solution(recovered),
                "the solver's point does not satisfy the CICO condition"
            );
            if recovered == plant {
                "solved; the plant itself, verified through the permutation".to_string()
            } else {
                "solved; another preimage, verified through the permutation".to_string()
            }
        }
        Ok(other) => format!("{:?}", other),
        Err(e) => format!("inconclusive — {}", e),
    };

    Row {
        rounds,
        variables: instance.variables(),
        equations: instance.equations(),
        terms: shape.terms,
        elapsed,
        verdict,
    }
}

/// Build the univariate at `r` rounds and root-find it, timing both halves separately.
///
/// Reported apart from the per-round ladder because the two numbers answer different questions:
/// building the degree-`3^r` polynomial is the *elimination*, and root-finding is the solve.
fn univariate_row(rounds: usize) -> (usize, Duration, Duration, usize, bool) {
    let mimc = FeistelMimc::<F>::new(FeistelMimcParameters::bounty(rounds)).expect("builds");
    let plant = F::new(PLANT);
    let instance = FeistelMimcCico::planted(mimc, FeistelMimcModel::Univariate, plant);

    let at = Instant::now();
    let polynomial = instance.univariate();
    let build = at.elapsed();
    let degree = polynomial.degree() as usize;

    let at = Instant::now();
    let found = instance.solutions();
    let solve = at.elapsed();

    for x in &found {
        assert!(
            instance.is_solution(*x),
            "a root of the univariate is not a CICO solution"
        );
    }
    (degree, build, solve, found.len(), found.contains(&plant))
}

fn header() {
    println!(
        "| {:>3} | {:>4} | {:>4} | {:>7} | {:>9} | {:<54} |",
        "r", "vars", "eqs", "terms", "ms", "outcome"
    );
    println!(
        "|{}|{}|{}|{}|{}|{}|",
        "-".repeat(5),
        "-".repeat(6),
        "-".repeat(6),
        "-".repeat(9),
        "-".repeat(11),
        "-".repeat(56)
    );
}

fn print_row(row: &Row) {
    println!(
        "| {:>3} | {:>4} | {:>4} | {:>7} | {:>9} | {:<54} |",
        row.rounds,
        row.variables,
        row.equations,
        row.terms,
        format!("{:.1}", row.elapsed.as_secs_f64() * 1e3),
        truncate(&row.verdict, 54)
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
    println!("# Feistel-MiMC CICO over p = 2^64 - 59");
    println!();
    println!(
        "The authoritative bounty ladder is r = {:?}; the withdrawn one was r = {:?}.",
        FEISTEL_MIMC_BOUNTY_ROUNDS, FEISTEL_MIMC_WITHDRAWN_ROUNDS
    );
    println!("alpha = 3, state width 2, CICO(1) on the trailing word: Perm(X, 0) = (Y, 0).");
    println!();

    // The port reproduces the reference's published vector, which is what makes "the real
    // parameters" a checkable claim rather than an assertion.
    let reference = FeistelMimc::<F>::new(FeistelMimcParameters::bounty(22)).expect("builds");
    let kat = reference.permutation(F::zero(), F::one());
    println!("zkfriendlyhashzoo records permutation([0, 1]) = (0xf874e35bbaf92376,");
    println!(
        "0x72af6f65901ac3f1) at r = 22. This port gives ({:#x}, {:#x}):",
        kat[0].value(),
        kat[1].value()
    );
    assert_eq!(kat[0].value(), 0xf874_e35b_baf9_2376);
    assert_eq!(kat[1].value(), 0x72af_6f65_901a_c3f1);
    println!("the SHAKE128 round-constant derivation, the seed width and the Feistel swap all");
    println!("agree with the reference.");
    println!();

    println!("## The per-round model: r cubics in r variables, planted target");
    println!();
    println!("`N - E = t - 2k = 0`, so the system is square and zero-dimensional with no slice.");
    println!("Every row asserts the system vanishes at the plant's own trace *before* solving and");
    println!("re-verifies any recovered input through the permutation.");
    println!();
    header();
    print_row(&attempt::<2>(2));
    print_row(&attempt::<3>(3));
    print_row(&attempt::<4>(4));
    print_row(&attempt::<5>(5));
    print_row(&attempt::<6>(6));
    print_row(&attempt::<7>(7));
    print_row(&attempt::<8>(8));
    print_row(&attempt::<9>(9));
    print_row(&attempt::<10>(10));

    println!();
    println!("## The univariate model: one generator of degree 3^r");
    println!();
    println!("The same solution set, reached by eliminating the r - 1 intermediate variables by");
    println!("substitution. The elimination is exact and costs degree exponentially.");
    println!();
    println!(
        "| {:>3} | {:>9} | {:>10} | {:>10} | {:>5} | {:<24} |",
        "r", "degree", "build ms", "roots ms", "roots", "plant found"
    );
    println!(
        "|{}|{}|{}|{}|{}|{}|",
        "-".repeat(5),
        "-".repeat(11),
        "-".repeat(12),
        "-".repeat(12),
        "-".repeat(7),
        "-".repeat(26)
    );
    for rounds in 2..=9 {
        let (degree, build, solve, roots, has_plant) = univariate_row(rounds);
        println!(
            "| {:>3} | {:>9} | {:>10} | {:>10} | {:>5} | {:<24} |",
            rounds,
            degree,
            format!("{:.1}", build.as_secs_f64() * 1e3),
            format!("{:.1}", solve.as_secs_f64() * 1e3),
            roots,
            has_plant
        );
    }

    println!();
    println!("## The stated objective, target zero");
    println!();
    println!("Not planted: the bounty asks for the trailing output word to be *zero*, and at a");
    println!("reduced round count that need not have a solution over the base field. An empty");
    println!("solution set below is a fact about that rung, not a failure of anything.");
    println!();
    println!("| {:>3} | {:>5} | {:<40} |", "r", "roots", "witness");
    println!("|{}|{}|{}|", "-".repeat(5), "-".repeat(7), "-".repeat(42));
    for rounds in 1..=8 {
        let mimc = FeistelMimc::<F>::new(FeistelMimcParameters::bounty(rounds)).expect("builds");
        let stated = FeistelMimcCico::new(mimc, FeistelMimcModel::Univariate);
        let found = stated.solutions();
        for x in &found {
            assert!(
                stated.is_solution(*x),
                "a root of the stated univariate is not a CICO solution"
            );
        }
        let witness = match found.first() {
            Some(x) => format!("{}", x),
            None => "none over this field".to_string(),
        };
        println!("| {:>3} | {:>5} | {:<40} |", rounds, found.len(), witness);
    }

    println!();
    println!("## What the absent MDS layer buys");
    println!();
    println!("docs/research/poseidon.md §4 measures nine variables solving at t = 2 and failing");
    println!("at t = 3, and attributes the difference to the dense MDS layer. Feistel-MiMC has no");
    println!("MDS layer at all, so the comparison to make is at matched variable count *and*");
    println!("matched algebraic dimension — both systems here are square, N - E = 0, which is the");
    println!("trap docs/research/degree-profiles.md §4 records.");
    println!();
    println!("The easiest authoritative instance is r = 22 and the easiest withdrawn one r = 6.");
    println!("Nothing above is a statement about either: see docs/research/mimc-rescue.md for");
    println!("what the published records actually claim and at what cost.");
}
