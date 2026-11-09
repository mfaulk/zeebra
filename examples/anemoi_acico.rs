//! The runner for Anemoi's third model, `ACICO` (eprint 2025/814), read in the order that keeps
//! the claims apart.
//!
//! - `structure` walks `N` at `α = 3` over DRL and checks the basis against Proposition 2's
//!   leading monomials, the quotient dimension against Proposition 4's **proved** `(α + 2)^N`, and
//!   the F4 step-degree sequence against the published claim that the solving degree is flat in
//!   the round count. **Machine-independent** — every number is algebraic, so a disagreement is a
//!   defect and not a timing.
//! - `weighted` does the same at `α ∈ {5, 7, 11}` over the weighted order Definition 15 specifies,
//!   against Proposition 3. Reachable only since #306 landed [`MonomialOrder::Weighted`].
//! - `shape` reports both halves of the shape-position question and labels which is which: the
//!   syntactic hypotheses of Theorem 8, *deduced*, and the separating condition Theorem 8 omits,
//!   *computed*. See `src/grobner/shape_certificate.rs` for why the first half is not sufficient.
//! - `cost <N>` times F4, the conversion and root finding separately, and **refuses to print a
//!   number** unless `ZEEBRA_MACHINE` and `ZEEBRA_AFFINITY` are set, for the reason
//!   `examples/anemoi_ladder.rs` states.
//!
//! ```sh
//! cargo run --release --example anemoi_acico structure
//! cargo run --release --example anemoi_acico weighted
//! cargo run --release --example anemoi_acico shape
//! ZEEBRA_MACHINE=... ZEEBRA_AFFINITY=... tools/benchlock.sh \
//!     cargo run --release --example anemoi_acico cost 4
//! ```

use std::time::Instant;

use rand::SeedableRng;
use zeebra::{
    fields::Zp1481823929,
    grobner::{
        f4_reported,
        fglm::{
            fglm_to_lex_with_options, separating_variables, shape_lex_basis, shape_report,
            FglmOptions, QuotientAlgebra,
        },
        research::{
            anemoi::{Anemoi, AnemoiParameters, ANEMOI_ACICO_PRIME},
            anemoi_cico::{AnemoiCico, AnemoiModel},
            proved_acico_quotient_dimension,
        },
        shape_position_hypotheses, solve_from_lex_basis, F4Options, HilbertSeries, SolveOptions,
        SolveOutcome,
    },
    Monomial, MonomialOrder, MultivariatePolynomial, WeightedTieBreak,
};

/// The 31-bit prime eprint 2025/814 §7.3 measures over.
type A = Zp1481823929;

const DRL: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    match arguments.first().map(String::as_str).unwrap_or("structure") {
        "structure" => structure(),
        "weighted" => weighted(),
        "shape" => shape(),
        "cost" => {
            let rounds: usize = arguments
                .get(1)
                .expect("usage: anemoi_acico cost <rounds>")
                .parse()
                .expect("a round count");
            cost(rounds);
        }
        other => panic!(
            "usage: anemoi_acico [structure | weighted | shape | cost <rounds>]; got {other}"
        ),
    }
}

/// An `ACICO` instance at the paper's prime.
fn instance(alpha: u32, rounds: usize) -> AnemoiCico<A> {
    let parameters = AnemoiParameters {
        prime: ANEMOI_ACICO_PRIME,
        alpha,
        l: 1,
        rounds,
    };
    AnemoiCico::new(
        Anemoi::new(parameters).expect("alpha is coprime to p - 1 at this prime"),
        AnemoiModel::Acico,
    )
}

/// Definition 15's weighted DRL order at `ℓ = 1`: `w(y_r) = α`, `w(s_r) = 2`, revlex ties.
fn wdrl(alpha: u32, rounds: usize) -> MonomialOrder {
    let mut weights = vec![alpha; rounds + 1];
    weights.extend(std::iter::repeat_n(2u32, rounds));
    MonomialOrder::weighted(&weights, WeightedTieBreak::ReverseLexicographic)
        .expect("the weights are positive")
}

/// What one rung's algebra says, with nothing timed.
struct Row {
    alpha: u32,
    rounds: usize,
    variables: usize,
    basis: usize,
    leading_monomials_agree: bool,
    dimension: i128,
    proved: u128,
    max_pair_degree: u64,
    step_degrees: Vec<u64>,

    /// Peak live nonzero entries, against `F4Options::default()`'s 20 000 000 allowance.
    ///
    /// Reported because "the basis is free" is a claim about a budget as well as a clock, and this
    /// is the budget Anemoi's other two models are refused on at this rung (#323).
    peak_live_nonzeros: usize,
}

/// The expected leading-monomial set, from Proposition 2 (DRL, `α = 3`) or Proposition 3 (WDRL).
fn expected_leads<const N: usize>(alpha: u32, rounds: usize, weighted: bool) -> Vec<Monomial<N>> {
    let mut expected = vec![Monomial::univariate(0, 1)];
    for round in 1..=rounds {
        if weighted {
            expected.push(Monomial::univariate(round, 2));
            expected.push(Monomial::univariate(rounds + round, alpha + 1));
        } else {
            expected.push(Monomial::univariate(round, alpha));
            expected.push(Monomial::univariate(rounds + round, alpha));
        }
        let mut exponents = [0u32; N];
        exponents[round] = 1;
        exponents[rounds + round] = 1;
        expected.push(Monomial::new(&exponents));
    }
    expected
}

fn row<const N: usize>(alpha: u32, rounds: usize, weighted: bool) -> Row {
    let order = if weighted { wdrl(alpha, rounds) } else { DRL };
    let instance = instance(alpha, rounds);
    let system: Vec<MultivariatePolynomial<N, A>> = instance.system::<N>().expect("the right N");
    let (basis, statistics) = f4_reported(&system, order, &F4Options::default());
    let basis = basis.expect("ACICO's basis is nearly free at these rungs");
    let mut leads: Vec<Monomial<N>> = basis.iter().map(|p| p.leading_monomial(order)).collect();
    let mut expected = expected_leads::<N>(alpha, rounds, weighted);
    leads.sort_by(|a, b| order.cmp(a, b));
    expected.sort_by(|a, b| order.cmp(a, b));
    let dimension = HilbertSeries::of_basis(&basis, order)
        .expect("a monomial ideal")
        .quotient_dimension(&leads)
        .expect("within budget")
        .expect("zero-dimensional");
    Row {
        alpha,
        rounds,
        variables: N,
        basis: basis.len(),
        leading_monomials_agree: leads == expected,
        dimension,
        proved: *proved_acico_quotient_dimension(alpha, rounds, 1).value(),
        max_pair_degree: statistics.max_pair_degree,
        peak_live_nonzeros: statistics.max_live_nonzeros,
        step_degrees: statistics.step_degrees,
    }
}

fn print_rows(rows: &[Row], proposition: &str) {
    println!("| `α` | `N` | variables | basis | {proposition} | `D` | proved `(α+2)^N` | agrees | `max_pair_degree` | step degrees | peak live nonzeros |");
    println!("|---:|---:|---:|---:|---|---:|---:|---|---:|---|---:|");
    for row in rows {
        println!(
            "| {} | {} | {} | {} | {} | {} | {} | {} | {} | {:?} | {} |",
            row.alpha,
            row.rounds,
            row.variables,
            row.basis,
            if row.leading_monomials_agree {
                "**agrees**"
            } else {
                "**DISAGREES**"
            },
            row.dimension,
            row.proved,
            if row.dimension == i128::try_from(row.proved).expect("small") {
                "yes"
            } else {
                "**NO — a defect**"
            },
            row.max_pair_degree,
            row.step_degrees,
            row.peak_live_nonzeros,
        );
    }
}

/// `α = 3` over DRL, against Propositions 2 and 4.
fn structure() {
    println!("# `ACICO` at `α = 3` over DRL — Propositions 2 and 4\n");
    let rows = vec![
        row::<3>(3, 1, false),
        row::<5>(3, 2, false),
        row::<7>(3, 3, false),
        row::<9>(3, 4, false),
        row::<11>(3, 5, false),
        row::<13>(3, 6, false),
    ];
    print_rows(&rows, "Proposition 2's leading monomials");
    println!();
    let flat = rows[1..]
        .iter()
        .all(|r| r.step_degrees == rows[1].step_degrees);
    println!(
        "The step-degree sequence is {} from `N = 2` on, which is the published \"solving degree \
         constant in the number of rounds\" in a stronger form than a constant maximum.",
        if flat {
            "**identical**"
        } else {
            "**not identical**"
        }
    );
}

/// `α ∈ {5, 7, 11}` over the weighted order, against Propositions 3 and 4.
fn weighted() {
    println!("# `ACICO` above `α = 3` over WDRL — Propositions 3 and 4\n");
    println!(
        "Weights are Definition 15's: `w(y) = α`, `w(s) = 2`, revlex ties. Reachable only since \
         #306 landed `MonomialOrder::Weighted`; #201 recorded this as a standing gap.\n"
    );
    let mut rows = Vec::new();
    for alpha in [5u32, 7, 11] {
        rows.push(row::<3>(alpha, 1, true));
        rows.push(row::<5>(alpha, 2, true));
        rows.push(row::<7>(alpha, 3, true));
    }
    print_rows(&rows, "Proposition 3's leading monomials");
}

/// Both halves of the shape-position question, labelled.
fn shape() {
    println!("# `ACICO` shape position — the deduced half and the computed half\n");
    println!("| `α` | `N` | `D` | hypotheses | strict variables | `deg` of the lex-last variable | separating | shape basis = classical |");
    println!("|---:|---:|---:|---|---|---:|---|---|");
    macro_rules! report {
        ($($alpha:literal, $rounds:literal => $n:literal, $weighted:literal;)+) => {$(
            let order = if $weighted { wdrl($alpha, $rounds) } else { DRL };
            let row = instance($alpha, $rounds);
            let system = row.system::<$n>().expect("the right N");
            let basis = zeebra::grobner::f4(&system, order).expect("a basis");
            let hypotheses = shape_position_hypotheses(&basis, order, &F4Options::default());
            let options = FglmOptions::unbounded();
            let algebra = QuotientAlgebra::new(&basis, order, &options)
                .expect("zero-dimensional, by Proposition 4");
            let found = shape_report(&algebra, $n - 1);
            let classical = fglm_to_lex_with_options(&basis, order, &options)
                .expect("the classical route").0;
            let agrees = shape_lex_basis(&algebra)
                .map(|shape| shape == classical)
                .unwrap_or(false);
            let separating = separating_variables(&algebra);
            println!(
                "| {} | {} | {} | {} | {} | {} | {} | {} |",
                $alpha, $rounds, found.dimension,
                match &hypotheses {
                    Ok(_) => "**discharged**".to_string(),
                    Err(gap) => format!("**gap: {gap:?}**"),
                },
                match &hypotheses {
                    Ok(h) => format!("{:?}", h.strict_variables()),
                    Err(_) => "—".to_string(),
                },
                found.minimal_polynomial_degree,
                if separating.len() == $n {
                    "all".to_string()
                } else {
                    format!("{separating:?}")
                },
                if agrees { "**yes**" } else { "**NO**" },
            );
        )+};
    }
    report! {
        3, 1 => 3, false;
        3, 2 => 5, false;
        3, 3 => 7, false;
        3, 4 => 9, false;
        5, 1 => 3, true;
        5, 2 => 5, true;
        7, 1 => 3, true;
        7, 2 => 5, true;
    }
    println!(
        "\nThe hypotheses column is a **deduction** about the instance; the two degree columns are \
         a **computation** on it. Theorem 8's printed hypotheses do not imply shape position — see \
         `src/grobner/shape_certificate.rs` — so neither column alone settles it, and neither is a \
         proof about the family."
    );
}

/// One rung through F4, the conversion and root finding, each timed separately.
fn cost(rounds: usize) {
    let (machine, affinity) = match (
        std::env::var("ZEEBRA_MACHINE"),
        std::env::var("ZEEBRA_AFFINITY"),
    ) {
        (Ok(machine), Ok(affinity)) => (machine, affinity),
        _ => {
            eprintln!(
                "refusing to time anything: set ZEEBRA_MACHINE and ZEEBRA_AFFINITY, and run under \
                 tools/benchlock.sh so the measurement is serialized against other agents. An \
                 unpinned wall-clock figure is not a measurement, and `structure` is the \
                 subcommand that needs no environment."
            );
            std::process::exit(2);
        }
    };
    println!("# `ACICO`, `α = 3`, `N = {rounds}`, p = {ANEMOI_ACICO_PRIME}");
    println!("machine {machine}, affinity {affinity}\n");
    macro_rules! run {
        ($n:literal) => {{
            let row = instance(3, $n / 2);
            let system = row.system::<$n>().expect("the right N");

            let start = Instant::now();
            let basis = zeebra::grobner::f4(&system, DRL).expect("a basis");
            let grobner = start.elapsed();

            let options = FglmOptions::unbounded();
            let start = Instant::now();
            let (lex, _) = fglm_to_lex_with_options(&basis, DRL, &options).expect("zero-dimensional");
            let conversion = start.elapsed();

            let start = Instant::now();
            let mut rng = rand::rngs::StdRng::from_seed([7; 32]);
            let solved = solve_from_lex_basis(&lex, &system, &SolveOptions::default(), &mut rng);
            let univariate = start.elapsed();

            let witness = match solved {
                Ok((SolveOutcome::Point(point), _)) => point
                    .iter()
                    .copied()
                    .find(|candidate| row.is_solution(*candidate)),
                _ => None,
            };
            println!("| stage | elapsed |");
            println!("|---|---:|");
            println!("| basis (F4) | {grobner:?} |");
            println!("| conversion (FGLM) | {conversion:?} |");
            println!("| univariate + root finding | {univariate:?} |");
            println!(
                "| **total** | {:?} |\n",
                grobner + conversion + univariate
            );
            match witness {
                Some(y) => println!(
                    "witness `y = {y}`, **verified by running the permutation** rather than the \
                     system that produced it"
                ),
                None => println!("no base-field point — zero-dimensional, and the roots are not in `F_p`"),
            }
        }};
    }
    match 2 * rounds + 1 {
        3 => run!(3),
        5 => run!(5),
        7 => run!(7),
        9 => run!(9),
        11 => run!(11),
        other => panic!("no compiled dimension for {other} variables; N = 1..5 are wired"),
    }
}
