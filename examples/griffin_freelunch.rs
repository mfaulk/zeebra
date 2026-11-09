//! Griffin/FreeLunch for [#202](https://github.com/mfaulk/zeebra/issues/202): does a monomial
//! order under which the input generators are already a Gröbner basis remove F4?
//!
//! - `basis` runs Zeebra's F4 on the checked-in `r ∈ {4, 5}` systems under the FreeLunch order
//!   `≺_G` and, for the control, with every pair criterion switched off. **Machine-independent** —
//!   every number printed is a count, so a disagreement is a defect and not a timing.
//! - `grevlex <r>` runs the same system through F4 under degrevlex under a stated budget, and
//!   reports where it stopped. This is the comparand `docs/research/griffin-freelunch.md` §11
//!   recorded as missing: §3's degrevlex figures are Singular and msolve on a surrogate prime,
//!   not Zeebra's own engine on `p`.
//! - `attack <r>` runs `matGen` and `polyDet` and checks the eliminant against the published
//!   witnesses. The whole attack with no Gröbner engine anywhere in it.
//! - Both timing subcommands **refuse to print a number** unless `ZEEBRA_MACHINE` and
//!   `ZEEBRA_AFFINITY` are set, for the reason `examples/anemoi_ladder.rs` states.
//!
//! ```sh
//! cargo run --release --example griffin_freelunch basis
//! ZEEBRA_MACHINE=... ZEEBRA_AFFINITY=... tools/benchlock.sh \
//!     cargo run --release --example griffin_freelunch grevlex 5
//! ZEEBRA_MACHINE=... ZEEBRA_AFFINITY=... tools/benchlock.sh \
//!     cargo run --release --example griffin_freelunch attack 5
//! ```

use std::time::{Duration, Instant};

use zeebra::{
    fields::PrimeFieldElement64,
    grobner::{
        f4_reported,
        research::griffin::{FreeLunchSystem, FREELUNCH_PRIME, FREELUNCH_R4, FREELUNCH_R5},
        F4Options, PairCriteria,
    },
    MonomialOrder, Polynomial, Zero,
};

type F = PrimeFieldElement64<FREELUNCH_PRIME>;

const DRL: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let rung = |default: usize| -> usize {
        arguments
            .get(1)
            .map(|r| r.parse().expect("a round count"))
            .unwrap_or(default)
    };
    match arguments.first().map(String::as_str).unwrap_or("basis") {
        "basis" => basis(),
        "grevlex" => grevlex(rung(5)),
        "attack" => attack(rung(5)),
        other => panic!("usage: griffin_freelunch [basis | grevlex <r> | attack <r>]; got {other}"),
    }
}

/// `ZEEBRA_MACHINE` and `ZEEBRA_AFFINITY`, or exit 2 rather than print an unpinned figure.
fn provenance() -> (String, String) {
    match (
        std::env::var("ZEEBRA_MACHINE"),
        std::env::var("ZEEBRA_AFFINITY"),
    ) {
        (Ok(machine), Ok(affinity)) => (machine, affinity),
        _ => {
            eprintln!(
                "refusing to time anything: set ZEEBRA_MACHINE and ZEEBRA_AFFINITY, and run under \
                 tools/benchlock.sh so the measurement is serialized against other agents. An \
                 unpinned wall-clock figure is not a measurement, and `basis` is the subcommand \
                 that needs no environment."
            );
            std::process::exit(2);
        }
    }
}

/// How much work F4 does under `≺_G`, against the same engine with the criteria switched off.
fn basis() {
    println!("# Griffin/FreeLunch: F4's work under the known-basis order");
    println!("# counts only, so this subcommand is machine-independent\n");
    println!(
        "| r | criteria | pairs | by 1st criterion | reduced | batches | largest matrix | basis |"
    );
    println!("|---|---|---|---|---|---|---|---|");
    row::<2>(FREELUNCH_R4, 4);
    row::<3>(FREELUNCH_R5, 5);
    println!(
        "\nUnder `≺_G` every pair falls to Buchberger's first criterion, so no Macaulay matrix is\n\
         built and the basis returned is the input. With the criteria off, the same engine on the\n\
         same input reduces every pair to zero through the matrix in the `matrix` column — which is\n\
         what the order is saving."
    );
}

fn row<const N: usize>(fixture: &str, rounds: usize) {
    let system = FreeLunchSystem::<N, F>::parse(fixture).expect("a readable fixture");
    let weighted = system.order().expect("an admissible weight vector");
    let every = PairCriteria {
        product: true,
        chain: true,
        gebauer_moller: true,
    };
    // `PairCriteria::default()` is `PRODUCT_ONLY`, so the first row is the shipped configuration.
    for (label, criteria) in [
        ("1st only (default)", PairCriteria::PRODUCT_ONLY),
        ("all three", every),
        ("none", PairCriteria::NONE),
    ] {
        let options = F4Options {
            criteria,
            ..F4Options::default()
        };
        let (basis, statistics) = f4_reported(&system.generators, weighted, &options);
        println!(
            "| {} | {} | {} | {} | {} | {} | {}x{} | {} |",
            rounds,
            label,
            statistics.pairs_considered,
            statistics.pairs_eliminated_by_product_criterion,
            statistics.pairs_reduced,
            statistics.batches,
            statistics.max_matrix_rows,
            statistics.max_matrix_columns,
            basis.map(|b| b.len().to_string()).unwrap_or("-".into()),
        );
    }
}

/// The degrevlex comparand, in Zeebra's own F4 on the real prime, under a stated budget.
fn grevlex(rounds: usize) {
    let (machine, affinity) = provenance();
    println!("# Griffin/FreeLunch degrevlex in Zeebra's F4, r = {rounds}, p = {FREELUNCH_PRIME}");
    println!("machine {machine}, affinity {affinity}\n");

    // A stated budget, so a run that does not finish reports a reproducible stopping point rather
    // than "it took too long". Twenty minutes and 8 GB of live matrix entries.
    let options = F4Options {
        max_wall_time: Some(Duration::from_secs(1_200)),
        ..F4Options::recommended().with_live_budget::<F>(8 << 30)
    };
    match rounds {
        4 => grevlex_rung::<2>(FREELUNCH_R4, &options),
        5 => grevlex_rung::<3>(FREELUNCH_R5, &options),
        other => panic!("only r = 4 and r = 5 are checked in; got {other}"),
    }
}

fn grevlex_rung<const N: usize>(fixture: &str, options: &F4Options) {
    let system = FreeLunchSystem::<N, F>::parse(fixture).expect("a readable fixture");
    let started = Instant::now();
    let (outcome, statistics) = f4_reported(&system.generators, DRL, options);
    let elapsed = started.elapsed();

    match &outcome {
        Ok(basis) => println!(
            "finished: {} elements in {:.3} s",
            basis.len(),
            elapsed.as_secs_f64()
        ),
        Err(error) => println!("stopped: {error} after {:.3} s", elapsed.as_secs_f64()),
    }
    println!("degree reached     {}", statistics.max_pair_degree);
    println!("batches            {}", statistics.batches);
    println!("pairs reduced      {}", statistics.pairs_reduced);
    println!(
        "largest matrix     {} x {}",
        statistics.max_matrix_rows, statistics.max_matrix_columns
    );
    println!("peak live nonzeros {}", statistics.max_live_nonzeros);
    println!(
        "\nSame polynomials, same field, same engine as the `basis` run above; only the order\n\
         differs. D_I = {}, so a finished basis is a {}-dimensional quotient either way.",
        system.quotient_dimension, system.quotient_dimension
    );
}

/// `matGen` and `polyDet`, checked against the published witnesses.
fn attack(rounds: usize) {
    let (machine, affinity) = provenance();
    println!("# Griffin/FreeLunch matGen + polyDet, r = {rounds}, p = {FREELUNCH_PRIME}");
    println!("machine {machine}, affinity {affinity}\n");
    match rounds {
        4 => attack_rung::<2>(FREELUNCH_R4),
        5 => attack_rung::<3>(FREELUNCH_R5),
        other => panic!("only r = 4 and r = 5 are checked in; got {other}"),
    }
}

fn attack_rung<const N: usize>(fixture: &str) {
    let system = FreeLunchSystem::<N, F>::parse(fixture).expect("a readable fixture");

    let started = Instant::now();
    let matrix = system.module_matrix().expect("matGen");
    let matgen = started.elapsed();

    let started = Instant::now();
    let eliminant = matrix.determinant().expect("polyDet");
    let polydet = started.elapsed();

    println!("D_H                {}", matrix.order());
    println!("D_I                {}", system.quotient_dimension);
    println!("alpha_0            {}", system.alpha0);
    println!(
        "matGen             {:.3} s, {} coefficients ({:.2} MB at 8 bytes)",
        matgen.as_secs_f64(),
        matrix.coefficients(),
        matrix.coefficients() as f64 * 8.0 / 1e6
    );
    println!(
        "polyDet            {:.3} s, degree {} from {} sample points",
        polydet.as_secs_f64(),
        eliminant.degree(),
        matrix.determinant_degree_bound() + 1
    );
    assert_eq!(
        eliminant.degree() as usize,
        system.quotient_dimension,
        "deg det M must be D_I"
    );

    if system.witnesses.is_empty() {
        println!("witnesses          none published at this round count");
    } else {
        for (i, witness) in system.witnesses.iter().enumerate() {
            let vanishes = eliminant.eval(&witness[0]).is_zero();
            println!(
                "witness {i}          x_0 = {:?}, eliminant vanishes: {}",
                witness[0], vanishes
            );
            assert!(vanishes, "the eliminant must vanish at a published witness");
        }
    }
    println!(
        "\nNo Gröbner basis was computed: the modelling equations are certified a Gröbner basis by\n\
         coprime leading monomials, and matGen reduces against them directly. polyDet is\n\
         {} scalar {}x{} determinants and one interpolation.",
        matrix.determinant_degree_bound() + 1,
        matrix.order(),
        matrix.order()
    );
}
