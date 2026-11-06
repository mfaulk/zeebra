//! M23-E: a resultant against F4, on the same full-width CICO slices.
//!
//! The spike the plan asks for, with the instance chosen so that the comparison means something:
//! these are the **registered** `t = 16` reductions M23-B measured, sliced the same way, so the
//! resultant's cost sits beside an F4 figure for exactly the same problem.
//!
//! ```text
//! cargo run --release --example resultant_cico            # the rows this construction reaches
//! cargo run --release --example resultant_cico -- --all   # attempt the rest; see §4 of the doc
//! cargo run --release --example resultant_cico -- --write # record the results on the scoreboard
//! ```
//!
//! # The structure the resultant exploits
//!
//! Fix twelve of the fourteen free inputs and two unknowns remain. Every S-box output is then a
//! *polynomial in those two*, because the permutation is a straight-line program: there is nothing
//! to solve for, only to evaluate. So the whole system collapses to **two polynomials in two
//! variables**, of degree `3^rounds` each, and the CICO condition is their common root.
//!
//! That is what F4 is not told. The S-box-per-variable formulation exists to keep the *degree*
//! bounded at the cost of 32 extra variables, and at `t = 16` those variables are what make the
//! matrices unaffordable (M23-B: fourteen of eighteen rows die on live entries at degree 4–5).
//! Eliminating them by evaluation trades the variables back for degree — and the question this
//! example answers is where that trade stops paying.
//!
//! # What is measured
//!
//! Per row: the time to build the two bivariate polynomials, their actual degree against `3^rounds`,
//! the resultant's actual degree against the Bézout bound `3^rounds × 3^rounds`, the univariate
//! root count, and whether a candidate verifies **through the permutation**. Nothing here decides
//! a candidate is a solution: a resultant root is a necessary condition, so every one is checked.

use std::time::{Duration, Instant};

use rand::{prelude::StdRng, SeedableRng};

use zeebra::{
    fields::PrimeFieldElement64,
    grobner::research::{
        bivariate_resultant, challenge, cico_bivariate, registry, ChallengeManifest, CicoInstance,
        Environment, Json, RunOutcome, RunRecord, Scoreboard, Specialization, Stage, StageCost,
        KOALABEAR_PRIME,
    },
    roots, FiniteField, MultivariatePolynomial, Polynomial, UnivariatePolynomial, Zero,
};

type K = PrimeFieldElement64<KOALABEAR_PRIME>;

/// What the symbolic evaluation produced for one row.
struct Bivariate {
    /// The two constrained output words, as polynomials in the two surviving inputs, with their
    /// targets already subtracted.
    outputs: Vec<MultivariatePolynomial<2, K>>,
    /// Their degrees.
    degrees: [u64; 2],
    /// Terms in each.
    terms: [usize; 2],
    /// How long the evaluation took.
    elapsed: Duration,
}

/// `cico_bivariate`, timed.
fn evaluate_symbolically(instance: &CicoInstance<K>, fixed: &[K]) -> Bivariate {
    let at = Instant::now();
    let outputs = cico_bivariate(instance, fixed).expect("two free inputs remain");
    Bivariate {
        degrees: [outputs[0].degree(), outputs[1].degree()],
        terms: [outputs[0].terms().len(), outputs[1].terms().len()],
        outputs,
        elapsed: at.elapsed(),
    }
}

fn main() {
    let write = std::env::args().any(|a| a == "--write");
    let mut board = Scoreboard::new();
    println!("# M23-E: a resultant against F4 on the registered t = 16 slices\n");
    println!(
        "Every row is a registered reduction of `poseidon31-cico-rf6-rp8`, sliced with twelve of \
         the fourteen free inputs fixed at seed 1 — the same slice M23-B and M23-C measured. The \
         resultant eliminates the second surviving input; the candidate is checked by running the \
         permutation.\n"
    );

    // Every row of M23-B's ladder, in round order. The ones past the reach of this construction
    // are *predicted* rather than attempted, with the arithmetic shown — a spike that hung on a
    // row it could never finish would measure the operator's patience.
    let attempt_all = std::env::args().any(|a| a == "--all");
    for id in [
        "poseidon31-cico-t16-rf2-rp0",
        "poseidon31-cico-t16-rf2-rp2",
        "poseidon31-cico-t16-rf4-rp0",
        "poseidon31-cico-t16-rf2-rp4",
        "poseidon31-cico-t16-rf4-rp2",
        "poseidon31-cico-t16-rf4-rp4",
        "poseidon31-cico-t16-rf6-rp0",
        "poseidon31-cico-t16-rf6-rp2",
        "poseidon31-cico-t16-rf6-rp4",
    ] {
        let manifest = challenge(id).expect("registered");
        let rounds = manifest.poseidon_parameters().expect("a CICO row").rounds();
        let degree = 3f64.powi(rounds as i32);
        // Sample count times the cost of one Sylvester determinant: `2d^2` points and an order-`2d`
        // matrix, so `16 d^5` field operations before any of the polynomial arithmetic.
        let predicted = 16.0 * degree.powi(5);
        if !attempt_all && predicted > 1e10 {
            println!("## {} — {} rounds\n", manifest.id, rounds);
            println!(
                "- not attempted: degree `3^{}` is {:.0}, so the resultant needs about {:.0} \
                 samples of an order-{:.0} determinant — **{:.1e} field operations** before the \
                 bivariate arithmetic, which itself has to cube a polynomial with {:.0} terms",
                rounds,
                degree,
                2.0 * degree * degree,
                2.0 * degree,
                predicted,
                degree * degree / 2.0
            );
            println!("- `--all` attempts it anyway\n");
            continue;
        }
        if let Some(record) = row(&manifest, 1) {
            board
                .add(record, &registry())
                .expect("a registered problem");
        }
    }

    // The records go beside F4's for the same problems, which is the point: `Comparison::of`
    // compares them because the identity digest is the same, so the factor between the two routes
    // is a scoreboard fact rather than a sentence in a document.
    if write {
        let registry = registry();
        for run in board.runs() {
            let manifest = registry
                .iter()
                .find(|c| c.id == run.challenge)
                .expect("checked on add");
            let name = format!(
                "{}--{}--{}.json",
                run.challenge,
                run.formulation.replace([' ', '(', ')', ','], "-"),
                run.environment.commit
            );
            std::fs::write(
                std::path::Path::new("research/scoreboard/runs").join(name),
                run.to_json(manifest).to_json() + "\n",
            )
            .expect("a writable file");
        }
        // And into the accumulated history, which is what the tables are rendered from. Read,
        // extend, write back — the same discipline as the scoreboard runner, so a record written
        // here survives the next render instead of being overwritten by it.
        let history_path = std::path::Path::new("research/scoreboard/results/history.json");
        let mut entries: Vec<Json> = match std::fs::read_to_string(history_path) {
            Ok(text) => Json::parse(&text)
                .expect("the history the scoreboard wrote")
                .get("runs")
                .map(|runs| runs.items().to_vec())
                .unwrap_or_default(),
            Err(_) => Vec::new(),
        };
        for run in board.runs() {
            let manifest = registry
                .iter()
                .find(|c| c.id == run.challenge)
                .expect("checked on add");
            entries.push(run.to_json(manifest));
        }
        std::fs::write(
            history_path,
            Json::object([
                ("schema", Json::int(RunRecord::SCHEMA)),
                ("run_count", Json::size(entries.len())),
                ("runs", Json::Array(entries)),
            ])
            .to_json()
                + "\n",
        )
        .expect("a writable file");
        println!(
            "\n{} records written to research/scoreboard/ and appended to the history; rerun \
             tools/scoreboard.sh to re-render the tables",
            board.runs().len()
        );
    }

    println!(
        "\n`rounds` is `R_F + R_P`, and both the polynomial degree and the resultant's degree are \
         powers of three in it: the straight-line evaluation triples the degree at every round, \
         with no variable left to absorb it. That is the whole trade — F4 pays 32 variables to \
         hold the degree at 3, and this pays degree `3^rounds` to hold the variables at two."
    );
}

/// One registered row: evaluate, eliminate, solve, verify.
fn row(manifest: &ChallengeManifest, seed: u64) -> Option<RunRecord> {
    let parameters = manifest.poseidon_parameters().expect("a CICO row");
    let rounds = parameters.rounds();
    let instance = manifest.cico_instance::<K>().expect("a registered problem");
    let free = instance.free_inputs();

    // The same slice the other experiments used, from the same seeded stream: the specialization
    // records its values, so the two agree by construction rather than by coincidence.
    let variables: Vec<usize> = (2..free).collect();
    let specialization =
        Specialization::<46, K>::seeded(&variables, seed).expect("distinct indices");
    let fixed: Vec<K> = (2..free)
        .map(|i| specialization.value_of(i).expect("fixed"))
        .collect();

    let built = evaluate_symbolically(&instance, &fixed);

    println!("## {} — {} rounds\n", manifest.id, rounds);
    println!(
        "- two bivariate outputs of degree {} and {} ({} and {} terms), built in {:.1} ms",
        built.degrees[0],
        built.degrees[1],
        built.terms[0],
        built.terms[1],
        built.elapsed.as_secs_f64() * 1e3
    );
    println!(
        "- `3^{}` is {}, so the degree is {}",
        rounds,
        3u64.pow(rounds as u32),
        if built.degrees[0] == 3u64.pow(rounds as u32) {
            "exactly the straight-line bound"
        } else {
            "below the straight-line bound"
        }
    );

    // `cico_bivariate` has already subtracted the targets, so a common root of these two is a
    // solution of the instance.
    let f = built.outputs[0].clone();
    let g = built.outputs[1].clone();

    let at = Instant::now();
    let resultant = match bivariate_resultant(&f, &g, 1) {
        Ok(resultant) => resultant,
        Err(error) => {
            println!("- the resultant was refused: {}\n", error);
            return None;
        }
    };
    let elimination = at.elapsed();
    let bezout = 3u64.pow(rounds as u32) * 3u64.pow(rounds as u32);
    println!(
        "- resultant of degree {} against a Bézout bound of {}, in {:.1} ms",
        resultant.degree(),
        bezout,
        elimination.as_secs_f64() * 1e3
    );

    let at = Instant::now();
    let candidates = roots(&resultant, &mut StdRng::seed_from_u64(7));
    let root_finding = at.elapsed();
    println!(
        "- {} roots over KoalaBear, found in {:.1} ms",
        candidates.len(),
        root_finding.as_secs_f64() * 1e3
    );

    // Each root of the resultant is a *necessary* condition on the first unknown. The second is
    // recovered by substituting and taking a common root, and the pair is then checked by running
    // the permutation — the only thing that decides whether it is a solution.
    let at = Instant::now();
    let mut witnesses = 0usize;
    for first in &candidates {
        for second in extend(&f, &g, *first) {
            let mut inputs = vec![*first, second];
            inputs.extend_from_slice(&fixed);
            if instance.is_solution(&inputs).unwrap_or(false) {
                witnesses += 1;
            }
        }
    }
    let verification = at.elapsed();
    println!(
        "- {} verified witnesses, checked through the permutation in {:.1} ms",
        witnesses,
        verification.as_secs_f64() * 1e3
    );
    let total = built.elapsed + elimination + root_finding + verification;
    println!("- **total {:.1} ms**\n", total.as_secs_f64() * 1e3);

    let mut record = RunRecord::new(
        manifest,
        format!("resultant, slice(12 fixed, seed {})", seed),
    );
    record.transformations = vec![
        format!("specialize free inputs 2..{} at seed {}", free, seed),
        format!(
            "evaluate the {} S-box variables away: two bivariate polynomials of degree {}",
            manifest.poseidon_parameters().expect("a CICO row").sboxes(),
            built.degrees[0]
        ),
        "eliminate the second unknown by a Sylvester resultant".to_string(),
    ];
    record.outcome = if witnesses > 0 {
        RunOutcome::VerifiedWitness
    } else {
        RunOutcome::SliceEstablishedNothing
    };
    record.verification = format!(
        "{} candidates checked by running permutation_plus_linear; {} verified",
        candidates.len(),
        witnesses
    );
    record.stages = vec![
        StageCost::new(Stage::Generation, built.elapsed)
            .with("bivariate_degree", built.degrees[0] as i64)
            .with("terms", built.terms[0] as i64),
        StageCost::new(Stage::Elimination, elimination)
            .with("resultant_degree", resultant.degree() as i64)
            .with("bezout_bound", bezout as i64),
        StageCost::new(Stage::Univariate, root_finding).with("roots", candidates.len() as i64),
        StageCost::new(Stage::Verification, verification).with("witnesses", witnesses as i64),
    ];
    record.environment = Environment {
        commit: commit(),
        machine: std::env::var("ZEEBRA_MACHINE").unwrap_or_else(|_| "unknown".to_string()),
        cpu: format!(
            "{} logical, affinity {}",
            std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(0),
            std::env::var("ZEEBRA_AFFINITY").unwrap_or_else(|_| "unpinned".to_string())
        ),
        build: "release, RUSTFLAGS from .cargo/config.toml".to_string(),
        policy: "straight-line evaluation, one Sylvester resultant by interpolation, no budget"
            .to_string(),
    };
    record.reproduce = "cargo run --release --example resultant_cico -- --write".to_string();
    Some(record)
}

/// The commit this was built from.
fn commit() -> String {
    std::process::Command::new("git")
        .args(["rev-parse", "--short", "HEAD"])
        .output()
        .ok()
        .and_then(|out| String::from_utf8(out.stdout).ok())
        .map(|s| s.trim().to_string())
        .unwrap_or_else(|| "unknown".to_string())
}

/// The second coordinates that extend `first` to a common root of `f` and `g`.
///
/// Substituting a resultant root leaves two univariate polynomials; their common roots are the
/// candidates. Taking the roots of one and testing the other is enough and needs no gcd.
fn extend(f: &MultivariatePolynomial<2, K>, g: &MultivariatePolynomial<2, K>, first: K) -> Vec<K> {
    let specialize = |p: &MultivariatePolynomial<2, K>| -> UnivariatePolynomial<K> {
        let mut coefficients: Vec<K> = Vec::new();
        for (monomial, coefficient) in p.terms() {
            let exponents = monomial.exponents();
            let power = exponents[1] as usize;
            if coefficients.len() <= power {
                coefficients.resize(power + 1, K::zero());
            }
            coefficients[power] += *coefficient * first.pow(exponents[0] as u128);
        }
        if coefficients.is_empty() {
            <UnivariatePolynomial<K> as Polynomial<K>>::zero()
        } else {
            UnivariatePolynomial::new(&coefficients)
        }
    };

    let fx = specialize(f);
    let gx = specialize(g);
    if fx.is_zero() || gx.is_zero() {
        // A whole line of solutions, or none: either way this is not the case the resultant was
        // built for, and reporting no candidate is the honest answer.
        return Vec::new();
    }
    roots(&fx, &mut StdRng::seed_from_u64(11))
        .into_iter()
        .filter(|second| gx.eval(second).is_zero())
        .collect()
}
