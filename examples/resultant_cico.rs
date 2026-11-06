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
//! cargo run --release --example resultant_cico -- --concurrency 1,8,32   # the scaling study
//! ```
//!
//! # Concurrency
//!
//! `--concurrency` takes a comma-separated list and **defaults to `1`**, so the figures recorded
//! before it existed reproduce unchanged. Each row runs the whole elimination-and-solve once per
//! entry, and the resultant's coefficients and the witness set are asserted **equal across the
//! list** — the determinants are independent and indexed, so a difference would be a bug and not a
//! race worth tolerating. With more than one entry a scaling table is printed, and each level is
//! recorded as its own scoreboard row carrying its own `concurrency`: `Comparison::of` refuses to
//! divide one by another, because that ratio is a core count rather than a solver speedup.
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
//! Per row, stage-separated: the time to build the two bivariate polynomials and their actual
//! degree against `3^rounds`; the Sylvester determinant evaluations and the interpolation,
//! reported apart because they are the two costs an implementation would attack separately; the
//! resultant's actual degree against the Bézout bound `3^rounds × 3^rounds`; root finding; lifting
//! each root to a candidate pair; and verification **through the permutation**. Nothing here
//! decides a candidate is a solution: a resultant root is a necessary condition, so every one is
//! checked.
//!
//! The resultant itself is also checked against a direct Sylvester determinant at points the
//! interpolation never sampled, which is what distinguishes a recovered polynomial from its own
//! evaluation table.
//!
//! Both interpolation routes run on the same two polynomials in the same process, and their
//! answers are asserted equal. That is the A/B: the subgroup route trades extra determinants for a
//! cheaper recovery, and only both figures together say which way the trade goes. On these rows it
//! goes the wrong way — see `docs/research/resultant-elimination.md` §6.5.

use std::time::{Duration, Instant};

use rand::{prelude::StdRng, SeedableRng};

use zeebra::{
    fields::PrimeFieldElement64,
    grobner::research::{
        bivariate_resultant_ntt_with, bivariate_resultant_reference_with, challenge,
        cico_bivariate, registry, sylvester_determinant_at, ChallengeManifest, CicoInstance,
        Environment, Json, ResultantOptions, ResultantRoute, ResultantStages, RunOutcome,
        RunRecord, Scoreboard, Specialization, Stage, StageCost, KOALABEAR_PRIME,
    },
    roots,
    util::peak_resident_bytes,
    FiniteField, MultivariatePolynomial, One, Polynomial, UnivariatePolynomial, Zero,
};

type K = PrimeFieldElement64<KOALABEAR_PRIME>;

/// Degree bound up to which the reference route is also run, as an A/B control.
///
/// 16 384 covers both four-round rows, whose bound is 13 122. That was unaffordable while
/// `lagrange_interpolate` was cubic — an extrapolated hour — and is affordable now that #162 made
/// it quadratic, which is exactly why the comparison is worth printing: the reference pays 1.4 s
/// of interpolation and saves 3 261 determinants against the subgroup route, and wins.
const AB_CONTROL_BOUND: usize = 16_384;

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

/// The `--concurrency` list, defaulting to a single uncontended run.
///
/// Parsed strictly: a malformed or zero entry stops the run rather than quietly becoming 1, since
/// the number is recorded on the scoreboard and a mis-parse would label a single-threaded figure as
/// a parallel one.
fn concurrencies() -> Vec<usize> {
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        let list = match arg.strip_prefix("--concurrency=") {
            Some(rest) => rest.to_string(),
            None if arg == "--concurrency" => args.next().unwrap_or_else(|| {
                panic!("--concurrency needs a comma-separated list, e.g. --concurrency 1,8,32")
            }),
            None => continue,
        };
        return list
            .split(',')
            .map(|entry| {
                let n: usize = entry
                    .trim()
                    .parse()
                    .unwrap_or_else(|_| panic!("{} is not a worker count", entry));
                assert!(n >= 1, "a worker count is at least 1");
                n
            })
            .collect();
    }
    vec![1]
}

fn main() {
    let write = std::env::args().any(|a| a == "--write");
    let concurrencies = concurrencies();
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
        // `1e11` rather than the `1e10` M23-E used: a four-round row went from an unfinished hour to
        // under a minute, essentially all of it determinants, so the rows worth attempting are the
        // ones whose *determinant* arithmetic fits. Six rounds is `3.3e15` and still does not.

        if !attempt_all && predicted > 1e11 {
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
        for record in row(&manifest, 1, &concurrencies) {
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
            // The concurrency is part of the file name only when it is not 1, so a single-threaded
            // row keeps the name its history is already filed under while a parallel row of the
            // same problem, formulation and commit lands beside it instead of on top of it.
            let name = format!(
                "{}--{}{}--{}.json",
                run.challenge,
                run.formulation.replace([' ', '(', ')', ','], "-"),
                match run.environment.concurrency {
                    1 => String::new(),
                    n => format!("--c{}", n),
                },
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

/// One registered row: evaluate once, then eliminate and solve at each degree of parallelism.
///
/// The symbolic evaluation is shared across the concurrency list — it is not the stage being
/// measured and is single-threaded at every level. The elimination-and-solve runs once per entry,
/// each a full pass down to running the permutation, and every pass's resultant and witness set is
/// asserted equal to the first's. The determinants are independent and written into their own
/// index, so the only thing a difference there could mean is a bug.
fn row(manifest: &ChallengeManifest, seed: u64, concurrencies: &[usize]) -> Vec<RunRecord> {
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

    let mut records: Vec<RunRecord> = Vec::new();
    let mut passes: Vec<Pass> = Vec::new();
    for &concurrency in concurrencies {
        if concurrencies.len() > 1 {
            println!("\n### {} worker{}\n", concurrency, plural(concurrency));
        }
        let Some(pass) = solve(
            &instance,
            &f,
            &g,
            &fixed,
            rounds,
            built.elapsed,
            concurrency,
        ) else {
            return records;
        };
        if let Some(first) = passes.first() {
            assert_eq!(
                pass.resultant, first.resultant,
                "the resultant at {} workers differs from the one at {}",
                concurrency, first.concurrency
            );
            assert_eq!(
                pass.witnesses, first.witnesses,
                "the witness set at {} workers differs from the one at {}",
                concurrency, first.concurrency
            );
            println!(
                "- byte-identical resultant coefficients and the identical witness set as at {} \
                 worker{}",
                first.concurrency,
                plural(first.concurrency)
            );
        }
        records.push(record(manifest, seed, free, &built, &pass, rounds));
        passes.push(pass);
    }

    if passes.len() > 1 {
        scaling(&passes);
    }
    println!();
    records
}

/// What one elimination-and-solve pass produced, at one degree of parallelism.
struct Pass {
    /// Workers the determinants were spread over.
    concurrency: usize,
    /// The eliminated polynomial. Compared across passes, so it is kept.
    resultant: UnivariatePolynomial<K>,
    /// The subgroup route's stage costs.
    stages: ResultantStages,
    /// The reference route's, when the A/B control ran.
    reference_stages: Option<ResultantStages>,
    /// Points off the interpolation domain that agreed with a direct determinant, and the cost.
    off_domain: (usize, Duration),
    /// Roots of the resultant, and the cost of finding them.
    candidates: (usize, Duration),
    /// Candidate pairs lifted from those roots, and the cost.
    pairs: (usize, Duration),
    /// The verified witnesses, in root order, and the cost of running the permutation on every
    /// candidate. Compared across passes.
    witnesses: Vec<(K, K)>,
    /// Time spent in `is_solution`.
    verification: Duration,
}

impl Pass {
    /// The elimination's wall clock: determinants plus recovery.
    fn elimination(&self) -> Duration {
        self.stages.sampling + self.stages.interpolation
    }
}

/// `s` unless `n` is 1, for the worker counts in the narrative.
fn plural(n: usize) -> &'static str {
    if n == 1 {
        ""
    } else {
        "s"
    }
}

/// Eliminate the second unknown at `concurrency` workers, then solve and verify.
///
/// `None` when the resultant is refused, which is a fact about the two polynomials and therefore
/// does not depend on the concurrency.
fn solve(
    instance: &CicoInstance<K>,
    f: &MultivariatePolynomial<2, K>,
    g: &MultivariatePolynomial<2, K>,
    fixed: &[K],
    rounds: usize,
    build: Duration,
    concurrency: usize,
) -> Option<Pass> {
    let options = ResultantOptions::with_concurrency(concurrency);
    let (resultant, stages) = match bivariate_resultant_ntt_with(f, g, 1, options) {
        Ok(pair) => pair,
        Err(error) => {
            println!("- the resultant was refused: {}\n", error);
            return None;
        }
    };
    let elimination = stages.sampling + stages.interpolation;
    let bezout = 3u64.pow(rounds as u32) * 3u64.pow(rounds as u32);
    match stages.route {
        ResultantRoute::Ntt { log_size } => println!(
            "- interpolated on the subgroup of order `2^{}` = {} (proven degree bound {}), so \
             recovery is one inverse NTT",
            log_size,
            1usize << log_size,
            stages.degree_bound
        ),
        ResultantRoute::Lagrange { points } => println!(
            "- no power-of-two subgroup covers the bound {}: Lagrange at {} consecutive points",
            stages.degree_bound, points
        ),
    }
    println!(
        "- {} Sylvester determinants of order {} on {} worker{} in {:.1} ms; interpolation {:.1} ms",
        stages.samples,
        stages.matrix_order,
        stages.concurrency,
        plural(stages.concurrency),
        stages.sampling.as_secs_f64() * 1e3,
        stages.interpolation.as_secs_f64() * 1e3
    );
    println!(
        "- resultant of degree {} against a Bézout bound of {}, in {:.1} ms",
        resultant.degree(),
        bezout,
        elimination.as_secs_f64() * 1e3
    );

    // The A/B. Both routes run on the same two polynomials in the same process, stage-separated,
    // and the two answers are compared — the subgroup route's win or loss is the difference
    // between its padded sample count and the reference's quadratic interpolation, and nothing
    // short of both figures distinguishes those.
    let reference_stages = if stages.degree_bound <= AB_CONTROL_BOUND {
        let (reference, rstages) =
            bivariate_resultant_reference_with(f, g, 1, options).expect("both involve the second");
        assert_eq!(
            reference, resultant,
            "the subgroup route and the reference disagree"
        );
        let reference_total = rstages.sampling + rstages.interpolation;
        println!(
            "- A/B: reference route, {} consecutive points — {} determinants {:.1} ms + \
             `lagrange_interpolate` {:.1} ms = **{:.1} ms**, same polynomial. Subgroup route is \
             {:.2}x that.",
            rstages.samples,
            rstages.samples,
            rstages.sampling.as_secs_f64() * 1e3,
            rstages.interpolation.as_secs_f64() * 1e3,
            reference_total.as_secs_f64() * 1e3,
            elimination.as_secs_f64() / reference_total.as_secs_f64()
        );
        Some(rstages)
    } else {
        println!(
            "- A/B skipped: the reference route's {} points exceed the control bound {}",
            stages.degree_bound + 1,
            AB_CONTROL_BOUND
        );
        None
    };

    // The interpolated polynomial is checked against the definition at points the interpolation
    // never saw. `degree_bound + 1` samples already determine it, so agreement at a point outside
    // the sample set is evidence about the construction rather than a restatement of it.
    let at = Instant::now();
    let fresh = off_domain_check(f, g, &resultant, &stages.route, 8);
    let independent = at.elapsed();
    println!(
        "- {} points outside the interpolation domain agree with a direct Sylvester determinant, \
         in {:.1} ms",
        fresh,
        independent.as_secs_f64() * 1e3
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
    // recovered by substituting and taking a common root — the lifting stage — and the pair is
    // then checked by running the permutation, which is the only thing that decides it.
    let at = Instant::now();
    let pairs: Vec<(K, K)> = candidates
        .iter()
        .flat_map(|first| {
            extend(f, g, *first)
                .into_iter()
                .map(move |second| (*first, second))
        })
        .collect();
    let lifting = at.elapsed();
    println!(
        "- {} candidate pairs lifted from {} roots in {:.1} ms",
        pairs.len(),
        candidates.len(),
        lifting.as_secs_f64() * 1e3
    );

    let at = Instant::now();
    let mut witnesses: Vec<(K, K)> = Vec::new();
    for (first, second) in &pairs {
        let mut inputs = vec![*first, *second];
        inputs.extend_from_slice(fixed);
        if instance.is_solution(&inputs).unwrap_or(false) {
            witnesses.push((*first, *second));
            println!("  - witness: x = {}, y = {}", first, second);
        }
    }
    let verification = at.elapsed();
    println!(
        "- {} verified witnesses, checked through `permutation_plus_linear` in {:.1} ms",
        witnesses.len(),
        verification.as_secs_f64() * 1e3
    );
    let pass = Pass {
        concurrency,
        resultant,
        stages,
        reference_stages,
        off_domain: (fresh, independent),
        candidates: (candidates.len(), root_finding),
        pairs: (pairs.len(), lifting),
        witnesses,
        verification,
    };
    let total = build + pass.elimination() + independent + root_finding + lifting + verification;
    println!("- **total {:.1} ms**", total.as_secs_f64() * 1e3);
    // The estimate is the live dense arrays: the sample vector, the domain and its inverse, and
    // the recovered coefficients, each of `samples` field elements.
    let estimated = 4 * pass.stages.samples * std::mem::size_of::<K>();
    match peak_resident_bytes() {
        Some(bytes) => println!(
            "- peak resident {:.1} MB measured process-wide; {:.1} MB estimated for the \
             interpolation's live arrays",
            bytes as f64 / 1e6,
            estimated as f64 / 1e6
        ),
        None => println!(
            "- {:.1} MB estimated for the interpolation's live arrays; no process measurement on \
             this platform",
            estimated as f64 / 1e6
        ),
    }
    Some(pass)
}

/// The scaling table across a concurrency list, with the parallel efficiency spelled out.
///
/// Efficiency is the measured determinant speedup divided by the worker ratio. It is the figure
/// that says whether the limit is core count or something else: near 1 means cores, well below it
/// means the sample loop is bounded by something the extra workers do not supply.
fn scaling(passes: &[Pass]) {
    let base = &passes[0];
    println!("\n### Scaling of the determinant stage\n");
    println!(
        "| workers | subgroup determinants | speedup | efficiency | reference determinants | \
         speedup | efficiency |"
    );
    println!("|---:|---:|---:|---:|---:|---:|---:|");
    for pass in passes {
        let ratio = pass.concurrency as f64 / base.concurrency as f64;
        let subgroup = base.stages.sampling.as_secs_f64() / pass.stages.sampling.as_secs_f64();
        let (reference, reference_efficiency) =
            match (&base.reference_stages, &pass.reference_stages) {
                (Some(b), Some(p)) => {
                    let speedup = b.sampling.as_secs_f64() / p.sampling.as_secs_f64();
                    (
                        format!("{:.1} ms | {:.2}x", p.sampling.as_secs_f64() * 1e3, speedup),
                        format!("{:.0}%", 100.0 * speedup / ratio),
                    )
                }
                _ => ("— | —".to_string(), "—".to_string()),
            };
        println!(
            "| {} | {:.1} ms | {:.2}x | {:.0}% | {} | {} |",
            pass.concurrency,
            pass.stages.sampling.as_secs_f64() * 1e3,
            subgroup,
            100.0 * subgroup / ratio,
            reference,
            reference_efficiency
        );
    }
    println!(
        "\nSpeedup and efficiency are against {} worker{}. Every row above recovered the same \
         resultant and the same witnesses.",
        base.concurrency,
        plural(base.concurrency)
    );
}

/// The scoreboard record for one pass.
fn record(
    manifest: &ChallengeManifest,
    seed: u64,
    free: usize,
    built: &Bivariate,
    pass: &Pass,
    rounds: usize,
) -> RunRecord {
    let bezout = 3u64.pow(rounds as u32) * 3u64.pow(rounds as u32);
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
    record.outcome = if pass.witnesses.is_empty() {
        RunOutcome::SliceEstablishedNothing
    } else {
        RunOutcome::VerifiedWitness
    };
    record.verification = format!(
        "{} candidate pairs checked by running permutation_plus_linear ({} verified); the \
         resultant itself checked against a direct Sylvester determinant at {} points outside \
         the interpolation domain",
        pass.pairs.0,
        pass.witnesses.len(),
        pass.off_domain.0
    );
    let mut eliminated = StageCost::new(Stage::Elimination, pass.elimination())
        .with("resultant_degree", pass.resultant.degree() as i64)
        .with("bezout_bound", bezout as i64)
        .with("degree_bound", pass.stages.degree_bound as i64)
        .with("samples", pass.stages.samples as i64)
        .with("matrix_order", pass.stages.matrix_order as i64)
        .with("concurrency", pass.stages.concurrency as i64)
        .with("sampling_us", pass.stages.sampling.as_micros() as i64)
        .with(
            "interpolation_us",
            pass.stages.interpolation.as_micros() as i64,
        );
    if let Some(rstages) = &pass.reference_stages {
        eliminated = eliminated
            .with("reference_samples", rstages.samples as i64)
            .with("reference_sampling_us", rstages.sampling.as_micros() as i64)
            .with(
                "reference_interpolation_us",
                rstages.interpolation.as_micros() as i64,
            );
    }
    record.stages = vec![
        StageCost::new(Stage::Generation, built.elapsed)
            .with("bivariate_degree", built.degrees[0] as i64)
            .with("terms", built.terms[0] as i64),
        eliminated,
        StageCost::new(Stage::Univariate, pass.candidates.1 + pass.pairs.1)
            .with("roots", pass.candidates.0 as i64)
            .with("lifted_pairs", pass.pairs.0 as i64)
            .with("lifting_us", pass.pairs.1.as_micros() as i64),
        StageCost::new(Stage::Verification, pass.verification + pass.off_domain.1)
            .with("witnesses", pass.witnesses.len() as i64)
            .with("off_domain_checks", pass.off_domain.0 as i64),
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
        concurrency: pass.concurrency,
        build: "release, RUSTFLAGS from .cargo/config.toml".to_string(),
        policy: format!(
            "straight-line evaluation, one Sylvester resultant by interpolation, {} determinant \
             worker{}, no budget",
            pass.concurrency,
            plural(pass.concurrency)
        ),
    };
    record.reproduce = format!(
        "cargo run --release --example resultant_cico -- --concurrency {} --write",
        pass.concurrency
    );
    record
}

/// How many fresh points agree with a direct Sylvester determinant.
///
/// Fresh means *outside the interpolation domain*: the subgroup of `2^k`-th roots of unity is
/// exactly the elements with `x^(2^k) = 1`, so anything else was never sampled. A polynomial of
/// degree below the domain size that agrees with the determinant on the whole domain **and** at a
/// point off it can only be the resultant.
fn off_domain_check(
    f: &MultivariatePolynomial<2, K>,
    g: &MultivariatePolynomial<2, K>,
    resultant: &UnivariatePolynomial<K>,
    route: &ResultantRoute,
    wanted: usize,
) -> usize {
    let in_domain: Box<dyn Fn(&K) -> bool> = match route {
        ResultantRoute::Ntt { log_size } => {
            let order = 1u128 << log_size;
            Box::new(move |x: &K| x.is_zero() || x.pow(order).is_one())
        }
        // Consecutive points `0, 1, ..., points - 1`.
        ResultantRoute::Lagrange { points } => {
            let points = *points as u64;
            Box::new(move |x: &K| (0..points).any(|i| *x == K::new(i)))
        }
    };

    let mut rng = StdRng::seed_from_u64(0x00ff_d01a);
    let mut agreed = 0usize;
    let mut drawn = 0usize;
    while agreed < wanted && drawn < 4 * wanted {
        let x = K::random(&mut rng);
        drawn += 1;
        if in_domain(&x) {
            continue;
        }
        let direct = sylvester_determinant_at(f, g, 1, x).expect("both involve the second");
        assert_eq!(
            resultant.eval(&x),
            direct,
            "the interpolated resultant disagrees with the determinant at {}",
            x
        );
        agreed += 1;
    }
    agreed
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
