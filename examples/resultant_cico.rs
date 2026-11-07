//! M23-E: a resultant against F4, on the same full-width CICO slices.
//!
//! The spike the plan asks for, with the instance chosen so that the comparison means something:
//! these are the **registered** `t = 16` reductions M23-B measured, sliced the same way, so the
//! resultant's cost sits beside an F4 figure for exactly the same problem.
//!
//! ```text
//! cargo run --release --example resultant_cico              # every row the budget admits
//! cargo run --release --example resultant_cico -- --write   # record on the scoreboard
//! cargo run --release --example resultant_cico -- --concurrency 1,8,32   # the scaling study
//! cargo run --release --example resultant_cico -- --ntt-ab  # the superseded §6.5 A/B
//! cargo run --release --example resultant_cico -- --row poseidon31-cico-t16-rf2-rp4 --build-only
//! cargo run --release --example resultant_cico -- --row poseidon31-cico-t16-rf2-rp4 \
//!     --max-samples 6562 --wall-budget 14400      # one named row under one named budget
//! ```
//!
//! # Rows and budgets
//!
//! `--row` is repeatable and restricts the ladder to the rows named. `--max-samples` and
//! `--wall-budget` are the two budgets, and a row over either is **costed and skipped** with its
//! arithmetic printed rather than started. There is no `--all`: it removed the guard entirely,
//! which put a 12.9-day row beside a bounded one, and a budget is not a thing to switch off
//! wholesale. `--build-only` times `cico_bivariate` alone and stops, which is the one bounded
//! measurement a row past the budget still supports.
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
//! # The sample count, and the A/B that justifies it
//!
//! The sample set is sized against [JAZ] slide 22's **experimental** degree `alpha^(2 R_F + R_P)`
//! rather than against the proven Bézout-sized bound: 730 determinants instead of 13 123 on
//! `rf2-rp2`. The formula is unproven in its source, so the recovered polynomial is checked
//! against a direct Sylvester determinant off the interpolation domain, and the proven path takes
//! over if the check refuses it — see `DegreeSource`.
//!
//! Where the proven bound is still affordable, both counts run on the same two polynomials in the
//! same process at the same concurrency and their coefficients are asserted equal: that is the
//! A/B, and it is what turns "fewer samples" into "the same answer from fewer samples".
//! `--ntt-ab` additionally re-measures the power-of-two subgroup route, whose loss is the measured
//! negative result of `docs/research/resultant-elimination.md` §6.5.

use std::time::{Duration, Instant};

use rand::{prelude::StdRng, SeedableRng};

use zeebra::{
    fields::PrimeFieldElement64,
    grobner::research::{
        bivariate_resultant_ntt_with, bivariate_resultant_predicted,
        bivariate_resultant_reference_with, challenge, cico_bivariate, predicted_resultant_degree,
        registry, sylvester_determinant_at, ChallengeManifest, CicoInstance, DegreeSource,
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

/// Samples a row may take before it is costed and skipped rather than started.
///
/// 16 384 admits both four-round rows under the proven bound and the predicted count alike. The
/// six-round rows start at 6 562 samples, and it is the wall-clock budget rather than this that
/// refuses them: those samples are order-1 458 determinants.
const DEFAULT_MAX_SAMPLES: usize = 16_384;

/// Predicted determinant wall clock a row may take before it is costed and skipped, in seconds.
const DEFAULT_WALL_BUDGET_SECONDS: usize = 1_800;

/// One order-162 Sylvester determinant at **one** worker, measured.
///
/// `examples/determinant_sweep`, five orders, three draws each, under `tools/benchlock.sh` —
/// `docs/research/resultant-elimination.md` §6.9. It replaces the 2.868 ms §6.5 derived from
/// 37 634.3 ms over 13 123 samples, because **that figure no longer reproduces on this machine**:
/// the same 13 123-determinant reference route measured 45 131.0 ms (3.439 ms each) in M25, and the
/// synthetic sweep 3.624 ms. A cost model whose job is to refuse runs must not be anchored to the
/// fastest figure ever recorded, so the anchor is the larger, current one and §6.9 records the
/// unexplained 1.2x gap as a finding.
const DETERMINANT_MS_AT_162: f64 = 3.624;

/// The matrix order that cost was measured at.
const MEASURED_ORDER: f64 = 162.0;

/// The exponent measured above the L2 footprint: `core(order) ∝ order^2.9953`, ±0.0285.
///
/// §6.9's sweep, fitted over orders 486, 1 458 and 4 374 — every order whose matrix exceeds this
/// machine's 512 kB L2 — with a worst residual of 3.7%. The kernel is **cubic** up there to within
/// the measurement, and the 3.116 exponent #289 was opened with is not reproduced: it came from
/// dividing a 32-worker core-time at order 1 458 by a single-worker one at order 162, and the
/// width is what the excess was.
///
/// Below L2 the sweep measures 2.79 — fixed per-determinant overhead that the small orders cannot
/// amortize — and that is *sub*-cubic, so a model using it would predict less work than cubic.
/// [`determinant_core_ms`] therefore takes the larger of the two laws rather than this one.
const ABOVE_L2_EXPONENT: f64 = 2.9953;

/// How much core-time one determinant gains per doubling of the worker count, measured.
///
/// Core-time per determinant — wall clock times workers — is not flat in the worker count on this
/// box: §6.9 measures 2.404 s, 2.821 s and 3.148 s at order 1 458 on 1, 8 and 32 workers, which is
/// about 6.5% a doubling and is the all-core clock rather than bandwidth. A budget guard that
/// costed a 32-worker run at the single-worker figure would under-predict it by 30%, and a guard
/// that under-predicts refuses nothing.
const CORE_TIME_PER_DOUBLING: f64 = 0.065;

/// Core-time of one Sylvester determinant at `matrix_order` on `workers` workers, in milliseconds.
///
/// The **larger** of the measured above-L2 law and the cubic, both anchored at order 162, times the
/// measured width penalty. Taking the larger is deliberate and is the whole point of the
/// calibration: the fitted exponent 2.9953 is *below* 3, so using the fit alone would predict less
/// work than the cubic this guard has always used, and a cost model that under-predicts is a budget
/// that authorizes a run nobody costed. If a future sweep measures an exponent above 3, this picks
/// it up with no further change.
///
/// Measured at orders 18 to 4 374 and at 1, 8 and 32 workers. Above 4 374 — which is every row past
/// seven rounds — it is an **extrapolation**, and every caller labels it as one.
fn determinant_core_ms(matrix_order: usize, workers: usize) -> f64 {
    let ratio = matrix_order as f64 / MEASURED_ORDER;
    let cubic = DETERMINANT_MS_AT_162 * ratio.powi(3);
    let fitted = DETERMINANT_MS_AT_162 * ratio.powf(ABOVE_L2_EXPONENT);
    cubic.max(fitted) * width_penalty(workers)
}

/// The measured core-time penalty for running at `workers` workers, as a factor.
///
/// Linear in `log2(workers)` through the three widths §6.9 measured, and extrapolated at the same
/// slope beyond 32 rather than held flat: nothing wider has been measured, and flattening it would
/// make the guard optimistic exactly where it has no evidence.
fn width_penalty(workers: usize) -> f64 {
    1.0 + CORE_TIME_PER_DOUBLING * (workers.max(1) as f64).log2()
}

/// The value of a `--flag <value>` argument, if it was given and parses.
fn flag_value(flag: &str) -> Option<usize> {
    let args: Vec<String> = std::env::args().collect();
    let at = args.iter().position(|a| a == flag)?;
    args.get(at + 1)?.parse().ok()
}

/// Every value of a repeatable `--flag <value>` argument.
fn flag_values(flag: &str) -> Vec<String> {
    let args: Vec<String> = std::env::args().collect();
    args.iter()
        .enumerate()
        .filter(|(_, a)| *a == flag)
        .filter_map(|(at, _)| args.get(at + 1).cloned())
        .collect()
}

/// A duration in whatever unit a reader can hold in their head.
fn human_seconds(seconds: f64) -> String {
    if seconds < 90.0 {
        format!("{:.1} s", seconds)
    } else if seconds < 5_400.0 {
        format!("{:.1} min", seconds / 60.0)
    } else if seconds < 172_800.0 {
        format!("{:.2} h", seconds / 3_600.0)
    } else {
        format!("{:.2} d", seconds / 86_400.0)
    }
}

/// What one registered row is predicted to cost, before anything is attempted.
///
/// The sample counts are exact — they come from the row's own `alpha`, `R_F` and `R_P` — and the
/// times are extrapolations from one measured determinant at order 162.
struct RowCost {
    /// `R_F + R_P`.
    rounds: usize,
    /// The S-box exponent.
    alpha: u32,
    /// Full rounds.
    r_f: usize,
    /// Partial rounds.
    r_p: usize,
    /// `alpha^(2 R_F + R_P)`, the experimental degree.
    predicted_degree: usize,
    /// Samples the prediction needs.
    samples: usize,
    /// Samples the proven `2d²` bound needs.
    proven_samples: usize,
    /// Order of the Sylvester matrix, `2 · 3^rounds`.
    matrix_order: usize,
    /// Predicted determinant wall clock for `samples`, over the given worker count.
    predicted_seconds: f64,
    /// The same for `proven_samples`.
    proven_seconds: f64,
}

impl RowCost {
    /// Cost `manifest` at `workers` determinant workers.
    fn of(manifest: &ChallengeManifest, workers: usize) -> Self {
        let parameters = manifest.poseidon_parameters().expect("a CICO row");
        let rounds = parameters.rounds();
        let degree = 3usize.pow(rounds as u32);
        let predicted_degree =
            predicted_resultant_degree(parameters.alpha, parameters.r_f, parameters.r_p)
                .expect("the predicted degree fits a usize");
        let matrix_order = 2 * degree;
        // Core-time per determinant, divided by the workers that share it. `determinant_core_ms`
        // carries both the cost law and the measured penalty for running wide.
        let each = determinant_core_ms(matrix_order, workers) / 1e3 / workers.max(1) as f64;
        let samples = predicted_degree + 1;
        let proven_samples = 2 * degree * degree + 1;
        Self {
            rounds,
            alpha: parameters.alpha,
            r_f: parameters.r_f,
            r_p: parameters.r_p,
            predicted_degree,
            samples,
            proven_samples,
            matrix_order,
            predicted_seconds: samples as f64 * each,
            proven_seconds: proven_samples as f64 * each,
        }
    }
}

/// `cico_bivariate` alone on one row, which is the whole of `--build-only`.
///
/// The build has been under 1% of every row measured, and at six rounds that is the thing in most
/// doubt: the outputs have ~266 000 terms and the cost law behind the estimate has never been
/// checked at that size. Timing it apart is single-threaded, interruptible and cheap, which an
/// attempt at the determinants is not.
fn build_alone(manifest: &ChallengeManifest, seed: u64) -> Bivariate {
    let instance = manifest.cico_instance::<K>().expect("a registered problem");
    let free = instance.free_inputs();
    let variables: Vec<usize> = (2..free).collect();
    let specialization =
        Specialization::<46, K>::seeded(&variables, seed).expect("distinct indices");
    let fixed: Vec<K> = (2..free)
        .map(|i| specialization.value_of(i).expect("fixed"))
        .collect();
    evaluate_symbolically(&instance, &fixed)
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
    let build_only = std::env::args().any(|a| a == "--build-only");
    let concurrencies = concurrencies();
    let wanted = flag_values("--row");
    let max_samples = flag_value("--max-samples").unwrap_or(DEFAULT_MAX_SAMPLES);
    let wall_budget = flag_value("--wall-budget").unwrap_or(DEFAULT_WALL_BUDGET_SECONDS) as f64;
    if std::env::args().any(|a| a == "--all") {
        eprintln!(
            "--all is gone: it removed the cost guard entirely, which admitted a 12.9-day row \
             beside a bounded one. Name the row and its budget instead:\n  --row <challenge-id> \
             --max-samples <n> --wall-budget <seconds>"
        );
        std::process::exit(64);
    }

    let mut board = Scoreboard::new();
    println!("# M23-E: a resultant against F4 on the registered t = 16 slices\n");
    println!(
        "Every row is a registered reduction of `poseidon31-cico-rf6-rp8`, sliced with twelve of \
         the fourteen free inputs fixed at seed 1 — the same slice M23-B and M23-C measured. The \
         resultant eliminates the second surviving input; the candidate is checked by running the \
         permutation.\n"
    );

    println!(
        "Budget: at most {} samples a row, and {:.0} s of predicted determinant wall clock at the \
         largest concurrency given. A row over either is **costed and skipped**, not attempted.\n",
        max_samples, wall_budget
    );

    // The ladder in round order. A row the budget refuses is costed and skipped rather than
    // started: at six rounds `rf4-rp2` is 34 single-core hours and `rf6-rp0` is 12.9 days, and a
    // run that discovered that by hanging would measure the operator's patience.
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
        if !wanted.is_empty() && !wanted.iter().any(|named| named.as_str() == id) {
            continue;
        }
        let manifest = challenge(id).expect("registered");
        let workers = concurrencies.iter().copied().max().unwrap_or(1);
        let cost = RowCost::of(&manifest, workers);
        println!("## {} — {} rounds\n", manifest.id, cost.rounds);
        println!(
            "- predicted degree `{}^(2·{} + {})` = {}, so {} samples of an order-{} determinant; \
             the proven `2d²` bound would need {}",
            cost.alpha,
            cost.r_f,
            cost.r_p,
            cost.predicted_degree,
            cost.samples,
            cost.matrix_order,
            cost.proven_samples
        );
        println!(
            "- predicted determinant wall clock **{}** on {} worker{}, from {:.3} ms per \
             determinant measured at order 162 and one worker, scaled by the measured \
             `order^{:.4}` law and a {:.2}x penalty for running at this width — **{}** at order {}",
            human_seconds(cost.predicted_seconds),
            workers,
            plural(workers),
            DETERMINANT_MS_AT_162,
            ABOVE_L2_EXPONENT,
            width_penalty(workers),
            if cost.matrix_order <= 4_374 {
                "measured"
            } else {
                "an extrapolation"
            },
            cost.matrix_order
        );

        // Before the budget, because the budget is on the determinants and this runs none of
        // them. The build is the stage whose cost law is least checked: at six rounds the outputs
        // have ~266 000 terms where every row measured so far had ~3 400.
        if build_only {
            let built = build_alone(&manifest, 1);
            println!(
                "- `--build-only`: degrees {} and {}, {} and {} terms, built in **{}** \
                 single-threaded",
                built.degrees[0],
                built.degrees[1],
                built.terms[0],
                built.terms[1],
                human_seconds(built.elapsed.as_secs_f64())
            );
            match peak_resident_bytes() {
                Some(bytes) => println!("- peak resident **{:.2} GB**\n", bytes as f64 / 1e9),
                None => println!("- no process memory measurement on this platform\n"),
            }
            continue;
        }
        if cost.samples > max_samples || cost.predicted_seconds > wall_budget {
            println!(
                "- **not attempted**: {} the budget. Raise it deliberately — `--row {} \
                 --max-samples {} --wall-budget {:.0}` — or leave the row as a prediction\n",
                if cost.samples > max_samples {
                    "the sample count exceeds"
                } else {
                    "the predicted wall clock exceeds"
                },
                id,
                cost.samples,
                cost.predicted_seconds.ceil()
            );
            continue;
        }
        if cost.proven_seconds > wall_budget {
            println!(
                "- the proven `2d²` fallback is **unaffordable** here: {} samples is {}. If the \
                 off-domain check refuses the prediction on this row, the result is *prediction \
                 falsified, generic bound unaffordable* — a counterexample to the published \
                 formula, and a better outcome than the witness",
                cost.proven_samples,
                human_seconds(cost.proven_seconds)
            );
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

    let predicted_degree =
        predicted_resultant_degree(parameters.alpha, parameters.r_f, parameters.r_p)
            .expect("the predicted degree fits a usize");

    let built = evaluate_symbolically(&instance, &fixed);

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
            (rounds, predicted_degree),
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
    /// Points off the interpolation domain that agreed with a direct Sylvester determinant.
    off_domain_checks: usize,
    /// Off-domain validation this example took **itself**, which is zero on a held prediction.
    ///
    /// The route validates its own prediction and reports the cost in `stages.validation`, so on a
    /// held row there is nothing left to pay. Keeping the two apart is what stops the check being
    /// charged to a stage twice — see `Pass::validation`.
    extra_validation: Duration,
    /// Roots of the resultant, and the cost of finding them.
    candidates: (usize, Duration),
    /// Candidate pairs lifted from those roots, and the cost.
    pairs: (usize, Duration),
    /// The verified witnesses, in root order, and the cost of running the permutation on every
    /// candidate. Compared across passes.
    witnesses: Vec<(K, K)>,
    /// Time spent in `is_solution`.
    verification: Duration,
    /// The row's measured wall clock, which the recorded stages must sum to.
    total: Duration,
}

impl Pass {
    /// The off-domain validation's wall clock, counted **once**.
    ///
    /// On a held prediction this is the route's own check; otherwise the route took none and this
    /// is the one this example took. The two are never both nonzero.
    fn validation(&self) -> Duration {
        self.stages.validation + self.extra_validation
    }

    /// The elimination's wall clock: determinants, recovery and validation.
    ///
    /// Validation is charged **here and nowhere else**. `Stage::Verification` is the independent
    /// check of a *candidate* — a recovered input pair run through the permutation — whereas the
    /// off-domain check is what decides which polynomial the elimination returns at all, and on a
    /// falsified row `stages.validation` already contains the refused attempt's own determinants.
    /// Charging it to both stages, as this example did before M25, inflated every recorded total by
    /// the cost of the check: 17.4 s of a six-round row.
    fn elimination(&self) -> Duration {
        self.stages.elapsed() + self.extra_validation
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
    shape: (usize, usize),
    build: Duration,
    concurrency: usize,
) -> Option<Pass> {
    let (rounds, predicted_degree) = shape;
    let options = ResultantOptions::with_concurrency(concurrency);
    // Sized against [JAZ] slide 22's experimental degree, and validated off the domain inside the
    // route rather than trusted — see `DegreeSource`.
    let (resultant, stages) =
        match bivariate_resultant_predicted(f, g, 1, predicted_degree, options) {
            Ok(pair) => pair,
            Err(error) => {
                println!("- the resultant was refused: {}\n", error);
                return None;
            }
        };
    let elimination = stages.elapsed();
    let bezout = 3u64.pow(rounds as u32) * 3u64.pow(rounds as u32);
    println!(
        "- predicted degree {} from `alpha^(2 R_F + R_P)`, so {} samples against the proven \
         bound's {}",
        predicted_degree,
        predicted_degree + 1,
        stages.degree_bound + 1
    );
    match stages.degree_source {
        DegreeSource::PredictionHeld { degree } => println!(
            "- the prediction **held**: {} points outside the sample set agree with a direct \
             Sylvester determinant, so degree {} pinned the resultant",
            stages.off_domain_checks, degree
        ),
        DegreeSource::PredictionFalsified { degree } => println!(
            "- the prediction was **falsified**: degree {} did not survive the off-domain check, \
             so the proven bound produced the answer — a counterexample to [JAZ] slide 22 on this \
             row",
            degree
        ),
        DegreeSource::Proven => println!(
            "- the prediction is no smaller than the proven bound, so the proven path was taken"
        ),
    }
    match stages.route {
        ResultantRoute::Ntt { log_size } => println!(
            "- interpolated on the subgroup of order `2^{}` = {} (proven degree bound {}), so \
             recovery is one inverse NTT",
            log_size,
            1usize << log_size,
            stages.degree_bound
        ),
        ResultantRoute::Lagrange { points } => println!(
            "- Lagrange at {} consecutive points (proven degree bound {})",
            points, stages.degree_bound
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

    // The A/B against the **proven** sample count, on the same two polynomials in the same
    // process and at the same concurrency: the predicted count's whole claim is that it returns
    // the identical polynomial from far fewer determinants, and only running both says so.
    let held = matches!(stages.degree_source, DegreeSource::PredictionHeld { .. });
    let reference_stages = if stages.degree_bound <= AB_CONTROL_BOUND && held {
        let (reference, rstages) =
            bivariate_resultant_reference_with(f, g, 1, options).expect("both involve the second");
        assert_eq!(
            reference, resultant,
            "the predicted count and the proven bound disagree"
        );
        let reference_total = rstages.sampling + rstages.interpolation;
        println!(
            "- A/B: proven bound, {} consecutive points — {} determinants {:.1} ms + \
             `lagrange_interpolate` {:.1} ms = **{:.1} ms**, same coefficients. The predicted \
             count is **{:.2}x faster** on {:.2}x fewer determinants.",
            rstages.samples,
            rstages.samples,
            rstages.sampling.as_secs_f64() * 1e3,
            rstages.interpolation.as_secs_f64() * 1e3,
            reference_total.as_secs_f64() * 1e3,
            reference_total.as_secs_f64() / elimination.as_secs_f64(),
            rstages.samples as f64 / stages.samples as f64
        );
        Some(rstages)
    } else if !held {
        println!("- A/B skipped: the answer already came from the proven path");
        None
    } else {
        println!(
            "- A/B skipped: the proven bound's {} points exceed the control bound {}, so the \
             prediction is the only affordable route here",
            stages.degree_bound + 1,
            AB_CONTROL_BOUND
        );
        None
    };

    // The superseded §6.5 comparison, kept reachable and off by default: the subgroup route pads
    // the sample count to a power of two, which costs more determinants than the quasi-linear
    // recovery saves. Re-measuring it costs 16 384 determinants a row.
    if std::env::args().any(|a| a == "--ntt-ab") {
        let (ntt, nstages) =
            bivariate_resultant_ntt_with(f, g, 1, options).expect("both involve the second");
        assert_eq!(ntt, resultant, "the subgroup route disagrees");
        println!(
            "- A/B: subgroup route, {} samples — {:.1} ms determinants + {:.1} ms inverse NTT",
            nstages.samples,
            nstages.sampling.as_secs_f64() * 1e3,
            nstages.interpolation.as_secs_f64() * 1e3
        );
    }

    // The interpolated polynomial is checked against the definition at points the interpolation
    // never saw. A held prediction has already paid for that inside the route, so its count and
    // cost are reported from there rather than by taking a second set of determinants.
    let (fresh, extra_validation) = if held {
        (stages.off_domain_checks, Duration::ZERO)
    } else {
        let at = Instant::now();
        let fresh = off_domain_check(f, g, &resultant, &stages.route, 8);
        (fresh, at.elapsed())
    };
    println!(
        "- {} points outside the interpolation domain agree with a direct Sylvester determinant, \
         in {:.1} ms — {} consistency check, not a proof of a polynomial identity",
        fresh,
        (stages.validation + extra_validation).as_secs_f64() * 1e3,
        if held {
            "a probabilistic"
        } else {
            "an independent"
        }
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
    let mut pass = Pass {
        concurrency,
        resultant,
        stages,
        reference_stages,
        off_domain_checks: fresh,
        extra_validation,
        candidates: (candidates.len(), root_finding),
        pairs: (pairs.len(), lifting),
        witnesses,
        verification,
        total: Duration::ZERO,
    };
    // Validation is inside `elimination()`, so it must not be added again here. The row total and
    // the recorded stage durations come from this one expression, and `record` asserts they agree.
    pass.total = build + pass.elimination() + root_finding + lifting + verification;
    println!("- **total {:.1} ms**", pass.total.as_secs_f64() * 1e3);
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
        pass.off_domain_checks
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
        )
        // Inside this stage's `elapsed`, and inside no other's.
        .with("validation_us", pass.validation().as_micros() as i64);
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
        // Running the permutation on each candidate pair, and that alone. The off-domain check is
        // elimination work and is charged there; only its *count* is descriptive here.
        StageCost::new(Stage::Verification, pass.verification)
            .with("witnesses", pass.witnesses.len() as i64)
            .with("off_domain_checks", pass.off_domain_checks as i64),
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
    // Name the row. The default budgets admit it, so the bare command does reproduce this record
    // — but it also runs every other row on the way, which for a 60-minute six-round row is an
    // hour of unrelated work to re-derive one line.
    record.reproduce = format!(
        "cargo run --release --example resultant_cico -- --row {} --concurrency {} --write",
        record.challenge, pass.concurrency
    );
    // Measured process RSS, kept apart from any `peak_estimated_bytes`: this route builds no
    // Macaulay matrix, and on the six-round row the two would differ by four orders of magnitude.
    record.measured_peak_resident_bytes = peak_resident_bytes().map(|b| b as usize);
    // `RunRecord::elapsed` is the sum of the stages, so a duration charged to two stages inflates
    // the recorded row total silently. Asserting the sum against the total this row actually
    // printed is the check that catches it on every run rather than on review.
    assert_eq!(
        record.elapsed(),
        pass.total,
        "the recorded stage durations must sum to the row's measured total"
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
