//! The runner for the registered Anemoi ladder, read in the order that keeps it honest.
//!
//! The split between the subcommands is the point.
//!
//! - `list` prints the registered rows with their published per-step figures.
//! - `dimensions [id-substring]` computes `dim F_p[x]/I` and checks it against `(α + 2)^N`.
//!   **Machine-independent**, so it needs no pinned environment and a disagreement is a defect
//!   rather than a timing. The optional filter exists because the `N = 6` rows cost minutes of F4
//!   each and the gate is worth running on them alone.
//! - `shape [id-substring]` asks whether `R/I` is in shape position in the lex-last variable, and
//!   whether the shape route's lex basis is the classical conversion's. **Machine-independent** for
//!   the same reason `dimensions` is — a minimal-polynomial degree is not a timing.
//! - `budgets [id-substring]` says which F4 budget binds at a rung, under each of four
//!   configurations. **Machine-independent** — every figure is a count — and cheap, because a
//!   configuration that crosses a budget is refused early.
//! - `peak <id>` lifts every resource budget and reports what the row actually needs. The
//!   expensive half of `budgets`, and the only honest input to sizing a budget: a refusal reports
//!   the limit plus a row, which reads as a near miss whatever the real peak is (#323).
//! - `row <id>` runs one row through F4, FGLM and root finding, each timed separately, and
//!   **refuses to print a single number** unless `ZEEBRA_MACHINE` and `ZEEBRA_AFFINITY` are set.
//!
//! A wall-clock figure from an unpinned environment is not a measurement, and this box's noise
//! swamps most changes. The refusal is there so that a figure cannot be produced by accident and
//! then quoted; see `docs/research/anemoi.md` §8 for why the published Magma times are not a
//! head-to-head with it either.
//!
//! ```sh
//! cargo run --release --example anemoi_ladder list
//! cargo run --release --example anemoi_ladder dimensions
//! cargo run --release --example anemoi_ladder dimensions n6
//! cargo run --release --example anemoi_ladder shape n3
//! cargo run --release --example anemoi_ladder budgets anemoi17-cico-n6
//! cargo run --release --example anemoi_ladder peak anemoi17-cico-n6-pcico
//! ZEEBRA_MACHINE=... ZEEBRA_AFFINITY=... tools/benchlock.sh \
//!     cargo run --release --example anemoi_ladder row anemoi64-cico-n3-fcico
//! ```

use std::time::{Duration, Instant};

use rand::SeedableRng;
use zeebra::{
    fields::{PrimeFieldElement64, Zp18446744073709551263},
    grobner::{
        f4_reported,
        fglm::{
            fglm_to_lex_with_options, separating_variables, shape_lex_basis, shape_report,
            FglmMemory, FglmOptions, FglmStatistics, OperatorConstruction, OperatorStorage,
            QuotientAlgebra,
        },
        research::{
            anemoi::{ANEMOI_17_PRIME, ANEMOI_32_PRIME, ANEMOI_64_PRIME},
            anemoi_cico::{dispatch_anemoi_cico, AnemoiCico, AnemoiCicoVisitor},
            challenge, published_quotient_dimension, registry, ChallengeManifest,
        },
        solve_from_lex_basis, F4Options, HilbertSeries, InterreductionRoute, SolveOptions,
        SolveOutcome,
    },
    util::peak_resident_bytes,
    KnownOrder, Monomial, MonomialOrder, MultivariatePolynomial,
};

/// `2^64 - 353`, the characteristic the published ladder is over.
type A64 = Zp18446744073709551263;

/// `2^32 - 209`. `PrimeFieldElement64` is const-generic, so the second characteristic of #283
/// needed no new field code — only this line.
type A32 = PrimeFieldElement64<ANEMOI_32_PRIME>;

/// `65537`, #283's control characteristic.
type A17 = PrimeFieldElement64<ANEMOI_17_PRIME>;

/// Call `$body::<F>()` with the field the manifest's own prime names.
///
/// A macro rather than a trait object because every path below is generic over `F: KnownOrder` and
/// a `dyn` boundary cannot carry the `const N` dispatch underneath it. `anemoi_cico_instance`
/// rejects a mismatched field, so picking the wrong arm here fails loudly rather than quietly
/// measuring Anemoi over the wrong characteristic.
macro_rules! with_field {
    ($prime:expr, $body:ident($($arg:expr),* $(,)?)) => {
        match $prime {
            ANEMOI_64_PRIME => $body::<A64>($($arg),*),
            ANEMOI_32_PRIME => $body::<A32>($($arg),*),
            ANEMOI_17_PRIME => $body::<A17>($($arg),*),
            prime => panic!("no field is wired for p = {prime}"),
        }
    };
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let command = arguments.first().map(String::as_str).unwrap_or("list");
    match command {
        "list" => list(),
        "dimensions" => dimensions(arguments.get(1).map(String::as_str)),
        "shape" => shape(arguments.get(1).map(String::as_str)),
        "budgets" => budgets(arguments.get(1).map(String::as_str)),
        "peak" => {
            let id = arguments
                .get(1)
                .expect("usage: anemoi_ladder peak <challenge-id>");
            peak(id);
        }
        "msolve" => {
            let id = arguments
                .get(1)
                .expect("usage: anemoi_ladder msolve <challenge-id>");
            emit_msolve(id);
        }
        "row" => {
            let id = arguments
                .get(1)
                .expect("usage: anemoi_ladder row <challenge-id>");
            row(id);
        }
        other => panic!(
            "usage: anemoi_ladder [list | dimensions [id-substring] | shape [id-substring] | \
             budgets [id-substring] | peak <challenge-id> | msolve <challenge-id> | \
             row <challenge-id>]; got {other}"
        ),
    }
}

/// Every registered Anemoi row, with the published figures it is to be read against.
fn list() {
    println!("# the registered Anemoi ladder\n");
    println!("| row | variables | generators | degrees | published basis | published conversion |");
    println!("|---|---:|---:|---|---|---|");
    for manifest in anemoi_rows() {
        let parameters = manifest.anemoi_parameters().expect("an Anemoi row");
        let model = manifest.anemoi_model().expect("an Anemoi row");
        let degrees: Vec<String> = model
            .generator_degrees(parameters.rounds, parameters.alpha)
            .iter()
            .map(|d| d.to_string())
            .collect();
        let figure = |index: usize| match manifest.reference_points.get(index) {
            Some(point) => point.reported_time.to_string(),
            None => "not published".to_string(),
        };
        println!(
            "| `{}` | {} | {} | {} | {} | {} |",
            manifest.id,
            manifest.variables().expect("a size"),
            manifest.equations().expect("a size"),
            degrees.join(", "),
            figure(0),
            figure(1),
        );
    }
    println!(
        "\nPublished figures are Magma V2.26-2 on an Intel Xeon E5-2630 v3 @ 2.40 GHz \
         (Six Worlds). They are not a head-to-head with this machine; see \
         docs/research/anemoi.md section 8."
    );
}

/// The machine-independent check, and the one that gates everything else.
///
/// Exits nonzero on a disagreement rather than printing a table entry: `dim F_p[x]/I` does not
/// depend on the machine, the library or the wall clock, so a mismatch is a defect in Zeebra or in
/// the model.
fn dimensions(filter: Option<&str>) {
    println!("# quotient dimension against (alpha + 2)^N\n");
    println!("| row | variables | observed D | published D | agrees |");
    println!("|---|---:|---:|---:|---|");
    let mut disagreements = 0;
    let mut checked = 0;
    for manifest in anemoi_rows() {
        if let Some(filter) = filter {
            if !manifest.id.contains(filter) {
                continue;
            }
        }
        let prime = manifest.anemoi_parameters().expect("an Anemoi row").prime;
        disagreements += with_field!(prime, one_dimension(&manifest));
        checked += 1;
    }
    assert!(checked > 0, "no registered Anemoi row matched the filter");
    println!(
        "\nMachine-independent: no environment is pinned for this check and none is needed. The \
         published value is Claim::Observed, not Claim::Proved -- it is a measurement from one \
         implementation, and the designers' corresponding statement is a conjecture."
    );
    if disagreements > 0 {
        eprintln!(
            "{disagreements} row(s) disagree with (alpha + 2)^N; this is a defect, not a timing"
        );
        std::process::exit(1);
    }
}

/// One row's quotient dimension against `(α + 2)^N`, printed; returns 1 on a disagreement.
fn one_dimension<F: KnownOrder>(manifest: &ChallengeManifest) -> usize {
    let parameters = manifest.anemoi_parameters().expect("an Anemoi row");
    let instance = manifest
        .anemoi_cico_instance::<F>()
        .expect("the registered field");
    let published = *published_quotient_dimension(parameters.alpha, parameters.rounds).value();
    let observed = match dispatch_anemoi_cico::<F, _>(&instance, Dimension(parameters.rounds)) {
        Ok(DimensionOutcome::Finite(dimension)) => dimension,
        Ok(DimensionOutcome::PositiveDimensional {
            basis_elements,
            without_pure_power,
        }) => {
            println!(
                "| `{}` | {} | positive-dimensional | {} | **no** |",
                manifest.id,
                instance.variables(),
                published
            );
            eprintln!(
                "{}: positive-dimensional against a published D of {}. The degrevlex basis has {} \
                 elements and no pure power of variable(s) {:?} appears among their leading \
                 monomials, which is why socle_degree_bound has no bound. Either the generator is \
                 wrong at this round count or the basis is incomplete; an independent engine on \
                 the same system tells them apart.",
                manifest.id, published, basis_elements, without_pure_power
            );
            return 1;
        }
        Ok(DimensionOutcome::NoBasis(why)) => {
            println!(
                "| `{}` | {} | not reached ({}) | {} | — |",
                manifest.id,
                instance.variables(),
                why,
                published
            );
            return 0;
        }
        Err(e) => {
            println!(
                "| `{}` | {} | not reached ({}) | {} | — |",
                manifest.id,
                instance.variables(),
                e,
                published
            );
            return 0;
        }
    };
    let agrees = observed == published;
    println!(
        "| `{}` | {} | {} | {} | {} |",
        manifest.id,
        instance.variables(),
        observed,
        published,
        if agrees { "yes" } else { "**no**" }
    );
    usize::from(!agrees)
}

/// One row, staged, with the environment pinned.
fn row(id: &str) {
    let manifest = challenge(id).unwrap_or_else(|| panic!("{id} is not registered"));
    assert_eq!(
        manifest.parameters.family(),
        "anemoi-cico",
        "{id} is not an Anemoi row"
    );
    let (machine, affinity) = match (
        std::env::var("ZEEBRA_MACHINE"),
        std::env::var("ZEEBRA_AFFINITY"),
    ) {
        (Ok(machine), Ok(affinity)) => (machine, affinity),
        _ => {
            eprintln!(
                "refusing to time anything: set ZEEBRA_MACHINE and ZEEBRA_AFFINITY, and run under \
                 tools/benchlock.sh so the measurement is serialized against other agents. An \
                 unpinned wall-clock figure is not a measurement, and `dimensions` is the \
                 subcommand that needs no environment."
            );
            std::process::exit(2);
        }
    };

    let parameters = manifest.anemoi_parameters().expect("an Anemoi row");
    with_field!(parameters.prime, run_row(&manifest, &machine, &affinity));
}

/// One row, over the field its own parameters name.
fn run_row<F: KnownOrder>(manifest: &ChallengeManifest, machine: &str, affinity: &str) {
    let parameters = manifest.anemoi_parameters().expect("an Anemoi row");
    let instance = manifest
        .anemoi_cico_instance::<F>()
        .expect("the registered field");
    println!("# {} ({})", manifest.id, manifest.class);
    println!("- field:    p = {}", parameters.prime);
    println!("- digest:   {}", manifest.digest());
    println!("- machine:  {machine}, affinity {affinity}");
    println!("- derived:  {}", instance.anemoi.derived_digest());
    println!(
        "- size:     {} variables, {} generators, degrees {:?}",
        instance.variables(),
        instance.equations(),
        manifest
            .anemoi_model()
            .expect("an Anemoi row")
            .generator_degrees(parameters.rounds, parameters.alpha)
    );
    for point in manifest.reference_points {
        println!("- published: {point}");
    }

    let stages = dispatch_anemoi_cico::<F, _>(&instance, Solve(&instance, parameters.rounds))
        .expect("a compiled dimension");
    println!("\n| stage | elapsed | detail |");
    println!("|---|---:|---|");
    for (stage, elapsed, detail) in &stages.steps {
        println!("| {} | {:?} | {} |", stage, elapsed, detail);
    }
    let total: Duration = stages.steps.iter().map(|(_, elapsed, _)| *elapsed).sum();
    println!("| **total** | {total:?} | |");

    match stages.witness {
        Some(witness) => {
            // Checked through the permutation, not through the system that produced it.
            assert!(
                instance.is_solution(witness),
                "the recovered root is not a CICO solution of the permutation"
            );
            println!(
                "\nwitness: Anemoi(0, {}) has first output word zero, checked through the \
                 permutation. {}",
                witness,
                manifest.significance(true)
            );
        }
        None => println!("\nno witness recovered; {}", manifest.significance(false)),
    }
    println!(
        "\nThe published figures above are Magma on a 2015-era Xeon. Report the stage split, or \
         the ratio with both machines named -- never the ratio alone."
    );
}

/// Shape position on the registered rows — machine-independent, like `dimensions`.
///
/// Whether `1, t, ..., t^{D-1}` is a basis of `R/I` is an algebraic fact, so this subcommand pins
/// no environment and prints no clock. It is #224's question 2, and `fglm::shape` had never been
/// run on a cryptanalytic system: `MILESTONE-FGLM-SCALABILITY.md` §8.3's measured reach is the
/// katsura family, nothing else in the benchmark corpus, and 76 of 120 differential fixtures.
///
/// Filter, because the cost is the *basis*: `n1`–`n4` are seconds, `n5` is a minute and `n6` does
/// not reach a basis at all (#323). `tests/anemoi_shape_position.rs` pins `n1` and `n2` in the
/// suite.
fn shape(filter: Option<&str>) {
    println!("# shape position on the registered Anemoi rows\n");
    // "variables" and not "N": the models use 2N and N+1 variables for the same round count, so a
    // column headed N would read as the rung on one model and not the other.
    println!("| row | variables | D | deg of last variable | separating variables | shape basis |");
    println!("|---|---:|---:|---:|---|---|");
    let mut misses = 0;
    let mut checked = 0;
    for manifest in anemoi_rows() {
        if let Some(filter) = filter {
            if !manifest.id.contains(filter) {
                continue;
            }
        }
        let prime = manifest.anemoi_parameters().expect("an Anemoi row").prime;
        misses += with_field!(prime, one_shape(&manifest));
        checked += 1;
    }
    assert!(checked > 0, "no registered Anemoi row matched the filter");
    println!(
        "\nMachine-independent: a minimal-polynomial degree against a quotient dimension. \
         `ACICO` (#201) is the model whose shape position is *proved* -- syntactically, from \
         eprint 2025/814 section 5 -- so a miss there would be a detector defect. These two models \
         carry no such proof, so a miss here would be a fact about the model."
    );
    if misses > 0 {
        eprintln!("{misses} row(s) are not in shape position in the lex-last variable");
    }
}

/// One row's shape-position probe, printed; returns 1 when the lex-last variable does not separate.
fn one_shape<F: KnownOrder>(manifest: &ChallengeManifest) -> usize {
    let parameters = manifest.anemoi_parameters().expect("an Anemoi row");
    let instance = manifest
        .anemoi_cico_instance::<F>()
        .expect("the registered field");
    let variables = instance.variables();
    let outcome = dispatch_anemoi_cico::<F, _>(&instance, Shape(parameters.rounds))
        .expect("a compiled dimension");
    match outcome {
        ShapeOutcome::Probed {
            dimension,
            minimal_polynomial_degree,
            separating,
            agrees,
        } => {
            let separating = if separating.is_empty() {
                "none".to_string()
            } else {
                separating
                    .iter()
                    .map(|v| format!("x_{v}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            };
            println!(
                "| `{}` | {} | {} | {} | {} | {} |",
                manifest.id,
                variables,
                dimension,
                minimal_polynomial_degree,
                separating,
                match agrees {
                    Some(true) => "**yes**, equal to the classical conversion's",
                    Some(false) => "**WRONG** -- differs from the classical conversion's",
                    None => "no -- not separating",
                }
            );
            assert_ne!(
                agrees,
                Some(false),
                "{}: the shape route produced a different lex basis from the classical \
                 conversion's, and the reduced lex basis is unique",
                manifest.id
            );
            usize::from(minimal_polynomial_degree != dimension)
        }
        ShapeOutcome::NotReached(why) => {
            println!(
                "| `{}` | {} | not reached ({}) | — | — | — |",
                manifest.id, variables, why
            );
            0
        }
    }
}

/// Does one variable's Krylov sequence span the quotient, and does the shape route agree?
///
/// The route is compared against the classical conversion rather than trusted: the reduced lex
/// basis is unique, so equality is the whole correctness statement. That is how
/// `examples/fglm_ablation.rs` validates every other FGLM strategy.
struct Shape(usize);

impl<F: KnownOrder> AnemoiCicoVisitor<F> for Shape {
    type Output = ShapeOutcome;

    fn visit<const N: usize>(self, system: &[MultivariatePolynomial<N, F>]) -> ShapeOutcome {
        let order = MonomialOrder::GradedReverseLexicographic;
        let (basis, f4) = f4_reported(system, order, &basis_options(self.0));
        let basis = match basis {
            Ok(basis) => basis,
            Err(e) => {
                return ShapeOutcome::NotReached(format!(
                    "F4 refused: {e} -- peak live nonzeros {}",
                    f4.max_live_nonzeros
                ))
            }
        };
        // Unbounded, because the budgets exist to stop a caller paying for a conversion by
        // accident and this is a deliberate diagnostic. `recommended()` caps `D` at 4 096, which
        // would refuse the `N = 6` rung on a budget rather than on the algebra.
        let options = FglmOptions::unbounded();
        let algebra = match QuotientAlgebra::new(&basis, order, &options) {
            Ok(algebra) => algebra,
            Err(e) => return ShapeOutcome::NotReached(format!("no quotient algebra: {e}")),
        };
        let report = shape_report(&algebra, N - 1);
        let agrees = match shape_lex_basis(&algebra) {
            Ok(shape) => match fglm_to_lex_with_options(&basis, order, &options) {
                Ok((classical, _)) => Some(shape == classical),
                Err(e) => return ShapeOutcome::NotReached(format!("no classical basis: {e}")),
            },
            Err(_) => None,
        };
        ShapeOutcome::Probed {
            dimension: report.dimension,
            minimal_polynomial_degree: report.minimal_polynomial_degree,
            separating: separating_variables(&algebra),
            agrees,
        }
    }
}

/// What the shape-position probe found.
enum ShapeOutcome {
    /// The quotient algebra was built and probed.
    Probed {
        /// `dim F_p[x]/I`.
        dimension: usize,
        /// The degree of `x_{N-1}`'s minimal polynomial; equal to `dimension` iff it separates.
        minimal_polynomial_degree: usize,
        /// Every variable whose powers span the quotient.
        separating: Vec<usize>,
        /// Whether the shape route's lex basis equalled the classical conversion's; `None` when
        /// the shape route declined because the lex-last variable does not separate.
        agrees: Option<bool>,
    },

    /// The probe did not get far enough to have an opinion.
    NotReached(String),
}

/// Which F4 budget binds at this rung, and under which configuration — counts, so no clock.
///
/// #322 and #323 were both filed after a budget was discovered by being refused at it, and both
/// treated the crossing as a property of the *system*. It is a property of the system **and the
/// strategies**: the budgets below are identical in `F4Options::baseline` and
/// `F4Options::recommended`, so every line here is the same four numbers against a different
/// computation, and a row that is refused under one configuration and completes under another
/// localizes the cost to the strategy rather than to the rung.
///
/// Every run is at the **default budgets**, which is what makes this cheap: a configuration that
/// crosses one is refused early, and one that does not completes and reports a true peak. The
/// peak from a refused run is a lower bound — F4 stops the instant the limit is crossed, so the
/// live count it reports is the limit plus a row, which is why Anemoi `N = 6` `PCICO` looked like
/// a near miss at 20 000 112 of 20 000 000 and peaks 1.42x higher. `peak <id>` lifts the budgets
/// to measure the real one, and is separate because that is the expensive half.
///
/// Filter, for the same reason `shape` has one: the `n5` and `n6` rows are where the question is.
fn budgets(filter: Option<&str>) {
    println!("# which F4 budget binds, by rung and by configuration\n");
    println!(
        "| row | variables | configuration | outcome | batches | peak rows | peak columns | \
         peak live nonzeros | budget pressure |"
    );
    println!("|---|---:|---|---|---:|---:|---:|---:|---|");
    let mut checked = 0;
    for manifest in anemoi_rows() {
        if let Some(filter) = filter {
            if !manifest.id.contains(filter) {
                continue;
            }
        }
        let prime = manifest.anemoi_parameters().expect("an Anemoi row").prime;
        with_field!(prime, one_budget_row(&manifest));
        checked += 1;
    }
    assert!(checked > 0, "no registered Anemoi row matched the filter");
    println!(
        "\nEvery figure is a count and reproduces on any machine. `+` marks a peak from a refused \
         run, which is a lower bound. Budget pressure is `F4Statistics::near_budget` at 80% \
         against the configuration's own budgets (#468), worst first. The configurations vary one \
         strategy each from `F4Options::default()`; `both off` is the default as it stood before \
         #575 moved the two interreduction flags together."
    );
}

/// The configurations one rung is run under, each at the default budgets.
///
/// Named for what they vary from `F4Options::default()`, not for what they are, because the
/// question is which strategy moves the binding budget.
fn budget_configurations() -> Vec<(&'static str, F4Options)> {
    let default = F4Options::default();
    vec![
        ("`default`", default.clone()),
        (
            "`reduce_batch_rows: false`",
            F4Options {
                reduce_batch_rows: false,
                ..default.clone()
            },
        ),
        (
            "`interreduction: Division`",
            F4Options {
                interreduction: InterreductionRoute::Division,
                ..default.clone()
            },
        ),
        (
            "both off (the pre-#575 default)",
            F4Options {
                reduce_batch_rows: false,
                interreduction: InterreductionRoute::Division,
                ..default
            },
        ),
    ]
}

/// One row, once per configuration, printed as it goes.
///
/// Printed inside the loop rather than collected, because a configuration that does not return is
/// the result for that line and a collected table would lose every line before it.
struct Budgets {
    id: String,
    variables: usize,
}

impl<F: KnownOrder> AnemoiCicoVisitor<F> for Budgets {
    type Output = ();

    fn visit<const N: usize>(self, system: &[MultivariatePolynomial<N, F>]) {
        let order = MonomialOrder::GradedReverseLexicographic;
        for (name, options) in budget_configurations() {
            let (basis, statistics) = f4_reported(system, order, &options);
            let outcome = match &basis {
                Ok(basis) => format!("completes, {} elements", basis.len()),
                Err(e) => format!("refused on `{}`", e.limit_name()),
            };
            let pressure: Vec<String> = statistics
                .near_budget(&options, 0.8)
                .iter()
                .map(|approach| {
                    format!(
                        "{} at {:.0}%",
                        approach.budget,
                        100.0 * approach.utilisation()
                    )
                })
                .collect();
            println!(
                "| `{}` | {} | {} | {} | {} | {} | {} | {}{} | {} |",
                self.id,
                self.variables,
                name,
                outcome,
                statistics.batches,
                statistics.max_matrix_rows,
                statistics.max_matrix_columns,
                statistics.max_live_nonzeros,
                if basis.is_ok() { "" } else { "+" },
                pressure.join("; "),
            );
        }
    }
}

/// One row's configurations, dispatched on the compiled variable count.
fn one_budget_row<F: KnownOrder>(manifest: &ChallengeManifest) {
    let instance = manifest
        .anemoi_cico_instance::<F>()
        .expect("the registered field");
    dispatch_anemoi_cico::<F, _>(
        &instance,
        Budgets {
            id: manifest.id.to_string(),
            variables: manifest.variables().expect("a size"),
        },
    )
    .expect("a compiled variable count")
}

/// What one row's F4 actually needs, with every resource budget lifted out of the way.
///
/// The expensive half of `budgets`, and separate from it for that reason: a refusal is cheap and a
/// peak is not. **A peak is the only honest input to sizing a budget.** #490 proposes lifting
/// `max_live_nonzeros` to 25 000 000 on the strength of three workloads that crossed 20 000 000 by
/// under 0.05%, and Anemoi `N = 6` `PCICO` is one of them — but that 0.0006% is the overshoot of a
/// run stopped at the limit, and the row's real peak is 28 435 493 (anemoi.md §8a.8). The lift
/// would be refused again.
///
/// Reported per configuration, because the peak is a property of the strategies too.
fn peak(id: &str) {
    let manifest = anemoi_rows()
        .into_iter()
        .find(|c| c.id == id)
        .unwrap_or_else(|| panic!("no registered Anemoi row is called {id}"));
    println!("# {id}: what F4 needs, budgets lifted\n");
    println!(
        "| configuration | outcome | batches | peak rows | peak columns | peak live nonzeros | \
         peak live MB | over the default allowance |"
    );
    println!("|---|---|---:|---:|---:|---:|---:|---:|");
    let prime = manifest.anemoi_parameters().expect("an Anemoi row").prime;
    with_field!(prime, one_peak(&manifest));
    println!(
        "\nBudgets lifted to {} live entries and {} matrix rows/columns; the strategies are each \
         configuration's own and are not lifted, because a peak measured under a different \
         reduction route is a peak for a different computation. The last column is the peak over \
         `F4Options::default()`'s live-entry allowance -- what a correctly sized budget has to \
         clear, as against what a refusal reports.",
        LIFTED_LIVE_ENTRIES, LIFTED_MATRIX_SHAPE
    );
}

/// Live entries the `peak` subcommand admits: 6.4 GB at 16 bytes, against a 4.53 GB observed peak
/// for the heaviest row this family has reached (anemoi.md §8a.8).
const LIFTED_LIVE_ENTRIES: usize = 400_000_000;

/// Rows and columns the `peak` subcommand admits, 20x the default. `FCICO` `N = 6` crossed the
/// 200 000 default in symbolic preprocessing (anemoi.md §8a.8), so this budget has to be lifted
/// too or the row is refused before any entry is counted.
const LIFTED_MATRIX_SHAPE: usize = 4_000_000;

/// Every resource budget lifted, with `strategies`' strategies left exactly as they are.
fn lifted(strategies: F4Options) -> F4Options {
    F4Options {
        max_matrix_rows: LIFTED_MATRIX_SHAPE,
        max_matrix_columns: LIFTED_MATRIX_SHAPE,
        ..strategies.with_live_entries::<A64>(LIFTED_LIVE_ENTRIES)
    }
}

/// One row's peak profile per configuration.
struct Peak;

impl<F: KnownOrder> AnemoiCicoVisitor<F> for Peak {
    type Output = ();

    fn visit<const N: usize>(self, system: &[MultivariatePolynomial<N, F>]) {
        let order = MonomialOrder::GradedReverseLexicographic;
        let allowance = F4Options::default().live_entry_allowance::<F>();
        for (name, strategies) in budget_configurations() {
            let (basis, statistics) = f4_reported(system, order, &lifted(strategies));
            println!(
                "| {} | {} | {} | {} | {} | {}{} | {} | {:.2}x |",
                name,
                match &basis {
                    Ok(basis) => format!("completes, {} elements", basis.len()),
                    Err(e) => format!("refused on `{}`", e.limit_name()),
                },
                statistics.batches,
                statistics.max_matrix_rows,
                statistics.max_matrix_columns,
                statistics.max_live_nonzeros,
                if basis.is_ok() { "" } else { "+" },
                statistics.max_live_nonzeros * statistics.bytes_per_entry / 1_000_000,
                statistics.max_live_nonzeros as f64 / allowance as f64,
            );
        }
    }
}

/// One row's peak profile, dispatched on the compiled variable count.
fn one_peak<F: KnownOrder>(manifest: &ChallengeManifest) {
    let instance = manifest
        .anemoi_cico_instance::<F>()
        .expect("the registered field");
    dispatch_anemoi_cico::<F, _>(&instance, Peak).expect("a compiled variable count")
}

/// The registered Anemoi rows, in registry order.
fn anemoi_rows() -> Vec<ChallengeManifest> {
    registry()
        .into_iter()
        .filter(|c| c.parameters.family() == "anemoi-cico")
        .collect()
}

/// `dim F_p[x]/I`, from the leading-term ideal of the degrevlex basis.
///
/// Combinatorial once F4 has finished, so it costs nothing beyond the basis — which is why this is
/// the check that runs first.
struct Dimension(usize);

impl<F: KnownOrder> AnemoiCicoVisitor<F> for Dimension {
    type Output = DimensionOutcome;

    fn visit<const N: usize>(self, system: &[MultivariatePolynomial<N, F>]) -> DimensionOutcome {
        let order = MonomialOrder::GradedReverseLexicographic;
        let (basis, f4) = f4_reported(system, order, &basis_options(self.0));
        let basis = match basis {
            Ok(basis) => basis,
            Err(e) => {
                return DimensionOutcome::NoBasis(format!(
                    "F4 refused: {e} -- after {} batches at pair degree {}, peak live nonzeros {}",
                    f4.batches, f4.max_pair_degree, f4.max_live_nonzeros
                ))
            }
        };
        let leads: Vec<_> = basis.iter().map(|p| p.leading_monomial(order)).collect();
        let Ok(series) = HilbertSeries::of_basis(&basis, order) else {
            return DimensionOutcome::NoBasis("the Hilbert series was refused".to_string());
        };
        match series.quotient_dimension(&leads) {
            Ok(Some(dimension)) => match u128::try_from(dimension) {
                Ok(dimension) => DimensionOutcome::Finite(dimension),
                Err(_) => DimensionOutcome::NoBasis(format!("dimension {dimension} is negative")),
            },
            // `socle_degree_bound` returns `None` exactly when some variable has no pure power in
            // the minimal leading ideal, which is the zero-dimensionality criterion. Naming those
            // variables is the difference between a verdict and a lead: "positive-dimensional" on
            // a row whose reference publishes a finite `D` does not say whether the generator is
            // wrong or the basis is incomplete, and the missing pure powers point at which.
            Ok(None) => DimensionOutcome::PositiveDimensional {
                basis_elements: basis.len(),
                without_pure_power: variables_without_a_pure_power(&leads),
            },
            Err(e) => DimensionOutcome::NoBasis(format!("the Hilbert series was refused: {e}")),
        }
    }
}

/// What the dimension check found.
enum DimensionOutcome {
    /// `dim F_p[x]/I`, finite.
    Finite(u128),

    /// No pure power of these variables is in the leading ideal, so the quotient is infinite.
    PositiveDimensional {
        /// Elements of the degrevlex basis that was computed.
        basis_elements: usize,
        /// Variable indices with no pure power among the leading monomials.
        without_pure_power: Vec<usize>,
    },

    /// The check did not get far enough to have an opinion.
    NoBasis(String),
}

/// Variable indices with no pure power among `leads`.
///
/// A monomial is a pure power of variable `i` when every other exponent is zero and the `i`th is
/// not. The quotient is finite-dimensional precisely when every variable has one.
fn variables_without_a_pure_power<const N: usize>(leads: &[Monomial<N>]) -> Vec<usize> {
    (0..N)
        .filter(|variable| {
            !leads.iter().any(|lead| {
                lead.exponents()[*variable] > 0
                    && lead
                        .exponents()
                        .iter()
                        .enumerate()
                        .all(|(other, exponent)| other == *variable || *exponent == 0)
            })
        })
        .collect()
}

/// What one staged solve produced.
struct Stages<F> {
    /// `(stage, elapsed, detail)`, in the order the solve took them.
    steps: Vec<(&'static str, Duration, String)>,

    /// The recovered free input word, if any.
    witness: Option<F>,
}

/// F4, then FGLM, then root finding, each timed separately.
///
/// Separately because the published finding is that the conversion costs 2 400x the basis at
/// `N = 5`, and a combined figure would hide it. Which stage is the wall is the result; "it was
/// slower" is not.
struct Solve<'a, F: KnownOrder>(&'a AnemoiCico<F>, usize);

impl<F: KnownOrder> AnemoiCicoVisitor<F> for Solve<'_, F> {
    type Output = Stages<F>;

    fn visit<const N: usize>(self, system: &[MultivariatePolynomial<N, F>]) -> Stages<F> {
        let order = MonomialOrder::GradedReverseLexicographic;
        let mut steps = Vec::new();

        let start = Instant::now();
        let (basis, f4) = f4_reported(system, order, &basis_options(self.1));
        let elapsed = start.elapsed();
        let basis = match basis {
            Ok(basis) => basis,
            Err(e) => {
                steps.push(("grobner", elapsed, format!("did not complete: {e}")));
                return Stages {
                    steps,
                    witness: None,
                };
            }
        };
        steps.push((
            "grobner",
            elapsed,
            format!(
                "{} basis elements, {} batches, highest pair degree {}, peak live nonzeros {}",
                basis.len(),
                f4.batches,
                f4.max_pair_degree,
                f4.max_live_nonzeros
            ),
        ));

        let options = conversion_options::<N, F>(&basis, order);
        let start = Instant::now();
        let conversion = fglm_to_lex_with_options(&basis, order, &options);
        let elapsed = start.elapsed();
        let (lex, fglm) = match conversion {
            Ok(pair) => pair,
            Err(e) => {
                // Printed rather than swallowed: a budget refusal is the result at N = 6, and
                // "did not complete" alone would not say which budget.
                steps.push(("conversion", elapsed, format!("did not complete: {e}")));
                return Stages {
                    steps,
                    witness: None,
                };
            }
        };
        steps.push((
            "conversion",
            elapsed,
            format!(
                "D = {}, {} relations, {} operator entries",
                fglm.quotient_dimension, fglm.target_basis_elements, fglm.operator_entries
            ),
        ));
        report_conversion_footprint(&fglm);

        let start = Instant::now();
        let mut rng = rand::rngs::StdRng::from_seed([7; 32]);
        let solved = solve_from_lex_basis(&lex, system, &SolveOptions::default(), &mut rng);
        let elapsed = start.elapsed();
        let (detail, witness) = match solved {
            Ok((SolveOutcome::Point(point), _)) => {
                // Which coordinate is `y_0` depends on the model, so every coordinate is offered to
                // the permutation and the permutation decides. The point is already verified
                // against the system; this is the independent check.
                let witness = point
                    .iter()
                    .copied()
                    .find(|candidate| self.0.is_solution(*candidate));
                ("a point over the base field".to_string(), witness)
            }
            Ok((SolveOutcome::NoBaseFieldPoint, _)) => {
                ("zero-dimensional, no base-field point".to_string(), None)
            }
            Ok((SolveOutcome::Inconsistent, _)) => ("inconsistent".to_string(), None),
            Err(e) => (format!("did not complete: {e}"), None),
        };
        steps.push(("univariate", elapsed, detail));

        Stages { steps, witness }
    }
}

/// The conversion options for a basis of this quotient dimension, and the pre-flight that chose
/// them, printed before the conversion runs.
///
/// `FglmOptions::recommended` caps `D` at 4 096 and the dense blocks at 20 M cells, which `N = 5`
/// fits with 465 625 cells to spare and `N = 6` exceeds on all four budgets before allocating
/// anything. So at `D > 4 096` this lifts the budgets — and says so, with the figure it computed
/// from `D` alone, so that a run which then dies in the allocator is a predicted outcome rather
/// than a surprise. `unbounded()` resets the strategies to the reference ones, so the two the
/// M18-5 ablation chose are set back explicitly.
fn conversion_options<const N: usize, F: KnownOrder>(
    basis: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
) -> FglmOptions {
    let recommended = FglmOptions {
        measure_stages: true,
        ..FglmOptions::recommended()
    };
    let Some(dimension) = quotient_dimension(basis, order) else {
        return recommended;
    };
    let dimension = usize::try_from(dimension).unwrap_or(usize::MAX);
    let blocks = FglmMemory::dense_blocks_for::<F>(dimension);
    println!(
        "- preflight: D = {dimension}, dense blocks {}",
        match blocks {
            Some((span, accepted, bytes)) => format!(
                "{span} span + {accepted} accepted cells = {:.2} GiB",
                bytes as f64 / (1 << 30) as f64
            ),
            None => "overflow".to_string(),
        }
    );
    if dimension <= recommended.max_quotient_dimension {
        println!("- budgets:   recommended, unchanged");
        return recommended;
    }
    println!(
        "- budgets:   LIFTED -- D = {dimension} exceeds max_quotient_dimension {}, and the dense \
         blocks exceed max_span_entries {}. The strategies stay BatchedBorder + Adaptive; only the \
         limits move, and the figure above is what this run is betting it can hold.",
        recommended.max_quotient_dimension, recommended.max_span_entries
    );
    FglmOptions {
        measure_stages: true,
        ..FglmOptions::unbounded()
            .with_operator_construction(OperatorConstruction::BatchedBorder)
            .with_operator_storage(OperatorStorage::Adaptive)
    }
}

/// `dim F_p[x]/I` from a degrevlex basis, or `None` if it is not zero-dimensional.
fn quotient_dimension<const N: usize, F: KnownOrder>(
    basis: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
) -> Option<u128> {
    let leads: Vec<_> = basis.iter().map(|p| p.leading_monomial(order)).collect();
    let series = HilbertSeries::of_basis(basis, order).ok()?;
    u128::try_from(series.quotient_dimension(&leads).ok()??).ok()
}

/// What the conversion actually held, three ways, beside what the process held.
///
/// Entries, cells and bytes are three different numbers and the extrapolation to `N = 6` depends on
/// not confusing them; `FglmMemory`'s own docs make the distinction and this prints all three. The
/// `peak` line is the process and is **not** attributable to the conversion — it covers F4's peak
/// too, and this binary does one row per invocation so that it means something at all.
fn report_conversion_footprint(fglm: &FglmStatistics) {
    let m = &fglm.memory;
    let gib = |bytes: usize| bytes as f64 / (1 << 30) as f64;
    println!("\n| conversion footprint | value |");
    println!("|---|---:|");
    println!("| quotient dimension `D` | {} |", fglm.quotient_dimension);
    println!("| operator entries | {} |", m.operator_entries);
    println!("| operator cells | {} |", m.operator_cells);
    println!("| operator bytes | {:.3} GiB |", gib(m.operator_bytes));
    println!("| dense columns of `N*D` | {} |", m.dense_columns);
    println!("| span cells | {} |", m.span_cells);
    println!("| accepted-vector cells | {} |", m.accepted_vector_cells);
    println!(
        "| dense-block bytes | {:.3} GiB |",
        gib(m.dense_block_bytes)
    );
    println!("| estimated total | {:.3} GiB |", gib(m.estimated_bytes()));
    println!("| span row operations | {} |", fglm.span_row_operations);
    match peak_resident_bytes() {
        Some(peak) => println!(
            "| process peak RSS | {:.3} GiB |",
            peak as f64 / (1u64 << 30) as f64
        ),
        None => println!("| process peak RSS | unavailable |"),
    }

    let t = &fglm.timings;
    println!("\n| conversion stage | elapsed | share |");
    println!("|---|---:|---:|");
    let sum = t.sum().as_secs_f64();
    let share = |d: Duration| {
        if sum > 0.0 {
            format!("{:.1}%", 100.0 * d.as_secs_f64() / sum)
        } else {
            "-".to_string()
        }
    };
    for (name, elapsed) in [
        ("quotient basis", t.quotient_basis),
        ("border classification", t.border_classification),
        ("normal forms (scalar)", t.normal_forms),
        ("border symbolic (batched)", t.border_symbolic),
        ("column assembly", t.column_assembly),
        ("lex walk / dependence", t.dependence),
    ] {
        println!("| {name} | {elapsed:?} | {} |", share(elapsed));
    }
    println!("| **measured sum** | {:?} | |", t.sum());
}

/// The row's generators in msolve's input format, on stdout.
///
/// Exists so that the #283 verdict can rest on a **same-machine** comparand rather than only on a
/// cross-machine ratio against 2015-era Magma. msolve's modular path wants a prime under `2^31`, so
/// this is usable at `p = 65537` and `p = 2^32 - 209` and not at `p = 2^64 - 353` — which is why
/// #283's control characteristic is the one that can carry the comparison.
///
/// Three lines of header then one polynomial per line, comma-separated with no trailing comma, as
/// `msolve -h` specifies. The variable order is the generator's own, so `x0` is this crate's
/// variable 0 and the orderings are the same degrevlex.
fn emit_msolve(id: &str) {
    let manifest = challenge(id).unwrap_or_else(|| panic!("{id} is not registered"));
    let prime = manifest.anemoi_parameters().expect("an Anemoi row").prime;
    with_field!(prime, write_msolve(&manifest));
}

/// [`emit_msolve`] over the field the row names.
fn write_msolve<F: KnownOrder>(manifest: &ChallengeManifest) {
    struct Emit;
    impl<F: KnownOrder> AnemoiCicoVisitor<F> for Emit {
        type Output = ();
        fn visit<const N: usize>(self, system: &[MultivariatePolynomial<N, F>]) {
            let names: Vec<String> = (0..N).map(|i| format!("x{i}")).collect();
            println!("{}", names.join(","));
            println!("{}", F::order_limbs()[0]);
            let lines: Vec<String> = system
                .iter()
                .map(|p| {
                    let mut terms: Vec<String> = p
                        .terms()
                        .iter()
                        .map(|(monomial, c)| {
                            let mut factors = vec![format!("{c}")];
                            for (i, e) in monomial.exponents().iter().enumerate() {
                                if *e > 0 {
                                    factors.push(format!("{}^{}", names[i], e));
                                }
                            }
                            factors.join("*")
                        })
                        .collect();
                    // Sorted so the emitted file is byte-stable across runs; `terms()` is a
                    // HashMap and its iteration order is not.
                    terms.sort();
                    if terms.is_empty() {
                        "0".to_string()
                    } else {
                        terms.join("+")
                    }
                })
                .collect();
            println!("{}", lines.join(",\n"));
        }
    }
    let instance = manifest
        .anemoi_cico_instance::<F>()
        .expect("the registered field");
    dispatch_anemoi_cico::<F, _>(&instance, Emit).expect("a compiled dimension");
}

/// The F4 options for a row at this round count, with the budgets that bind at `N = 6` lifted.
///
/// `F4Options::recommended`'s `max_live_nonzeros` of 20 M — 320 MB at 16 bytes an entry — is not a
/// generous limit here and not a mistaken one either, and `N = 6` crosses it in both models. The
/// default is right for a library call and wrong for a run whose whole purpose is to reach the
/// next rung, so this lifts it for `N >= 6`.
///
/// **Three of the four budgets below were sized against refusals, and section 8a.9 re-measured the
/// peaks they were standing in for.** Two consequences, neither of which moves a number here:
///
///   * the live-entry lift is the only one the default still needs. #575 cut `N = 6` `PCICO`'s
///     peak matrix from 82 608 x 97 388 rows to 23 211 x 35 246 and `FCICO`'s row count by 11.7x,
///     so `max_matrix_rows` and `max_matrix_columns` no longer bind at this rung under the
///     default — they bind under `reduce_batch_rows: false`, which this runner does not set but a
///     reader comparing against `F4Options::baseline` would;
///   * 200 000 000 is 8.3x the measured `PCICO` peak of 24 011 204 rather than the 10x-over-a-near-
///     miss it was written as. The margin is the point and is kept: the quantity moved by 14.6x on
///     one rung in one commit (section 8a.9), so a lift sized tightly against today's peak would
///     be a lift that has to be revisited.
///
/// Lifted for `N >= 6` only, so the `N <= 5` figures in `docs/research/anemoi.md` section 8a.3 stay
/// reproducible from this binary: a budget that never binds does not change a result, but a run
/// taken under different options is not the same measurement and should not look like one. Section
/// 8a.9 records that `N = 5` `FCICO` **no longer** completes under the default, which is a change
/// in the default rather than in this function.
fn basis_options(rounds: usize) -> F4Options {
    let recommended = F4Options::recommended();
    if rounds < 6 {
        return recommended;
    }
    // Four budgets, not one, and each was found by a separate refusal rather than by reading the
    // struct — which is the #322 pattern three times over:
    //
    //   * `max_live_nonzeros`, crossed by PCICO N = 6 by 112 entries in 20 million;
    //   * `max_live_bytes`, which must move with it because the allowance is the *min* of the two
    //     and 320 MB / 16 is exactly the same 20 M, so lifting the entry count alone is a no-op.
    //     `with_live_entries` now sets the pair from one number, so this no longer has to be kept
    //     in step by hand — which is the half of #322 this workaround was standing in for;
    //   * `max_matrix_rows`, crossed by FCICO N = 6 in symbolic preprocessing after 3.8 s. For
    //     reference the published Magma run on this exact row peaks at 173 808 x 189 401, *inside*
    //     the 200 000 default — so this crate's preprocessing enumerates more rows than Magma's for
    //     the same system, and the default is not obviously the wrong size for a library;
    //   * `max_matrix_columns`, lifted with it because a matrix wide enough to need the rows will
    //     need the columns, and discovering that with a second 4-second refusal is waste.
    //
    // The row and column counts are not a memory budget: memory is bounded by the live-entry
    // budget above, and a sparse row costs what its entries cost. Printed rather than silent, for
    // the same reason the conversion pre-flight is printed.
    let lifted = 200_000_000;
    let lifted_rows = 4_000_000;
    let budget = recommended.clone().with_live_entries::<A64>(lifted);
    let lifted_bytes = budget.max_live_bytes;
    println!(
        "- f4 budget: LIFTED to {lifted} live nonzeros ({lifted_bytes} bytes) from {} ({}), and \
         to {lifted_rows} matrix rows/columns from {}/{} -- N = {rounds} crosses all four, each \
         found by a separate refusal. A refused basis is not a statement about the ideal.",
        recommended.max_live_nonzeros,
        recommended.max_live_bytes,
        recommended.max_matrix_rows,
        recommended.max_matrix_columns
    );
    F4Options {
        max_matrix_rows: lifted_rows,
        max_matrix_columns: lifted_rows,
        ..budget
    }
}
