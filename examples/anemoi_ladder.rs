//! The runner for the registered Anemoi ladder, read in the order that keeps it honest.
//!
//! Three subcommands, and the split between them is the point.
//!
//! - `list` prints the ten registered rows with their published per-step figures.
//! - `dimensions` computes `dim F_p[x]/I` and checks it against `(α + 2)^N`. **Machine-independent**,
//!   so it needs no pinned environment and a disagreement is a defect rather than a timing.
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
//! ZEEBRA_MACHINE=... ZEEBRA_AFFINITY=... tools/benchlock.sh \
//!     cargo run --release --example anemoi_ladder row anemoi64-cico-n3-fcico
//! ```

use std::time::{Duration, Instant};

use rand::SeedableRng;
use zeebra::{
    fields::Zp18446744073709551263,
    grobner::{
        f4_reported,
        fglm::{fglm_to_lex_with_options, FglmOptions},
        research::{
            anemoi_cico::{dispatch_anemoi_cico, AnemoiCico, AnemoiCicoVisitor},
            challenge, published_quotient_dimension, registry, ChallengeManifest,
        },
        solve_from_lex_basis, F4Options, HilbertSeries, SolveOptions, SolveOutcome,
    },
    MonomialOrder, MultivariatePolynomial,
};

/// The field every registered Anemoi row is over.
type A = Zp18446744073709551263;

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let command = arguments.first().map(String::as_str).unwrap_or("list");
    match command {
        "list" => list(),
        "dimensions" => dimensions(),
        "row" => {
            let id = arguments
                .get(1)
                .expect("usage: anemoi_ladder row <challenge-id>");
            row(id);
        }
        other => {
            panic!("usage: anemoi_ladder [list | dimensions | row <challenge-id>]; got {other}")
        }
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
fn dimensions() {
    println!("# quotient dimension against (alpha + 2)^N\n");
    println!("| row | variables | observed D | published D | agrees |");
    println!("|---|---:|---:|---:|---|");
    let mut disagreements = 0;
    for manifest in anemoi_rows() {
        let parameters = manifest.anemoi_parameters().expect("an Anemoi row");
        let instance = manifest
            .anemoi_cico_instance::<A>()
            .expect("the registered field");
        let published = *published_quotient_dimension(parameters.alpha, parameters.rounds).value();
        let observed = match dispatch_anemoi_cico::<A, _>(&instance, Dimension) {
            Ok(Some(dimension)) => dimension,
            Ok(None) => {
                println!(
                    "| `{}` | {} | positive-dimensional | {} | **no** |",
                    manifest.id,
                    instance.variables(),
                    published
                );
                disagreements += 1;
                continue;
            }
            Err(e) => {
                println!(
                    "| `{}` | {} | not reached ({}) | {} | — |",
                    manifest.id,
                    instance.variables(),
                    e,
                    published
                );
                continue;
            }
        };
        let agrees = observed == published;
        if !agrees {
            disagreements += 1;
        }
        println!(
            "| `{}` | {} | {} | {} | {} |",
            manifest.id,
            instance.variables(),
            observed,
            published,
            if agrees { "yes" } else { "**no**" }
        );
    }
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
    let instance = manifest
        .anemoi_cico_instance::<A>()
        .expect("the registered field");
    println!("# {} ({})", manifest.id, manifest.class);
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

    let stages =
        dispatch_anemoi_cico::<A, _>(&instance, Solve(&instance)).expect("a compiled dimension");
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
                witness.value(),
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
struct Dimension;

impl AnemoiCicoVisitor<A> for Dimension {
    type Output = Option<u128>;

    fn visit<const N: usize>(self, system: &[MultivariatePolynomial<N, A>]) -> Option<u128> {
        let order = MonomialOrder::GradedReverseLexicographic;
        let (basis, _) = f4_reported(system, order, &F4Options::default());
        let basis = basis.ok()?;
        let leads: Vec<_> = basis.iter().map(|p| p.leading_monomial(order)).collect();
        let series = HilbertSeries::of_basis(&basis, order).ok()?;
        let dimension = series.quotient_dimension(&leads).ok()??;
        u128::try_from(dimension).ok()
    }
}

/// What one staged solve produced.
struct Stages {
    /// `(stage, elapsed, detail)`, in the order the solve took them.
    steps: Vec<(&'static str, Duration, String)>,

    /// The recovered free input word, if any.
    witness: Option<A>,
}

/// F4, then FGLM, then root finding, each timed separately.
///
/// Separately because the published finding is that the conversion costs 2 400x the basis at
/// `N = 5`, and a combined figure would hide it. Which stage is the wall is the result; "it was
/// slower" is not.
struct Solve<'a>(&'a AnemoiCico<A>);

impl AnemoiCicoVisitor<A> for Solve<'_> {
    type Output = Stages;

    fn visit<const N: usize>(self, system: &[MultivariatePolynomial<N, A>]) -> Stages {
        let order = MonomialOrder::GradedReverseLexicographic;
        let mut steps = Vec::new();

        let start = Instant::now();
        let (basis, f4) = f4_reported(system, order, &F4Options::default());
        let elapsed = start.elapsed();
        let Ok(basis) = basis else {
            steps.push(("grobner", elapsed, "did not complete".to_string()));
            return Stages {
                steps,
                witness: None,
            };
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

        let start = Instant::now();
        let conversion = fglm_to_lex_with_options(&basis, order, &FglmOptions::default());
        let elapsed = start.elapsed();
        let Ok((lex, fglm)) = conversion else {
            steps.push(("conversion", elapsed, "did not complete".to_string()));
            return Stages {
                steps,
                witness: None,
            };
        };
        steps.push((
            "conversion",
            elapsed,
            format!(
                "D = {}, {} relations, {} operator entries",
                fglm.quotient_dimension, fglm.target_basis_elements, fglm.operator_entries
            ),
        ));

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
