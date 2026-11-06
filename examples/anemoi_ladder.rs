//! The runner for the registered Anemoi ladder, read in the order that keeps it honest.
//!
//! Three subcommands, and the split between them is the point.
//!
//! - `list` prints the registered rows with their published per-step figures.
//! - `dimensions [id-substring]` computes `dim F_p[x]/I` and checks it against `(α + 2)^N`.
//!   **Machine-independent**, so it needs no pinned environment and a disagreement is a defect
//!   rather than a timing. The optional filter exists because the `N = 6` rows cost minutes of F4
//!   each and the gate is worth running on them alone.
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
            fglm_to_lex_with_options, FglmMemory, FglmOptions, FglmStatistics,
            OperatorConstruction, OperatorStorage,
        },
        research::{
            anemoi::{ANEMOI_17_PRIME, ANEMOI_32_PRIME, ANEMOI_64_PRIME},
            anemoi_cico::{dispatch_anemoi_cico, AnemoiCico, AnemoiCicoVisitor},
            challenge, published_quotient_dimension, registry, ChallengeManifest,
        },
        solve_from_lex_basis, F4Options, HilbertSeries, SolveOptions, SolveOutcome,
    },
    util::peak_resident_bytes,
    KnownOrder, MonomialOrder, MultivariatePolynomial,
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
            "usage: anemoi_ladder [list | dimensions [id-substring] | msolve <challenge-id> | \
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
    let observed = match dispatch_anemoi_cico::<F, _>(&instance, Dimension) {
        Ok(Some(dimension)) => dimension,
        Ok(None) => {
            println!(
                "| `{}` | {} | positive-dimensional | {} | **no** |",
                manifest.id,
                instance.variables(),
                published
            );
            return 1;
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

    let stages =
        dispatch_anemoi_cico::<F, _>(&instance, Solve(&instance)).expect("a compiled dimension");
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

impl<F: KnownOrder> AnemoiCicoVisitor<F> for Dimension {
    type Output = Option<u128>;

    fn visit<const N: usize>(self, system: &[MultivariatePolynomial<N, F>]) -> Option<u128> {
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
struct Solve<'a, F: KnownOrder>(&'a AnemoiCico<F>);

impl<F: KnownOrder> AnemoiCicoVisitor<F> for Solve<'_, F> {
    type Output = Stages<F>;

    fn visit<const N: usize>(self, system: &[MultivariatePolynomial<N, F>]) -> Stages<F> {
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
        report_conversion_footprint::<F>(&fglm);

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
fn report_conversion_footprint<F: KnownOrder>(fglm: &FglmStatistics) {
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
