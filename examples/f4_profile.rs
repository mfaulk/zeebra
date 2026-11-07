//! Where an F4 computation's time goes, per stage, for a named configuration.
//!
//! `examples/f4_statistics.rs` reports what the algorithm *did* — matrices, rows, fill-in. This
//! reports what it *cost*, broken down by stage, which is the measurement an optimization has to
//! move. The two are complementary: a change that halves the row count and does not shorten the
//! computation is visible here and not there.
//!
//! The stage columns come from `F4Options::measure_stages`, which reads a clock four times per
//! batch, plus once for the final interreduction. `other` is the total less every stage: pair
//! selection and basis bookkeeping. A large `other` means the breakdown is looking in the wrong
//! place.
//!
//! ```text
//! cargo run --release --example f4_profile                 # the baseline, every system
//! cargo run --release --example f4_profile -- baseline     # the same, named
//! cargo run --release --example f4_profile -- list         # the configurations available
//! cargo run --release --example f4_profile -- mq           # #349: the competitive MQ split
//! cargo run --release --example f4_profile -- mq-counts    # that stage's operation counts
//! cargo run --release --example f4_profile -- mq-matrix    # #471: the two interreduction routes
//! cargo run --release --example f4_profile -- mq-instance   # that instance's canonical text
//! ```
//!
//! `mq-instance` emits the digest-pinned instance rather than a measurement, so that an external
//! engine can be driven on the same ideal and its own counters compared against the columns here
//! (#447). The text is `Instance::canonical`, which is what the digest is taken over, so a
//! consumer in another language can re-derive the digest and refuse a mismatch.
//!
//! Each configuration is one row of the milestone's ablation table. They are named here rather
//! than assembled at each call site so that every workstream reports the same thing.

use std::time::Duration;

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura, planted},
        external::{instance, REFERENCE_CHARACTERISTIC},
        f4_with_options, CacheMode, F4Options, F4Statistics, PairCriteria, ReducerSelection,
        ReductionStrategy,
    },
    linalg::Backend,
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

type F = Zp2147483647;

const ALL: [(&str, MonomialOrder); 3] = [
    ("lex", MonomialOrder::Lexicographic),
    ("grlex", MonomialOrder::GradedLexicographic),
    ("grevlex", MonomialOrder::GradedReverseLexicographic),
];

const GRADED: [(&str, MonomialOrder); 2] = [
    ("grlex", MonomialOrder::GradedLexicographic),
    ("grevlex", MonomialOrder::GradedReverseLexicographic),
];

/// The configurations of the ablation study, by name.
///
/// Every one starts from `F4Options::baseline()` and turns on exactly what its name says, so the
/// difference between two rows of the table is the difference between two configurations and
/// nothing else. `measure_stages` is on throughout, including in the baseline, so the overhead of
/// measuring is common to every row.
fn configuration(name: &str) -> Option<F4Options> {
    let base = F4Options {
        measure_stages: true,
        ..F4Options::baseline()
    };
    let options = match name {
        "baseline" => base,
        // A only: structured elimination.
        "a" => F4Options {
            reduction: ReductionStrategy::Structured,
            ..base
        },
        // B only: preprocessing. Two sub-configurations, because the reducer cache has to be
        // measured before it is used, and `count` is how that is done.
        "b" => F4Options {
            reducer_selection: ReducerSelection::LargestLeadingMonomial,
            reducer_cache: CacheMode::Count,
            ..base
        },
        "b-count" => F4Options {
            reducer_cache: CacheMode::Count,
            ..base
        },
        // C only: pair criteria.
        "c" => F4Options {
            criteria: PairCriteria::ALL,
            ..base
        },
        // D only: the linear-algebra backend.
        "d" => F4Options {
            elimination: Backend::Adaptive,
            ..base
        },
        "d-dense" => F4Options {
            elimination: Backend::Dense,
            ..base
        },
        "ab" => F4Options {
            reduction: ReductionStrategy::Structured,
            reducer_selection: ReducerSelection::LargestLeadingMonomial,
            reducer_cache: CacheMode::Count,
            ..base
        },
        "ad" => F4Options {
            reduction: ReductionStrategy::Structured,
            elimination: Backend::Adaptive,
            ..base
        },
        // What the milestone recommends. M16-B's merged contribution is a cheaper monomial hash,
        // which is unconditional and so already in every configuration including `baseline`; its
        // two *optional* strategies were measured and rejected, which is why they are not here.
        "recommended" | "acd" => F4Options {
            reduction: ReductionStrategy::Structured,
            criteria: PairCriteria::ALL,
            elimination: Backend::Adaptive,
            ..base
        },
        // Everything, including what measurement rejected, for the ablation's sake.
        "abcd" => F4Options {
            reduction: ReductionStrategy::Structured,
            reducer_selection: ReducerSelection::LargestLeadingMonomial,
            reducer_cache: CacheMode::Count,
            criteria: PairCriteria::ALL,
            elimination: Backend::Adaptive,
            ..base
        },
        _ => return None,
    };
    Some(options)
}

const CONFIGURATIONS: [&str; 12] = [
    "baseline",
    "a",
    "b",
    "b-count",
    "c",
    "d",
    "d-dense",
    "ab",
    "ad",
    "acd",
    "recommended",
    "abcd",
];

/// A deterministic random system: N quadratics in N variables. Same construction as the benchmark.
fn random_system<const N: usize>(seed: u64) -> Vec<MultivariatePolynomial<N, F>> {
    use rand::{prelude::StdRng, Rng, SeedableRng};
    let mut rng = StdRng::seed_from_u64(seed);
    (0..N)
        .map(|_| {
            let terms: Vec<(zeebra::Monomial<N>, F)> = (0..2 * N)
                .map(|_| {
                    let mut exponents = [0u32; N];
                    exponents[rng.gen_range(0..N)] += 1;
                    if rng.gen_bool(0.5) {
                        exponents[rng.gen_range(0..N)] += 1;
                    }
                    (zeebra::Monomial::new(&exponents), F::random(&mut rng))
                })
                .collect();
            MultivariatePolynomial::new(&terms)
        })
        .collect()
}

fn planted_point<const N: usize>(seed: u64) -> Vec<F> {
    use rand::{prelude::StdRng, SeedableRng};
    let mut rng = StdRng::seed_from_u64(seed);
    (0..N).map(|_| F::random(&mut rng)).collect()
}

fn millis(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1e3
}

fn header() {
    println!(
        "{:<12} {:<8} {:>9} {:>8} {:>8} {:>9} {:>7} {:>8} {:>8} {:>7} {:>7} {:>6}",
        "system",
        "order",
        "total/ms",
        "symb/ms",
        "cons/ms",
        "elim/ms",
        "ext/ms",
        "inter/ms",
        "other/ms",
        "batches",
        "pairs",
        "basis"
    );
}

fn row<const N: usize>(
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
    orders: &[(&str, MonomialOrder)],
    options: &F4Options,
) {
    for &(order_name, order) in orders {
        let (basis, s): (Vec<_>, F4Statistics) = match f4_with_options(system, order, options) {
            Ok(result) => result,
            Err(error) => {
                println!("{:<12} {:<8} {}", name, order_name, error);
                continue;
            }
        };

        let stages = s.stages;
        let other = s.total.saturating_sub(stages.sum());
        println!(
            "{:<12} {:<8} {:>9.2} {:>8.2} {:>8.2} {:>9.2} {:>7.2} {:>8.2} {:>8.2} {:>7} {:>7} {:>6}",
            name,
            order_name,
            millis(s.total),
            millis(stages.symbolic),
            millis(stages.construction),
            millis(stages.elimination),
            millis(stages.extraction),
            millis(stages.interreduction),
            millis(other),
            s.batches,
            s.pairs_reduced,
            basis.len()
        );
    }
}

/// The counters an optimization is judged on, beside the stage times.
fn diagnostics<const N: usize>(
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
    orders: &[(&str, MonomialOrder)],
    options: &F4Options,
) {
    for &(order_name, order) in orders {
        let Ok((_, s)) = f4_with_options(system, order, options) else {
            continue;
        };
        println!(
            "{:<12} {:<8} {:>8} {:>8} {:>8} {:>9.1} {:>8} {:>9.3} {:>8} {:>8} {:>8.2}",
            name,
            order_name,
            s.reducer_rows,
            s.reducer_rows_reused,
            s.divisor_queries,
            s.divisor_scan_steps_per_query(),
            s.criteria.total(),
            s.criteria.chain as f64 / s.pairs_considered.max(1) as f64,
            s.structured_batches,
            s.free_pivots,
            s.stage_coverage()
        );
    }
}

/// Which of the three tables [`each_system`] prints.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Report {
    /// Per-stage times.
    Stages,
    /// The counters an optimization is judged on.
    Diagnostics,
    /// The per-step degree sequence.
    Degrees,
}

/// `[4, 5, 5, 5, 6]` as `4, 5x3, 6`.
///
/// Run-length encoded because consecutive batches at one degree are the common case — a degree
/// split across batches by the pair cap — and a few hundred bare integers per row would not be
/// readable. The encoding is lossless: `5x3` is three steps at degree five, in order.
fn render_degree_sequence(degrees: &[u64]) -> String {
    let mut runs: Vec<String> = Vec::new();
    let mut index = 0;
    while index < degrees.len() {
        let degree = degrees[index];
        let length = degrees[index..]
            .iter()
            .take_while(|d| **d == degree)
            .count();
        runs.push(if length == 1 {
            format!("{degree}")
        } else {
            format!("{degree}x{length}")
        });
        index += length;
    }
    runs.join(", ")
}

/// The per-step degree sequence — #442, and Magma's `GroebnerBasis` second return value.
///
/// The maximum is already in `max_pair_degree`; what only the sequence shows is the *shape* — a
/// monotone climb, a jump, or a fall back to a lower degree after a mutant.
fn degree_sequence<const N: usize>(
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
    orders: &[(&str, MonomialOrder)],
    options: &F4Options,
) {
    for &(order_name, order) in orders {
        let Ok((_, s)) = f4_with_options(system, order, options) else {
            continue;
        };
        println!(
            "{:<12} {:<8} {:>7} {:>6} {:>6}  {}",
            name,
            order_name,
            s.batches,
            s.max_pair_degree,
            s.observed_solving_degree()
                .map_or("—".to_string(), |d| d.to_string()),
            render_degree_sequence(&s.step_degrees)
        );
    }
}

/// The header of [`degree_sequence`]'s table.
fn degree_sequence_header() {
    println!(
        "{:<12} {:<8} {:>7} {:>6} {:>6}  degrees per step",
        "system", "order", "batches", "maxdeg", "obsdeg"
    );
}

/// Every system of the comparison corpus, under the configuration given.
///
/// A system is labelled by its variable count, which is the convention the preceding milestone's
/// tables use: "katsura-5" is `katsura::<5, F>()`, five variables.
fn each_system(options: &F4Options, report: Report) {
    macro_rules! go {
        ($n:literal, $label:expr, $system:expr, $orders:expr) => {{
            let system: Vec<MultivariatePolynomial<$n, F>> = $system;
            match report {
                Report::Stages => row::<$n>($label, &system, $orders, options),
                Report::Diagnostics => diagnostics::<$n>($label, &system, $orders, options),
                Report::Degrees => degree_sequence::<$n>($label, &system, $orders, options),
            }
        }};
    }

    go!(4, "cyclic-4", cyclic::<4, F>(), &ALL);
    go!(5, "cyclic-5", cyclic::<5, F>(), &ALL);
    go!(4, "katsura-4", katsura::<4, F>(), &ALL);
    go!(5, "katsura-5", katsura::<5, F>(), &ALL);
    go!(6, "katsura-6", katsura::<6, F>(), &ALL);
    go!(7, "katsura-7", katsura::<7, F>(), &GRADED);
    go!(4, "random-4", random_system::<4>(5), &ALL);
    go!(
        6,
        "planted-6",
        planted::<6, F>(&planted_point::<6>(9)),
        &ALL
    );
}

/// From `research/competitive/results/history.json`: both the zeebra and singular
/// `reduced-grobner-basis` records for `mq-random-10` carry this digest.
const RECORDED_DIGEST: &str = "72d0ad315fc25409792625465578d18329597d3ee183e75f257774d9215803b2";

/// The digest-pinned `mq-random-10` instance, or a panic.
///
/// Shared by [`competitive_mq`] and [`print_mq_instance`] so that the stage split and the text
/// handed to an external engine cannot drift apart: a comparison of counters across two engines is
/// only a comparison if both ran the same ideal.
fn mq_instance() -> zeebra::grobner::external::Instance {
    let built = instance(
        "mq-random-10",
        REFERENCE_CHARACTERISTIC,
        MonomialOrder::GradedReverseLexicographic,
    )
    .expect("mq-random-10 is a corpus rung with a compiled dimension");

    assert_eq!(
        built.digest(),
        RECORDED_DIGEST,
        "the generated instance is not the one the 4.11x was measured on"
    );
    assert_eq!(built.variables.len(), 10, "ten variables");
    built
}

/// The instance as canonical text, for an external engine's own harness — #447.
///
/// Prints the digest and then `Instance::canonical` verbatim. Nothing is measured: the point is
/// that Groebner.jl's pair, matrix and row counters be taken on the ideal `mq` profiles and not on
/// a same-named rebuild, and the digest is what lets the other side check that.
fn print_mq_instance() {
    let built = mq_instance();
    println!("digest {}", built.digest());
    print!("{}", built.canonical());
}

/// The inside of the interreduction stage: which half, and what the reductions cost.
///
/// # Why this is a separate report
///
/// `docs/research/groebner-jl-gap.md` §3 measures final interreduction at **13 871x**
/// Groebner.jl's, where the next worst stage is 97.1x, and §4 attributes the difference to
/// intermediate expression swell — then records that the attribution is **inferred, not
/// measured**, because nothing counted terms popped or divisor tests. This prints the counters
/// that settle it, and the three ratios point at three different fixes:
///
/// - **swell** (`popped/ans` large) — the stage is building intermediates the answer does not
///   contain, and the fix is not building them: one Macaulay matrix instead of `n` divisions.
/// - **scan** (`tests/pop` large) — the reducer search dominates, and the fix is an index.
/// - **rewrite** (`rw/tail` large) — `subtract_shifted` is copying terms no divisor tail reaches,
///   and the fix is windowing the merge.
fn interreduction<const N: usize>(
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
    orders: &[(&str, MonomialOrder)],
    options: &F4Options,
) {
    println!(
        "{:<12} {:<8} {:>6} {:>7} {:>10} {:>9} {:>12} {:>13} {:>7} {:>5} {:>8} {:>8} {:>8}",
        "system",
        "order",
        "elts",
        "red/%",
        "popped",
        "ans",
        "tails",
        "rewritten",
        "maxwrk",
        "steps",
        "swell",
        "scan",
        "rw/tail"
    );
    for &(order_name, order) in orders {
        let Ok((_, s)) = f4_with_options(system, order, options) else {
            println!("{:<12} {:<8} refused", name, order_name);
            continue;
        };
        let c = s.interreduction;
        println!(
            "{:<12} {:<8} {:>6} {:>7.2} {:>10} {:>9} {:>12} {:>13} {:>7} {:>5} {:>8.1} {:>8.1} {:>8.1}",
            name,
            order_name,
            s.interreduction_elements,
            100.0 * s.interreduction_reduce_share(),
            c.terms_popped,
            c.remainder_terms,
            c.tail_terms_merged,
            c.terms_rewritten,
            c.max_working_terms,
            c.reduction_steps,
            c.swell_factor(),
            c.divisor_tests_per_term(),
            c.rewrite_amplification(),
        );
        println!();
        println!(
            "    divisor tests {} over {} terms popped against {} reducers a call",
            c.divisor_tests,
            c.terms_popped,
            c.reducers.checked_div(c.calls).unwrap_or(0)
        );
        println!(
            "    the verdict: swell {:.1}x, scan {:.1} tests a term, rewrite {:.1}x amplification",
            c.swell_factor(),
            c.divisor_tests_per_term(),
            c.rewrite_amplification()
        );
    }
}

/// The division and matrix interreduction routes, measured against each other on one build.
///
/// Interleaved and repeated, because this box's run-to-run spread is wide enough that a single
/// pair of runs cannot separate a real change from noise — and because the two routes have to be
/// compared on *one* build to keep a compiler difference out of the ratio.
///
/// The bases are asserted **equal**, not merely both valid. A reduced Gröbner basis is unique, so
/// this is exact equality and the right failure mode for a route substitution.
fn compare_interreduction_routes() {
    let built = mq_instance();
    let names: Vec<&str> = built.variables.iter().map(String::as_str).collect();
    let mut compiled = [""; 10];
    compiled.copy_from_slice(&names[..10]);
    let system: Vec<MultivariatePolynomial<10, F>> = built
        .system
        .iter()
        .map(|text| {
            MultivariatePolynomial::parse(text, compiled).expect("this crate rendered this text")
        })
        .collect();

    let order = MonomialOrder::GradedReverseLexicographic;
    let division = F4Options {
        measure_stages: true,
        ..F4Options::default()
    };
    let matrix = F4Options {
        measure_stages: true,
        interreduce_by_matrix: true,
        ..F4Options::default()
    };

    println!(
        "{:<4} {:<9} {:>10} {:>10} {:>9} {:>6}",
        "rep", "route", "total/ms", "inter/ms", "inter/%", "basis"
    );

    let mut reference: Option<Vec<MultivariatePolynomial<10, F>>> = None;
    for rep in 1..=3 {
        for (label, options) in [("division", &division), ("matrix", &matrix)] {
            let (basis, s) = match f4_with_options(&system, order, options) {
                Ok(result) => result,
                Err(error) => {
                    println!("{rep:<4} {label:<9} {error}");
                    continue;
                }
            };
            match &reference {
                None => reference = Some(basis.clone()),
                Some(expected) => assert_eq!(
                    &basis, expected,
                    "{label} returned a different basis from the first run; a reduced \
                     Grobner basis is unique, so this is a correctness failure"
                ),
            }
            let share = if s.total.is_zero() {
                0.0
            } else {
                100.0 * s.stages.interreduction.as_secs_f64() / s.total.as_secs_f64()
            };
            println!(
                "{:<4} {:<9} {:>10.2} {:>10.2} {:>9.2} {:>6}",
                rep,
                label,
                millis(s.total),
                millis(s.stages.interreduction),
                share,
                basis.len()
            );
            if let Some(m) = s.interreduction_matrix {
                println!(
                    "     matrix {} x {}, {} nonzeros, {} elements{}",
                    m.rows,
                    m.columns,
                    m.nonzeros,
                    m.elements,
                    if m.fell_back {
                        " -- FELL BACK to the division route, so this timing is not the matrix route's"
                    } else {
                        ""
                    }
                );
            }
        }
    }
}

/// The competitive-board MQ instance, profiled per stage — #349.
///
/// `mq-random-10` is the instance M25 measured Zeebra **4.11x slower than Singular** on, and it is
/// the corpus family closest in shape to a cryptanalytic system. Everything else this example
/// profiles is a classical benchmark whose stage shares were what the H-series was scoped against;
/// the losing instance's split was never taken, so the optimization backlog was prioritized from
/// katsura and cyclic and applied to a gap measured on neither.
///
/// It is **not** in [`each_system`] because it is not a comparison-corpus system and because it
/// costs about half a minute a run, which a default invocation should not pay.
///
/// # The equivalence check, which is the point of doing it this way
///
/// This builds the instance through `grobner::external::instance` at
/// [`REFERENCE_CHARACTERISTIC`] under grevlex, and **asserts its identity digest against the one
/// in the retained record**. A stage split taken on a different instance than the 4.11x was
/// measured on would answer a different question while looking like an answer to this one.
fn competitive_mq(options: &F4Options) {
    let built = mq_instance();

    let names: Vec<&str> = built.variables.iter().map(String::as_str).collect();
    let mut compiled = [""; 10];
    compiled.copy_from_slice(&names[..10]);
    let system: Vec<MultivariatePolynomial<10, F>> = built
        .system
        .iter()
        .map(|text| {
            MultivariatePolynomial::parse(text, compiled).expect("this crate rendered this text")
        })
        .collect();

    println!();
    println!("## #349: the competitive MQ instance, per stage");
    println!();
    println!(
        "`mq-random-10` at GF({}) under grevlex, digest `{}` — the instance the 4.11x against",
        REFERENCE_CHARACTERISTIC,
        &RECORDED_DIGEST[..16]
    );
    println!(
        "Singular was measured on (28.709 s against 6.959 s, one worker, affinity 0-7). One order"
    );
    println!("only, because that is the order the record was taken under.");
    println!();
    header();
    row::<10>(
        "mq-random-10",
        &system,
        &[("grevlex", MonomialOrder::GradedReverseLexicographic)],
        options,
    );
    println!();
    diagnostics::<10>(
        "mq-random-10",
        &system,
        &[("grevlex", MonomialOrder::GradedReverseLexicographic)],
        options,
    );
    println!();
    degree_sequence_header();
    degree_sequence::<10>(
        "mq-random-10",
        &system,
        &[("grevlex", MonomialOrder::GradedReverseLexicographic)],
        options,
    );

    if options.count_interreduction {
        println!();
        println!("### Inside the interreduction stage — #436's split, and #447 §4's loose end");
        println!();
        println!(
            "Counts only. This run pays ~36% for the per-reducer counter, so its durations above"
        );
        println!("are not comparable with a `mq` run's. The counts are exact either way.");
        println!();
        interreduction::<10>(
            "mq-random-10",
            &system,
            &[("grevlex", MonomialOrder::GradedReverseLexicographic)],
            options,
        );
    }
}

fn main() {
    let argument = std::env::args().nth(1).unwrap_or_else(|| "baseline".into());

    if argument == "mq-instance" {
        print_mq_instance();
        return;
    }

    if argument == "list" {
        println!("configurations: {}", CONFIGURATIONS.join(", "));
        println!(
            "modes: mq (the #349 competitive MQ stage split), mq-counts (its operation\n             counts), mq-instance (its canonical text)"
        );
        return;
    }

    if argument == "mq" {
        // `default()`, not `baseline()`, because that is what the record was taken under:
        // `examples/competitive_sweep.rs` builds its Zeebra solver from `F4Options::default()`.
        // The difference is not cosmetic — under `baseline()` this instance does not finish at
        // all, refusing at 20 000 277 live nonzero entries against the 20 000 000 budget both
        // configurations share. Profiling the ablation's starting point would be a stage split of
        // a computation no record describes.
        let options = F4Options {
            measure_stages: true,
            ..F4Options::default()
        };
        competitive_mq(&options);
        return;
    }

    if argument == "mq-matrix" {
        // The two interreduction routes, interleaved in one process on one build. #471's A/B:
        // `docs/research/groebner-jl-gap.md` §4 puts the division route at 13 871x Groebner.jl's
        // for this stage and projects ~170 ms for a matrix pass at Zeebra's own per-operation
        // constant. Both routes return the same reduced basis — asserted here, not assumed.
        println!();
        println!("## #471: final interreduction, division route against matrix route");
        println!();
        println!("Interleaved in one process on one build, so no cross-build or cross-session");
        println!("difference is in the comparison. Both bases asserted equal.");
        println!();
        compare_interreduction_routes();
        return;
    }

    if argument == "mq-counts" {
        // Operation counts rather than durations. Separate from `mq` because the per-reducer
        // counter costs about a third of the stage, so one run cannot report both a trustworthy
        // stage split and these counters — see `F4Options::count_interreduction`.
        let options = F4Options {
            count_interreduction: true,
            ..F4Options::default()
        };
        competitive_mq(&options);
        return;
    }

    let Some(options) = configuration(&argument) else {
        eprintln!(
            "unknown configuration {:?}; one of {}",
            argument,
            CONFIGURATIONS.join(", ")
        );
        std::process::exit(2);
    };

    println!("configuration: {}", argument);
    println!();
    println!(
        "Stage times. `inter` is the final interreduction, which happens once rather than per"
    );
    println!("batch. `other` is the total less every stage: pair selection and basis bookkeeping.");
    println!();
    header();
    each_system(&options, Report::Stages);

    println!();
    println!(
        "Diagnostics. `reused` is reducer multiples that had been built before, which is zero"
    );
    println!(
        "unless the reducer cache is counting or storing. `scan/q` is basis elements examined"
    );
    println!("per divisor lookup: the basis size for a linear scan, one for a perfect index.");
    println!("`cov` is the share of the total the four stages account for.");
    println!();
    println!(
        "{:<12} {:<8} {:>8} {:>8} {:>8} {:>9} {:>8} {:>9} {:>8} {:>8} {:>8}",
        "system",
        "order",
        "reducers",
        "reused",
        "div/q",
        "scan/q",
        "elim'd",
        "chain%",
        "struct",
        "free_piv",
        "cov"
    );
    each_system(&options, Report::Diagnostics);

    println!();
    println!("Degrees per step — #442, the sequence Magma's `GroebnerBasis` returns as `D`.");
    println!("`maxdeg` is `max_pair_degree`, accumulated over the pairs as selected; `obsdeg` is");
    println!("the maximum of the sequence, which omits any selection every criterion discarded.");
    println!("`5x3` is three consecutive batches at degree five.");
    println!();
    degree_sequence_header();
    each_system(&options, Report::Degrees);
}
