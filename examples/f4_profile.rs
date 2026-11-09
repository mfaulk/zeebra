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
//! cargo run --release --example f4_profile -- divmask     # #331: the divisor-mask counters
//! cargo run --release --example f4_profile -- mq-matrix    # #471: the two interreduction routes
//! cargo run --release --example f4_profile -- mq-instance   # that instance's canonical text
//! cargo run --release --example f4_profile -- construction # #330: construction, split four ways
//! cargo run --release --example f4_profile -- scatter     # #582: the scatter, split four ways
//! cargo run --release --example f4_profile -- handles     # #621: handles against the hash read
//! ```
//!
//! `mq-instance` emits the digest-pinned instance rather than a measurement, so that an external
//! engine can be driven on the same ideal and its own counters compared against the columns here
//! (#447). The text is `Instance::canonical`, which is what the digest is taken over, so a
//! consumer in another language can re-derive the digest and refuse a mismatch.
//!
//! Each configuration is one row of the milestone's ablation table. They are named here rather
//! than assembled at each call site so that every workstream reports the same thing.

use std::time::{Duration, Instant};

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura, planted},
        external::{instance, REFERENCE_CHARACTERISTIC},
        f4::{symbolic_preprocessing, MacaulayMatrix, ScatterPrefix},
        f4_with_options, trace_batches, CacheMode, ConstructionTimings, F4Options, F4Statistics,
        InterreductionRoute, PairCriteria, ReducerSelection, ReductionStrategy,
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
        // The per-step region split #440 stage 1 asked for. The merge span is the expensive
        // region — one monomial multiply and one `MonomialOrder::cmp` an element — and the two
        // window regions are `extend_from_slice`, so the shares say whether the rewrite is
        // comparison work or bandwidth, and therefore whether a heap can pay.
        println!(
            "    regions: below {} ({:.1}%), span {} ({:.1}%), above {} ({:.1}%) of {} rewritten",
            c.terms_below_window,
            100.0 * c.below_window_share(),
            c.terms_in_merge_span,
            100.0 * c.merge_span_share(),
            c.terms_above_window,
            100.0 * c.above_window_share(),
            c.terms_rewritten,
        );
        println!(
            "    merge ops: {} monomial multiplies, {} order comparisons over {} steps",
            c.merge_monomial_multiplies, c.merge_comparisons, c.reduction_steps,
        );
    }
}

/// Echelon against reduced batch rows, over both interreduction routes, on one build.
///
/// #477's question, as four arms rather than two. The payoff it claims is a smaller final
/// autoreduce matrix, and that matrix only exists when the matrix route is selected — but that
/// flag is **off by default** (#507 is the issue that decides it), so measuring only the matrix
/// route would answer a question about a path no board row describes. The division arms are what
/// say whether this flag pays on the path that ships today.
///
/// The price is the batch elimination stage, the payoff is the interreduction stage, and the only
/// figure that decides it is the total. Interleaved and repeated for the same reason
/// [`compare_interreduction_routes`] is, and every basis is asserted equal to the first.
fn compare_batch_row_forms() {
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
    let arm = |interreduction: InterreductionRoute, reduce_batch_rows: bool| F4Options {
        measure_stages: true,
        interreduction,
        reduce_batch_rows,
        ..F4Options::default()
    };
    // Named routes rather than `ByOrder`, because this table is a 2x2 over the two flags and
    // `ByOrder` would make one axis depend on the order the other arm is also measured under.
    let arms = [
        ("div+echelon", arm(InterreductionRoute::Division, false)),
        ("div+reduced", arm(InterreductionRoute::Division, true)),
        ("mat+echelon", arm(InterreductionRoute::Matrix, false)),
        ("mat+reduced", arm(InterreductionRoute::Matrix, true)),
    ];

    println!(
        "{:<4} {:<13} {:>10} {:>10} {:>10} {:>13} {:>6}",
        "rep", "arm", "total/ms", "elim/ms", "inter/ms", "backsub rows", "basis"
    );

    let mut reference: Option<Vec<MultivariatePolynomial<10, F>>> = None;
    for rep in 1..=3 {
        for (label, options) in &arms {
            let (basis, s) = match f4_with_options(&system, order, options) {
                Ok(result) => result,
                Err(error) => {
                    println!("{rep:<4} {label:<13} {error}");
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
            println!(
                "{:<4} {:<13} {:>10.2} {:>10.2} {:>10.2} {:>13} {:>6}",
                rep,
                label,
                millis(s.total),
                millis(s.stages.elimination),
                millis(s.stages.interreduction),
                match s.back_substituted_rows {
                    Some(rows) => rows.to_string(),
                    None => "-".to_string(),
                },
                basis.len()
            );
            match s.interreduction_matrix {
                Some(m) => println!(
                    "     autoreduce matrix {} x {} = {} cells, {} nonzeros, {} elements{}",
                    m.rows,
                    m.columns,
                    m.rows.saturating_mul(m.columns),
                    m.nonzeros,
                    m.elements,
                    if m.fell_back {
                        " -- FELL BACK to the division route, so this timing is not the matrix route's"
                    } else {
                        ""
                    }
                ),
                None => println!("     autoreduce matrix: none built (division route)"),
            }
        }
    }
}

/// `reduce_batch_rows` on the classical rungs, which is what a default flip would have to survive.
///
/// `mq-random-10` is one instance under one order, and §3a.1b of
/// `docs/research/interreduction-cost.md` is the standing warning against reading a default off
/// one: the matrix interreduction route is 1.07x–1.72x faster on three rungs and **25x slower** on
/// katsura-5 under lex, because a basis in shape position is the best case for iterated division
/// and the worst case for a matrix. This flag is a different lever — it changes the batch path, not
/// the interreduction route — but it has the same exposure: the second pass is paid per batch
/// whether or not the final stage was ever expensive, so an instance whose interreduction already
/// costs a millisecond has nothing to win and a pass to pay for.
///
/// So katsura-5 under lex is in this table deliberately. The interreduction route is off on both
/// arms, which is the shipping default.
fn compare_batch_row_forms_on_the_rungs() {
    /// Minimum of this many interleaved repetitions; these instances run in milliseconds, where
    /// one pair of runs cannot separate a real change from this box's spread.
    const REPETITIONS: usize = 7;

    let echelon = F4Options::default();
    let reduced = F4Options {
        reduce_batch_rows: true,
        ..F4Options::default()
    };

    println!(
        "{:<13} {:<9} {:>12} {:>12} {:>8} {:>13} {:>6}",
        "instance", "order", "echelon/ms", "reduced/ms", "ratio", "backsub rows", "basis"
    );

    fn row<const N: usize>(
        label: &str,
        system: &[MultivariatePolynomial<N, F>],
        orders: &[MonomialOrder],
        echelon: &F4Options,
        reduced: &F4Options,
        repetitions: usize,
    ) {
        for order in orders {
            let mut best_echelon = f64::INFINITY;
            let mut best_reduced = f64::INFINITY;
            let mut rows_examined = None;
            let mut length = 0usize;
            let mut reference: Option<Vec<MultivariatePolynomial<N, F>>> = None;

            for _ in 0..repetitions {
                for (is_reduced, options) in [(false, echelon), (true, reduced)] {
                    let start = Instant::now();
                    let Ok((basis, statistics)) = f4_with_options(system, *order, options) else {
                        println!("{label:<13} {:<9} refused its budgets", order.name());
                        return;
                    };
                    let elapsed = start.elapsed().as_secs_f64() * 1e3;
                    match &reference {
                        None => reference = Some(basis.clone()),
                        Some(expected) => assert_eq!(
                            &basis,
                            expected,
                            "{label} under {} returned a different basis; a reduced Grobner \
                             basis is unique, so this is a correctness failure",
                            order.name()
                        ),
                    }
                    length = basis.len();
                    if is_reduced {
                        best_reduced = best_reduced.min(elapsed);
                        rows_examined = statistics.back_substituted_rows;
                    } else {
                        best_echelon = best_echelon.min(elapsed);
                    }
                }
            }

            println!(
                "{:<13} {:<9} {:>12.4} {:>12.4} {:>8.2} {:>13} {:>6}",
                label,
                order.name(),
                best_echelon,
                best_reduced,
                best_echelon / best_reduced,
                match rows_examined {
                    Some(rows) => rows.to_string(),
                    None => "-".to_string(),
                },
                length
            );
        }
    }

    const LEX: [MonomialOrder; 1] = [MonomialOrder::Lexicographic];
    const GREVLEX: [MonomialOrder; 1] = [MonomialOrder::GradedReverseLexicographic];

    // The 25x-regression rung for the matrix route, under the order that causes it.
    row(
        "katsura-5",
        &katsura::<5, F>(),
        &LEX,
        &echelon,
        &reduced,
        REPETITIONS,
    );
    row(
        "katsura-5",
        &katsura::<5, F>(),
        &GREVLEX,
        &echelon,
        &reduced,
        REPETITIONS,
    );
    row(
        "katsura-6",
        &katsura::<6, F>(),
        &GREVLEX,
        &echelon,
        &reduced,
        REPETITIONS,
    );
    row(
        "cyclic-5",
        &cyclic::<5, F>(),
        &GREVLEX,
        &echelon,
        &reduced,
        REPETITIONS,
    );
    row(
        "cyclic-4",
        &cyclic::<4, F>(),
        &LEX,
        &echelon,
        &reduced,
        REPETITIONS,
    );
}

/// #330: where matrix construction's time actually goes, split four ways.
///
/// The split is the measurement #330's kill criterion was stated on before anything was
/// implemented. Handing out column indices during symbolic interning can only remove the column
/// collection and the map build; the scatter is paid either way. So if `set+sort` plus `map` is
/// under a third of construction, the restructuring is refuted and the issue closes.
///
/// Two configurations, because they build different matrices and the recorded §8.5 figure was
/// taken under only one of them. `recommended` is what §8.5 reports and is what this re-measures
/// against; `default` is what ships, and a conclusion about the shipping engine has to be taken
/// there. Repeated and min-reduced, because this box's run-to-run spread is wide.
fn construction_split() {
    const REPETITIONS: usize = 9;
    let configurations = [
        (
            "recommended",
            configuration("recommended").expect("a named configuration"),
        ),
        (
            "default",
            F4Options {
                measure_stages: true,
                ..F4Options::default()
            },
        ),
    ];

    println!(
        "{:<12} {:<8} {:<12} {:>9} {:>8} {:>8} {:>7} {:>7} {:>8} {:>8} {:>8} {:>7} {:>9} {:>9}",
        "system",
        "order",
        "config",
        "total/ms",
        "con/ms",
        "collect",
        "sort",
        "map",
        "scatter",
        "rows",
        "assm",
        "con%",
        "criterion",
        "removable"
    );

    for (config_name, options) in &configurations {
        for (name, order, run) in systems_of_interest() {
            // The fastest of several runs: the floor is the run least disturbed by the rest of the
            // box, and a mean over a shared machine measures the neighbours.
            let mut best: Option<F4Statistics> = None;
            for _ in 0..REPETITIONS {
                let Some(statistics) = run(order, options) else {
                    continue;
                };
                if best.as_ref().is_none_or(|b| statistics.total < b.total) {
                    best = Some(statistics);
                }
            }
            let Some(s) = best else {
                println!(
                    "{:<12} {:<8} {:<12} refused",
                    name,
                    order.name(),
                    config_name
                );
                continue;
            };
            let split = s.stages.construction_split;
            println!(
                "{:<12} {:<8} {:<12} {:>9.2} {:>8.2} {:>8.2} {:>7.2} {:>7.2} {:>8.2} {:>8.2} {:>8.2} {:>6.0}% {:>8.0}% {:>8.0}%",
                name,
                order.name(),
                config_name,
                millis(s.total),
                millis(s.stages.construction),
                millis(split.collect),
                millis(split.sort),
                millis(split.map),
                millis(split.scatter),
                millis(split.scatter_rows),
                millis(split.scatter_assemble),
                100.0 * millis(s.stages.construction) / millis(s.total),
                100.0 * split.handout_share(),
                100.0 * split.removable_share()
            );
        }
    }
}

/// #330's A/B: the column handout against the rehashing it replaces, in one process on one build.
///
/// Every batch of a real computation is replayed and built both ways, interleaved so that a drift
/// in the machine's state lands on both arms. The matrices are asserted **equal** — construction
/// is not an approximation, and two routes that built different matrices would make the ratio
/// meaningless. Only `collect` should move: the sort, the map and the scatter are the same code on
/// both arms, so they double as a control on the measurement itself.
fn construction_routes() {
    const REPETITIONS: usize = 5;

    println!(
        "{:<12} {:<8} {:<9} {:>8} {:>8} {:>8} {:>7} {:>7} {:>8} {:>9} {:>8}",
        "system",
        "order",
        "route",
        "batches",
        "build/ms",
        "collect",
        "sort",
        "map",
        "scatter",
        "criterion",
        "speedup"
    );

    macro_rules! arm {
        ($name:expr, $order:expr, $system:expr) => {{
            let order = $order;
            let system = $system;
            let traced = F4Options {
                measure_stages: true,
                ..configuration("recommended").expect("a named configuration")
            };
            let trace = match trace_batches(&system, order, &traced) {
                Ok((_, _, trace)) => Some(trace),
                Err(_) => {
                    println!("{:<12} {:<8} did not finish", $name, order.name());
                    None
                }
            };
            if let Some(trace) = trace {
                // Preprocess once per batch, outside the timing: the handout's saving is in
                // construction, and charging preprocessing to either arm would bury it.
                let batches: Vec<_> = trace
                    .batches()
                    .iter()
                    .map(|batch| {
                        let preprocessed = symbolic_preprocessing(&batch.basis, &batch.pairs);
                        (batch.basis.clone(), preprocessed)
                    })
                    .collect();

                let mut rehash = Duration::MAX;
                let mut handout = Duration::MAX;
                let mut rehash_split = ConstructionTimings::default();
                let mut handout_split = ConstructionTimings::default();
                let mut columns = 0usize;
                for _ in 0..REPETITIONS {
                    let mut a = Duration::ZERO;
                    let mut b = Duration::ZERO;
                    let mut a_split = ConstructionTimings::default();
                    let mut b_split = ConstructionTimings::default();
                    let mut seen = 0usize;
                    for (basis, preprocessed) in &batches {
                        let started = Instant::now();
                        let (old, old_split) = MacaulayMatrix::build_rehashing_for_benchmark(
                            basis,
                            preprocessed,
                            order,
                            true,
                        );
                        a += started.elapsed();
                        a_split.add(&old_split);

                        let started = Instant::now();
                        let (new, new_split) = MacaulayMatrix::build_measured(
                            basis,
                            preprocessed,
                            order,
                            usize::MAX,
                            usize::MAX,
                            true,
                        )
                        .expect("an unbounded construction cannot exceed its budget");
                        b += started.elapsed();
                        b_split.add(&new_split);

                        assert_eq!(old, new, "the two routes must build the same matrix");
                        seen += new.num_columns();
                    }
                    if a < rehash {
                        rehash = a;
                        rehash_split = a_split;
                    }
                    if b < handout {
                        handout = b;
                        handout_split = b_split;
                    }
                    columns = seen;
                }

                let _ = columns;
                // The rehashing row is the pre-#330 construction stage, so its `criterion` column
                // is the quantity the issue stated its kill criterion on, measured on the same
                // build as the route that replaces it.
                for (route, split, elapsed) in [
                    ("rehashing", rehash_split, rehash),
                    ("handout", handout_split, handout),
                ] {
                    println!(
                        "{:<12} {:<8} {:<9} {:>8} {:>8.2} {:>8.2} {:>7.2} {:>7.2} {:>8.2} {:>8.0}% {:>7.2}x",
                        $name,
                        order.name(),
                        route,
                        batches.len(),
                        millis(elapsed),
                        millis(split.collect),
                        millis(split.sort),
                        millis(split.map),
                        millis(split.scatter),
                        100.0 * split.handout_share(),
                        rehash.as_secs_f64() / elapsed.as_secs_f64()
                    );
                }
            }
        }};
    }

    arm!("cyclic-5", MonomialOrder::Lexicographic, cyclic::<5, F>());
    arm!("katsura-5", MonomialOrder::Lexicographic, katsura::<5, F>());
    arm!("katsura-6", MonomialOrder::Lexicographic, katsura::<6, F>());
    arm!(
        "katsura-6",
        MonomialOrder::GradedReverseLexicographic,
        katsura::<6, F>()
    );
    arm!(
        "katsura-7",
        MonomialOrder::GradedLexicographic,
        katsura::<7, F>()
    );
}

/// #621: the handle scatter against the hashing scatter it replaces, one process, one build.
///
/// Both arms read the same `Preprocessed`, which is built once per batch outside the timing — the
/// handles are a side effect of preprocessing's own deduplication test, so charging preprocessing
/// to the construction arms would bury the difference and double-count work neither arm does.
///
/// The arms differ in `map` and `scatter`, and in nothing else: `collect` pairs each monomial with
/// its handle on the handle arm and copies the arena alone on the hashing arm, and both sorts call
/// the same comparator on the same monomials. `entries/col` is the quantity #621 stated its kill
/// criterion on — the per-entry lookup can be removed at most once per entry, and entries
/// outnumber columns by that ratio — so it is reported beside the times rather than derived
/// elsewhere.
///
/// Arm order rotates per repetition and each arm is min-reduced over its own runs, because a
/// monotone drift in this box's state would otherwise land entirely on whichever arm runs last.
/// The matrices are asserted equal, which is what makes this a measurement of cost rather than of
/// two different matrices.
fn scatter_routes() {
    const REPETITIONS: usize = 7;

    println!(
        "{:<12} {:<8} {:<9} {:>7} {:>8} {:>9} {:>8} {:>7} {:>7} {:>8} {:>9} {:>8}",
        "system",
        "order",
        "route",
        "batches",
        "entries",
        "entries/col",
        "build/ms",
        "collect",
        "sort",
        "map",
        "scatter",
        "speedup"
    );

    macro_rules! arm {
        ($name:expr, $order:expr, $system:expr) => {{
            let order = $order;
            let system = $system;
            let traced = F4Options {
                measure_stages: true,
                ..configuration("recommended").expect("a named configuration")
            };
            let trace = match trace_batches(&system, order, &traced) {
                Ok((_, _, trace)) => Some(trace),
                Err(_) => {
                    println!("{:<12} {:<8} did not finish", $name, order.name());
                    None
                }
            };
            if let Some(trace) = trace {
                let batches: Vec<_> = trace
                    .batches()
                    .iter()
                    .map(|batch| {
                        let preprocessed = symbolic_preprocessing(&batch.basis, &batch.pairs);
                        (batch.basis.clone(), preprocessed)
                    })
                    .collect();

                // The shape, taken once and outside every arm. Both routes build the same matrix,
                // so there is one answer.
                let mut entries = 0usize;
                let mut columns = 0usize;
                for (basis, preprocessed) in &batches {
                    let handled = MacaulayMatrix::build(basis, preprocessed, order);
                    let (hashed, _) = MacaulayMatrix::build_hashed_scatter_for_benchmark(
                        basis,
                        preprocessed,
                        order,
                        false,
                    );
                    assert_eq!(handled, hashed, "the two routes must build the same matrix");
                    entries += handled.nonzeros();
                    columns += handled.num_columns();
                }

                let mut floor = [Duration::MAX; 2];
                let mut splits = [ConstructionTimings::default(); 2];
                for repetition in 0..REPETITIONS {
                    let mut elapsed = [Duration::ZERO; 2];
                    let mut split = [ConstructionTimings::default(); 2];
                    for slot in 0..2 {
                        let which = (slot + repetition) % 2;
                        for (basis, preprocessed) in &batches {
                            let started = Instant::now();
                            let one = if which == 0 {
                                MacaulayMatrix::build_hashed_scatter_for_benchmark(
                                    basis,
                                    preprocessed,
                                    order,
                                    true,
                                )
                                .1
                            } else {
                                MacaulayMatrix::build_measured(
                                    basis,
                                    preprocessed,
                                    order,
                                    usize::MAX,
                                    usize::MAX,
                                    true,
                                )
                                .expect("an unbounded construction cannot exceed its budget")
                                .1
                            };
                            elapsed[which] += started.elapsed();
                            split[which].add(&one);
                        }
                    }
                    for index in 0..2 {
                        if elapsed[index] < floor[index] {
                            floor[index] = elapsed[index];
                            splits[index] = split[index];
                        }
                    }
                }

                for (index, route) in ["hashing", "handles"].into_iter().enumerate() {
                    println!(
                        "{:<12} {:<8} {:<9} {:>7} {:>8} {:>11.2} {:>8.2} {:>7.2} {:>7.2} {:>8.2} {:>9.2} {:>7.2}x",
                        $name,
                        order.name(),
                        route,
                        batches.len(),
                        entries,
                        entries as f64 / columns.max(1) as f64,
                        millis(floor[index]),
                        millis(splits[index].collect),
                        millis(splits[index].sort),
                        millis(splits[index].map),
                        millis(splits[index].scatter),
                        floor[0].as_secs_f64() / floor[index].as_secs_f64()
                    );
                }
            }
        }};
    }

    arm!("cyclic-5", MonomialOrder::Lexicographic, cyclic::<5, F>());
    arm!("katsura-5", MonomialOrder::Lexicographic, katsura::<5, F>());
    arm!("katsura-6", MonomialOrder::Lexicographic, katsura::<6, F>());
    arm!(
        "katsura-6",
        MonomialOrder::GradedReverseLexicographic,
        katsura::<6, F>()
    );
    arm!(
        "katsura-7",
        MonomialOrder::GradedLexicographic,
        katsura::<7, F>()
    );
    arm!(
        "katsura-7",
        MonomialOrder::GradedReverseLexicographic,
        katsura::<7, F>()
    );
}

/// #582: where the row scatter's time goes — shift, lookup, row build, assembly.
///
/// The scatter's two halves are clocked by `build_hashed_scatter_for_benchmark`, which is the
/// scatter as #582 measured it. The three steps *inside* the row half are per term, where
/// `Instant::now()` costs more than the work it would time, so they come from `ScatterPrefix`'s
/// nested ablation and are read off as differences between adjacent arms.
///
/// The `Row` arm is that route's loop verbatim, so the `ablat` column against `rows` is a control
/// on the whole method: if those two disagree, the differences beside them mean nothing. Arm order
/// rotates per repetition and each arm is min-reduced over its own runs, because a monotone drift
/// in this box's state would otherwise land entirely on whichever arm runs last.
///
/// Since #621 the shipping scatter reads a handle rather than shifting and hashing, so this table
/// describes the route #621 replaced. `f4_profile handles` is the A/B between the two.
fn scatter_split() {
    const REPETITIONS: usize = 7;

    println!(
        "{:<12} {:<8} {:>7} {:>9} {:>8} {:>9} {:>8} {:>8} {:>9} {:>8} {:>8}",
        "system",
        "order",
        "batches",
        "scatter/ms",
        "rows",
        "assm",
        "ablat",
        "shift",
        "lookup",
        "rowbuild",
        "lookup%"
    );

    macro_rules! arm {
        ($name:expr, $order:expr, $system:expr) => {{
            let order = $order;
            let system = $system;
            let traced = F4Options {
                measure_stages: true,
                ..configuration("recommended").expect("a named configuration")
            };
            let trace = match trace_batches(&system, order, &traced) {
                Ok((_, _, trace)) => Some(trace),
                Err(_) => {
                    println!("{:<12} {:<8} did not finish", $name, order.name());
                    None
                }
            };
            if let Some(trace) = trace {
                // Preprocessed once per batch, outside every arm: preprocessing is a different
                // stage and charging it here would bury the differences this table is made of.
                let batches: Vec<_> = trace
                    .batches()
                    .iter()
                    .map(|batch| {
                        let preprocessed = symbolic_preprocessing(&batch.basis, &batch.pairs);
                        (batch.basis.clone(), preprocessed)
                    })
                    .collect();

                let mut floor = [Duration::MAX; 4];
                let mut assemble_floor = Duration::MAX;
                let mut checksums = [0u64; 3];

                for repetition in 0..REPETITIONS {
                    let mut elapsed = [Duration::ZERO; 4];
                    let mut assemble = Duration::ZERO;
                    for slot in 0..4 {
                        let which = (slot + repetition) % 4;
                        let prefix = match which {
                            0 => Some(ScatterPrefix::Shift),
                            1 => Some(ScatterPrefix::ShiftAndLookup),
                            2 => Some(ScatterPrefix::Row),
                            _ => None,
                        };
                        for (basis, preprocessed) in &batches {
                            match prefix {
                                Some(prefix) => {
                                    let timing = MacaulayMatrix::scatter_prefix_for_benchmark(
                                        basis,
                                        preprocessed,
                                        order,
                                        prefix,
                                    );
                                    elapsed[which] += timing.elapsed;
                                    checksums[which] =
                                        checksums[which].wrapping_add(timing.checksum);
                                }
                                None => {
                                    // The *hashing* route, not `build_measured`: since #621 the
                                    // shipping scatter reads a handle and the ablation arms shift
                                    // and hash, so `build_measured` would not be a control on
                                    // them. This keeps #582's table reproducible and the
                                    // `ablat`-against-`rows` check meaningful.
                                    let (_, split) =
                                        MacaulayMatrix::build_hashed_scatter_for_benchmark(
                                            basis,
                                            preprocessed,
                                            order,
                                            true,
                                        );
                                    elapsed[3] += split.scatter_rows;
                                    assemble += split.scatter_assemble;
                                }
                            }
                        }
                    }
                    for (best, run) in floor.iter_mut().zip(elapsed) {
                        *best = (*best).min(run);
                    }
                    assemble_floor = assemble_floor.min(assemble);
                }

                // An arm the optimizer emptied would report a plausible time and no output.
                assert!(
                    checksums.iter().all(|sum| *sum != 0),
                    "an ablation arm produced nothing"
                );

                let [shift, lookup, ablation, rows] = floor;
                // Adjacent arms are nested prefixes, so a difference is one step's cost. Saturating
                // because on a step whose cost is near the measurement's own noise the ordering can
                // invert, and a negative duration would be a lie rather than a surprise.
                let lookup_cost = lookup.saturating_sub(shift);
                let row_build = ablation.saturating_sub(lookup);
                let scatter = rows + assemble_floor;
                println!(
                    "{:<12} {:<8} {:>7} {:>10.2} {:>8.2} {:>9.2} {:>8.2} {:>8.2} {:>9.2} {:>8.2} {:>7.0}%",
                    $name,
                    order.name(),
                    batches.len(),
                    millis(scatter),
                    millis(rows),
                    millis(assemble_floor),
                    millis(ablation),
                    millis(shift),
                    millis(lookup_cost),
                    millis(row_build),
                    100.0 * millis(lookup_cost) / millis(scatter)
                );
            }
        }};
    }

    arm!("cyclic-5", MonomialOrder::Lexicographic, cyclic::<5, F>());
    arm!("katsura-6", MonomialOrder::Lexicographic, katsura::<6, F>());
    arm!(
        "katsura-6",
        MonomialOrder::GradedReverseLexicographic,
        katsura::<6, F>()
    );
    arm!(
        "katsura-7",
        MonomialOrder::GradedLexicographic,
        katsura::<7, F>()
    );
}

/// The instances §8.5 reports construction as the dominant stage on, plus the graded controls.
///
/// Boxed closures because the systems have different variable counts, so they are different types
/// and cannot share a slice.
#[allow(clippy::type_complexity)]
fn systems_of_interest() -> Vec<(
    &'static str,
    MonomialOrder,
    Box<dyn Fn(MonomialOrder, &F4Options) -> Option<F4Statistics>>,
)> {
    macro_rules! entry {
        ($name:expr, $order:expr, $system:expr) => {{
            let runner: Box<dyn Fn(MonomialOrder, &F4Options) -> Option<F4Statistics>> =
                Box::new(move |order, options| {
                    f4_with_options(&$system, order, options)
                        .ok()
                        .map(|(_, statistics)| statistics)
                });
            ($name, $order, runner)
        }};
    }

    vec![
        entry!("cyclic-5", MonomialOrder::Lexicographic, cyclic::<5, F>()),
        entry!("katsura-5", MonomialOrder::Lexicographic, katsura::<5, F>()),
        entry!("katsura-6", MonomialOrder::Lexicographic, katsura::<6, F>()),
        entry!(
            "katsura-6",
            MonomialOrder::GradedReverseLexicographic,
            katsura::<6, F>()
        ),
        entry!(
            "katsura-7",
            MonomialOrder::GradedLexicographic,
            katsura::<7, F>()
        ),
    ]
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
        interreduction: InterreductionRoute::Matrix,
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

/// #331: what a 32-bit calibrated divisor mask would have decided in symbolic preprocessing.
///
/// #585 stage 1: how much of `symbolic` is the divisor search, as a projection.
///
/// The end-to-end saving a divisor mask could buy is
///
/// ```text
///   symbolic's share of the run            (measured, 23% on katsura-6 lex)
///     x  the divisor search's share of symbolic      <- this binary
///     x  the mask's hit rate                 (measured by `divmask`, 96.7%)
///     x  (1 - mask cost / exponent-compare cost)     <- stage 2's, if there is one
/// ```
///
/// and #585 gates the kernel on the second factor rather than building first. If the divisor
/// search is a small share of `symbolic`, a 96.7% hit rate on it is a null result and the axis
/// retires.
///
/// # Why this is a projection and says so
///
/// Timing the search directly would mean a clock per divisibility test, and `measure_stages`
/// already reads one four times per *batch* for a reason — per-test timing would measure itself.
/// So this multiplies two things that are each cheap to get honestly:
///
/// - `divisor_scan_steps`, which the shipped scan increments once per test unconditionally, at one
///   add per test. Free, exact, machine-independent.
/// - a per-step cost, taken by running `MonicBasis::find_divisor_with` — **the shipped scan
///   itself**, not a reconstruction of it — over a real basis and dividing by the steps it reports.
///   The counter the cost is divided by is the same counter the projection multiplies, so the loop
///   overhead, the early exit and the branch behaviour are all inside the figure rather than
///   assumed away.
///
/// The product is a *projection* and is labelled one in the output. What makes it trustworthy
/// enough to gate a decision on is that both factors come from the shipped code at the shipped
/// optimization level in the same binary.
///
/// # The two bounds
///
/// A negative answer exits `checked_div` early and a positive one compares every variable, so the
/// per-step cost is not one number. Both are measured and the projection is reported as a range:
/// the search cannot be cheaper than the all-negative figure implies nor dearer than the
/// all-positive one, and `divmask`'s measured negative share says which end the truth sits near.
fn symbolic_split() {
    println!();
    println!("## #585 stage 1: the divisor search's share of `symbolic`, projected");
    println!();
    println!("ISA: {}", zeebra::util::isa_floor());
    println!();
    println!("`symbolic/ms` and `run/ms` are measured. `steps` is the exact count the shipped");
    println!("scan increments, one add per divisibility test. `ns/step-` and `ns/step+` are the");
    println!("per-step cost of `MonicBasis::find_divisor_with` itself over a real basis, divided");
    println!("by the steps it reported, for an all-negative and an all-positive population — a");
    println!("negative answer exits early, so the two bracket the truth.");
    println!();
    println!("`search%` is the projection: steps x per-step cost, over the measured `symbolic`.");
    println!("It is a **projection, not a measurement**, which is the honest label #585 asks for.");
    println!("`of run%` carries it to the whole run, which is the factor the mask's 96.7% hit");
    println!("rate would multiply.");
    println!();
    println!(
        "{:<12} {:<8} {:>5} {:>11} {:>9} {:>13} {:>9} {:>9} {:>16} {:>12}",
        "system",
        "order",
        "vars",
        "symbolic/ms",
        "run/ms",
        "steps",
        "ns/step-",
        "ns/step+",
        "search% of sym",
        "of run%"
    );
    println!(
        "{}",
        [14usize, 10, 7, 13, 11, 15, 11, 11, 18, 14]
            .iter()
            .map(|w| "-".repeat(*w))
            .collect::<Vec<_>>()
            .join("|")
    );

    macro_rules! go {
        ($n:literal, $label:expr, $system:expr, $order:expr, $order_name:expr) => {{
            let system: Vec<MultivariatePolynomial<$n, F>> = $system;
            // `measure_stages` only, never `measure_divmask`: that one replays every scan and
            // would be timing a different program.
            let options = F4Options {
                measure_stages: true,
                ..F4Options::default()
            };
            let (basis, statistics) = f4_with_options(&system, $order, &options)
                .expect("the instance finishes under the default budget");

            let (negative_ns, positive_ns) = per_step_cost::<$n>(&basis, $order);
            let steps = statistics.divisor_scan_steps as f64;
            let symbolic_ms = millis(statistics.stages.symbolic);
            let run_ms = millis(statistics.total);
            // The projection, at both ends of the per-step bracket.
            let low_ms = steps * negative_ns / 1e6;
            let high_ms = steps * positive_ns / 1e6;
            let share = |ms: f64| if symbolic_ms > 0.0 { 100.0 * ms / symbolic_ms } else { 0.0 };
            let of_run = |ms: f64| if run_ms > 0.0 { 100.0 * ms / run_ms } else { 0.0 };

            println!(
                "{:<12} {:<8} {:>5} {:>11.2} {:>9.2} {:>13} {:>9.1} {:>9.1} {:>7.1}-{:>6.1}%                  {:>5.1}-{:>5.1}%",
                $label,
                $order_name,
                $n,
                symbolic_ms,
                run_ms,
                statistics.divisor_scan_steps,
                negative_ns,
                positive_ns,
                share(low_ms),
                share(high_ms),
                of_run(low_ms),
                of_run(high_ms)
            );
        }};
    }

    go!(
        6,
        "katsura-6",
        katsura::<6, F>(),
        MonomialOrder::Lexicographic,
        "lex"
    );
    go!(
        7,
        "katsura-7",
        katsura::<7, F>(),
        MonomialOrder::GradedLexicographic,
        "grlex"
    );
    go!(
        6,
        "katsura-6",
        katsura::<6, F>(),
        MonomialOrder::GradedLexicographic,
        "grlex"
    );
    go!(
        5,
        "cyclic-5",
        cyclic::<5, F>(),
        MonomialOrder::GradedReverseLexicographic,
        "grevlex"
    );

    println!();
    println!("The two `symbolic`-share columns are the second factor of #585's product. Carried");
    println!("through the other three — symbolic's share of the run, the 96.7% hit rate, and the");
    println!("mask's own cost, which stage 2 would have to measure — they bound what a shipped");
    println!("mask could save end to end.");
}

/// The per-step cost of the shipped divisor scan, in nanoseconds, as (all-negative, all-positive).
///
/// Runs `MonicBasis::find_divisor_with` — the function symbolic preprocessing calls — and divides
/// by the `divisor_scan_steps` it reports, so the quotient is the real loop's cost per test rather
/// than an isolated `checked_div`.
///
/// The all-positive population asks for each basis element's own leading monomial, which divides
/// and so makes the scan compare every variable before returning. The all-negative one asks for a
/// monomial built to be divisible by nothing in the basis — one with a single variable at exponent
/// one, below every lead — so every step fails and exits early.
fn per_step_cost<const N: usize>(
    basis: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
) -> (f64, f64) {
    use zeebra::grobner::f4::MonicBasis;
    use zeebra::grobner::{ReducerSelection, SymbolicCounts};
    use zeebra::Monomial;

    let monic = MonicBasis::new(basis, order);
    let leads: Vec<Monomial<N>> = basis
        .iter()
        .map(|element| element.leading_monomial(order))
        .collect();
    // Divisible by nothing: a single variable at exponent one is below every lead of a basis whose
    // elements all have positive degree, and the asserted step count below is what checks that the
    // population really is all-negative rather than merely intended to be.
    let mut exponents = [0u32; N];
    exponents[N - 1] = 1;
    let miss = Monomial::new(&exponents);

    let cost = |queries: &[Monomial<N>], repetitions: usize| -> (f64, usize) {
        let mut counts = SymbolicCounts::default();
        let start = Instant::now();
        for _ in 0..repetitions {
            for query in queries {
                std::hint::black_box(monic.find_divisor_with(
                    query,
                    ReducerSelection::FirstApplicable,
                    &mut counts,
                ));
            }
        }
        let elapsed = start.elapsed().as_secs_f64();
        (elapsed, counts.divisor_scan_steps)
    };

    // Enough repetitions that the clock is not the measurement, and the step count scales with it
    // so the quotient does not care how many there were.
    let repetitions = 2_000;
    let (negative_seconds, negative_steps) = cost(&[miss], repetitions * leads.len().max(1));
    let (positive_seconds, positive_steps) = cost(&leads, repetitions);

    // The all-negative population must have scanned the whole basis every time, or it was not
    // all-negative and the bracket's lower end is wrong.
    assert_eq!(
        negative_steps,
        repetitions * leads.len().max(1) * leads.len(),
        "the miss monomial was divisible by something, so this is not an all-negative population"
    );

    let per = |seconds: f64, steps: usize| {
        if steps == 0 {
            0.0
        } else {
            seconds * 1e9 / steps as f64
        }
    };
    (
        per(negative_seconds, negative_steps),
        per(positive_seconds, positive_steps),
    )
}

/// Counters only, which is what the issue asks for: `F4Options::measure_divmask` replays each
/// divisibility test against the mask *after* the real answer is known, so nothing a mask could get
/// wrong can reach the basis. The run is therefore slower than a shipping one and its durations are
/// not quotable — the three columns are exact and machine-independent, which is the whole reason to
/// settle this before writing a kernel.
///
/// The two instances are the ones #331 names, because the decision is per instance and not global:
/// `MILESTONE-F4-OPTIMIZATION.md` §8.5 puts `symbolic` at **23% of katsura-6 lex** and **5% of
/// katsura-7 grlex**, so the same mask hit rate is worth four times as much on the first.
fn divmask_counters() {
    println!();
    println!("## #331: the divisor mask, counted rather than used");
    println!();
    println!("ISA: {}", zeebra::util::isa_floor());
    println!("mask width: {} bits", zeebra::grobner::DIVMASK_BITS);
    println!();
    println!("`tests` is divisibility tests symbolic preprocessing performed — the same");
    println!("population as `scan` under the shipping scan, asserted equal by");
    println!("`test_the_probe_replays_exactly_the_scan_the_policy_performed`. `neg` answered");
    println!("not-divisible, which is all a mask can ever shortcut. `decided` is the subset a");
    println!("32-bit mask with input-calibrated thresholds settles without an exponent compare.");
    println!("`of neg` and `of tests` are that subset over each denominator; the second is the");
    println!("one that bounds what a kernel could save, because a positive answer stays in the");
    println!("stage's cost whatever the representation.");
    println!();
    println!("`tests/q` is tests per divisor lookup, which is what the dividend's own mask");
    println!("amortizes over: the lead masks are cached on the basis the way msolve caches");
    println!("`bs->lm`, so the only mask a query has to build is the one it asks about. That is");
    println!("the figure that decides whether `Monomial<N>` has to carry a mask field at all.");
    println!();
    println!("`maxexp` is the largest exponent in the input, which is what the thresholds are");
    println!("calibrated from. Each variable gets `32/vars` bits, and an input whose exponent");
    println!("range is at or below that count calibrates to unit steps — exactly the thresholds");
    println!("a fixed scheme would pick. Where that holds the calibration earns nothing, and");
    println!("msolve's reason for having one is inputs with ranges wide enough to need it.");
    println!();
    println!(
        "{:<12} {:<8} {:>5} {:>7} {:>7} {:>12} {:>12} {:>12} {:>8} {:>9} {:>8}",
        "system",
        "order",
        "vars",
        "bits/v",
        "maxexp",
        "tests",
        "neg",
        "decided",
        "of neg",
        "of tests",
        "tests/q"
    );

    macro_rules! go {
        ($n:literal, $label:expr, $system:expr, $order:expr, $order_name:expr) => {{
            let system: Vec<MultivariatePolynomial<$n, F>> = $system;
            let options = F4Options {
                measure_divmask: true,
                ..F4Options::default()
            };
            let maximum_exponent = system
                .iter()
                .flat_map(|polynomial| polynomial.terms().keys())
                .flat_map(|monomial| monomial.exponents().iter().copied())
                .max()
                .unwrap_or(0);
            let (_, statistics) = f4_with_options(&system, $order, &options)
                .expect("the instance finishes under the default budget");
            let negative = statistics.divmask_negative.max(1) as f64;
            println!(
                "{:<12} {:<8} {:>5} {:>7} {:>7} {:>12} {:>12} {:>12} {:>7.1}% {:>8.1}% {:>8.1}",
                $label,
                $order_name,
                $n,
                zeebra::grobner::DIVMASK_BITS / $n,
                maximum_exponent,
                statistics.divmask_tests,
                statistics.divmask_negative,
                statistics.divmask_decided,
                100.0 * statistics.divmask_decided as f64 / negative,
                100.0 * statistics.divmask_decided_share(),
                statistics.divisor_scan_steps_per_query()
            );
        }};
    }

    go!(
        6,
        "katsura-6",
        katsura::<6, F>(),
        MonomialOrder::Lexicographic,
        "lex"
    );
    go!(
        7,
        "katsura-7",
        katsura::<7, F>(),
        MonomialOrder::GradedLexicographic,
        "grlex"
    );
    // Two controls. katsura-6 grlex is the same ideal under the order where `symbolic` is small,
    // which separates "the mask works here" from "this order asks a lot of divisibility
    // questions"; cyclic-5 is a different family, so a hit rate that is a property of katsura
    // rather than of the technique shows up as a disagreement.
    go!(
        6,
        "katsura-6",
        katsura::<6, F>(),
        MonomialOrder::GradedLexicographic,
        "grlex"
    );
    go!(
        5,
        "cyclic-5",
        cyclic::<5, F>(),
        MonomialOrder::GradedReverseLexicographic,
        "grevlex"
    );
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
            "modes: mq (the #349 competitive MQ stage split), mq-counts (its operation
             counts), mq-matrix (#471's interreduction route A/B), mq-rows (#477's
             batch row form A/B), mq-instance (its canonical text), divmask,\n             symbolic-split (#585 stage 1)
             (#331's divisor-mask counters), construction (#330's four-way split of
             the construction stage), scatter (#582's four-way split of the scatter),
             handles (#621's A/B of the handle scatter against the hashing one)"
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

    if argument == "construction" {
        // #330's measurement, and its refutation condition: the two phases a column-index handout
        // would remove, priced against the scatter it would not.
        println!();
        println!("## #330: matrix construction, split four ways");
        println!();
        println!("ISA: {}", zeebra::util::isa_floor());
        println!(
            "`collect` is the distinct-monomial set, `sort` the column order, `map` the\n\
             monomial-to-column map, `scatter` writing the rows through it. `criterion` is\n\
             (collect+sort+map)/construction, the quantity #330 stated its kill criterion on:\n\
             under 33% the issue closes. `removable` is (collect+map)/construction — what a\n\
             column-index handout would actually remove, since interning with an index does not\n\
             remove anybody's column sort."
        );
        println!();
        construction_split();
        println!();
        println!("### The handout against the rehashing it replaces, one process, one build");
        println!();
        construction_routes();
        return;
    }

    if argument == "handles" {
        // #621: the per-entry hash read the scatter was 81-89%, against reading the column off the
        // handle symbolic preprocessing already assigned.
        println!();
        println!("## #621: the handle scatter against the hashing scatter");
        println!();
        println!("ISA: {}", zeebra::util::isa_floor());
        println!(
            "One process, one build, arms interleaved with the order rotated per repetition and\n\
             each min-reduced over its own runs. Both arms read the same `Preprocessed`, built\n\
             once per batch outside the timing. Every pair of matrices asserted equal.\n\
             `entries/col` is #621's kill criterion: under 2.0 the restructuring buys nothing,\n\
             because the per-entry lookup can be removed at most once per entry."
        );
        println!();
        scatter_routes();
        return;
    }

    if argument == "scatter" {
        // #582: construction is now the scatter, and nothing had ever been inside it.
        println!();
        println!("## #582: the row scatter, split four ways");
        println!();
        println!("ISA: {}", zeebra::util::isa_floor());
        println!(
            "`rows` and `assm` are the scatter's two clocked halves: the per-row loop and\n\
             `SparseMatrix::new` plus the row-provenance copy. `shift`, `lookup` and `rowbuild`\n\
             are per *term* and come from a nested ablation instead, because a clock read costs\n\
             more than a term's work: each arm is a prefix of the next and adjacent arms are\n\
             differenced. `ablat` is the ablation's full arm, which is the shipping loop verbatim,\n\
             so `ablat` against `rows` is the control. `lookup%` is the per-term map lookup over\n\
             the whole scatter — under a third, #582 says to close and stop working on\n\
             construction."
        );
        println!();
        scatter_split();
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

    if argument == "mq-rows" {
        // #477: does making each batch's candidates come out reduced pay for the second pass it
        // costs? Crossed with the interreduction route, because the payoff lands in a different
        // place on each — a smaller autoreduce matrix on the matrix route, fewer term rewrites on
        // the division one — and the division route is what ships today.
        println!();
        println!("## #477: batch rows left echelon against left reduced");
        println!();
        println!("ISA: {}", zeebra::util::isa_floor());
        println!("instance digest: {}", RECORDED_DIGEST);
        println!();
        println!("Four arms: both interreduction routes crossed with both batch row forms,");
        println!("interleaved in one process on one build. The division arms are the ones that");
        println!("describe the shipping default. Every basis asserted equal to the first.");
        println!();
        compare_batch_row_forms();
        println!();
        println!("### The classical rungs, where a default flip would have to survive");
        println!();
        println!("Division interreduction on both arms, which is the shipping default. Minimum of");
        println!("7 interleaved repetitions. katsura-5 under lex is here deliberately: it is the");
        println!("rung the matrix interreduction route regresses 25x on.");
        println!();
        compare_batch_row_forms_on_the_rungs();
        return;
    }

    if argument == "symbolic-split" {
        // #585 stage 1. A projection, labelled as one; see `symbolic_split`.
        symbolic_split();
        return;
    }

    if argument == "divmask" {
        divmask_counters();
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
