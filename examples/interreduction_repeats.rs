//! How much of the final interreduction's work is work an earlier element's reduction already did.
//!
//! #436's candidate 2, the one its other three were adjudicated without: element `i` and element
//! `i + 1` are reduced against almost the same divisor set, and nothing is cached between them.
//! `NormalFormCounts` cannot answer it — every field there is per-call and summed, so 247
//! reductions against overlapping divisors sum identically to 247 unrelated ones
//! (`docs/research/interreduction-cost.md` §3g.2).
//!
//! The quantity this prints is the **repeat rate**: over the stage's reduction steps, the share
//! whose `(quotient monomial, reducer leading monomial)` pair an earlier step already took, and
//! the share of those whose reducer tail was unchanged — the only ones a cache could have served.
//! The loop rewrites each element in place as it goes, so the second is not implied by the first
//! in general; in this loop it turns out to equal it, for the reason
//! `buchberger::interreduction_stop_tests::test_every_repeat_in_the_interreduction_loop_is_reusable`
//! pins. Both are reported, because an instrument that assumed the equality could not have found
//! it.
//!
//! Counts, not durations. They are exact and machine-independent, so this example is not a
//! benchmark and its numbers do not move with the box's load.
//!
//! ```text
//! cargo run --release --example interreduction_repeats
//! cargo run --release --example interreduction_repeats -- katsura-6 --order lex
//! ```
//!
//! Two input arms per rung, because the input decides the stage:
//!
//! - `echelon` is [`F4Options::baseline`]'s candidate form, which every figure in §3 was taken
//!   under.
//! - `reduced` is `reduce_batch_rows`, which `F4Options::recommended` carries since #575: a
//!   candidate leaves its batch already in normal form, so the stage has far less to do.
//!
//! The stage itself is run by the **division** route in both arms, because that is the route
//! candidate 2 is about. Under the shipping default this rung does not take it at all — the
//! order is graded, so `InterreductionRoute::ByOrder` builds one Macaulay matrix and the loop
//! never runs — which is itself the first thing #569 has to be read against.

use zeebra::{
    grobner::{
        benchmark_systems::{cyclic, katsura},
        external::{instance, REFERENCE_CHARACTERISTIC},
        f4::{observer::TracedBatch, reduce_batch},
        interreduce_counting_repeats_for_benchmark, trace_batches, F4Options, InterreductionRoute,
    },
    util::isa_floor,
    MonomialOrder, MultivariatePolynomial,
};

type F = zeebra::fields::Zp2147483647;

/// The digest the `mq-random-10` figures in `docs/research/interreduction-cost.md` were taken on.
const RECORDED_DIGEST: &str = "72d0ad315fc25409792625465578d18329597d3ee183e75f257774d9215803b2";

/// Whether candidates entered the stage in echelon form or already reduced.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Arm {
    Echelon,
    Reduced,
}

impl Arm {
    fn label(self) -> &'static str {
        match self {
            Self::Echelon => "echelon",
            Self::Reduced => "reduced",
        }
    }

    /// The options the *trace* runs under. Only `reduce_batch_rows` differs, because only it
    /// changes the basis the stage is handed.
    fn options(self) -> F4Options {
        F4Options {
            reduce_batch_rows: self == Self::Reduced,
            // The route is irrelevant to the trace — the batches are the same either way — but
            // naming it keeps this from depending on whatever the default becomes next.
            interreduction: InterreductionRoute::Division,
            ..F4Options::recommended()
        }
    }
}

/// The basis entering the final interreduction, reconstructed exactly.
///
/// The last traced batch's basis **plus that batch's candidates**, which is what `f4_into` hands
/// the stage. The candidates are not in the trace, so the batch is replayed to produce them — the
/// batch's result is a function of its input and the options, which is what makes the replay the
/// same candidates rather than merely similar ones. `benches/f4_stages.rs` uses the basis alone
/// and so measures a slightly smaller input; the element count printed here is what lets this be
/// compared against the stage §3 measured.
fn pre_interreduction_basis<const N: usize>(
    batches: &[TracedBatch<N, F>],
    order: MonomialOrder,
    options: &F4Options,
) -> Vec<MultivariatePolynomial<N, F>> {
    let Some(last) = batches.last() else {
        return Vec::new();
    };
    let mut basis: Vec<MultivariatePolynomial<N, F>> = (0..last.basis.len())
        .map(|i| MultivariatePolynomial::new(&last.basis.element(i).terms))
        .collect();
    match reduce_batch(&last.basis, &last.pairs, order, options) {
        Ok(outcome) => basis.extend(outcome.candidates),
        // A refused replay would be a defect rather than a finding — the batch ran once already,
        // under these options, to get into the trace at all.
        Err(error) => panic!("replaying the last traced batch: {:?}", error),
    }
    basis
}

fn header() {
    println!(
        "{:<14} {:<8} {:<8} {:>5} {:>5} {:>9} {:>8} {:>8} {:>8} {:>7} {:>12} {:>14} {:>7}",
        "system",
        "order",
        "arm",
        "elts",
        "calls",
        "steps",
        "pairs",
        "repeat%",
        "reuse%",
        "within",
        "tails",
        "rewritten",
        "cache%"
    );
}

fn run<const N: usize>(
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    order_name: &str,
) {
    for arm in [Arm::Echelon, Arm::Reduced] {
        let options = arm.options();
        let Ok((_, _, trace)) = trace_batches(system, order, &options) else {
            println!("{:<14} {:<8} {:<8} refused", name, order_name, arm.label());
            continue;
        };
        let basis = pre_interreduction_basis(trace.batches(), order, &options);
        if basis.len() < 2 {
            println!(
                "{:<14} {:<8} {:<8} one element, nothing to repeat against",
                name,
                order_name,
                arm.label()
            );
            continue;
        }
        let elements = basis.len();
        let (_, counts, repeats) = interreduce_counting_repeats_for_benchmark(basis, order);

        // The tracker counts the same steps the per-call counters do, so a divergence here is an
        // instrument fault rather than a finding.
        assert_eq!(
            repeats.steps(),
            counts.reduction_steps,
            "the repeat tracker and the step counter must see the same steps"
        );

        // What a cache keyed on the pair would hold is the *shifted tail*, so the share of the
        // stage's term traffic it could address is the tail terms against the terms rewritten.
        // The merge of a shifted tail into the working polynomial is not cacheable — the working
        // polynomial differs at every step — and §3d measured that merge as where the cost is.
        let cache_share = if counts.terms_rewritten == 0 {
            0.0
        } else {
            counts.tail_terms_merged as f64 / counts.terms_rewritten as f64
        };
        println!(
            "{:<14} {:<8} {:<8} {:>5} {:>5} {:>9} {:>8} {:>8.2} {:>8.2} {:>7} {:>12} {:>14} {:>7.2}",
            name,
            order_name,
            arm.label(),
            elements,
            counts.calls,
            counts.reduction_steps,
            repeats.distinct_pairs(),
            100.0 * repeats.repeat_rate(),
            100.0 * repeats.reusable_rate(),
            repeats.repeated_steps_within_one_call(),
            counts.tail_terms_merged,
            counts.terms_rewritten,
            100.0 * cache_share,
        );
    }
}

/// The digest-pinned `mq-random-10` system, built through the comparison corpus.
fn mq_random_10() -> Vec<MultivariatePolynomial<10, F>> {
    let built = instance(
        "mq-random-10",
        REFERENCE_CHARACTERISTIC,
        MonomialOrder::GradedReverseLexicographic,
    )
    .expect("mq-random-10 is a corpus rung with a compiled dimension");
    assert_eq!(
        built.digest(),
        RECORDED_DIGEST,
        "the generated instance is not the one §3's figures were measured on"
    );
    let names: Vec<&str> = built.variables.iter().map(String::as_str).collect();
    let mut compiled = [""; 10];
    compiled.copy_from_slice(&names[..10]);
    built
        .system
        .iter()
        .map(|text| {
            MultivariatePolynomial::parse(text, compiled).expect("this crate rendered this text")
        })
        .collect()
}

fn order_named(name: &str) -> Option<(MonomialOrder, &'static str)> {
    match name {
        "grevlex" => Some((MonomialOrder::GradedReverseLexicographic, "grevlex")),
        "grlex" => Some((MonomialOrder::GradedLexicographic, "grlex")),
        "lex" => Some((MonomialOrder::Lexicographic, "lex")),
        _ => None,
    }
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let mut rungs: Vec<String> = Vec::new();
    let mut order = (MonomialOrder::GradedReverseLexicographic, "grevlex");
    let mut index = 0;
    while index < arguments.len() {
        match arguments[index].as_str() {
            "--order" => {
                index += 1;
                let Some(named) = arguments.get(index).and_then(|n| order_named(n)) else {
                    eprintln!("--order takes grevlex, grlex or lex");
                    std::process::exit(2);
                };
                order = named;
            }
            rung => rungs.push(rung.to_string()),
        }
        index += 1;
    }
    if rungs.is_empty() {
        rungs.push("mq-random-10".to_string());
    }

    println!("# interreduction repeat rate — #436's candidate 2, #569");
    println!("# {}", isa_floor());
    println!(
        "# `repeat%` is reduction steps whose (quotient, reducer lead) pair recurred; `reuse%` is"
    );
    println!(
        "# those whose reducer tail was unchanged, which is the share a cache could have served."
    );
    println!("# `within` is repeats inside one call, which the loop's shape makes zero.");
    println!("# `elts` is the input; `calls` is what minimization left of it, one reduction each.");
    println!(
        "# `cache%` is tail terms against terms rewritten: the share of the stage's term traffic a"
    );
    println!("# cache of shifted tails could address at all, whatever its hit rate.");
    println!();
    header();
    for rung in &rungs {
        match rung.as_str() {
            "mq-random-10" => run("mq-random-10", &mq_random_10(), order.0, order.1),
            "katsura-5" => run("katsura-5", &katsura::<5, F>(), order.0, order.1),
            "katsura-6" => run("katsura-6", &katsura::<6, F>(), order.0, order.1),
            "katsura-7" => run("katsura-7", &katsura::<7, F>(), order.0, order.1),
            "cyclic-5" => run("cyclic-5", &cyclic::<5, F>(), order.0, order.1),
            "cyclic-6" => run("cyclic-6", &cyclic::<6, F>(), order.0, order.1),
            other => {
                eprintln!("unknown rung {:?}", other);
                std::process::exit(2);
            }
        }
    }
}
