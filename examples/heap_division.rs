//! #562's A/B: Monagan–Pearce heap division against the merge route, on the consumers that still
//! divide.
//!
//! ```text
//! cargo run --release --example heap_division                         # every workload, 5 reps
//! cargo run --release --example heap_division -- --reps 9 border-katsura-7 lex-katsura-6
//! ```
//!
//! One binary, a runtime switch ([`DivisionRoute`]) and the two routes **interleaved** within each
//! rep, with the arm order alternating rep to rep, so drift in the machine's load lands on both arms
//! rather than on whichever ran second. Every workload's outputs are asserted equal across the
//! routes before anything is timed: the heap is only worth timing if it computes the same thing.
//!
//! Workloads, chosen because each is a caller that still takes the division route by default or is
//! the instance the counters were taken on:
//!
//! - `border-*`: FGLM's scalar border reduction — every border monomial of a grevlex basis reduced
//!   against that basis, which is `reduce_border_monomial`'s loop.
//! - `lex-*`: final interreduction of a lex basis. `InterreductionRoute::ByOrder` keeps lex on the
//!   division route, so this is the shipping default's path. `katsura-7` under lex refuses at the
//!   trace's live-nonzero budget, so that ladder stops at 6.
//! - `mq-random-10`: final interreduction under grevlex on the digest-pinned instance
//!   `docs/research/interreduction-cost.md` §3d counted. Not the default path since #471.
//! - `mdr-border-*`: the border workload through `multi_div_rem`, whose merge route is the
//!   hash-map oracle rather than `normal_form`.

use std::time::{Duration, Instant};

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura},
        external::{instance, REFERENCE_CHARACTERISTIC},
        f4,
        f4::{observer::TracedBatch, reduce_batch},
        fglm::{BorderIndex, QuotientBasis},
        interreduce_with_route_for_benchmark, trace_batches, F4Options, InterreductionRoute,
    },
    util::isa_floor,
    DivisionRoute, MonomialOrder, MultivariatePolynomial, One,
};

type F = Zp2147483647;

/// The digest `docs/research/interreduction-cost.md` §3's `mq-random-10` figures were taken on.
const RECORDED_DIGEST: &str = "72d0ad315fc25409792625465578d18329597d3ee183e75f257774d9215803b2";

const ROUTES: [DivisionRoute; 2] = [DivisionRoute::Merge, DivisionRoute::Heap];

fn millis(d: Duration) -> f64 {
    d.as_secs_f64() * 1e3
}

fn median(values: &mut [f64]) -> f64 {
    values.sort_by(f64::total_cmp);
    let n = values.len();
    if n % 2 == 1 {
        values[n / 2]
    } else {
        (values[n / 2 - 1] + values[n / 2]) / 2.0
    }
}

/// Time `run` under each route for `reps` interleaved reps and print one row per rep and a summary.
fn ab(name: &str, reps: usize, mut run: impl FnMut(DivisionRoute) -> Duration) {
    let mut merge = Vec::with_capacity(reps);
    let mut heap = Vec::with_capacity(reps);
    for rep in 0..reps {
        // Alternate which arm goes first, so a monotone drift cannot favour one.
        let arms = if rep % 2 == 0 {
            [ROUTES[0], ROUTES[1]]
        } else {
            [ROUTES[1], ROUTES[0]]
        };
        let mut times = [0.0f64; 2];
        for route in arms {
            let elapsed = millis(run(route));
            times[usize::from(route == DivisionRoute::Heap)] = elapsed;
        }
        println!(
            "| {:<20} | {:>3} | {:>12.2} | {:>12.2} | {:>7.3}x |",
            name,
            rep + 1,
            times[0],
            times[1],
            times[0] / times[1]
        );
        merge.push(times[0]);
        heap.push(times[1]);
    }
    let mut ratios: Vec<f64> = merge.iter().zip(&heap).map(|(m, h)| m / h).collect();
    let spread = |v: &[f64]| {
        v.iter().copied().fold(f64::MIN, f64::max) / v.iter().copied().fold(f64::MAX, f64::min)
    };
    let (merge_spread, heap_spread) = (spread(&merge), spread(&heap));
    let wins = ratios.iter().filter(|r| **r > 1.0).count();
    println!(
        "| {:<20} | med | {:>12.2} | {:>12.2} | {:>7.3}x | merge spread {:.3}x, heap spread {:.3}x, heap faster {}/{}",
        name,
        median(&mut merge.clone()),
        median(&mut heap.clone()),
        median(&mut ratios),
        merge_spread,
        heap_spread,
        wins,
        reps
    );
}

/// Every border monomial of `source`'s quotient, as one-term polynomials.
fn border_terms<const N: usize>(
    source: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
) -> Vec<MultivariatePolynomial<N, F>> {
    let quotient = QuotientBasis::new(source, order, usize::MAX).expect("zero-dimensional");
    BorderIndex::new(&quotient)
        .monomials()
        .iter()
        .map(|m| MultivariatePolynomial::new(&[(*m, F::one())]))
        .collect()
}

fn border<const N: usize>(
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
    reps: usize,
    inner: usize,
) {
    let order = MonomialOrder::GradedReverseLexicographic;
    let source = f4(system, order).expect("within limits");
    let terms = border_terms(&source, order);
    for term in &terms {
        assert_eq!(
            term.normal_form_with(&source, order, DivisionRoute::Heap),
            term.normal_form(&source, order),
            "{name}: the routes disagree"
        );
    }
    println!(
        "# {name}: {} border monomials against {} elements, the border {inner}x a sample",
        terms.len(),
        source.len()
    );
    ab(name, reps, |route| {
        let at = Instant::now();
        for _ in 0..inner {
            for term in &terms {
                std::hint::black_box(term.normal_form_with(&source, order, route));
            }
        }
        at.elapsed()
    });
}

fn multi_div_rem_border<const N: usize>(
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
    reps: usize,
    inner: usize,
) {
    let order = MonomialOrder::GradedReverseLexicographic;
    let source = f4(system, order).expect("within limits");
    let terms = border_terms(&source, order);
    for term in &terms {
        assert_eq!(
            term.multi_div_rem_with(&source, order, DivisionRoute::Heap),
            term.multi_div_rem(&source, order),
            "{name}: the routes disagree"
        );
    }
    println!(
        "# {name}: {} border monomials against {} elements, the border {inner}x a sample",
        terms.len(),
        source.len()
    );
    ab(name, reps, |route| {
        let at = Instant::now();
        for _ in 0..inner {
            for term in &terms {
                std::hint::black_box(term.multi_div_rem_with(&source, order, route));
            }
        }
        at.elapsed()
    });
}

/// The basis entering final interreduction: the last traced batch's basis plus its candidates,
/// replayed — the same reconstruction `examples/interreduction_repeats.rs` makes.
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
    let outcome = reduce_batch(&last.basis, &last.pairs, order, options)
        .expect("the batch ran once already under these options");
    basis.extend(outcome.candidates);
    basis
}

fn interreduction<const N: usize>(
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    reps: usize,
    inner: usize,
) {
    // Candidates in echelon form (`reduce_batch_rows` off), because that is the input §3 counted;
    // the route is named so the trace does not depend on the default.
    let options = F4Options {
        reduce_batch_rows: false,
        interreduction: InterreductionRoute::Division,
        ..F4Options::recommended()
    };
    let (_, _, trace) = trace_batches(system, order, &options).expect("within limits");
    let basis = pre_interreduction_basis(trace.batches(), order, &options);
    assert_eq!(
        interreduce_with_route_for_benchmark(basis.clone(), order, DivisionRoute::Heap),
        interreduce_with_route_for_benchmark(basis.clone(), order, DivisionRoute::Merge),
        "{name}: the routes disagree"
    );
    println!(
        "# {name}: {} elements entering interreduction, the stage {inner}x a sample",
        basis.len()
    );
    ab(name, reps, |route| {
        // Cloned before the clock starts: the stage consumes its input.
        let inputs: Vec<_> = (0..inner).map(|_| basis.clone()).collect();
        let at = Instant::now();
        for input in inputs {
            std::hint::black_box(interreduce_with_route_for_benchmark(input, order, route));
        }
        at.elapsed()
    });
}

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
        "not the instance §3 counted"
    );
    let names: Vec<&str> = built.variables.iter().map(String::as_str).collect();
    let mut compiled = [""; 10];
    compiled.copy_from_slice(&names[..10]);
    built
        .system
        .iter()
        .map(|text| MultivariatePolynomial::parse(text, compiled).expect("rendered by this crate"))
        .collect()
}

const WORKLOADS: [&str; 7] = [
    "border-katsura-7",
    "border-cyclic-6",
    "mdr-border-katsura-5",
    "lex-katsura-5",
    "lex-katsura-6",
    "lex-cyclic-5",
    "mq-random-10",
];

fn main() {
    let mut reps = 5;
    let mut wanted: Vec<String> = Vec::new();
    let mut arguments = std::env::args().skip(1);
    while let Some(argument) = arguments.next() {
        if argument == "--reps" {
            reps = arguments
                .next()
                .and_then(|n| n.parse().ok())
                .expect("--reps takes a count");
        } else if WORKLOADS.contains(&argument.as_str()) {
            wanted.push(argument);
        } else {
            eprintln!("unknown workload {argument:?}; known: {WORKLOADS:?}");
            std::process::exit(2);
        }
    }
    if wanted.is_empty() {
        wanted = WORKLOADS.iter().map(|w| w.to_string()).collect();
    }

    println!("# heap division A/B (#562), GF(2^31 - 1), {reps} interleaved reps");
    println!("# {}", isa_floor());
    println!("# ratio = merge / heap, so above 1 means the heap is faster");
    println!();
    println!(
        "| {:<20} | rep | {:>12} | {:>12} | {:>8} |",
        "workload", "merge ms", "heap ms", "ratio"
    );
    let lex = MonomialOrder::Lexicographic;
    for workload in &wanted {
        match workload.as_str() {
            // Inner repeats put every merge-route sample at roughly 150 ms or more.
            "border-katsura-7" => border(workload, &katsura::<7, F>(), reps, 8),
            "border-cyclic-6" => border(workload, &cyclic::<6, F>(), reps, 10),
            "mdr-border-katsura-5" => multi_div_rem_border(workload, &katsura::<5, F>(), reps, 100),
            "lex-katsura-5" => interreduction(workload, &katsura::<5, F>(), lex, reps, 1000),
            "lex-katsura-6" => interreduction(workload, &katsura::<6, F>(), lex, reps, 200),
            "lex-cyclic-5" => interreduction(workload, &cyclic::<5, F>(), lex, reps, 750),
            "mq-random-10" => interreduction(
                workload,
                &mq_random_10(),
                MonomialOrder::GradedReverseLexicographic,
                reps,
                1,
            ),
            _ => unreachable!("filtered above"),
        }
    }
}
