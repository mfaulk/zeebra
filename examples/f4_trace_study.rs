//! How often a conventional-F4 trace transfers across instances of one shape (#1190).
//!
//! For each family, learns a trace on seed 0 and compares it with the trace of seeds
//! `1..=--seeds` (default 30). Two variants per family: `coefficients` redraws every coefficient
//! on the template's support; `constants` keeps the seed-0 coefficients and changes only the
//! constants (for dense MQ, a fresh planted point — the guessed-value / CICO-target analogue).
//! Prints one Markdown row per family: how many instances the trace replays on exactly, the
//! first divergence of the rest by kind, and the share of pair rows and of pair-row products that
//! end zero — what a replay skips in elimination. Counts are deterministic; nothing is timed.
//!
//! `cargo run --release --example f4_trace_study -- [--seeds=N] [--quick]`
use rand::{rngs::StdRng, Rng, SeedableRng};
use std::collections::BTreeMap;
use zeebra::{
    fields::{Zp2147483647, Zp541, Zp65537},
    grobner::{
        benchmark_systems::{cyclic, eco, katsura},
        f4::tracing::{compare, learn, Divergence, F4Trace},
        F4Options,
    },
    KnownOrder, Monomial, MonomialOrder, MultivariatePolynomial,
};

#[derive(Clone, Copy)]
enum Variant {
    Coefficients,
    Constants,
}

impl Variant {
    fn name(self) -> &'static str {
        match self {
            Variant::Coefficients => "coefficients",
            Variant::Constants => "constants",
        }
    }
}

fn prime<F: KnownOrder>() -> u64 {
    F::characteristic_limbs()[0]
}

fn nonzero<F: KnownOrder>(rng: &mut StdRng) -> F {
    F::new(rng.gen_range(1..prime::<F>()))
}

/// The template's support with fresh coefficients. `Constants` draws the nonconstant ones from
/// seed 0 and only the constants from `seed`.
fn redraw<const N: usize, F: KnownOrder>(
    template: &[MultivariatePolynomial<N, F>],
    variant: Variant,
    seed: u64,
) -> Vec<MultivariatePolynomial<N, F>> {
    let coefficient_seed = match variant {
        Variant::Coefficients => seed,
        Variant::Constants => 0,
    };
    let mut coefficients = StdRng::seed_from_u64(coefficient_seed);
    let mut constants = StdRng::seed_from_u64(seed ^ 0xC0FF_EE00);
    template
        .iter()
        .map(|p| {
            let mut monomials: Vec<Monomial<N>> = p.terms().keys().copied().collect();
            monomials.sort();
            let terms: Vec<(Monomial<N>, F)> = monomials
                .into_iter()
                .map(|m| {
                    let c = nonzero::<F>(&mut coefficients);
                    if m == Monomial::one() {
                        (m, nonzero::<F>(&mut constants))
                    } else {
                        (m, c)
                    }
                })
                .collect();
            MultivariatePolynomial::new(&terms)
        })
        .collect()
}

/// #945's dense MQ shape: `2N` quadratics with every monomial of degree 1 and 2, planted at a
/// point. Coefficients come from `coefficient_seed`, the point from `point_seed`.
fn dense_mq<const N: usize, F: KnownOrder>(
    coefficient_seed: u64,
    point_seed: u64,
) -> Vec<MultivariatePolynomial<N, F>> {
    let mut point_rng = StdRng::seed_from_u64(point_seed ^ 0x5EED);
    let point: Vec<F> = (0..N)
        .map(|_| F::new(point_rng.gen_range(0..prime::<F>())))
        .collect();
    let mut monomials = Vec::new();
    for i in 0..N {
        for j in i..N {
            let mut e = [0u32; N];
            e[i] += 1;
            e[j] += 1;
            monomials.push(e);
        }
    }
    for i in 0..N {
        let mut e = [0u32; N];
        e[i] = 1;
        monomials.push(e);
    }
    let value = |e: &[u32; N]| {
        e.iter()
            .zip(&point)
            .fold(F::one(), |acc, (&k, &x)| (0..k).fold(acc, |a, _| a * x))
    };
    let mut rng = StdRng::seed_from_u64(coefficient_seed);
    (0..2 * N)
        .map(|_| {
            let mut sum = F::zero();
            let mut terms: Vec<(Monomial<N>, F)> = monomials
                .iter()
                .map(|e| {
                    let c = nonzero::<F>(&mut rng);
                    sum += c * value(e);
                    (Monomial::new(e), c)
                })
                .collect();
            terms.push((Monomial::one(), F::zero() - sum));
            MultivariatePolynomial::new(&terms)
        })
        .collect()
}

#[derive(Default)]
struct Row {
    instances: usize,
    transfers: usize,
    divergences: BTreeMap<&'static str, usize>,
    matched_rounds: Vec<usize>,
    rounds: usize,
    pair_rows: usize,
    zero_rows: usize,
    products: usize,
    zero_products: usize,
}

fn kind(d: Divergence) -> &'static str {
    match d {
        Divergence::Pairs => "pairs",
        Divergence::Support => "support-grew",
        Divergence::SupportShrank => "support-shrank",
        Divergence::KeptRow => "kept-row",
        Divergence::SkippedRow => "SILENT",
        Divergence::Length => "length",
    }
}

fn run<const N: usize, F: KnownOrder>(
    label: &str,
    variant: Variant,
    seeds: u64,
    instance: impl Fn(u64) -> Vec<MultivariatePolynomial<N, F>>,
) {
    let order = MonomialOrder::GradedReverseLexicographic;
    let options = F4Options::default();
    let trace = |seed| -> F4Trace<N> { learn(&instance(seed), order, &options).unwrap().1 };
    let learned = trace(0);
    let mut row = Row {
        rounds: learned.rounds.len(),
        pair_rows: learned.pair_rows(),
        zero_rows: learned.zero_rows(),
        products: learned.products(),
        zero_products: learned.zero_row_products(),
        ..Row::default()
    };
    for seed in 1..=seeds {
        let observed = trace(seed);
        let comparison = compare(&learned, &observed);
        row.instances += 1;
        match comparison.divergence {
            None => row.transfers += 1,
            Some(d) => {
                *row.divergences.entry(kind(d)).or_default() += 1;
                row.matched_rounds.push(comparison.matched_rounds);
            }
        }
    }
    let divergences = if row.divergences.is_empty() {
        "—".to_string()
    } else {
        row.divergences
            .iter()
            .map(|(k, n)| format!("{k} {n}"))
            .collect::<Vec<_>>()
            .join(", ")
    };
    row.matched_rounds.sort();
    let matched = row
        .matched_rounds
        .get(row.matched_rounds.len() / 2)
        .map_or("—".to_string(), |m| m.to_string());
    let pct = |a: usize, b: usize| 100.0 * a as f64 / b.max(1) as f64;
    println!(
        "| {label} | {} | {} | {}/{} | {divergences} | {matched} | {} | {} | {:.1}% | {} | {:.1}% |",
        prime::<F>(),
        variant.name(),
        row.transfers,
        row.instances,
        row.rounds,
        row.pair_rows,
        pct(row.zero_rows, row.pair_rows),
        row.products,
        pct(row.zero_products, row.products),
    );
}

fn templated<const N: usize, F: KnownOrder>(
    label: &str,
    seeds: u64,
    template: fn() -> Vec<MultivariatePolynomial<N, F>>,
) {
    let base = template();
    for variant in [Variant::Coefficients, Variant::Constants] {
        run::<N, F>(label, variant, seeds, |seed| redraw(&base, variant, seed));
    }
}

fn mq<const N: usize, F: KnownOrder>(label: &str, seeds: u64) {
    run::<N, F>(label, Variant::Coefficients, seeds, |s| {
        dense_mq::<N, F>(s, s)
    });
    run::<N, F>(label, Variant::Constants, seeds, |s| dense_mq::<N, F>(0, s));
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let seeds = args
        .iter()
        .find_map(|a| a.strip_prefix("--seeds="))
        .map_or(30, |s| s.parse().expect("--seeds=N"));
    let quick = args.iter().any(|a| a == "--quick");
    println!(
        "| family | p | variant | transfers | first divergence | median matched rounds | rounds | pair rows | zero rows | pair-row products | zero-row products |"
    );
    println!("|---|---:|---|---:|---|---:|---:|---:|---:|---:|---:|");
    type P31 = Zp2147483647;
    mq::<6, P31>("dense-mq-6", seeds);
    templated::<6, P31>("katsura-6", seeds, katsura::<6, P31>);
    if quick {
        return;
    }
    mq::<8, P31>("dense-mq-8", seeds);
    mq::<9, P31>("dense-mq-9", seeds);
    mq::<10, P31>("dense-mq-10", seeds);
    mq::<8, Zp65537>("dense-mq-8", seeds);
    mq::<9, Zp65537>("dense-mq-9", seeds);
    mq::<8, Zp541>("dense-mq-8", seeds);
    templated::<8, P31>("katsura-8", seeds, katsura::<8, P31>);
    templated::<8, Zp65537>("katsura-8", seeds, katsura::<8, Zp65537>);
    templated::<8, Zp541>("katsura-8", seeds, katsura::<8, Zp541>);
    templated::<10, P31>("katsura-10", seeds, katsura::<10, P31>);
    templated::<9, P31>("eco-9", seeds, eco::<9, P31>);
    templated::<11, P31>("eco-11", seeds, eco::<11, P31>);
    templated::<9, Zp65537>("eco-9", seeds, eco::<9, Zp65537>);
    templated::<9, Zp541>("eco-9", seeds, eco::<9, Zp541>);
    templated::<6, P31>("cyclic-6", seeds, cyclic::<6, P31>);
    templated::<7, P31>("cyclic-7", seeds, cyclic::<7, P31>);
}
