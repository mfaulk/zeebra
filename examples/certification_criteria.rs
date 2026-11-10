//! What the pair-elimination criteria prune from a **certification** pass, and what that saves.
//!
//! Certification checks Buchberger's criterion over every pair of the returned basis, which is
//! `|G|²/2` normal forms and can cost many times the solve (`docs/research/hilbert-driven.md`
//! §5). Only some criteria transfer to a static basis — the
//! product criterion and Gebauer–Möller's lcm-divisibility criteria do, the history-dependent
//! chain criterion does not — so the share that transfers is measured here before it is believed.
//!
//! ```text
//! cargo run --release --example certification_criteria
//! cargo run --release --example certification_criteria -- list
//! cargo run --release --example certification_criteria -- katsura-6
//! ```
//!
//! Columns. `all` is `|G|(|G|-1)/2`, every pair Buchberger's criterion names; `product` is the
//! pairs with relatively prime leading monomials; `gm` is the pairs Gebauer–Möller's static pair
//! set drops, product criterion included; `kept` is what survives, and `saved` is the share
//! pruned. `chain↑` is how many of the kept pairs have *any* basis element dividing their lcm —
//! the whole pool a chain-criterion variant could draw from, and an upper bound rather than a
//! saving, since the bare divisibility is the classic unsound shortcut. `strict↑` is the subset of
//! that pool with a witness whose **two** lcms both differ from the pair's, which is the part a
//! static basis could discard soundly by descent on the lcm; it is the number that decides whether
//! a chain criterion is worth writing. `naive ms` and `pruned ms` are the two certification
//! passes, reported last because structural counters are exact and wall clock on this machine is
//! not.

use std::time::Instant;

use zeebra::{
    fields::PrimeFieldElement64,
    grobner::{
        benchmark_systems::{cyclic, katsura},
        certify_f4_output,
        pairs::{are_relatively_prime, divides, leading_monomials},
        s_polynomial, CriterionCounts, PairCriteria, PairQueue,
    },
    FiniteField, Monomial, MonomialOrder, MultivariatePolynomial,
};

type P = PrimeFieldElement64<2_147_483_647>;

const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

/// Gebauer–Möller's static pair set, which is the configuration certification can use: the
/// lcm-divisibility criteria plus the product criterion, and no chain criterion.
const STATIC: PairCriteria = PairCriteria {
    product: true,
    chain: false,
    gebauer_moller: true,
};

fn header() {
    println!(
        "{:<22} {:>6} {:>8} {:>8} {:>8} {:>8} {:>8} {:>8} {:>8} {:>11} {:>11}",
        "instance",
        "basis",
        "all",
        "product",
        "gm",
        "kept",
        "saved",
        "chain↑",
        "strict↑",
        "naive ms",
        "pruned ms"
    );
}

fn measure<const N: usize, F: FiniteField>(
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
    time_it: bool,
) {
    let basis = match zeebra::grobner::f4(system, GREVLEX) {
        Ok(basis) => basis,
        Err(error) => {
            println!("{:<22} limits exceeded: {:?}", name, error);
            return;
        }
    };
    let leads = leading_monomials(&basis, GREVLEX);
    let size = leads.len();
    let all = size * size.saturating_sub(1) / 2;

    // The product criterion alone, which needs no pair set at all: relatively prime leading
    // monomials are a property of the two elements.
    let product = (0..size)
        .flat_map(|i| ((i + 1)..size).map(move |j| (i, j)))
        .filter(|&(i, j)| are_relatively_prime(&leads[i], &leads[j]))
        .count();

    // Gebauer–Möller over the static basis: seeding is incremental, so each element meets the same
    // prefix it would during a run.
    let mut counts = CriterionCounts::default();
    let mut queue = PairQueue::<N>::seeded_from_leads(&leads, &STATIC, &mut counts);
    let kept = queue.len();

    // The pool a chain-criterion variant could draw from: a kept pair whose lcm some other basis
    // element's leading monomial divides. Divisibility alone is not a sufficient condition, so
    // this bounds the remaining opportunity without being a saving.
    let mut chain_pool = 0;
    let mut strict_pool = 0;
    while let Some(pair) = queue.pop() {
        let witnesses = (0..size)
            .filter(|&k| k != pair.left && k != pair.right)
            .filter(|&k| divides(&leads[k], &pair.lcm));
        let mut any = false;
        let mut strict = false;
        for k in witnesses {
            any = true;
            strict |= Monomial::lcm(&leads[pair.left], &leads[k]) != pair.lcm
                && Monomial::lcm(&leads[k], &leads[pair.right]) != pair.lcm;
        }
        chain_pool += usize::from(any);
        strict_pool += usize::from(strict);
    }

    let (naive, pruned) = if time_it {
        let at = Instant::now();
        let held = buchberger_criterion_over_every_pair(&basis);
        let naive = at.elapsed().as_secs_f64() * 1e3;
        assert!(held, "{}: the all-pairs reference itself failed", name);

        let at = Instant::now();
        let report = certify_f4_output(system, &basis, GREVLEX);
        let pruned = at.elapsed().as_secs_f64() * 1e3;
        assert!(
            report.is_complete(),
            "{}: {:?}",
            name,
            report.first_failure()
        );
        (naive, pruned)
    } else {
        (f64::NAN, f64::NAN)
    };

    println!(
        "{:<22} {:>6} {:>8} {:>8} {:>8} {:>8} {:>7.1}% {:>8} {:>8} {:>11.1} {:>11.1}",
        name,
        size,
        all,
        product,
        counts.gebauer_moller,
        kept,
        if all == 0 {
            0.0
        } else {
            100.0 * (all - kept) as f64 / all as f64
        },
        chain_pool,
        strict_pool,
        naive,
        pruned,
    );
}

/// Buchberger's criterion over every pair, as certification checked it before the criteria were
/// applied. The reference the pruned check is timed against.
fn buchberger_criterion_over_every_pair<const N: usize, F: FiniteField>(
    basis: &[MultivariatePolynomial<N, F>],
) -> bool {
    let nonzero: Vec<&MultivariatePolynomial<N, F>> =
        basis.iter().filter(|p| !p.is_zero()).collect();
    for (index, f) in nonzero.iter().enumerate() {
        for g in nonzero.iter().skip(index + 1) {
            if !s_polynomial(f, g, GREVLEX)
                .normal_form(basis, GREVLEX)
                .is_zero()
            {
                return false;
            }
        }
    }
    true
}

fn instances() -> Vec<&'static str> {
    vec!["katsura-5", "katsura-6", "cyclic-5", "cyclic-6"]
}

fn run(name: &str, time_it: bool) {
    match name {
        "katsura-5" => measure(name, &katsura::<5, P>(), time_it),
        "katsura-6" => measure(name, &katsura::<6, P>(), time_it),
        "cyclic-5" => measure(name, &cyclic::<5, P>(), time_it),
        "cyclic-6" => measure(name, &cyclic::<6, P>(), time_it),
        other => println!("unknown instance `{}`; `-- list` names them.", other),
    }
}

fn main() {
    let argument = std::env::args().nth(1);
    let time_it = std::env::var("ZEEBRA_SKIP_TIMING").is_err();

    match argument.as_deref() {
        Some("list") => {
            for name in instances() {
                println!("{}", name);
            }
        }
        Some(name) => {
            header();
            run(name, time_it);
        }
        None => {
            header();
            for name in instances() {
                run(name, time_it);
            }
        }
    }
}
