use zeebra::{
    fields::Zp2147483647 as F,
    grobner::{benchmark_systems::katsura, f4_with_options, F4Options},
    util::peak_resident_bytes,
    MonomialOrder, MultivariatePolynomial,
};

fn run<const N: usize>(order: MonomialOrder) {
    // Match f4_profile's recommended preset, including its division interreduction route.
    let options = F4Options {
        measure_stages: true,
        ..F4Options::baseline()
    };
    let options = F4Options {
        reduction: zeebra::grobner::ReductionStrategy::Structured,
        criteria: zeebra::grobner::PairCriteria::ALL,
        elimination: zeebra::linalg::Backend::Adaptive,
        ..options
    };
    let (basis, statistics) = f4_with_options(&katsura::<N, F>(), order, &options).unwrap();
    let s = statistics.stages;
    eprintln!("katsura-{N} {} total_ms={:.3} symbolic_ms={:.3} construction_ms={:.3} elimination_ms={:.3} interreduction_ms={:.3} peak_rss_bytes={:?}",
        order.name(), statistics.total.as_secs_f64() * 1000.0,
        s.symbolic.as_secs_f64() * 1000.0, s.construction.as_secs_f64() * 1000.0,
        s.elimination.as_secs_f64() * 1000.0, s.interreduction.as_secs_f64() * 1000.0,
        peak_resident_bytes());
    print_basis(&basis, order);
}

fn print_basis<const N: usize>(basis: &[MultivariatePolynomial<N, F>], order: MonomialOrder) {
    // Exponent and coefficient text compares the full bases across binaries without hashing caches.
    for polynomial in basis {
        let mut terms: Vec<_> = polynomial.terms().iter().collect();
        terms.sort_unstable_by(|a, b| order.cmp(b.0, a.0));
        for (monomial, coefficient) in terms {
            print!("{:?}:{coefficient};", monomial.exponents());
        }
        println!();
    }
}

fn main() {
    match std::env::args().nth(1).as_deref() {
        Some("katsura-5-lex") => run::<5>(MonomialOrder::Lexicographic),
        Some("katsura-6-lex") => run::<6>(MonomialOrder::Lexicographic),
        Some("katsura-7-grlex") => run::<7>(MonomialOrder::GradedLexicographic),
        Some("katsura-7-grevlex") => run::<7>(MonomialOrder::GradedReverseLexicographic),
        _ => {
            eprintln!("usage: monomial_degree_profile katsura-5-lex|katsura-6-lex|katsura-7-grlex|katsura-7-grevlex");
            std::process::exit(2);
        }
    }
}
