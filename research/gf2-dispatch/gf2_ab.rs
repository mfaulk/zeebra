//! #794: whole F4 solves at `F4Options::default()`, for a two-binary A/B across #777.
use std::time::{Duration, Instant};

use rand::{rngs::StdRng, Rng, SeedableRng};
use zeebra::{
    fields::Zp2,
    grobner::{
        benchmark_systems::cyclic,
        f4::{f4_with_options, F4Options},
        field_equations::with_field_equations,
    },
    Monomial, MonomialOrder, MultivariatePolynomial, One, Zero,
};

const ORDER: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

fn random_mq<const N: usize>(
    seed: u64,
    equations: usize,
    density: f64,
) -> Vec<MultivariatePolynomial<N, Zp2>> {
    let mut rng = StdRng::seed_from_u64(seed);
    let plant: [Zp2; N] = std::array::from_fn(|_| {
        if rng.gen_bool(0.5) {
            Zp2::one()
        } else {
            Zp2::zero()
        }
    });
    let system: Vec<_> = (0..equations)
        .map(|_| {
            let mut terms = Vec::new();
            for i in 0..N {
                for j in i..N {
                    if rng.gen_bool(density) {
                        let mut exponents = [0u32; N];
                        exponents[i] += 1;
                        exponents[j] += 1;
                        terms.push((Monomial::new(&exponents), Zp2::one()));
                    }
                }
            }
            let mut polynomial = MultivariatePolynomial::new(&terms);
            let value = polynomial.eval(&plant);
            polynomial += MultivariatePolynomial::new(&[(Monomial::one(), Zp2::zero() - value)]);
            polynomial
        })
        .collect();
    with_field_equations(&system).expect("GF(2) has an order")
}

fn time<const N: usize>(label: &str, system: &[MultivariatePolynomial<N, Zp2>], reps: usize) {
    let options = F4Options::default();
    let mut best = Duration::MAX;
    let mut size = 0;
    for _ in 0..reps {
        let start = Instant::now();
        let (basis, _) = f4_with_options(system, ORDER, &options).expect("solves");
        best = best.min(start.elapsed());
        size = basis.len();
    }
    println!("{label}\t{size}\t{:.3}", best.as_secs_f64() * 1e3);
}

fn main() {
    let reps: usize = std::env::args().nth(1).map_or(5, |r| r.parse().unwrap());
    if std::env::args().nth(2).as_deref() == Some("sweep") {
        time::<13>("mq-13-d0.05", &random_mq::<13>(794, 13, 0.05), reps);
        time::<14>("mq-14-d0.10", &random_mq::<14>(794, 14, 0.1), reps);
        time::<15>("mq-15-d0.05", &random_mq::<15>(794, 15, 0.05), reps);
        time::<15>("overdetermined-mq-15-d0.15", &random_mq::<15>(794, 30, 0.15), reps);
        time::<16>("overdetermined-mq-16-d0.10", &random_mq::<16>(794, 32, 0.1), reps);
        time::<16>("mq-16-d0.15", &random_mq::<16>(794, 16, 0.15), reps);
        time::<12>("mq-12-d0.05", &random_mq::<12>(794, 12, 0.05), reps);
        time::<12>("sparse-mq-12", &random_mq::<12>(272, 12, 0.05), reps);
        time::<8>("cyclic-8", &with_field_equations(&cyclic::<8, Zp2>()).unwrap(), reps);
        time::<9>("cyclic-9", &with_field_equations(&cyclic::<9, Zp2>()).unwrap(), reps);
        return;
    }
    time::<10>("mq-10", &random_mq::<10>(272, 10, 0.3), reps);
    time::<12>("mq-12", &random_mq::<12>(272, 12, 0.3), reps);
    time::<13>("mq-13", &random_mq::<13>(272, 13, 0.3), reps);
    time::<14>("overdetermined-mq-14", &random_mq::<14>(272, 28, 0.3), reps);
    time::<16>("overdetermined-mq-16", &random_mq::<16>(272, 32, 0.3), reps);
    time::<12>("sparse-mq-12", &random_mq::<12>(272, 12, 0.05), reps);
    time::<8>("cyclic-8", &with_field_equations(&cyclic::<8, Zp2>()).unwrap(), reps);
    time::<9>("cyclic-9", &with_field_equations(&cyclic::<9, Zp2>()).unwrap(), reps);
}
