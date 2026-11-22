//! Dense bivariate products by Kronecker substitution against the dense triangle (#944).
//!
//! Two arms on random dense operands of total degree `d` (every coefficient nonzero), for the
//! square `p²` and the cube step `p² · p`:
//!
//! 1. **triangle** — `MultiplyRoute::DenseTriangle`, what `a * b` selects for this shape
//! 2. **kronecker** — `try_multiply_kronecker`, `y → x^K` through one NTT product
//!
//! The arms are interleaved per repetition and the best of `reps` is reported. Agreement is
//! checked outside the timing. The triangle arm is skipped above `triangle_max_degree`, where it
//! takes minutes; a skipped cell is marked, never reported as a result.
//!
//! ```text
//! cargo run --release --example bivariate_kronecker
//! cargo run --release --example bivariate_kronecker -- degrees=27,81,243,729 reps=3
//! cargo run --release --example bivariate_kronecker -- triangle_max_degree=81
//! ```

use std::time::{Duration, Instant};

use rand::{rngs::StdRng, Rng, SeedableRng};
use zeebra::{
    fields::KoalaBear, multiply_multivariate_unstable, try_multiply_kronecker,
    util::peak_resident_bytes, FiniteField, Monomial, MultiplyRoute, MultivariatePolynomial,
};

type F = KoalaBear;

fn dense(d: u32, rng: &mut StdRng) -> MultivariatePolynomial<2, F> {
    let mut terms = Vec::new();
    for total in 0..=d {
        for a in 0..=total {
            terms.push((
                Monomial::<2>::new(&[a, total - a]),
                F::new(rng.gen_range(1..2_130_706_433u64)),
            ));
        }
    }
    MultivariatePolynomial::new(&terms)
}

fn best<T>(reps: usize, mut f: impl FnMut() -> T) -> (Duration, T) {
    let mut fastest = Duration::MAX;
    let mut out = None;
    for _ in 0..reps {
        let start = Instant::now();
        let value = f();
        fastest = fastest.min(start.elapsed());
        out = Some(value);
    }
    (fastest, out.expect("reps >= 1"))
}

fn arg(name: &str) -> Option<String> {
    std::env::args()
        .skip(1)
        .find_map(|a| a.strip_prefix(&format!("{name}=")).map(str::to_owned))
}

fn main() {
    let degrees: Vec<u32> = arg("degrees")
        .map(|s| s.split(',').map(|d| d.parse().expect("a degree")).collect())
        .unwrap_or_else(|| vec![3, 6, 9, 15, 27, 40, 54, 81, 121, 243]);
    let reps: usize = arg("reps").map_or(5, |r| r.parse().expect("a count"));
    let triangle_max: u32 =
        arg("triangle_max_degree").map_or(243, |r| r.parse().expect("a degree"));
    let mut rng = StdRng::seed_from_u64(1);

    println!("| d | terms | step | product degree | triangle | kronecker | ratio |");
    println!("|---:|---:|---|---:|---:|---:|---:|");
    for &d in &degrees {
        let p = dense(d, &mut rng);
        let (k_square_time, square) = best(reps, || {
            try_multiply_kronecker(&p, &p, &mut rng).expect("KoalaBear hosts the domain")
        });
        let (k_cube_time, cube) = best(reps, || {
            try_multiply_kronecker(&square, &p, &mut rng).expect("KoalaBear hosts the domain")
        });
        for (step, k_time, lhs, k_out) in [
            ("p²", k_square_time, &p, &square),
            ("p²·p", k_cube_time, &square, &cube),
        ] {
            let triangle = (d <= triangle_max).then(|| {
                best(reps, || {
                    multiply_multivariate_unstable(lhs, &p, MultiplyRoute::DenseTriangle)
                })
            });
            let (t_cell, ratio) = match triangle {
                Some((t_time, t_out)) => {
                    assert_eq!(&t_out, k_out, "the routes disagree at d = {d}, {step}");
                    (
                        format!("{:.3} ms", t_time.as_secs_f64() * 1e3),
                        format!("{:.2}x", t_time.as_secs_f64() / k_time.as_secs_f64()),
                    )
                }
                None => ("skipped".to_owned(), "—".to_owned()),
            };
            println!(
                "| {d} | {} | {step} | {} | {t_cell} | {:.3} ms | {ratio} |",
                p.terms().len(),
                k_out.degree(),
                k_time.as_secs_f64() * 1e3,
            );
        }
    }
    if let Some(bytes) = peak_resident_bytes() {
        println!(
            "\npeak RSS (whole process): {:.1} MiB",
            bytes as f64 / (1 << 20) as f64
        );
    }
}
