//! What batch inversion is worth, where it was wired in, and where it was not.
//!
//! #118. Montgomery's trick replaces n inversions with one inversion and `3(n-1)`
//! multiplications, so what it buys depends entirely on the ratio between inversion and
//! multiplication in the field. Three things are reported, and keeping them apart is the point:
//!
//! 1. **The routine.** `batch_invert` against n separate `inverse()` calls, per field and per
//!    batch size, so the speedup and the batch size at which it starts winning are measured
//!    rather than asserted.
//! 2. **The integration.** `FFTDomain::inverse` and `fft::interpolate`, each against a local
//!    reimplementation of exactly what it used to do. Both paths run on the same input in the
//!    same process and their outputs are asserted equal, so the speedup is an A/B of two
//!    implementations of one function and not of two programs.
//! 3. **What was deliberately left alone.** F4's pivot normalization cannot be batched without
//!    changing the elimination — see §"F4" below — so this reports the *headroom* instead:
//!    `pivot_inversions` against `row_operations` on real systems, which bounds what batching
//!    there could ever save.
//!
//! ```text
//! cargo run --release --example batch_inversion
//! cargo run --release --example batch_inversion -- list
//! cargo run --release --example batch_inversion -- routine
//! cargo run --release --example batch_inversion -- fft
//! cargo run --release --example batch_inversion -- f4
//! ```

use std::time::{Duration, Instant};

use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    evaluate,
    fields::{batch_inverse, batch_invert, Bls12_381Fr, Bn254Fr, PrimeFieldElement64},
    grobner::{
        benchmark_systems::{cyclic, katsura},
        f4::f4_reported,
        F4Options, F4Statistics,
    },
    interpolate, FFTDomain, FiniteField, KnownOrder, MonomialOrder, Polynomial,
    UnivariatePolynomial,
};

/// Mersenne-31, `2^31 - 1`, backed by a `u64`. Inversion here is `a^(p-2)`.
type Mersenne31In64 = PrimeFieldElement64<2_147_483_647>;

/// Goldilocks, `2^64 - 2^32 + 1`.
type Goldilocks = PrimeFieldElement64<18_446_744_069_414_584_321>;

/// KoalaBear, the NTT-friendly 31-bit prime, backed by a `u64`.
type KoalaBearIn64 = PrimeFieldElement64<2_130_706_433>;

/// Repetitions of each timed operation, so a single measurement is not a single sample.
const REPEATS: usize = 25;

/// Time `work` `REPEATS` times and return the fastest run.
///
/// The minimum rather than the mean: every source of noise on this box adds time, so the fastest
/// run is the one least contaminated by something else.
fn fastest<T>(mut work: impl FnMut() -> T) -> Duration {
    let mut best = Duration::MAX;
    for _ in 0..REPEATS {
        let at = Instant::now();
        let value = work();
        let elapsed = at.elapsed();
        std::hint::black_box(value);
        best = best.min(elapsed);
    }
    best
}

/// `n` nonzero elements of F.
fn nonzero<F: FiniteField>(n: usize, seed: u64) -> Vec<F> {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut values = Vec::with_capacity(n);
    while values.len() < n {
        let candidate = F::random(&mut rng);
        if !candidate.is_zero() {
            values.push(candidate);
        }
    }
    values
}

// === 1. the routine ===

/// `batch_invert` against n separate inversions, over one field, at several batch sizes.
fn routine_for_field<F: FiniteField>(name: &str) {
    println!("\n### {}  ({} bytes per element)", name, size_of::<F>());
    println!(
        "| {:>8} | {:>14} | {:>14} | {:>9} | {:>12} |",
        "n", "one at a time", "batched", "speedup", "ns/element"
    );
    println!(
        "|{:->10}|{:->16}|{:->16}|{:->11}|{:->14}|",
        "", "", "", "", ""
    );

    for &n in &[1usize, 2, 4, 8, 16, 64, 256, 1024, 16_384] {
        let values = nonzero::<F>(n, 0x1_7A17 + n as u64);

        let one_at_a_time = fastest(|| values.iter().map(|x| x.inverse()).collect::<Vec<F>>());
        let batched = fastest(|| {
            let mut owned = values.clone();
            batch_invert(&mut owned);
            owned
        });

        // The two must agree. Checked outside the timing, and for every size, because a speedup
        // on a wrong answer is not a speedup.
        assert_eq!(
            batch_inverse(&values),
            values.iter().map(|x| x.inverse()).collect::<Vec<F>>(),
            "{name}: batch and elementwise disagree at n = {n}"
        );

        println!(
            "| {:>8} | {:>11.3} µs | {:>11.3} µs | {:>8.2}x | {:>12.1} |",
            n,
            one_at_a_time.as_secs_f64() * 1e6,
            batched.as_secs_f64() * 1e6,
            one_at_a_time.as_secs_f64() / batched.as_secs_f64(),
            batched.as_secs_f64() * 1e9 / n as f64,
        );
    }
}

// === 2. the integration ===

/// What `FFTDomain::inverse` did before: one `inverse()` per element.
fn domain_inverse_elementwise<F: FiniteField>(domain: &FFTDomain<F>) -> Vec<F> {
    domain.powers().iter().map(|w_i| w_i.inverse()).collect()
}

/// `interpolate` with each of its two inversion decisions switchable.
///
/// Three of the four combinations are reported, which is what separates the two contributions:
/// `(false, false)` is the original, `(true, false)` is the original with only the domain inverse
/// batched, and `(true, true)` is what the library now does.
fn interpolate_variant<F: FiniteField>(
    x: &[F],
    w: &FFTDomain<F>,
    batched_domain: bool,
    hoisted_scale: bool,
) -> UnivariatePolynomial<F> {
    let w_inv = if batched_domain {
        w.inverse()
    } else {
        FFTDomain::new(domain_inverse_elementwise(w))
    };
    let unscaled = evaluate(&UnivariatePolynomial::new(x), &w_inv);

    let n = <F as FiniteField>::new(w.size() as u64);
    let coefficients: Vec<_> = if hoisted_scale {
        let n_inverse = n.inverse();
        unscaled.into_iter().map(|c| c * n_inverse).collect()
    } else {
        // `c / n` is `c * n.inverse()`, so this is one inversion per coefficient as written.
        unscaled.into_iter().map(|c| c / n).collect()
    };
    UnivariatePolynomial::new(&coefficients)
}

/// The two FFT call sites, old implementation against new, over one field.
fn fft_for_field<F: KnownOrder>(name: &str, seed: u64) {
    let two_adicity = F::two_adicity();
    println!("\n### {}  ({} bytes per element)", name, size_of::<F>());
    println!(
        "| {:>8} | {:<28} | {:>14} | {:>14} | {:>9} |",
        "n", "call site", "before", "after", "speedup"
    );
    println!(
        "|{:->10}|{:->30}|{:->16}|{:->16}|{:->11}|",
        "", "", "", "", ""
    );

    for log_n in [8u32, 12, 16] {
        if log_n > two_adicity {
            println!(
                "| {:>8} | two-adicity is {}, so no domain of this size exists |",
                1usize << log_n,
                two_adicity
            );
            continue;
        }
        let n = 1usize << log_n;
        let mut rng = StdRng::seed_from_u64(seed ^ log_n as u64);
        let w = F::two_adic_root_of_unity(log_n, &mut rng);
        let domain = FFTDomain::from_generator(w, n);

        // `FFTDomain::inverse`.
        assert_eq!(
            domain.inverse().powers(),
            domain_inverse_elementwise(&domain),
            "{name}: the batched domain inverse disagrees at n = {n}"
        );
        let before = fastest(|| domain_inverse_elementwise(&domain));
        let after = fastest(|| domain.inverse());
        println!(
            "| {:>8} | {:<28} | {:>11.3} µs | {:>11.3} µs | {:>8.2}x |",
            n,
            "FFTDomain::inverse",
            before.as_secs_f64() * 1e6,
            after.as_secs_f64() * 1e6,
            before.as_secs_f64() / after.as_secs_f64(),
        );

        // `interpolate`, which pays the domain inverse *and* the 1/n scaling. Every variant must
        // invert the transform, which is the only check that they are the same function.
        let p = UnivariatePolynomial::<F>::rand(n as u64 - 1, &mut rng);
        let values = evaluate(&p, &domain);
        assert_eq!(
            interpolate(&values, &domain),
            p,
            "{name}: round trip at {n}"
        );
        for (batched, hoisted) in [(false, false), (true, false), (true, true)] {
            assert_eq!(
                interpolate_variant(&values, &domain, batched, hoisted),
                p,
                "{name}: variant ({batched}, {hoisted}) at n = {n}"
            );
        }

        let original = fastest(|| interpolate_variant(&values, &domain, false, false));
        let domain_only = fastest(|| interpolate_variant(&values, &domain, true, false));
        let after = fastest(|| interpolate(&values, &domain));
        for (what, before, now) in [
            ("interpolate: batch the domain", original, domain_only),
            ("interpolate: hoist the 1/n", domain_only, after),
            ("interpolate: both", original, after),
        ] {
            println!(
                "| {:>8} | {:<28} | {:>11.3} µs | {:>11.3} µs | {:>8.2}x |",
                n,
                what,
                before.as_secs_f64() * 1e6,
                now.as_secs_f64() * 1e6,
                before.as_secs_f64() / now.as_secs_f64(),
            );
        }
    }
}

// === 3. what was left alone ===

/// F4's pivot-inversion headroom on one system.
fn f4_headroom<const N: usize, F: FiniteField>(
    label: &str,
    system: Vec<zeebra::MultivariatePolynomial<N, F>>,
) -> (String, F4Statistics, Duration) {
    let options = F4Options {
        measure_stages: true,
        ..F4Options::default()
    };
    let at = Instant::now();
    let (result, statistics) =
        f4_reported(&system, MonomialOrder::GradedReverseLexicographic, &options);
    let elapsed = at.elapsed();
    assert!(result.is_ok(), "{label} must complete");
    (label.to_string(), statistics, elapsed)
}

fn f4_headroom_katsura<const N: usize, F: FiniteField>(
    label: &str,
) -> (String, F4Statistics, Duration) {
    f4_headroom::<N, F>(label, katsura::<N, F>())
}

fn f4_headroom_cyclic<const N: usize, F: FiniteField>(
    label: &str,
) -> (String, F4Statistics, Duration) {
    f4_headroom::<N, F>(label, cyclic::<N, F>())
}

fn report_f4() {
    type P = PrimeFieldElement64<2_147_483_647>;

    println!("\n## 3. F4's pivot normalization: the headroom, not an integration");
    println!();
    println!(
        "Pivot inversions are *not* batched, and cannot be without changing the elimination.\n\n\
         In `row_echelon_within` a row is normalized at the moment it becomes a pivot, and every \
         later row relies on it: the factor that clears a column is the incoming row's leading \
         coefficient *because* the pivot's is one. Deferring the scaling and storing `c^-1` per \
         pivot instead would keep the inversion count identical, so that is not the obstruction. \
         The obstruction is ordering. Pivots are *discovered* one at a time, each after the \
         reductions that used the previous ones, so their coefficients are never all in hand at \
         once — and a batch needs exactly that. Whichever way the scaling is arranged, collecting \
         the pivots first means reducing rows against unnormalized pivots in a different order, \
         which is a different elimination.\n\n\
         `reduced_row_echelon`'s second pass, which #118 proposed as the integration point, has \
         nothing left to batch: the first pass already normalized every pivot. The same ordering \
         argument applies to `linalg::echelon`, the dense kernels, `crout`'s LU and FGLM's \
         incremental span, which all invert at pivot discovery. The one bulk site elsewhere is \
         making a generator list monic, where the leading coefficients *are* all available — but \
         F4 and Buchberger keep their bases monic, so that loop finds almost nothing to invert."
    );
    println!();
    println!(
        "So the question is how much there is to win at all. `pivot_inversions / row_operations` \
         is the share of the elimination's work that any batching could touch, and it is an \
         over-estimate: a row operation is many multiplications, an inversion is one:"
    );
    println!();
    println!(
        "| {:<12} | {:>14} | {:>16} | {:>9} | {:>10} |",
        "system", "row ops", "pivot inversions", "share", "F4 time"
    );
    println!(
        "|{:->14}|{:->16}|{:->18}|{:->11}|{:->12}|",
        "", "", "", "", ""
    );

    let runs = [
        f4_headroom_katsura::<4, P>("katsura-4"),
        f4_headroom_katsura::<5, P>("katsura-5"),
        f4_headroom_katsura::<6, P>("katsura-6"),
        f4_headroom_katsura::<7, P>("katsura-7"),
        f4_headroom_cyclic::<5, P>("cyclic-5"),
        f4_headroom_cyclic::<6, P>("cyclic-6"),
    ];
    for (label, statistics, elapsed) in &runs {
        let share = if statistics.row_operations == 0 {
            0.0
        } else {
            statistics.pivot_inversions as f64 / statistics.row_operations as f64
        };
        println!(
            "| {:<12} | {:>14} | {:>16} | {:>8.3}% | {:>9.1} ms |",
            label,
            statistics.row_operations,
            statistics.pivot_inversions,
            share * 100.0,
            elapsed.as_secs_f64() * 1e3,
        );
    }
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let selector = arguments.first().cloned().unwrap_or_else(|| "all".into());

    if selector == "list" {
        println!("sections: all, routine, fft, f4");
        return;
    }

    println!("# Batch inversion: the routine, the integration, and the headroom left alone");
    println!();
    println!(
        "Each timing is the fastest of {REPEATS} runs. Every comparison asserts that the two \
         paths produce the same values before reporting a ratio."
    );

    let all = selector == "all";

    if all || selector == "routine" {
        println!("\n\n## 1. `batch_invert` against n separate inversions");
        println!();
        println!(
            "One inversion and `3(n-1)` multiplications against n inversions. The crossover is \
             where the three multiplications per element start costing less than one inversion."
        );
        routine_for_field::<Mersenne31In64>("Mersenne-31, 2^31 - 1");
        routine_for_field::<Goldilocks>("Goldilocks, 2^64 - 2^32 + 1");
        routine_for_field::<Bn254Fr>("BN254 Fr, 254 bits");
        routine_for_field::<Bls12_381Fr>("BLS12-381 Fr, 255 bits");
    }

    if all || selector == "fft" {
        println!("\n\n## 2. The two FFT call sites, before against after");
        println!();
        println!(
            "`FFTDomain::inverse` was one `inverse()` per power. `fft::interpolate` paid that \
             *and* divided every coefficient by n, which is a second inversion per coefficient \
             since `Div` is multiplication by `inverse()`."
        );
        fft_for_field::<KoalaBearIn64>("KoalaBear, 2^31 - 2^24 + 1", 0x4b0a);
        fft_for_field::<Goldilocks>("Goldilocks, 2^64 - 2^32 + 1", 0x601d);
        fft_for_field::<Bn254Fr>("BN254 Fr, 254 bits", 0xb254);
    }

    if all || selector == "f4" {
        report_f4();
    }
}
