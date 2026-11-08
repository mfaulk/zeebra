//! Where Bluestein starts beating the quadratic definition at a prime-power factor.
//!
//! Issue #375, which #357 left open when it landed `src/fft/bluestein.rs` without dispatching to
//! it. `dft` is `O(m^2)` but allocation-free and branch-free — one accumulator and an incremented
//! twiddle index. Bluestein is `O(m log m)` but pays three `m`-length chirp passes, two `L`-length
//! forward transforms, an `L`-length pointwise product, an `L`-length inverse transform and a
//! `batch_inverse` of the convolution domain, at `L = (2m - 1).next_power_of_two()` — up to `4m` —
//! and it rebuilds the chirp tables on every call. So the quadratic route wins below some size.
//!
//! # The sizes are not ours to choose
//!
//! This sweep cannot step through sizes the way the other crossover binaries here do, and the
//! reason is worth stating because it bounds what the measurement can say. A domain of size `m`
//! needs a primitive `m`-th root of unity, so `m` must divide `q - 1`; the dispatch is reached
//! only at an **odd prime power**; and Bluestein additionally needs the field's two-adicity to
//! cover `log2 L`. Those three together leave very few sizes per field:
//!
//! - Goldilocks, `q - 1 = 2^32 * 3 * 5 * 17 * 257 * 65537`: **3, 5, 17, 257, 65537**.
//! - KoalaBear, `q - 1 = 2^24 * 127`: **127**.
//! - BabyBear, `q - 1 = 2^27 * 3 * 5`: **3, 5**.
//!
//! So the crossover is **bracketed, not pinned** — and that is sufficient rather than a
//! compromise, because the dispatch is only ever asked about sizes the field can host. Precision
//! between 17 and 257 over Goldilocks would be precision nothing can use. The sweep reports which
//! sizes each field could host, so the bracket is visible rather than implied.
//!
//! Every timed result goes through `std::hint::black_box`: the two arms return their output in the
//! buffer they were handed, and an arm whose result nobody reads is an arm LLVM may delete.
//!
//! ```text
//! cargo run --release --example bluestein_crossover
//! cargo run --release --example bluestein_crossover -- goldilocks
//! ```

use std::time::{Duration, Instant};

use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    bluestein_convolution_domain, bluestein_convolution_length, bluestein_crossover_unstable,
    bluestein_transform, dft_unstable,
    fields::{Bn254Fr, KoalaBear, PrimeFieldElement64},
    util::peak_resident_bytes,
    FFTDomain, FiniteField, KnownOrder,
};

/// Goldilocks, `2^64 - 2^32 + 1`. The richest factorization any field here offers.
type Goldilocks = PrimeFieldElement64<18_446_744_069_414_584_321>;

/// BabyBear, `2^27 * 3 * 5 + 1`.
type BabyBear = PrimeFieldElement64<2_013_265_921>;

/// Candidate odd prime-power sizes. A field hosts the ones dividing its `q - 1`; the rest are
/// skipped and reported as skipped.
const CANDIDATES: [usize; 24] = [
    3, 5, 7, 9, 11, 13, 17, 19, 23, 25, 27, 31, 49, 81, 101, 121, 125, 127, 243, 257, 625, 641,
    729, 2187,
];

/// Each arm's time is its fastest over at most this many interleaved repetitions, or fewer when
/// one pass already costs more than `PAIR_BUDGET`.
const MAX_REPETITIONS: usize = 9;

/// Target wall time for all repetitions at one size.
const PAIR_BUDGET: Duration = Duration::from_millis(500);

fn rule(widths: &[usize]) -> String {
    let mut line = String::from("|");
    for width in widths {
        line.push_str(&"-".repeat(*width));
        line.push('|');
    }
    line
}

/// The two routes at one prime-power size, interleaved, each reported as its fastest pass.
///
/// The arms are checked against each other once, outside the timing: a crossover measured against
/// a wrong answer is worthless.
fn pair<F: FiniteField>(
    values: &[F],
    domain: &FFTDomain<F>,
    convolution: &FFTDomain<F>,
) -> (Duration, Duration) {
    let mut quadratic = values.to_vec();
    dft_unstable(&mut quadratic, domain.powers());
    let mut bluestein = values.to_vec();
    bluestein_transform(&mut bluestein, domain, convolution);
    assert_eq!(
        quadratic,
        bluestein,
        "the two routes disagree at m = {}",
        values.len()
    );

    let mut best = (Duration::MAX, Duration::MAX);
    let mut spent = Duration::ZERO;
    let mut taken = 0;
    while taken < MAX_REPETITIONS && spent < PAIR_BUDGET {
        let mut buffer = values.to_vec();
        let start = Instant::now();
        dft_unstable(&mut buffer, domain.powers());
        let quadratic = start.elapsed();
        std::hint::black_box(&buffer);

        let mut buffer = values.to_vec();
        let start = Instant::now();
        bluestein_transform(&mut buffer, domain, convolution);
        let bluestein = start.elapsed();
        std::hint::black_box(&buffer);

        best.0 = best.0.min(quadratic);
        best.1 = best.1.min(bluestein);
        spent += quadratic + bluestein;
        taken += 1;
    }
    best
}

/// One field's sweep over every candidate size it can host.
fn sweep<F: KnownOrder>(name: &str, seed: u64) {
    let compiled_in = bluestein_crossover_unstable::<F>();
    println!("\n\n## {name}");
    println!("\n- an element is {} bytes", std::mem::size_of::<F>());
    println!("- the compiled-in crossover for this width is {compiled_in}");

    println!(
        "\n| {:>8} | {:>8} | {:>13} | {:>13} | {:>9} | {:>10} |",
        "m", "L", "dft/s", "bluestein/s", "speedup", "rule"
    );
    println!("{}", rule(&[10, 10, 15, 15, 11, 12]));

    let mut rng = StdRng::seed_from_u64(seed);
    let mut hosted: Vec<usize> = Vec::new();
    let mut skipped: Vec<usize> = Vec::new();
    let mut first_win: Option<usize> = None;
    let mut last_loss: Option<usize> = None;

    for m in CANDIDATES {
        let Ok(root) = F::try_root_of_unity(m as u64, &mut rng) else {
            skipped.push(m);
            continue;
        };
        let Ok(domain) = FFTDomain::try_from_generator(root, m) else {
            skipped.push(m);
            continue;
        };
        let Ok(convolution) = bluestein_convolution_domain::<F, _>(m, &mut rng) else {
            skipped.push(m);
            continue;
        };
        hosted.push(m);

        let values: Vec<F> = (0..m).map(|_| F::random(&mut rng)).collect();
        let (quadratic, bluestein) = pair(&values, &domain, &convolution);
        let speedup = quadratic.as_secs_f64() / bluestein.as_secs_f64();
        // The same 10% band the other crossover binaries here use: inside it the two cost the
        // same to within this box's spread, and the tiebreak is then the allocation-free route.
        if speedup > 1.1 {
            if first_win.is_none() {
                first_win = Some(m);
            }
        } else {
            last_loss = Some(m);
        }

        println!(
            "| {:>8} | {:>8} | {:>13.8} | {:>13.8} | {:>9.2} | {:>10} |",
            m,
            bluestein_convolution_length(m),
            quadratic.as_secs_f64(),
            bluestein.as_secs_f64(),
            speedup,
            if m > compiled_in { "bluestein" } else { "dft" },
        );
    }

    println!("- hosted: {hosted:?}");
    println!("- skipped, not dividing q - 1 or beyond the two-adicity: {skipped:?}");
    match (last_loss, first_win) {
        (Some(loss), Some(win)) => println!(
            "- the crossover is bracketed: dft still wins at m = {loss}, Bluestein wins by more \
             than 10% from m = {win}. Any constant in [{loss}, {win}) dispatches identically on \
             this field, since no size between them is hostable."
        ),
        (None, Some(win)) => println!(
            "- Bluestein wins at every hosted size, from m = {win} — no lower bracket on this \
             field"
        ),
        (Some(loss), None) => println!(
            "- dft wins at every hosted size up to m = {loss} — a null result on this field, to \
             report as one"
        ),
        (None, None) => println!("- no size was hostable on this field"),
    }
    match first_win {
        Some(win) => println!(
            "- the compiled-in {compiled_in} dispatches Bluestein from m > {compiled_in}, and the \
             measurement says it should win from m = {win}"
        ),
        None => println!("- the compiled-in {compiled_in} has nothing to act on here"),
    }
}

fn main() {
    let which = std::env::args().nth(1).unwrap_or_else(|| "all".into());

    println!("# Bluestein against the quadratic definition at a prime-power factor");
    println!("\nISA: {}", zeebra::util::isa_floor());
    println!("\nIssue #375. Both arms are checked against each other before the clock starts.");
    println!(
        "\n- each timed figure is the fastest of up to {MAX_REPETITIONS} interleaved repetitions"
    );
    println!("- `m` is the factor size and `L` the padded convolution length Bluestein uses");

    if which == "all" || which == "goldilocks" {
        sweep::<Goldilocks>("Goldilocks, 2^64 - 2^32 + 1", 0x0375_1001);
    }
    if which == "all" || which == "koalabear" {
        sweep::<KoalaBear>("KoalaBear, 2^31 - 2^24 + 1", 0x0375_1002);
    }
    if which == "all" || which == "babybear" {
        sweep::<BabyBear>("BabyBear, 2^27 * 3 * 5 + 1", 0x0375_1003);
    }
    if which == "all" || which == "bn254" {
        sweep::<Bn254Fr>("BN254 Fr, 254 bits", 0x0375_1004);
    }

    match peak_resident_bytes() {
        Some(bytes) => println!(
            "\n\nprocess peak resident set: {} bytes ({:.1} MiB)",
            bytes,
            bytes as f64 / (1024.0 * 1024.0)
        ),
        None => println!("\n\nprocess peak resident set: unavailable on this platform"),
    }
}
