//! Size profiles run separately from timing passes; use the bounded single-case mode for outliers.

use std::{
    cell::RefCell,
    time::{Duration, Instant},
};

use rand::{prelude::StdRng, Rng, SeedableRng};
use zeebra::{
    fields::{Bn254Fr, KoalaBear, PrimeFieldElement64},
    util::peak_resident_bytes,
    FiniteField, GcdRoute, KnownOrder, Monomial, MonomialOrder, MultivariatePolynomial,
};

/// Goldilocks, `2^64 - 2^32 + 1`.
type Goldilocks = PrimeFieldElement64<18_446_744_069_414_584_321>;

thread_local! {
    /// The first refusal Brown's route gave on this field, so the reason is reported once rather
    /// than once a shape — and so a column of blanks is never left unexplained.
    static REFUSAL: RefCell<Option<String>> = const { RefCell::new(None) };
}

/// Each arm's time is its fastest over at most this many interleaved repetitions, or fewer when
/// one pass already costs more than `PAIR_BUDGET`.
const MAX_REPETITIONS: usize = 5;

/// Target wall time for all repetitions at one shape.
///
/// A shape whose single pass already exceeds this gets exactly one repetition, and the `reps`
/// column says so. That matters here more than in the other sweeps in this repo, because the
/// interesting rows are precisely the expensive ones: a route that takes a second where the other
/// takes two milliseconds is reported from one pass, and a single pass is a weaker figure than a
/// minimum of five.
const PAIR_BUDGET: Duration = Duration::from_millis(900);

/// Shapes beyond this index are not swept at arity 4 and above.
///
/// Not a budget that triggers after the fact but a limit stated in advance, because the cost here
/// cannot be bounded reactively: a single pass of either route is synchronous and the primitive
/// route's growth with arity is steep enough that one call at `5 x 5` terms and exponent 4 over
/// four variables does not finish inside a 2 400 s run — which is how the first version of this
/// binary was killed by its own timeout mid-sweep, with two fields never reached. The omission is
/// itself a finding and is reported rather than silently applied.
const WIDE_ARITY_SHAPES: usize = 6;

/// A shape to measure: how many terms the shared factor and each cofactor get, and the largest
/// exponent any one variable takes.
#[derive(Clone, Copy)]
struct Shape {
    shared_terms: usize,
    cofactor_terms: usize,
    max_exponent: u32,
}

/// What one shape measured.
struct Row {
    primitive: Duration,
    subresultant: Duration,
    /// `None` where Brown's route refused this shape over this field, with the reason printed once.
    brown: Option<Duration>,
    repetitions: usize,
    #[cfg(feature = "research-work")]
    profiles: [zeebra::gcd_profile::GcdProfile; 3],
}

const SHAPES: [Shape; 7] = [
    Shape {
        shared_terms: 2,
        cofactor_terms: 2,
        max_exponent: 2,
    },
    Shape {
        shared_terms: 3,
        cofactor_terms: 3,
        max_exponent: 2,
    },
    Shape {
        shared_terms: 3,
        cofactor_terms: 3,
        max_exponent: 3,
    },
    Shape {
        shared_terms: 4,
        cofactor_terms: 4,
        max_exponent: 3,
    },
    Shape {
        shared_terms: 2,
        cofactor_terms: 6,
        max_exponent: 3,
    },
    Shape {
        shared_terms: 6,
        cofactor_terms: 2,
        max_exponent: 3,
    },
    Shape {
        shared_terms: 5,
        cofactor_terms: 5,
        max_exponent: 4,
    },
];

fn rule(widths: &[usize]) -> String {
    let mut line = String::from("|");
    for width in widths {
        line.push_str(&"-".repeat(*width));
        line.push('|');
    }
    line
}

/// A polynomial with `num_terms` drawn monomials, each exponent below `max_exponent`.
fn random_poly<const N: usize, F: FiniteField>(
    num_terms: usize,
    max_exponent: u32,
    rng: &mut StdRng,
) -> MultivariatePolynomial<N, F> {
    let terms: Vec<(Monomial<N>, F)> = (0..num_terms)
        .map(|_| {
            let mut exponents = [0u32; N];
            for e in exponents.iter_mut() {
                *e = rng.gen_range(0..max_exponent);
            }
            (Monomial::new(&exponents), F::random(rng))
        })
        .collect();
    MultivariatePolynomial::new(&terms)
}

/// A pair with a planted common factor, and the factor itself.
///
/// `None` when the draw was degenerate — a zero factor or cofactor leaves nothing to measure, and
/// skipping is better than measuring a GCD against zero, which is a different code path.
#[allow(clippy::type_complexity)]
fn planted<const N: usize, F: FiniteField>(
    shape: Shape,
    rng: &mut StdRng,
) -> Option<(
    MultivariatePolynomial<N, F>,
    MultivariatePolynomial<N, F>,
    MultivariatePolynomial<N, F>,
)> {
    let shared = random_poly::<N, F>(shape.shared_terms, shape.max_exponent, rng);
    let left = random_poly::<N, F>(shape.cofactor_terms, shape.max_exponent, rng);
    let right = random_poly::<N, F>(shape.cofactor_terms, shape.max_exponent, rng);
    if shared.is_zero() || left.is_zero() || right.is_zero() {
        return None;
    }
    Some((&shared * &left, &shared * &right, shared))
}

/// Both routes at one shape, interleaved, each reported as its fastest pass.
fn pair<const N: usize, F: KnownOrder>(
    f: &MultivariatePolynomial<N, F>,
    g: &MultivariatePolynomial<N, F>,
) -> Row {
    #[cfg(feature = "research-work")]
    let (primitive, primitive_profile) =
        zeebra::gcd_profile::measure(|| f.gcd_by(g, GcdRoute::PrimitivePrs));
    #[cfg(not(feature = "research-work"))]
    let primitive = f.gcd_by(g, GcdRoute::PrimitivePrs);
    #[cfg(feature = "research-work")]
    let (subresultant, subresultant_profile) =
        zeebra::gcd_profile::measure(|| f.gcd_by(g, GcdRoute::SubresultantPrs));
    #[cfg(not(feature = "research-work"))]
    let subresultant = f.gcd_by(g, GcdRoute::SubresultantPrs);
    assert_eq!(
        primitive, subresultant,
        "the two GCD routes disagree, so a timing comparison between them means nothing"
    );

    // Brown's route can refuse, so whether it is timed at all is decided before the clock starts —
    // and when it answers, it must agree, or there is nothing to compare.
    #[cfg(feature = "research-work")]
    let (brown_result, brown_profile) =
        zeebra::gcd_profile::measure(|| f.try_gcd_by(g, GcdRoute::Brown));
    #[cfg(not(feature = "research-work"))]
    let brown_result = f.try_gcd_by(g, GcdRoute::Brown);
    let brown_applies = match brown_result {
        Ok(value) => {
            assert_eq!(
                value, subresultant,
                "Brown's route disagrees with the references, so timing it means nothing"
            );
            true
        }
        Err(refusal) => {
            REFUSAL.with(|slot| {
                if slot.borrow().is_none() {
                    *slot.borrow_mut() = Some(refusal.to_string());
                }
            });
            false
        }
    };

    let mut best = (Duration::MAX, Duration::MAX, Duration::MAX);
    let mut spent = Duration::ZERO;
    let mut taken = 0;
    while taken < MAX_REPETITIONS && spent < PAIR_BUDGET {
        // Interleaved, arm by arm within one repetition, so a drift in the box's speed falls on
        // all three rather than on whichever ran last.
        let start = Instant::now();
        let value = f.gcd_by(g, GcdRoute::PrimitivePrs);
        let primitive_time = start.elapsed();
        std::hint::black_box(&value);

        let start = Instant::now();
        let value = f.gcd_by(g, GcdRoute::SubresultantPrs);
        let subresultant_time = start.elapsed();
        std::hint::black_box(&value);

        let brown_time = if brown_applies {
            let start = Instant::now();
            let value = f.try_gcd_by(g, GcdRoute::Brown);
            let elapsed = start.elapsed();
            std::hint::black_box(&value);
            elapsed
        } else {
            Duration::ZERO
        };

        best.0 = best.0.min(primitive_time);
        best.1 = best.1.min(subresultant_time);
        if brown_applies {
            best.2 = best.2.min(brown_time);
        }
        spent += primitive_time + subresultant_time + brown_time;
        taken += 1;
    }
    Row {
        primitive: best.0,
        subresultant: best.1,
        brown: brown_applies.then_some(best.2),
        repetitions: taken,
        #[cfg(feature = "research-work")]
        profiles: [primitive_profile, subresultant_profile, brown_profile],
    }
}

/// One arity's sweep over every shape.
fn sweep<const N: usize, F: KnownOrder>(seed: u64) -> (usize, usize) {
    println!(
        "\n| {:>7} | {:>7} | {:>5} | {:>7} | {:>7} | {:>13} | {:>13} | {:>13} | {:>9} | {:>9} | {:>5} |",
        "vars",
        "shared",
        "exp",
        "cofact",
        "f terms",
        "primitive/s",
        "subres/s",
        "brown/s",
        "sub/prim",
        "sub/brown",
        "reps"
    );
    println!("{}", rule(&[9, 9, 7, 9, 9, 15, 15, 15, 11, 11, 7]));

    let mut rng = StdRng::seed_from_u64(seed);
    let mut subresultant_wins = 0;
    let mut primitive_wins = 0;
    let mut brown_wins = 0;
    let mut brown_losses = 0;
    let mut brown_refusals = 0;

    let limit = if N >= 4 {
        WIDE_ARITY_SHAPES.min(SHAPES.len())
    } else {
        SHAPES.len()
    };
    if limit < SHAPES.len() {
        println!(
            "- at {} variables the last {} shape(s) are omitted: one pass of the primitive route \
             there does not finish inside this run's budget",
            N,
            SHAPES.len() - limit
        );
    }

    for shape in SHAPES.iter().take(limit).copied() {
        let Some((f, g, _shared)) = planted::<N, F>(shape, &mut rng) else {
            continue;
        };
        let row = pair(&f, &g);
        let (primitive, subresultant) = (row.primitive, row.subresultant);
        let speedup = primitive.as_secs_f64() / subresultant.as_secs_f64();
        // The same 10% band the other comparisons here use: inside it the two cost the same to
        // within this box's spread and neither route is established as the faster one.
        if speedup > 1.1 {
            subresultant_wins += 1;
        } else if speedup < 1.0 / 1.1 {
            primitive_wins += 1;
        }

        let brown_cell = match row.brown {
            Some(brown) => format!("{:>13.8}", brown.as_secs_f64()),
            None => format!("{:>13}", "refused"),
        };
        let brown_ratio = match row.brown {
            Some(brown) => format!("{:>9.2}", brown.as_secs_f64() / subresultant.as_secs_f64()),
            None => format!("{:>9}", "-"),
        };
        println!(
            "| {:>7} | {:>7} | {:>5} | {:>7} | {:>7} | {:>13.8} | {:>13.8} | {} | {:>9.2} | {} | {:>5} |",
            N,
            shape.shared_terms,
            shape.max_exponent,
            shape.cofactor_terms,
            f.terms().len(),
            primitive.as_secs_f64(),
            subresultant.as_secs_f64(),
            brown_cell,
            speedup,
            brown_ratio,
            row.repetitions,
        );
        #[cfg(feature = "research-work")]
        {
            println!("\n| route | PRS max terms | PRS max coefficient degree | raw max terms | raw coefficient degree | image max terms | image coefficient degree | interpolant max terms | interpolant coefficient degree |");
            println!("|---|---:|---:|---:|---:|---:|---:|---:|---:|");
            for (route, stats) in ["primitive", "subresultant", "brown"]
                .into_iter()
                .zip(row.profiles)
            {
                println!(
                    "| {route} | {} | {} | {} | {} | {} | {} | {} | {} |",
                    stats.prs_entries.max_terms,
                    stats.prs_entries.max_coefficient_degree,
                    stats.raw_remainders.max_terms,
                    stats.raw_remainders.max_coefficient_degree,
                    stats.brown_images.max_terms,
                    stats.brown_images.max_coefficient_degree,
                    stats.brown_interpolants.max_terms,
                    stats.brown_interpolants.max_coefficient_degree
                );
            }
        }
        if let Some(brown) = row.brown {
            let ratio = brown.as_secs_f64() / subresultant.as_secs_f64();
            if ratio > 1.1 {
                brown_losses += 1;
            } else if ratio < 1.0 / 1.1 {
                brown_wins += 1;
            }
        } else {
            brown_refusals += 1;
        }
    }
    if brown_refusals > 0 {
        let reason = REFUSAL
            .with(|slot| slot.borrow().clone())
            .unwrap_or_else(|| "no reason recorded".to_string());
        println!(
            "- Brown's route refused {brown_refusals} of {limit} shapes at {N} variables: {reason}"
        );
    }
    if brown_wins + brown_losses > 0 {
        println!(
            "- where it answered, Brown's route beat the default on {brown_wins} shapes by more \
             than 10% and lost on {brown_losses}"
        );
    }
    (subresultant_wins, primitive_wins)
}

/// The one-minute load average, or zero where `/proc` does not carry one.
fn one_minute_load() -> f64 {
    std::fs::read_to_string("/proc/loadavg")
        .ok()
        .and_then(|line| line.split_whitespace().next()?.parse().ok())
        .unwrap_or(0.0)
}

/// One field, every arity.
fn measure_field<F: KnownOrder>(name: &str, seed: u64) {
    println!("\n\n## {name}");
    println!("\n- an element is {} bytes", std::mem::size_of::<F>());
    REFUSAL.with(|slot| *slot.borrow_mut() = None);
    let mut subresultant = 0;
    let mut primitive = 0;
    for (arity, result) in [
        (2, sweep::<2, F>(seed ^ 2)),
        (3, sweep::<3, F>(seed ^ 3)),
        (4, sweep::<4, F>(seed ^ 4)),
    ] {
        let _ = arity;
        subresultant += result.0;
        primitive += result.1;
    }
    println!(
        "\n- across every arity and shape: the subresultant route wins {subresultant} shapes by \
         more than 10%, the primitive route wins {primitive}, the rest are within the band"
    );
    if primitive > subresultant {
        println!(
            "- **the default is not the faster route on this field**, which is the finding #407 \
             exists to establish and the reason the default was never justified on wall clock"
        );
    } else if subresultant > primitive {
        println!("- the default is the faster route on this field");
    } else {
        println!(
            "- neither route is established as faster on this field — a null result, to report as \
             one"
        );
    }
}

fn main() {
    if std::env::args().nth(1).as_deref() == Some("--case") {
        single_case();
        return;
    }
    let which = std::env::args().nth(1).unwrap_or_else(|| "all".into());

    println!("# The multivariate GCD routes: two remainder sequences against Brown's modular");
    println!("\nISA: {}", zeebra::util::isa_floor());
    println!(
        "\nIssues #407 and #434. #128 published no timings, so the per-route absolute figures here \
         began with #407 and the Brown's column with #434."
    );
    println!(
        "\n- one-minute load at the start of this run: **{:.2}**. Interleaving limits drift, but \
         neither durations nor ratios are guaranteed to survive contention. Use matched controls \
         and inspect repeat ranges before interpreting a difference.",
        one_minute_load()
    );
    println!(
        "- each timed figure is the fastest of up to {MAX_REPETITIONS} interleaved repetitions"
    );
    println!("- all three routes are asserted equal at every shape before the clock starts");
    println!(
        "- Brown's route can **refuse** — it needs a prime field with more elements than the \
         degree it interpolates over — and where it does, the cell reads `refused` and the reason \
         is printed once per field rather than once per shape"
    );
    println!("- `f terms` is the term count of the product actually handed to the GCD");
    println!(
        "- the monomial order throughout is {}",
        MonomialOrder::Lexicographic.name()
    );

    if which == "all" || which == "koalabear" {
        measure_field::<KoalaBear>("KoalaBear, 2^31 - 2^24 + 1", 0x0407_1001);
    }
    if which == "all" || which == "goldilocks" {
        measure_field::<Goldilocks>("Goldilocks, 2^64 - 2^32 + 1", 0x0407_1002);
    }
    if which == "all" || which == "bn254" {
        measure_field::<Bn254Fr>("BN254 Fr, 254 bits", 0x0407_1003);
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

fn single_case() {
    let args: Vec<_> = std::env::args().skip(2).collect();
    assert_eq!(
        args.len(),
        5,
        "--case FIELD ARITY SHAPE(0..6) ROUTE MODE(off|on)"
    );
    let route = match args[3].as_str() {
        "primitive" => GcdRoute::PrimitivePrs,
        "subresultant" => GcdRoute::SubresultantPrs,
        "brown" => GcdRoute::Brown,
        _ => panic!("unknown route"),
    };
    let observe = match args[4].as_str() {
        "off" => false,
        "on" => true,
        _ => panic!("mode must be off or on"),
    };
    let shape: usize = args[2].parse().expect("shape index");
    assert!(shape < SHAPES.len(), "shape index must be 0..6");
    let arity: usize = args[1].parse().expect("arity");
    macro_rules! dispatch {
        ($field:ty, $seed:expr) => {
            match arity {
                2 => case::<2, $field>($seed ^ 2, shape, route, observe),
                3 => case::<3, $field>($seed ^ 3, shape, route, observe),
                4 => case::<4, $field>($seed ^ 4, shape, route, observe),
                _ => panic!("arity must be 2, 3 or 4"),
            }
        };
    }
    match args[0].as_str() {
        "koalabear" => dispatch!(KoalaBear, 0x0407_1001),
        "goldilocks" => dispatch!(Goldilocks, 0x0407_1002),
        "bn254" => dispatch!(Bn254Fr, 0x0407_1003),
        _ => panic!("unknown field"),
    }
}

fn case<const N: usize, F: KnownOrder>(seed: u64, shape: usize, route: GcdRoute, observe: bool) {
    use zeebra::util::{sha256_hex, Json};
    let mut rng = StdRng::seed_from_u64(seed);
    // Replay all preceding draws so this is byte-for-byte the historical sweep's chosen pair.
    let mut selected = None;
    for current in SHAPES.iter().take(shape + 1) {
        selected = planted::<N, F>(*current, &mut rng);
    }
    let (f, g, shared) = selected.expect("degenerate fixture");
    let input = format!(
        "characteristic={:?}\nvariables={N}\n{f}\n{g}\n",
        F::characteristic_limbs()
    );
    let start = Instant::now();
    let (answer, elapsed, profile) = if observe {
        #[cfg(feature = "research-work")]
        {
            let (answer, profile) = zeebra::gcd_profile::measure(|| f.try_gcd_by(&g, route));
            let elapsed = start.elapsed();
            (answer, elapsed, profile.json())
        }
        #[cfg(not(feature = "research-work"))]
        panic!("on requires --features research-work");
    } else {
        let answer = f.try_gcd_by(&g, route);
        (answer, start.elapsed(), Json::Null)
    };
    let mut result = vec![
        ("arity", Json::size(N)),
        ("shape", Json::size(shape)),
        ("seed", Json::int(seed)),
        ("input", Json::string(&input)),
        ("input_sha256", Json::string(sha256_hex(input.as_bytes()))),
        ("input_terms", Json::size(f.terms().len())),
        ("other_terms", Json::size(g.terms().len())),
        ("route", Json::string(format!("{route:?}"))),
        ("observed", Json::Bool(observe)),
        ("elapsed_ns", Json::nanos(elapsed)),
        (
            "peak_rss_bytes",
            peak_resident_bytes().map_or(Json::Null, Json::int),
        ),
        ("profile", profile),
    ];
    match answer {
        Ok(gcd) => {
            assert!(f.exact_div(&gcd).is_some() && g.exact_div(&gcd).is_some());
            assert!(gcd.exact_div(&shared).is_some());
            result.push(("status", Json::string("completed")));
            result.push(("gcd", Json::string(gcd.to_string())));
        }
        Err(error) => {
            result.push(("status", Json::string("refused")));
            result.push(("refusal", Json::string(error.to_string())));
        }
    }
    println!("{}", Json::object(result).to_json());
}
