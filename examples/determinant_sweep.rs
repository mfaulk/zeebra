//! M25 #289: what one Sylvester determinant costs, measured across five matrix orders.
//!
//! ```text
//! cargo run --release --example determinant_sweep                     # the five-order sweep
//! cargo run --release --example determinant_sweep -- --repeats 3      # three draws a point
//! cargo run --release --example determinant_sweep -- --order 162 --order 486
//! cargo run --release --example determinant_sweep -- --concurrency 8  # core-time at width
//! cargo run --release --example determinant_sweep -- --order 1458 --determinants 128
//!                                                    # several determinants a worker, so the
//!                                                    # first-touch page faults are amortized
//! cargo run --release --example determinant_sweep -- --cost-only      # print the budget, run nothing
//! ```
//!
//! # Why this is not a subcommand of `resultant_cico`
//!
//! That example's subject is the **registered** CICO ladder, and every figure it prints is tied to
//! a named challenge, a sample count derived from that row's round numbers, and a budget guard that
//! refuses a row. A determinant cost law is a property of the kernel and of this machine's cache
//! hierarchy, not of any row: measuring it on a registered row would confound the exponent with
//! that row's particular degrees, and the orders worth measuring (4 374) are ones no affordable row
//! reaches. So the sweep runs on **random bivariate pairs** of named degree, and lives apart.
//!
//! # What is measured, and what is derived
//!
//! Per order: wall clock per determinant, core-time per determinant (wall × workers), the dense
//! matrix footprint in bytes, the worker count, and the number of determinants averaged over, with
//! `--repeats` independent draws so a spread is reported rather than one number. The sampling loop
//! is the same `sample_determinants` every resultant route uses; the one-off coefficient extraction
//! is outside the timer because it is per-row work and not per-determinant work.
//!
//! Then two fits, both printed with **per-point residuals**: one power law over all orders, and a
//! piecewise pair split at the order whose matrix stops fitting in L2. The piecewise verdict is the
//! point of the exercise — three timings on record already have a rising local slope (2.65 from 18
//! to 162, 3.12 from 162 to 1 458), which is convex in log-log and therefore not a single law.
//!
//! The degrees are chosen so the matrix order is the variable and nothing else is: degree 1 in the
//! surviving variable and `order / 2` in the eliminated one. Each matrix entry is then a linear
//! polynomial evaluated at the sample point, so building the matrix costs `O(order)` evaluations
//! and `O(order²)` writes against the LU's `O(order³)` — under 2% by operation count at order 162
//! and falling, which is what makes the determinant kernel the thing being timed.

use std::time::Instant;

use rand::{prelude::StdRng, SeedableRng};

use zeebra::{
    fields::PrimeFieldElement64,
    grobner::research::{
        fit_power_law, random_bivariate, time_sylvester_determinants, DeterminantBatch, PowerLawFit,
        KOALABEAR_PRIME,
    },
    util::peak_resident_bytes,
    FiniteField,
};

type K = PrimeFieldElement64<KOALABEAR_PRIME>;

/// The orders swept by default: `2 · 3^r` for `r = 2, 4, 5, 6, 7`.
///
/// These are the Sylvester orders the CICO ladder actually produces — a row of `r` rounds gives two
/// polynomials of degree `3^r` and a matrix of order `2 · 3^r` — plus 486, which no measured row
/// reaches but which sits in the gap between the 162 and 1 458 already on record. 4 374 is the
/// order whose 153 MB matrix separates L3 from main memory on this machine and is the point the
/// cache argument turns on, so it is in the default sweep rather than behind a flag.
const ORDERS: [usize; 5] = [18, 162, 486, 1_458, 4_374];

/// Determinants evaluated per draw at each order, chosen so every point costs seconds not hours.
///
/// Scaled against roughly `order³`: the counts fall by about 27x as the order triples, which keeps
/// each point near a constant wall clock while still averaging over enough determinants that the
/// per-determinant figure is not one draw's noise. At order 4 374 three determinants is all a
/// bounded sweep affords — one is about a minute — and the repeat count is what supplies the spread
/// there.
fn determinants_at(order: usize) -> usize {
    if let Some(override_count) = flag_value("--determinants") {
        return override_count.max(1);
    }
    match order {
        0..=31 => 20_000,
        32..=199 => 500,
        200..=599 => 100,
        600..=1_999 => 8,
        _ => 3,
    }
}

/// The value of a `--flag <value>` argument, if it was given and parses.
fn flag_value(flag: &str) -> Option<usize> {
    let args: Vec<String> = std::env::args().collect();
    let at = args.iter().position(|a| a == flag)?;
    args.get(at + 1)?.parse().ok()
}

/// Every value of a repeatable `--flag <value>` argument.
fn flag_values(flag: &str) -> Vec<usize> {
    let args: Vec<String> = std::env::args().collect();
    args.iter()
        .enumerate()
        .filter(|(_, a)| *a == flag)
        .filter_map(|(at, _)| args.get(at + 1)?.parse().ok())
        .collect()
}

/// Every draw taken at one order.
struct Point {
    /// Matrix order.
    order: usize,
    /// Bytes in one dense matrix of field elements.
    matrix_bytes: usize,
    /// Determinants in each draw.
    determinants: usize,
    /// Workers each draw used.
    concurrency: usize,
    /// Core-time per determinant, one entry per draw, in seconds.
    core: Vec<f64>,
    /// Wall clock per determinant, one entry per draw, in seconds.
    wall: Vec<f64>,
}

impl Point {
    /// The median core-time per determinant, which is what the fit is taken against.
    ///
    /// The median rather than the mean: a draw that collided with another agent's work on a shared
    /// L3 is slow, never fast, so the contamination is one-sided and a mean carries it.
    fn core_median(&self) -> f64 {
        median(&self.core)
    }

    /// The spread of the core-time draws, as a fraction of the median.
    fn core_spread(&self) -> f64 {
        let (lo, hi) = extremes(&self.core);
        (hi - lo) / self.core_median()
    }
}

/// The median of a nonempty sample.
fn median(values: &[f64]) -> f64 {
    let mut sorted = values.to_vec();
    sorted.sort_by(|a, b| a.partial_cmp(b).expect("no NaN in a measured duration"));
    let n = sorted.len();
    if n % 2 == 1 {
        sorted[n / 2]
    } else {
        0.5 * (sorted[n / 2 - 1] + sorted[n / 2])
    }
}

/// The smallest and largest of a nonempty sample.
fn extremes(values: &[f64]) -> (f64, f64) {
    values.iter().fold((f64::MAX, f64::MIN), |(lo, hi), v| {
        (lo.min(*v), hi.max(*v))
    })
}

/// A duration in whatever unit a reader can hold in their head.
fn human(seconds: f64) -> String {
    if seconds < 1e-3 {
        format!("{:.2} µs", seconds * 1e6)
    } else if seconds < 1.0 {
        format!("{:.3} ms", seconds * 1e3)
    } else if seconds < 90.0 {
        format!("{:.3} s", seconds)
    } else if seconds < 5_400.0 {
        format!("{:.2} min", seconds / 60.0)
    } else if seconds < 172_800.0 {
        format!("{:.2} h", seconds / 3_600.0)
    } else {
        format!("{:.2} d", seconds / 86_400.0)
    }
}

/// Bytes, in the unit that makes the cache level obvious.
fn bytes(n: usize) -> String {
    let n = n as f64;
    if n < 1e6 {
        format!("{:.0} kB", n / 1e3)
    } else {
        format!("{:.1} MB", n / 1e6)
    }
}

/// One draw at one order: build a fresh random pair, then time `determinants` determinants.
fn draw(order: usize, determinants: usize, concurrency: usize, seed: u64) -> DeterminantBatch {
    assert!(order % 2 == 0, "the order is split evenly between the pair");
    let half = (order / 2) as u32;
    let mut rng = StdRng::seed_from_u64(seed);
    // Degree 1 in the surviving variable, `order / 2` in the eliminated one: the matrix order is
    // `deg_y(f) + deg_y(g)`, and a linear coefficient keeps the pair small enough that building it
    // is not itself the measurement.
    let f = random_bivariate::<K, _>(1, half, &mut rng);
    let g = random_bivariate::<K, _>(1, half, &mut rng);
    // Abscissae away from 0 and 1, where a Sylvester entry could be degenerate by accident.
    let at: Vec<K> = (0..determinants).map(|i| K::new(i as u64 + 7)).collect();
    let (_, batch) = time_sylvester_determinants(&f, &g, 1, &at, concurrency)
        .expect("both polynomials have positive degree in the eliminated variable");
    assert_eq!(batch.matrix_order, order, "the pair has the named order");
    batch
}

/// The fit table for one named law over the points it was fitted to.
fn report_fit(name: &str, points: &[&Point], fit: &PowerLawFit) {
    println!(
        "\n**{}**: `core(order) = {:.4e} · order^{:.4}`, exponent standard error ±{:.4}, worst \
         residual {:+.1}%\n",
        name,
        fit.prefactor,
        fit.exponent,
        fit.exponent_stderr,
        100.0 * fit.worst_residual()
    );
    println!("| order | measured core-time | fitted | residual |");
    println!("|---:|---:|---:|---:|");
    for (point, residual) in points.iter().zip(&fit.residuals) {
        println!(
            "| {} | {} | {} | {:+.2}% |",
            point.order,
            human(point.core_median()),
            human(fit.at(point.order as f64)),
            100.0 * residual
        );
    }
}

fn main() {
    let repeats = flag_value("--repeats").unwrap_or(3).max(1);
    let concurrency = flag_value("--concurrency").unwrap_or(1).max(1);
    let wanted = flag_values("--order");
    let orders: Vec<usize> = if wanted.is_empty() {
        ORDERS.to_vec()
    } else {
        wanted
    };

    println!("# M25 #289: the Sylvester determinant cost law, measured\n");
    println!(
        "Random bivariate pairs over KoalaBear, degree 1 in the surviving variable and `order / 2` \
         in the eliminated one, so the matrix order is the only thing that varies. {} independent \
         draw{} per order at {} worker{}, through the same `sample_determinants` loop every \
         resultant route uses.\n",
        repeats,
        if repeats == 1 { "" } else { "s" },
        concurrency,
        if concurrency == 1 { "" } else { "s" }
    );

    // The budget, printed before anything runs. Order 4 374 is about a minute a determinant
    // single-threaded, so a sweep whose cost nobody costed is how an afternoon disappears.
    let mut budget = 0.0f64;
    println!("| order | determinants/draw | matrix | predicted wall, all draws |");
    println!("|---:|---:|---:|---:|");
    for &order in &orders {
        let determinants = determinants_at(order).max(concurrency);
        // The cubic anchor from `resultant-elimination.md` §6.5: 2.868 ms at order 162.
        let each = 2.868e-3 * (order as f64 / 162.0).powi(3);
        let predicted = each * determinants as f64 * repeats as f64 / concurrency as f64;
        budget += predicted;
        println!(
            "| {} | {} | {} | {} |",
            order,
            determinants,
            bytes(order * order * std::mem::size_of::<K>()),
            human(predicted)
        );
    }
    println!(
        "\nPredicted sweep cost **{}** from the cubic anchor — an extrapolation above order 162, \
         which is what this run exists to replace.\n",
        human(budget)
    );
    if std::env::args().any(|a| a == "--cost-only") {
        println!("`--cost-only`: nothing measured.");
        return;
    }

    let started = Instant::now();
    let mut points: Vec<Point> = Vec::new();
    for &order in &orders {
        // At least one determinant per worker, or the static block split leaves workers idle and
        // the run would report a width it never reached.
        let determinants = determinants_at(order).max(concurrency);
        let mut point = Point {
            order,
            matrix_bytes: 0,
            determinants,
            concurrency,
            core: Vec::new(),
            wall: Vec::new(),
        };
        for repeat in 0..repeats {
            // A different pair per draw, so a draw is an independent sample of the kernel's cost
            // and not a re-timing of one matrix.
            let batch = draw(
                order,
                determinants,
                concurrency,
                0x5_e51u64.wrapping_add(order as u64) ^ (repeat as u64 + 1),
            );
            point.matrix_bytes = batch.matrix_bytes;
            point.core.push(batch.core_per_determinant());
            point.wall.push(batch.wall_per_determinant());
        }
        println!(
            "- order {}: core-time **{}** per determinant (spread {:.1}%, wall {}), {} matrix, {} \
             determinants x {} draws",
            order,
            human(point.core_median()),
            100.0 * point.core_spread(),
            human(median(&point.wall)),
            bytes(point.matrix_bytes),
            determinants,
            repeats
        );
        points.push(point);
    }

    println!("\n## The sweep\n");
    println!(
        "| order | matrix | live set/worker | determinants | workers | draws | wall/determinant | \
         core-time/determinant | spread |"
    );
    println!("|---:|---:|---:|---:|---:|---:|---:|---:|---:|");
    for point in &points {
        println!(
            "| {} | {} | {} | {} | {} | {} | {} | **{}** | {:.1}% |",
            point.order,
            bytes(point.matrix_bytes),
            // Crout clones A and returns L, U and P beside it.
            bytes(4 * point.matrix_bytes),
            point.determinants,
            point.concurrency,
            point.core.len(),
            human(median(&point.wall)),
            human(point.core_median()),
            100.0 * point.core_spread()
        );
    }

    println!("\n## Local exponents between adjacent orders\n");
    println!("| from | to | ratio of orders | ratio of cost | local exponent |");
    println!("|---:|---:|---:|---:|---:|");
    for window in points.windows(2) {
        let (lo, hi) = (&window[0], &window[1]);
        let order_ratio = hi.order as f64 / lo.order as f64;
        let cost_ratio = hi.core_median() / lo.core_median();
        println!(
            "| {} | {} | {:.2}x | {:.1}x | **{:.3}** |",
            lo.order,
            hi.order,
            order_ratio,
            cost_ratio,
            cost_ratio.ln() / order_ratio.ln()
        );
    }

    // A single law over everything, then the piecewise alternative. The split is at the order whose
    // matrix leaves L2 (512 kB a core here): orders at or below it are overhead-dominated and the
    // ones above pay for a cache hierarchy the small ones never touch.
    let all: Vec<&Point> = points.iter().collect();
    let pairs: Vec<(f64, f64)> = all
        .iter()
        .map(|p| (p.order as f64, p.core_median()))
        .collect();
    println!("\n## The fit\n");
    match fit_power_law(&pairs) {
        Some(fit) => report_fit("single power law, every order", &all, &fit),
        None => println!("a single law needs two distinct orders; this sweep has one"),
    }

    const L2_BYTES: usize = 512 * 1024;
    let small: Vec<&Point> = points.iter().filter(|p| p.matrix_bytes <= L2_BYTES).collect();
    let large: Vec<&Point> = points.iter().filter(|p| p.matrix_bytes > L2_BYTES).collect();
    println!(
        "\nSplit at the L2 footprint — {} a core on this machine — which puts orders {:?} below and \
         {:?} above.",
        bytes(L2_BYTES),
        small.iter().map(|p| p.order).collect::<Vec<_>>(),
        large.iter().map(|p| p.order).collect::<Vec<_>>()
    );
    for (name, group) in [("below L2", &small), ("above L2", &large)] {
        let group_pairs: Vec<(f64, f64)> = group
            .iter()
            .map(|p| (p.order as f64, p.core_median()))
            .collect();
        match fit_power_law(&group_pairs) {
            Some(fit) => report_fit(&format!("piecewise, {}", name), group, &fit),
            None => println!(
                "\n**piecewise, {}**: {} point(s) — too few to fit, so no exponent is claimed",
                name,
                group.len()
            ),
        }
    }

    // The projections the go/no-go decision reads. Every number here is extrapolated from the table
    // above; the samples are exact, because they come from the rows' own round counts.
    println!("\n## Projected rows\n");
    println!(
        "Samples are exact — `alpha^(2 R_F + R_P) + 1` from each row's own parameters. The \
         per-determinant cost at order 1 458 is **measured** above; at order 13 122 it is \
         **extrapolated** and labelled.\n"
    );
    let anchor = points.iter().find(|p| p.order == 1_458);
    let measured_1458 = anchor.map(Point::core_median);
    let fit = fit_power_law(&pairs);
    println!("| row | samples | order | core-time/determinant | single-core | 32 workers |");
    println!("|---|---:|---:|---:|---:|---:|");
    for (row, samples, order) in [
        ("rf2-rp4 (6 rounds)", 6_562usize, 1_458usize),
        ("rf4-rp2 (6 rounds)", 59_050, 1_458),
        ("rf6-rp0 (6 rounds)", 531_442, 1_458),
        ("rf6-rp4 (8 rounds)", 43_046_722, 13_122),
    ] {
        let (each, label) = match (order, measured_1458, &fit) {
            (1_458, Some(measured), _) => (measured, "measured"),
            (_, _, Some(fit)) => (fit.at(order as f64), "extrapolated"),
            _ => continue,
        };
        let serial = each * samples as f64;
        println!(
            "| {} | {} | {} | {} ({}) | {} | {} |",
            row,
            samples,
            order,
            human(each),
            label,
            human(serial),
            human(serial / 32.0)
        );
    }

    println!(
        "\nSwept in {} wall.{}",
        human(started.elapsed().as_secs_f64()),
        match peak_resident_bytes() {
            Some(b) => format!(" Peak resident {:.2} GB.", b as f64 / 1e9),
            None => String::new(),
        }
    );
}
