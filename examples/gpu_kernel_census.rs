//! #86: the CPU side of the GPU-suitability question, per field width.
//!
//! Two modes, both public-API only:
//!
//! - `ceilings` measures, per field, the shipped elimination step `acc[c] -= v * factor` (the inner
//!   loop of `DenseAccumulator::subtract_scaled`) at three residencies of the pivot entries, a
//!   contiguous L1 arithmetic ceiling for the same step, and one core's streaming-read bandwidth.
//!   A kernel's measured rate divided by these says whether it is arithmetic- or bandwidth-bound.
//! - `f4` runs one public system over one field with stage clocks, and with
//!   `--features research-work` the serial entry-operation census, so a stage's measured time and
//!   its logical byte traffic come from the same run.
//!
//! ```text
//! cargo run --release --example gpu_kernel_census -- ceilings [--reps 5]
//! cargo run --release [--features research-work] --example gpu_kernel_census -- \
//!     f4 --system katsura-10 --field bn254 --workers 1 [--work]
//! ```
//!
//! Byte counts are logical (`(usize, F)` pivot entry read, accumulator cell read and written), not
//! DRAM traffic: no hardware counters are readable on the host (#87 §1).

use std::hint::black_box;
use std::time::{Duration, Instant};

use zeebra::{
    fields::{Bn254Fr, Gf256Mq, PrimeFieldElement64, Zp2147483647, Zp32003},
    grobner::{
        benchmark_systems::{cyclic, katsura},
        differential::{CaseField, GeneratedSystem, SystemShape},
        f4_reported, F4Options, F4Statistics, ParallelForward, ParallelSymbolic,
    },
    util::{peak_resident_bytes, Json},
    FiniteField, Monomial, MonomialOrder, MultivariatePolynomial,
};

type Goldilocks = PrimeFieldElement64<18446744069414584321>;
type Wide = PrimeFieldElement64<18446744073709551263>;
const ORDER: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

/// Accumulator width: `mq-random-10`'s largest batch has 12,020 columns (`m29-baseline-cost-model.md` §5).
const WIDTH: usize = 12_288;
/// Entries per simulated pivot row, close to the F4 batches' mean pivot length.
const ROW: usize = 64;

/// SplitMix64, so every arm sees the same columns and coefficients for a seed.
struct Mix(u64);

impl Mix {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A nonzero element every field here parses, including `Gf256Mq`'s bit patterns.
    fn element<F: FiniteField>(&mut self) -> F {
        F::from_str(&(1 + self.next() % 251).to_string()).expect("a small integer is an element")
    }
}

/// Sorted, distinct pivot rows over `WIDTH` columns, as `SparseRow` stores them.
fn pivot_rows<F: FiniteField>(entries: usize, seed: u64) -> Vec<(usize, F)> {
    let mut mix = Mix(seed);
    let mut out = Vec::with_capacity(entries);
    while out.len() < entries {
        let mut columns: Vec<usize> = (0..ROW)
            .map(|_| (mix.next() % WIDTH as u64) as usize)
            .collect();
        columns.sort_unstable();
        columns.dedup();
        columns.resize(ROW, columns[columns.len() - 1]);
        for column in columns {
            out.push((column, mix.element::<F>()));
        }
    }
    out.truncate(entries);
    out
}

/// The shipped step over `rows`, one prepared factor per `ROW` entries; returns products done.
fn eliminate<F: FiniteField>(acc: &mut [F], rows: &[(usize, F)], factors: &[F]) -> usize {
    let mut nonzeros = 0usize;
    for (row, factor) in rows.chunks(ROW).zip(factors.iter().cycle()) {
        let prepared = factor.prepare_factor();
        for (column, coefficient) in row {
            let before = acc[*column];
            let after = before - coefficient.mul_prepared(&prepared);
            acc[*column] = after;
            nonzeros += usize::from(before.is_zero());
            nonzeros -= usize::from(after.is_zero());
        }
    }
    black_box(nonzeros);
    rows.len()
}

/// `y[i] -= x[i] * factor` over 1,024 L1-resident cells: the step's arithmetic ceiling.
fn l1_axpy<F: FiniteField>(steps: usize) -> (usize, Duration) {
    let mut mix = Mix(7);
    let x: Vec<F> = (0..1024).map(|_| mix.element()).collect();
    let mut y: Vec<F> = (0..1024).map(|_| mix.element()).collect();
    let prepared = mix.element::<F>().prepare_factor();
    let started = Instant::now();
    for _ in 0..steps {
        for (yi, xi) in y.iter_mut().zip(black_box(&x)) {
            *yi = *yi - xi.mul_prepared(&prepared);
        }
    }
    black_box(&y);
    (steps * 1024, started.elapsed())
}

fn stream_read(buffer: &[u64], passes: usize) -> (usize, Duration) {
    let started = Instant::now();
    let mut sum = 0u64;
    for _ in 0..passes {
        for chunk in buffer.chunks(8) {
            for &v in chunk {
                sum = sum.wrapping_add(v);
            }
        }
    }
    black_box(sum);
    (passes * buffer.len() * 8, started.elapsed())
}

/// The crate's `Json` has no float; rates are printed to four decimals.
fn fl(x: f64) -> Json {
    Json::string(format!("{x:.4}"))
}

fn median(mut v: Vec<f64>) -> f64 {
    v.sort_by(f64::total_cmp);
    v[v.len() / 2]
}

/// One field's arms: name, bytes per product, and per-repetition rates.
fn field_ceilings<F: FiniteField>(name: &str, reps: usize, out: &mut Vec<Json>) {
    let cell = std::mem::size_of::<F>();
    let entry = std::mem::size_of::<(usize, F)>();
    let per_product = entry + 2 * cell;
    // Pivot-entry residencies: L2 (256 KiB), one CCD's L3 (16 MiB), and DRAM (1 GiB).
    let sizes = [("L2", 256usize << 10), ("L3", 16 << 20), ("DRAM", 1 << 30)];
    let pivots: Vec<Vec<(usize, F)>> = sizes
        .iter()
        .map(|(_, bytes)| pivot_rows::<F>(bytes / entry, 11))
        .collect();
    let mut mix = Mix(13);
    let factors: Vec<F> = (0..97).map(|_| mix.element()).collect();
    let mut acc: Vec<F> = (0..WIDTH).map(|_| mix.element()).collect();
    let mut rates: Vec<Vec<f64>> = vec![Vec::new(); sizes.len() + 1];
    for rep in 0..reps {
        for k in 0..=sizes.len() {
            let arm = (k + rep) % (sizes.len() + 1);
            let (ops, elapsed) = if arm == sizes.len() {
                l1_axpy::<F>(4096)
            } else {
                let rows = &pivots[arm];
                // At least 50 ms of work per timing, whatever the residency.
                let passes = (64 << 20) / (rows.len() * entry) + 1;
                let started = Instant::now();
                let mut ops = 0;
                for _ in 0..passes {
                    ops += eliminate(&mut acc, rows, &factors);
                }
                (ops, started.elapsed())
            };
            rates[arm].push(ops as f64 / elapsed.as_secs_f64() / 1e6);
        }
    }
    let l1 = median(rates[sizes.len()].clone());
    let mut arms = vec![(
        "L1 contiguous".to_string(),
        Json::object([
            ("mops", fl(l1)),
            ("logical_gbs", fl(l1 * (3 * cell) as f64 / 1e3)),
        ]),
    )];
    for (i, (label, _)) in sizes.iter().enumerate() {
        let m = median(rates[i].clone());
        arms.push((
            format!("{label} scatter"),
            Json::object([
                ("mops", fl(m)),
                ("logical_gbs", fl(m * per_product as f64 / 1e3)),
                ("of_l1", fl(m / l1)),
            ]),
        ));
    }
    let arms: Vec<(&str, Json)> = arms.iter().map(|(k, v)| (k.as_str(), v.clone())).collect();
    out.push(Json::object([
        ("field", Json::string(name)),
        ("type", Json::string(std::any::type_name::<F>())),
        ("cell_bytes", Json::size(cell)),
        ("entry_bytes", Json::size(entry)),
        ("bytes_per_product", Json::size(per_product)),
        ("arms", Json::object(arms)),
    ]));
}

fn ceilings(reps: usize) {
    let buffer: Vec<u64> = (0..(1usize << 27)).map(|i| i as u64).collect();
    let mut bandwidth = Vec::new();
    for _ in 0..reps {
        let (bytes, elapsed) = stream_read(&buffer, 2);
        bandwidth.push(bytes as f64 / elapsed.as_secs_f64() / 1e9);
    }
    let mut fields = Vec::new();
    field_ceilings::<Zp32003>("gf32003-u32", reps, &mut fields);
    field_ceilings::<Zp2147483647>("m31-u64", reps, &mut fields);
    field_ceilings::<Goldilocks>("goldilocks", reps, &mut fields);
    field_ceilings::<Wide>("p64-353", reps, &mut fields);
    field_ceilings::<Bn254Fr>("bn254", reps, &mut fields);
    field_ceilings::<Gf256Mq>("gf256mq", reps, &mut fields);
    println!(
        "{}",
        Json::object([
            ("mode", Json::string("ceilings")),
            ("reps", Json::size(reps)),
            ("stream_read_gbs_1t", fl(median(bandwidth))),
            ("fields", Json::Array(fields)),
        ])
        .to_json()
        .replace('\n', "")
    );
}

#[derive(Debug, PartialEq)]
struct Args {
    system: String,
    field: String,
    workers: usize,
    work: bool,
}

fn parse_f4(args: &[String]) -> Result<Args, String> {
    let mut parsed = Args {
        system: String::new(),
        field: String::new(),
        workers: 1,
        work: false,
    };
    let mut it = args.iter();
    while let Some(arg) = it.next() {
        let mut value = || it.next().cloned().ok_or(format!("{arg} needs a value"));
        match arg.as_str() {
            "--system" => parsed.system = value()?,
            "--field" => parsed.field = value()?,
            "--workers" => {
                parsed.workers = value()?
                    .parse()
                    .ok()
                    .filter(|&w| w > 0)
                    .ok_or("--workers takes a positive integer")?
            }
            "--work" => parsed.work = true,
            other => return Err(format!("unknown argument {other}")),
        }
    }
    if parsed.system.is_empty() || parsed.field.is_empty() {
        return Err("--system and --field are required".into());
    }
    Ok(parsed)
}

fn options(workers: usize) -> F4Options {
    F4Options {
        measure_stages: true,
        parallel_forward: if workers == 1 {
            ParallelForward::Serial
        } else {
            ParallelForward::Auto {
                max_workers: workers,
            }
        },
        parallel_symbolic: if workers == 1 {
            ParallelSymbolic::Serial
        } else {
            ParallelSymbolic::Auto {
                max_workers: workers,
            }
        },
        ..F4Options::default()
    }
}

/// `random_mq_instance`'s generator (seed `n`, `4n` terms), as the matrix corpus builds it.
fn mq<const N: usize, F: FiniteField>(field: CaseField) -> Vec<MultivariatePolynomial<N, F>> {
    let shape = SystemShape {
        variables: N,
        max_degree: 2,
        max_terms: 4 * N,
    };
    let generated = GeneratedSystem::generate(N as u64, shape, field);
    generated
        .polynomials
        .iter()
        .map(|terms| {
            let entries: Vec<(Monomial<N>, F)> = terms
                .iter()
                .map(|t| {
                    let mut e = [0u32; N];
                    e.copy_from_slice(&t.exponents);
                    (
                        Monomial::new(&e),
                        F::from_str(&t.coefficient.to_string()).expect("coefficient"),
                    )
                })
                .collect();
            MultivariatePolynomial::new(&entries)
        })
        .collect()
}

fn stages(s: &F4Statistics) -> Json {
    let t = s.stages;
    let ns = Json::nanos;
    Json::object([
        ("total_ns", ns(s.total)),
        ("symbolic_ns", ns(t.symbolic)),
        ("construction_ns", ns(t.construction)),
        ("forward_ns", ns(t.forward)),
        ("backward_ns", ns(t.backward)),
        ("extraction_ns", ns(t.extraction)),
        ("interreduction_ns", ns(t.interreduction)),
        ("other_ns", ns(s.total.saturating_sub(t.sum()))),
        ("batches", Json::size(s.batches)),
        ("max_matrix_rows", Json::size(s.max_matrix_rows)),
        ("max_matrix_columns", Json::size(s.max_matrix_columns)),
        ("bytes_per_entry", Json::size(s.bytes_per_entry)),
        ("row_operations", Json::size(s.row_operations)),
        ("max_live_nonzeros", Json::size(s.max_live_nonzeros)),
        (
            "backward_products",
            Json::size(s.candidate_reduction.coefficient_products),
        ),
    ])
}

fn run<const N: usize, F: FiniteField>(
    args: &Args,
    system: Vec<MultivariatePolynomial<N, F>>,
) -> Json {
    let options = options(args.workers);
    let solve = || f4_reported(&system, ORDER, &options);
    let started = Instant::now();
    #[cfg(feature = "research-work")]
    let ((result, statistics), work) = if args.work {
        let (r, w) = zeebra::linalg::work::measure(solve);
        let entry_bytes = w
            .batches
            .iter()
            .map(|b| b.sparse_entry_bytes)
            .max()
            .unwrap_or(0);
        let mut forward = w.outside_batch.forward;
        let mut backward = w.outside_batch.backward;
        for b in &w.batches {
            forward.accumulate(&b.forward);
            backward.accumulate(&b.backward);
        }
        (
            r,
            Json::object([
                ("sparse_entry_bytes", Json::size(entry_bytes)),
                ("forward", forward.json()),
                ("backward", backward.json()),
            ]),
        )
    } else {
        (solve(), Json::Null)
    };
    #[cfg(not(feature = "research-work"))]
    let ((result, statistics), work) = {
        assert!(!args.work, "--work requires --features research-work");
        (solve(), Json::Null)
    };
    let elapsed = started.elapsed();
    Json::object([
        ("mode", Json::string("f4")),
        ("system", Json::string(&args.system)),
        ("field", Json::string(&args.field)),
        ("field_type", Json::string(std::any::type_name::<F>())),
        ("cell_bytes", Json::size(std::mem::size_of::<F>())),
        ("workers", Json::size(args.workers)),
        (
            "status",
            Json::string(match &result {
                Ok(_) => "complete".to_string(),
                Err(e) => format!("stopped: {e}"),
            }),
        ),
        (
            "basis_elements",
            result.as_ref().map_or(Json::Null, |b| Json::size(b.len())),
        ),
        ("f4_call_ns", Json::nanos(elapsed)),
        (
            "peak_rss_bytes",
            peak_resident_bytes().map(Json::int).unwrap_or(Json::Null),
        ),
        ("statistics", stages(&statistics)),
        ("work", work),
    ])
}

/// The (system, field) pairs this census instantiates; each is one monomorphized F4.
fn dispatch(args: &Args) -> Result<Json, String> {
    let m31 = CaseField::prime(2147483647);
    let goldilocks = CaseField::prime(18446744069414584321);
    let gf256 = CaseField::binary(0x11D);
    Ok(match (args.system.as_str(), args.field.as_str()) {
        ("katsura-9", "goldilocks") => run(args, katsura::<10, Goldilocks>()),
        ("katsura-9", "bn254") => run(args, katsura::<10, Bn254Fr>()),
        ("katsura-10", "goldilocks") => run(args, katsura::<11, Goldilocks>()),
        ("katsura-10", "bn254") => run(args, katsura::<11, Bn254Fr>()),
        ("cyclic-7", "goldilocks") => run(args, cyclic::<7, Goldilocks>()),
        ("cyclic-7", "bn254") => run(args, cyclic::<7, Bn254Fr>()),
        ("cyclic-7", "gf256") => run(args, cyclic::<7, Gf256Mq>()),
        ("mq-9", "m31") => run(args, mq::<9, Zp2147483647>(m31)),
        ("mq-9", "goldilocks") => run(args, mq::<9, Goldilocks>(goldilocks)),
        ("mq-9", "gf256") => run(args, mq::<9, Gf256Mq>(gf256)),
        ("mq-10", "m31") => run(args, mq::<10, Zp2147483647>(m31)),
        ("mq-10", "gf256") => run(args, mq::<10, Gf256Mq>(gf256)),
        (system, field) => return Err(format!("no instantiation for {system} over {field}")),
    })
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("ceilings") => {
            let reps = match args.get(1..3) {
                Some([flag, n]) if flag == "--reps" => n.parse().expect("--reps takes an integer"),
                _ => 5,
            };
            ceilings(reps);
        }
        Some("f4") => {
            let parsed = parse_f4(&args[1..]).unwrap_or_else(|e| panic!("{e}"));
            let report = dispatch(&parsed).unwrap_or_else(|e| panic!("{e}"));
            println!("{}", report.to_json().replace('\n', ""));
        }
        _ => panic!(
            "usage: gpu_kernel_census ceilings | f4 --system S --field F [--workers W] [--work]"
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn strings(v: &[&str]) -> Vec<String> {
        v.iter().map(|s| s.to_string()).collect()
    }

    // The shipped step over a pivot row equals subtracting the scaled row from a dense copy.
    #[test]
    fn eliminate_matches_dense_subtraction() {
        let rows = pivot_rows::<Goldilocks>(ROW * 3, 5);
        let factors: Vec<Goldilocks> = vec![Goldilocks::new(3), Goldilocks::new(5)];
        let mut acc = vec![Goldilocks::new(1); WIDTH];
        let mut expected = acc.clone();
        for (row, factor) in rows.chunks(ROW).zip(factors.iter().cycle()) {
            for (c, v) in row {
                expected[*c] = expected[*c] - *v * *factor;
            }
        }
        assert_eq!(eliminate(&mut acc, &rows, &factors), ROW * 3);
        assert_eq!(acc, expected);
    }

    // Pivot rows are sorted within a row and stay inside the accumulator.
    #[test]
    fn pivot_rows_are_sorted_and_in_range() {
        let rows = pivot_rows::<Bn254Fr>(ROW * 4, 9);
        assert_eq!(rows.len(), ROW * 4);
        for row in rows.chunks(ROW) {
            assert!(row.windows(2).all(|w| w[0].0 <= w[1].0));
            assert!(row
                .iter()
                .all(|(c, v)| *c < WIDTH && !zeebra::Zero::is_zero(v)));
        }
    }

    // The generated MQ system has one generator per variable and only quadratic or lower terms.
    #[test]
    fn mq_is_square_and_quadratic() {
        let system = mq::<9, Gf256Mq>(CaseField::binary(0x11D));
        assert_eq!(system.len(), 9);
        assert!(system.iter().all(|p| p.degree() <= 2));
    }

    // Arguments parse, and a pair with no instantiation is refused rather than guessed.
    #[test]
    fn f4_arguments_parse_and_unknown_pairs_are_refused() {
        let args = parse_f4(&strings(&[
            "--system",
            "katsura-9",
            "--field",
            "bn254",
            "--workers",
            "16",
            "--work",
        ]))
        .unwrap();
        assert_eq!(
            args,
            Args {
                system: "katsura-9".into(),
                field: "bn254".into(),
                workers: 16,
                work: true
            }
        );
        assert!(parse_f4(&strings(&["--system", "katsura-9"])).is_err());
        let unknown = Args {
            system: "katsura-9".into(),
            field: "gf256".into(),
            workers: 1,
            work: false,
        };
        assert!(dispatch(&unknown).is_err());
    }
}
