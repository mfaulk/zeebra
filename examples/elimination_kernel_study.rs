#[path = "support/h13_delayed.rs"]
mod delayed;

use std::time::{Duration, Instant};
use zeebra::{
    fields::{Bn254Fr, Mersenne31, Zp18446744073709551557, Zp2147483647, Zp32003},
    grobner::{
        benchmark_systems::{cyclic, katsura},
        f4::{
            matrix_corpus::{capture_matrix, corpus, BatchSelector},
            structured::{self, BlockPlan},
        },
        F4Options,
    },
    linalg::{
        sparse::{back_substitute_pivots_within, SparseMatrix, SparseRow},
        Backend,
    },
    util::{peak_resident_bytes, Json, Sha256},
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

fn counter_command(
    output: &mut impl std::io::Write,
    input: &mut impl std::io::BufRead,
    command: &str,
) -> std::io::Result<()> {
    writeln!(output, "{command}")?;
    output.flush()?;
    let mut acknowledgement = String::new();
    input.read_line(&mut acknowledgement)?;
    if acknowledgement.trim() != "ack" {
        return Err(std::io::Error::other(
            "perf control acknowledgement missing",
        ));
    }
    Ok(())
}

struct Counters {
    command: std::fs::File,
    ack: std::io::BufReader<std::fs::File>,
}
impl Counters {
    fn open() -> Option<Self> {
        match (
            std::env::var_os("ZEEBRA_PERF_CTL"),
            std::env::var_os("ZEEBRA_PERF_ACK"),
        ) {
            (None, None) => None,
            (Some(ctl), Some(ack)) => Some(Self {
                command: std::fs::OpenOptions::new()
                    .write(true)
                    .open(ctl)
                    .expect("perf control FIFO"),
                ack: std::io::BufReader::new(
                    std::fs::File::open(ack).expect("perf acknowledgement FIFO"),
                ),
            }),
            _ => panic!("both perf FIFO paths are required"),
        }
    }
    fn send(&mut self, message: &str) {
        counter_command(&mut self.command, &mut self.ack, message).expect("perf region handshake");
    }
}

fn hash<F: FiniteField>(matrix: &SparseMatrix<F>) -> String {
    let mut h = Sha256::new();
    h.update(format!("{}:{};", matrix.num_rows(), matrix.num_columns()).as_bytes());
    for row in matrix.rows() {
        h.update(format!("r{}:", row.nonzeros()).as_bytes());
        for (column, value) in row.entries() {
            h.update(format!("{column}:{value};").as_bytes());
        }
    }
    h.hex()
}

// Nested deterministic tail masks retain every leading entry and the reducer-block invariant.
fn thin<F: FiniteField>(matrix: &SparseMatrix<F>, eighths: u64) -> SparseMatrix<F> {
    assert!((1..=8).contains(&eighths));
    let rows = matrix
        .rows()
        .iter()
        .enumerate()
        .map(|(i, row)| {
            let values: Vec<_> = row
                .entries()
                .iter()
                .enumerate()
                .filter(|(j, (column, _))| {
                    let mut x = (i as u64).wrapping_mul(0x9e3779b97f4a7c15) ^ (*column as u64);
                    x ^= x >> 30;
                    x = x.wrapping_mul(0xbf58476d1ce4e5b9);
                    x ^= x >> 27;
                    x = x.wrapping_mul(0x94d049bb133111eb);
                    x ^= x >> 31;
                    *j == 0 || x % 8 < eighths
                })
                .map(|(_, entry)| *entry)
                .collect();
            SparseRow::new(&values)
        })
        .collect();
    SparseMatrix::new(matrix.num_columns(), rows)
}

fn run<const N: usize, F: FiniteField>(
    field: &str,
    shape: &str,
    generators: &[MultivariatePolynomial<N, F>],
    eighths: u64,
    backend: Backend,
) {
    let (order, preset, batch) = match shape {
        "mq10" => (
            MonomialOrder::GradedReverseLexicographic,
            F4Options::default(),
            7,
        ),
        "k7" => (
            MonomialOrder::GradedReverseLexicographic,
            F4Options::default(),
            4,
        ),
        "c6" => (
            MonomialOrder::GradedReverseLexicographic,
            F4Options::default(),
            7,
        ),
        "k6lex" => (MonomialOrder::Lexicographic, F4Options::baseline(), 21),
        _ => panic!("shape must be k7, c6 or k6lex"),
    };
    let options = F4Options {
        max_wall_time: Some(Duration::from_secs(60)),
        ..preset
    };
    let mut captured = capture_matrix(
        "h13",
        generators,
        order,
        &options,
        BatchSelector::Prefix(batch),
    )
    .unwrap();
    if field == "m31" || field == "p64" {
        let prefix = match shape {
            "k7" => "katsura-7/grevlex",
            "c6" => "cyclic-6/grevlex",
            _ => "katsura-6/lex",
        };
        let label = format!(
            "{prefix}/{field}/{}",
            if shape == "k6lex" {
                "baseline"
            } else {
                "default"
            }
        );
        let spec = corpus().into_iter().find(|s| s.label == label).unwrap();
        assert_eq!(captured.fingerprint, spec.fingerprint);
    }
    if field == "p31" {
        let spec = corpus()
            .into_iter()
            .find(|s| s.label == "mq-random-10/grevlex/p31x64/default")
            .unwrap();
        assert_eq!(captured.fingerprint, spec.fingerprint);
    }
    let fingerprint = format!("{:?}", captured.fingerprint);
    *captured.matrix.matrix_mut() = thin(captured.matrix.matrix(), eighths);
    let input_hash = hash(captured.matrix.matrix());
    let initial = captured.matrix.nonzeros();
    let width = captured.matrix.num_columns();
    let height = captured.matrix.num_rows();
    let allowance = options.live_entry_allowance::<F>();
    let mut counters = Counters::open();
    if let Some(counters) = &mut counters {
        counters.send("enable");
    }
    let start = Instant::now();
    let mut outcome = structured::eliminate(
        BlockPlan::ReducersFirstBlock,
        backend,
        &mut captured.matrix,
        allowance,
    )
    .unwrap();
    let forward = start.elapsed();
    let start = Instant::now();
    back_substitute_pivots_within(
        captured.matrix.matrix_mut(),
        allowance,
        &mut outcome.statistics,
    )
    .unwrap();
    let backward = start.elapsed();
    if let Some(counters) = &mut counters {
        counters.send("disable");
    }
    println!(
        "{}",
        Json::object([
            (
                "counter_scope",
                Json::string(if counters.is_some() {
                    "elimination-region"
                } else {
                    "none"
                })
            ),
            ("field", Json::string(field)),
            ("shape", Json::string(shape)),
            ("eighths", Json::int(eighths)),
            ("backend", Json::string(format!("{backend:?}"))),
            ("source", Json::string(fingerprint)),
            ("input_hash", Json::string(input_hash)),
            ("rref_hash", Json::string(hash(captured.matrix.matrix()))),
            ("rows", Json::size(height)),
            ("columns", Json::size(width)),
            ("initial_nonzeros", Json::size(initial)),
            ("rank", Json::size(captured.matrix.matrix().nonzero_rows())),
            ("zero_rows", Json::size(outcome.statistics.zero_rows)),
            (
                "peak_nonzeros",
                Json::size(outcome.statistics.peak_nonzeros)
            ),
            ("final_nonzeros", Json::size(captured.matrix.nonzeros())),
            (
                "row_operations",
                Json::size(outcome.statistics.row_operations)
            ),
            ("forward_ns", Json::nanos(forward)),
            ("backward_ns", Json::nanos(backward)),
            ("elimination_ns", Json::nanos(forward + backward)),
            ("entry_allowance", Json::size(allowance)),
            (
                "dense_buffer_bytes",
                Json::size(match backend {
                    Backend::Dense => width * height * std::mem::size_of::<F>(),
                    Backend::Adaptive => width * std::mem::size_of::<F>(),
                    _ => 0,
                })
            ),
            (
                "peak_rss_bytes",
                peak_resident_bytes().map(Json::int).unwrap_or(Json::Null)
            ),
        ])
        .to_json()
    );
}

fn arithmetic() {
    use std::hint::black_box;
    use zeebra::linalg::DenseAccumulator;
    const WIDTH: usize = 4096;
    const PASSES: usize = 1024;
    let columns: Vec<_> = (0..WIDTH).collect();
    let values: Vec<_> = (0..WIDTH).map(|i| (1 + i % 32002) as u16).collect();
    let source = SparseRow::<Zp32003>::new(
        &columns
            .iter()
            .zip(&values)
            .map(|(&c, &v)| (c, Zp32003::new(v as u64)))
            .collect::<Vec<_>>(),
    );
    let factor = Zp32003::new(1234);
    let mut canonical = DenseAccumulator::new(WIDTH);
    canonical.load(&source);
    let start = Instant::now();
    for _ in 0..PASSES {
        canonical.subtract_scaled(black_box(&source), black_box(factor));
    }
    let generic_time = start.elapsed();
    let expected = canonical.take();
    let mut row = delayed::Delayed::<32003>::new(WIDTH);
    row.load(columns.iter().zip(&values).map(|(&c, &v)| (c, v as u64)));
    let start = Instant::now();
    for _ in 0..PASSES {
        row.subtract(black_box(&columns), black_box(&values), black_box(1234));
    }
    let delayed_time = start.elapsed();
    black_box(row.nonzeros());
    black_box(row.leading());
    let actual = SparseRow::<Zp32003>::new(
        &row.take()
            .into_iter()
            .map(|(c, v)| (c, Zp32003::new(v)))
            .collect::<Vec<_>>(),
    );
    assert_eq!(actual, expected);
    let mut canonical_pilot = delayed::Delayed::<32003, false>::new(WIDTH);
    canonical_pilot.load(columns.iter().zip(&values).map(|(&c, &v)| (c, v as u64)));
    let start = Instant::now();
    for _ in 0..PASSES {
        canonical_pilot.subtract(black_box(&columns), black_box(&values), black_box(1234));
    }
    let canonical_pilot_time = start.elapsed();
    let actual = SparseRow::<Zp32003>::new(
        &canonical_pilot
            .take()
            .into_iter()
            .map(|(c, v)| (c, Zp32003::new(v)))
            .collect::<Vec<_>>(),
    );
    assert_eq!(actual, expected);
    println!(
        "{}",
        Json::object([
            ("mode", Json::string("arithmetic")),
            ("entries", Json::size(WIDTH * PASSES)),
            ("generic_ns", Json::nanos(generic_time)),
            ("delayed_ns", Json::nanos(delayed_time)),
            ("canonical_pilot_ns", Json::nanos(canonical_pilot_time)),
            (
                "p15_headroom",
                Json::int(delayed::Delayed::<32003>::headroom())
            ),
            (
                "p31_headroom",
                Json::int(delayed::Delayed::<2147483647>::headroom())
            ),
            (
                "peak_rss_bytes",
                peak_resident_bytes().map(Json::int).unwrap_or(Json::Null)
            ),
        ])
        .to_json()
    );
}

fn main() {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if args == ["--arithmetic"] {
        arithmetic();
        return;
    }
    assert_eq!(args.len(), 4, "FIELD SHAPE EIGHTHS BACKEND");
    let field = args[0].as_str();
    let shape = args[1].as_str();
    let eighths = args[2].parse().unwrap();
    let backend = match args[3].as_str() {
        "sparse" => Backend::Sparse,
        "dense" => Backend::Dense,
        "adaptive" => Backend::Adaptive,
        _ => panic!("backend"),
    };
    if field == "p31" {
        assert_eq!(shape, "mq10");
        use zeebra::grobner::differential::{CaseField, GeneratedSystem, SystemShape};
        let generated = GeneratedSystem::generate(
            10,
            SystemShape {
                variables: 10,
                max_degree: 2,
                max_terms: 40,
            },
            CaseField::prime(2147483647),
        );
        let system: Vec<MultivariatePolynomial<10, Zp2147483647>> = generated
            .polynomials
            .iter()
            .map(|terms| {
                MultivariatePolynomial::new(
                    &terms
                        .iter()
                        .map(|term| {
                            let mut exponents = [0; 10];
                            exponents.copy_from_slice(&term.exponents);
                            (
                                zeebra::Monomial::new(&exponents),
                                Zp2147483647::new(term.coefficient),
                            )
                        })
                        .collect::<Vec<_>>(),
                )
            })
            .collect();
        run(field, shape, &system, eighths, backend);
        return;
    }
    macro_rules! dispatch {
        ($f:ty) => {
            match shape {
                "k7" => run(field, shape, &katsura::<7, $f>(), eighths, backend),
                "c6" => run(field, shape, &cyclic::<6, $f>(), eighths, backend),
                "k6lex" => run(field, shape, &katsura::<6, $f>(), eighths, backend),
                _ => panic!("shape"),
            }
        };
    }
    match field {
        "m31" => dispatch!(Mersenne31),
        "p64" => dispatch!(Zp18446744073709551557),
        "bn254" => dispatch!(Bn254Fr),
        "p15" => dispatch!(Zp32003),
        _ => panic!("field"),
    }
}

#[cfg(test)]
mod tests {
    use super::delayed::Delayed;
    use super::*;
    // Delayed subtraction reports exact modular support, clears cancellation residue and permits scratch reuse.
    #[test]
    fn cancellation_and_reuse() {
        let mut row = Delayed::<32003>::new(66);
        row.load([(0, 1), (64, 2)]);
        row.subtract(&[0, 65], &[1, 7], 1);
        assert_eq!(row.nonzeros(), 2);
        assert_eq!(row.leading(), Some((64, 2)));
        assert_eq!(row.take(), vec![(64, 2), (65, 31996)]);
        row.load([(0, 3)]);
        assert_eq!(row.take(), vec![(0, 3)]);
    }
    // A completely cancelled row must leave every delayed cell zero before a later load.
    #[test]
    fn zero_row_reuse_clears_multiples() {
        let mut row = Delayed::<32003>::new(2);
        row.load([(0, 1)]);
        row.subtract(&[0], &[1], 1);
        assert_eq!(row.leading(), None);
        assert!(row.take().is_empty());
        row.load([(0, 5), (1, 1)]);
        assert_eq!(row.take(), vec![(0, 5), (1, 1)]);
    }
    // The exact accumulation bound fits at the boundary and rejects one additional worst-case product.
    #[test]
    fn headroom_is_exact() {
        for (p, n) in [
            (32003u128, Delayed::<32003>::headroom()),
            (2147483647, Delayed::<2147483647>::headroom()),
        ] {
            let bound = (p - 1) + n as u128 * (p - 1).pow(2);
            assert!(bound <= u64::MAX as u128);
            assert!(bound + (p - 1).pow(2) > u64::MAX as u128);
        }
    }
    // Thinning retains ordered supports, every leading entry and nested masks, with the identity at eight eighths.
    #[test]
    fn nested_masks_preserve_leads() {
        let input = SparseMatrix::new(
            65,
            vec![SparseRow::<Zp32003>::new(
                &(0..65)
                    .map(|i| (i, Zp32003::new(i as u64 + 1)))
                    .collect::<Vec<_>>(),
            )],
        );
        let mut previous = thin(&input, 1);
        for level in [2, 4, 8] {
            let next = thin(&input, level);
            for entry in previous.row(0).entries() {
                assert!(next.row(0).entries().contains(entry));
            }
            assert_eq!(next.row(0).leading_column(), Some(0));
            previous = next;
        }
        assert_eq!(previous, input);
    }
    // Adaptive and sparse elimination agree exactly and refuse fill-in at the same operation, including generic fallbacks.
    #[test]
    #[allow(deprecated)]
    fn exact_results_and_mid_operation_limits() {
        fn check<F: FiniteField>() {
            let input = SparseMatrix::new(
                4,
                vec![
                    SparseRow::<F>::new(&[(0, F::new(1)), (1, F::new(1)), (2, F::new(1))]),
                    SparseRow::<F>::new(&[(0, F::new(1)), (3, F::new(1))]),
                ],
            );
            for cap in [4, 5, 6, 100] {
                let mut a = input.clone();
                let mut b = input.clone();
                let sa = zeebra::linalg::row_echelon_with(Backend::Sparse, &mut a, cap);
                let sb = zeebra::linalg::row_echelon_with(Backend::Adaptive, &mut b, cap);
                assert_eq!(sa, sb);
                if sa.is_ok() {
                    assert_eq!(a, b);
                }
            }
        }
        check::<Zp32003>();
        check::<Mersenne31>();
        check::<Zp18446744073709551557>();
        check::<Bn254Fr>();
        check::<zeebra::fields::Zp221360928884514619393>();
        check::<zeebra::fields::Gf256>();
        check::<zeebra::fields::Gf13Pow4>();
    }
    // Region counters require an acknowledged command and reject a closed or invalid acknowledgement stream.
    #[test]
    fn counter_control_requires_acknowledgement() {
        use std::io::Cursor;
        let mut output = Vec::new();
        counter_command(&mut output, &mut Cursor::new(b"ack\n"), "enable").unwrap();
        assert_eq!(output, b"enable\n");
        assert!(counter_command(&mut output, &mut Cursor::new(b""), "disable").is_err());
        assert!(counter_command(&mut output, &mut Cursor::new(b"wrong\n"), "disable").is_err());
    }
}
