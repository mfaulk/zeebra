//! Zeebra's side of the linear-algebra comparison against FFLAS-FFPACK, SpaSM, M4RI and FLINT
//! (#1209), and the exporter that hands those tools the matrices.
//!
//! ```text
//! linalg_comparands export <corpus-label> <out>      <out>.sms and <out>.meta (prime, split)
//! linalg_comparands synthetic <dense|sparse> <rows> <cols> <per-row> <prime> <seed> <out>
//! linalg_comparands rref <in> <arm> <workers> <reps>  arm: f4 | lane | gf2 | blocked | matrix
//! linalg_comparands mul <n> <prime> <seed> <arm> <reps>   arm: matrix | blocked
//! linalg_comparands canon <file.sms> <prime> [rows]   RREF digest of any matrix, untimed;
//!                                                     `rows` stands in for its row count
//! ```
//!
//! `rref` and `mul` print the protocol of `tools/external/linalg-drivers/common.h`, so one parser
//! reads Zeebra and every comparand, and a digest equality is an entry-for-entry equality of the
//! reduced row echelon form or the product. Only the elimination or the product is timed.
//!
//! A corpus export writes the rows reducers first and records the split, so the `f4` arm runs the
//! shipped forward kernel exactly as F4 hands it the batch: the reducer block taken as pivots,
//! then the back-substitution `RowForm::Reduced` runs. Comparands see the same file and know
//! nothing of the split.
use std::{
    fs::File,
    io::{BufRead, BufReader, BufWriter, Write},
    path::Path,
    sync::atomic::AtomicBool,
    time::Instant,
};

use zeebra::{
    fields::{KnownOrder, PrimeFieldElement32, PrimeFieldElement64},
    grobner::f4::{
        macaulay::io::write_sms,
        matrix_corpus::{capture_matrix, visit_corpus_entry, MatrixEntryVisitor, MatrixSpec},
    },
    linalg::{
        blocked::{self, BlockedCounts, BlockedOptions, DenseMatrix, Modulus},
        concurrent, gauss_jordan_elimination,
        gf2::{reduced_row_echelon_four_russians, BitMatrix},
        lane::LaneKernel,
        reduce_rows_against_pivots_with,
        sparse::{back_substitute_pivots_within, reduced_row_echelon, SparseMatrix, SparseRow},
        Backend, Matrix,
    },
    FiniteField, MultivariatePolynomial,
};

/// What a `.meta` sidecar records: SMS itself carries neither the prime nor the reducer split.
#[derive(Debug, PartialEq)]
struct Meta {
    prime: u64,
    split: usize,
    label: String,
}

fn write_meta(path: &Path, meta: &Meta) -> std::io::Result<()> {
    std::fs::write(
        path,
        format!(
            "prime={}\nsplit={}\nlabel={}\n",
            meta.prime, meta.split, meta.label
        ),
    )
}

fn read_meta(path: &Path) -> Result<Meta, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let field = |key: &str| {
        text.lines()
            .find_map(|l| l.strip_prefix(key)?.strip_prefix('='))
            .ok_or(format!("{}: no {key}", path.display()))
    };
    Ok(Meta {
        prime: field("prime")?.parse().map_err(|e| format!("prime: {e}"))?,
        split: field("split")?.parse().map_err(|e| format!("split: {e}"))?,
        label: field("label")?.to_string(),
    })
}

/// Reads SMS into rows sorted by column, summing repeated entries as SpaSM and FLINT do.
fn read_sms<F: FiniteField>(path: &Path) -> Result<SparseMatrix<F>, String> {
    let file = File::open(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let mut lines = BufReader::with_capacity(1 << 20, file).lines();
    let header = lines
        .next()
        .ok_or("empty SMS")?
        .map_err(|e| e.to_string())?;
    let dims: Vec<usize> = header
        .split_whitespace()
        .take(2)
        .map(|t| t.parse().map_err(|e| format!("SMS header: {e}")))
        .collect::<Result<_, _>>()?;
    let (rows, cols) = (dims[0], dims[1]);
    let mut entries: Vec<Vec<(usize, F)>> = vec![Vec::new(); rows];
    for line in lines {
        let line = line.map_err(|e| e.to_string())?;
        let mut parts = line.split_whitespace();
        let mut next = || parts.next().ok_or("short SMS line");
        let (i, j, v) = (next()?, next()?, next()?);
        let (i, j): (usize, usize) = (
            i.parse().map_err(|e| format!("{e}"))?,
            j.parse().map_err(|e| format!("{e}"))?,
        );
        if i == 0 && j == 0 {
            break;
        }
        if i > rows || j > cols || i == 0 || j == 0 {
            return Err(format!("SMS index {i} {j} outside {rows}x{cols}"));
        }
        let value = match v.strip_prefix('-') {
            Some(magnitude) => -F::new(magnitude.parse().map_err(|e| format!("{e}"))?),
            None => F::new(v.parse().map_err(|e| format!("{e}"))?),
        };
        entries[i - 1].push((j - 1, value));
    }
    let rows = entries
        .into_iter()
        .map(|mut row| {
            row.sort_by_key(|(c, _)| *c);
            let mut merged: Vec<(usize, F)> = Vec::with_capacity(row.len());
            for (c, v) in row {
                match merged.last_mut() {
                    Some((last, sum)) if *last == c => *sum += v,
                    _ => merged.push((c, v)),
                }
            }
            merged.retain(|(_, v)| !v.is_zero());
            SparseRow::from_sorted(merged).expect("sorted and nonzero")
        })
        .collect();
    Ok(SparseMatrix::new(cols, rows))
}

const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;

fn fnv_word(state: &mut u64, word: u64) {
    for byte in word.to_le_bytes() {
        *state ^= u64::from(byte);
        *state = state.wrapping_mul(0x0100_0000_01b3);
    }
}

fn residue<F: FiniteField>(x: &F) -> u64 {
    x.word_residue().expect("a word-size prime field")
}

/// The protocol digest of a matrix already in reduced row echelon form, rows in any order, as the
/// RREF of an input of `input_rows` rows (a route may have dropped the zero rows).
fn rref_digest<F: FiniteField>(input_rows: usize, matrix: &SparseMatrix<F>) -> (usize, u64) {
    let mut rows: Vec<&SparseRow<F>> = matrix.rows().iter().filter(|r| !r.is_zero()).collect();
    rows.sort_by_key(|r| r.leading_column());
    let mut state = FNV_OFFSET;
    fnv_word(&mut state, input_rows as u64);
    fnv_word(&mut state, matrix.num_columns() as u64);
    fnv_word(&mut state, rows.len() as u64);
    for row in &rows {
        fnv_word(&mut state, row.nonzeros() as u64);
        for (c, v) in row.entries() {
            fnv_word(&mut state, *c as u64);
            fnv_word(&mut state, residue(v));
        }
    }
    (rows.len(), state)
}

fn product_digest(entries: impl IntoIterator<Item = u64>) -> u64 {
    let mut state = FNV_OFFSET;
    for e in entries {
        fnv_word(&mut state, e);
    }
    state
}

fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

/// The operands of `mul`, exactly as the C drivers draw them.
fn random_square(state: &mut u64, prime: u64, n: usize) -> Vec<u64> {
    (0..n * n).map(|_| splitmix64(state) % prime).collect()
}

/// A synthetic matrix: every entry drawn (`dense`), or `per_row` distinct columns per row with
/// nonzero values (`sparse`). Deterministic in the seed.
fn synthetic<F: FiniteField>(
    dense: bool,
    rows: usize,
    cols: usize,
    per_row: usize,
    prime: u64,
    seed: u64,
) -> SparseMatrix<F> {
    let mut state = seed;
    let rows = (0..rows)
        .map(|_| {
            let mut entries: Vec<(usize, F)> = if dense {
                (0..cols)
                    .map(|c| (c, F::new(splitmix64(&mut state) % prime)))
                    .collect()
            } else {
                let mut columns: Vec<usize> = Vec::with_capacity(per_row);
                while columns.len() < per_row.min(cols) {
                    let c = (splitmix64(&mut state) % cols as u64) as usize;
                    if !columns.contains(&c) {
                        columns.push(c);
                    }
                }
                columns.sort_unstable();
                columns
                    .into_iter()
                    .map(|c| (c, F::new(1 + splitmix64(&mut state) % (prime - 1))))
                    .collect()
            };
            entries.retain(|(_, v)| !v.is_zero());
            SparseRow::from_sorted(entries).expect("sorted and nonzero")
        })
        .collect();
    SparseMatrix::new(cols, rows)
}

/// A comparand-protocol result.
#[derive(Clone, Copy, Debug, PartialEq)]
struct Reduced {
    rank: usize,
    digest: u64,
    seconds: f64,
}

/// One Zeebra arm on a copy of `input`, timed over the elimination alone.
fn rref_arm<F: FiniteField + Send + Sync>(
    input: &SparseMatrix<F>,
    split: usize,
    arm: &str,
    workers: usize,
) -> Result<Reduced, String> {
    if workers > 1 && arm != "f4" {
        return Err(format!("the {arm} arm has no parallel route"));
    }
    let mut matrix = input.clone();
    let started = Instant::now();
    let reduced = match arm {
        "f4" => {
            let mut statistics = if workers == 1 {
                reduce_rows_against_pivots_with(Backend::Adaptive, &mut matrix, split, usize::MAX)
                    .expect("unbounded")
            } else {
                let config = concurrent::Config {
                    workers,
                    ..concurrent::Config::default()
                };
                F::concurrent_elimination()
                    .ok_or("no concurrent handle")?
                    .reduce(&mut matrix, split, &config, &AtomicBool::new(false))
                    .map_err(|e| format!("{e:?}"))?
                    .statistics
            };
            back_substitute_pivots_within(&mut matrix, usize::MAX, &mut statistics)
                .expect("unbounded");
            matrix
        }
        "lane" => {
            let lane = F::small_prime_lane()
                .or_else(F::prime31_lane)
                .ok_or("no lane for this prime")?;
            let mut statistics = LaneKernel::default()
                .reduce_rows_against_pivots(&lane, &mut matrix, split, usize::MAX)
                .expect("unbounded");
            back_substitute_pivots_within(&mut matrix, usize::MAX, &mut statistics)
                .expect("unbounded");
            matrix
        }
        "blocked" => {
            let lane = F::small_prime_lane().ok_or("no small-prime lane for this prime")?;
            if Modulus::new(lane.modulus()).is_none() {
                return Err("the blocked arm needs a prime below 2^26".into());
            }
            let columns: Vec<usize> = (0..matrix.num_columns()).collect();
            let mut counts = BlockedCounts::default();
            blocked::reduced_echelon_of_sparse(
                &lane,
                &matrix,
                &columns,
                BlockedOptions::default(),
                &mut counts,
            )
        }
        "gf2" => {
            if !(F::ONE + F::ONE).is_zero() {
                return Err("the gf2 arm needs p = 2".into());
            }
            let rows = matrix.rows().to_vec();
            let mut bits = BitMatrix::pack_binary(&rows, matrix.num_columns()).ok_or("not 0/1")?;
            let started = Instant::now();
            let statistics = reduced_row_echelon_four_russians(&mut bits, 8);
            let seconds = started.elapsed().as_secs_f64();
            let rows = (0..bits.num_rows())
                .map(|r| bits.row_to_sparse(r))
                .collect();
            let (rank, digest) = rref_digest(
                input.num_rows(),
                &SparseMatrix::<F>::new(bits.num_columns(), rows),
            );
            assert_eq!(rank, statistics.rank);
            return Ok(Reduced {
                rank,
                digest,
                seconds,
            });
        }
        "matrix" => {
            let mut cells = vec![F::ZERO; matrix.num_rows() * matrix.num_columns()];
            for (r, row) in matrix.rows().iter().enumerate() {
                for (c, v) in row.entries() {
                    cells[r * matrix.num_columns() + c] = *v;
                }
            }
            let dense = Matrix::new(matrix.num_rows(), matrix.num_columns(), &cells);
            let started = Instant::now();
            let reduced = gauss_jordan_elimination(&dense);
            let seconds = started.elapsed().as_secs_f64();
            let rows = reduced
                .rows()
                .map(|row| SparseRow::from_dense(&row.cloned().collect::<Vec<_>>()))
                .collect();
            let (rank, digest) = rref_digest(
                input.num_rows(),
                &SparseMatrix::<F>::new(matrix.num_columns(), rows),
            );
            return Ok(Reduced {
                rank,
                digest,
                seconds,
            });
        }
        other => return Err(format!("unknown arm {other}")),
    };
    let seconds = started.elapsed().as_secs_f64();
    let (rank, digest) = rref_digest(input.num_rows(), &reduced);
    Ok(Reduced {
        rank,
        digest,
        seconds,
    })
}

/// One product arm; returns the digest and the seconds of the product alone.
fn mul_arm<F: FiniteField>(
    n: usize,
    prime: u64,
    seed: u64,
    arm: &str,
) -> Result<(u64, f64), String> {
    let mut state = seed;
    let a = random_square(&mut state, prime, n);
    let b = random_square(&mut state, prime, n);
    match arm {
        "matrix" => {
            let to =
                |v: &[u64]| Matrix::new(n, n, &v.iter().map(|&x| F::new(x)).collect::<Vec<_>>());
            let (x, y) = (to(&a), to(&b));
            let started = Instant::now();
            let z = &x * &y;
            let seconds = started.elapsed().as_secs_f64();
            Ok((
                product_digest(z.rows().flat_map(|r| r.map(residue).collect::<Vec<_>>())),
                seconds,
            ))
        }
        "blocked" => {
            let modulus = u32::try_from(prime)
                .ok()
                .and_then(Modulus::new)
                .ok_or("the blocked arm needs a prime below 2^26")?;
            let to = |v: &[u64]| {
                DenseMatrix::from_residues(
                    modulus,
                    n,
                    n,
                    &v.iter().map(|&x| x as u32).collect::<Vec<_>>(),
                )
            };
            let (x, y) = (to(&a), to(&b));
            let mut counts = BlockedCounts::default();
            let started = Instant::now();
            let z = blocked::multiply(modulus, &x, &y, BlockedOptions::default(), &mut counts);
            let seconds = started.elapsed().as_secs_f64();
            Ok((
                product_digest(z.residues().into_iter().map(u64::from)),
                seconds,
            ))
        }
        other => Err(format!("unknown arm {other}")),
    }
}

/// Runs `$body` with `F` bound to Zeebra's word-size type for `$prime`.
macro_rules! with_field {
    ($prime:expr, $F:ident => $body:expr) => {
        match $prime {
            2 => {
                type $F = PrimeFieldElement32<2>;
                $body
            }
            31 => {
                type $F = PrimeFieldElement32<31>;
                $body
            }
            32003 => {
                type $F = PrimeFieldElement32<32003>;
                $body
            }
            65521 => {
                type $F = PrimeFieldElement32<65521>;
                $body
            }
            2013265921 => {
                type $F = PrimeFieldElement32<2013265921>;
                $body
            }
            2147483647 => {
                type $F = PrimeFieldElement32<2147483647>;
                $body
            }
            18446744073709551557 => {
                type $F = PrimeFieldElement64<18446744073709551557>;
                $body
            }
            other => Err(format!(
                "prime {other} is not one of 2, 31, 32003, 65521, 2013265921, 2147483647, 18446744073709551557"
            )),
        }
    };
}

fn write_matrix<F: KnownOrder>(
    out: &str,
    matrix: &SparseMatrix<F>,
    meta: &Meta,
) -> Result<(), String> {
    let sms = format!("{out}.sms");
    let mut writer = BufWriter::new(File::create(&sms).map_err(|e| format!("{sms}: {e}"))?);
    write_sms(&mut writer, matrix).map_err(|e| e.to_string())?;
    writer.flush().map_err(|e| e.to_string())?;
    write_meta(Path::new(&format!("{out}.meta")), meta).map_err(|e| e.to_string())
}

struct Export<'a> {
    out: &'a str,
    result: Option<Result<(), String>>,
}

impl MatrixEntryVisitor for Export<'_> {
    fn visit<const N: usize, F: KnownOrder>(
        &mut self,
        spec: &MatrixSpec,
        generators: fn() -> Vec<MultivariatePolynomial<N, F>>,
    ) {
        self.result = Some((|| {
            let prime = match (F::order_limbs(), F::characteristic_limbs()) {
                ([q], [p]) if q == p => *p,
                _ => {
                    return Err(format!(
                        "{} is not over a word-size prime field",
                        spec.label
                    ))
                }
            };
            let options = spec.options.options();
            let mut captured = capture_matrix(
                spec.label,
                &generators(),
                spec.order,
                &options,
                spec.selector,
            )
            .map_err(|e| e.to_string())?;
            let split = captured.matrix.partition_reducers_first();
            let meta = Meta {
                prime,
                split,
                label: spec.label.to_string(),
            };
            write_matrix(self.out, captured.matrix.matrix(), &meta)?;
            println!(
                "exported {} rows={} cols={} split={split} prime={prime}",
                spec.label,
                captured.matrix.matrix().num_rows(),
                captured.matrix.matrix().num_columns()
            );
            Ok(())
        })());
    }
}

fn parse<T: std::str::FromStr>(s: &str, what: &str) -> Result<T, String> {
    s.parse().map_err(|_| format!("bad {what}: {s}"))
}

fn run(args: &[String]) -> Result<(), String> {
    match args.first().map(String::as_str) {
        Some("export") if args.len() == 3 => {
            let mut export = Export {
                out: &args[2],
                result: None,
            };
            if !visit_corpus_entry(&args[1], &mut export) {
                return Err(format!("unknown corpus label {}", args[1]));
            }
            export.result.expect("dispatched")
        }
        Some("synthetic") if args.len() == 8 => {
            let dense = match args[1].as_str() {
                "dense" => true,
                "sparse" => false,
                other => return Err(format!("unknown kind {other}")),
            };
            let (rows, cols, per_row): (usize, usize, usize) = (
                parse(&args[2], "rows")?,
                parse(&args[3], "cols")?,
                parse(&args[4], "per-row")?,
            );
            let (prime, seed): (u64, u64) = (parse(&args[5], "prime")?, parse(&args[6], "seed")?);
            with_field!(prime, F => {
                let matrix = synthetic::<F>(dense, rows, cols, per_row, prime, seed);
                let label = format!("synthetic-{}/{rows}x{cols}/{per_row}/p{prime}/s{seed}", args[1]);
                write_matrix(&args[7], &matrix, &Meta { prime, split: 0, label })
            })
        }
        Some("rref") if args.len() == 5 => {
            let meta = read_meta(Path::new(&format!("{}.meta", args[1])))?;
            let (workers, reps): (usize, usize) =
                (parse(&args[3], "workers")?, parse(&args[4], "reps")?);
            with_field!(meta.prime, F => {
                let input = read_sms::<F>(Path::new(&format!("{}.sms", args[1])))?;
                for _ in 0..reps {
                    let r = rref_arm(&input, meta.split, &args[2], workers)?;
                    println!(
                        "rref rows={} cols={} rank={} digest={:016x} seconds={:.6}",
                        input.num_rows(), input.num_columns(), r.rank, r.digest, r.seconds
                    );
                }
                Ok(())
            })
        }
        Some("mul") if args.len() == 6 => {
            let (n, prime, seed): (usize, u64, u64) = (
                parse(&args[1], "n")?,
                parse(&args[2], "prime")?,
                parse(&args[3], "seed")?,
            );
            let reps: usize = parse(&args[5], "reps")?;
            with_field!(prime, F => {
                for _ in 0..reps {
                    let (digest, seconds) = mul_arm::<F>(n, prime, seed, &args[4])?;
                    println!("mul n={n} digest={digest:016x} seconds={seconds:.6}");
                }
                Ok(())
            })
        }
        Some("canon") if args.len() == 3 || args.len() == 4 => {
            let prime: u64 = parse(&args[2], "prime")?;
            with_field!(prime, F => {
                let mut matrix = read_sms::<F>(Path::new(&args[1]))?;
                let rows = match args.get(3) {
                    Some(rows) => parse(rows, "rows")?,
                    None => matrix.num_rows(),
                };
                reduced_row_echelon(&mut matrix);
                let (rank, digest) = rref_digest(rows, &matrix);
                println!("canon rank={rank} digest={digest:016x}");
                Ok(())
            })
        }
        _ => Err(
            "usage: linalg_comparands export|synthetic|rref|mul|canon … (see the file header)"
                .into(),
        ),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if let Err(error) = run(&args) {
        eprintln!("linalg_comparands: {error}");
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zeebra::fields::{Mersenne31, Zp2, Zp32003};

    fn scratch(tag: &str) -> std::path::PathBuf {
        let dir = std::env::temp_dir().join(format!("zeebra-linalg-{tag}-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        dir
    }

    fn sms(text: &str, tag: &str) -> std::path::PathBuf {
        let path = scratch(tag).join("m.sms");
        std::fs::write(&path, text).unwrap();
        path
    }

    // The digests the C drivers print on the same two matrices (FLINT, FFLAS-FFPACK and SpaSM on
    // the first, all four on the second), so the Rust and C encodings cannot drift apart.
    #[test]
    fn digests_match_the_c_drivers() {
        let a = sms(
            "3 4 M\n1 2 5\n1 4 7\n2 1 3\n2 2 1\n3 1 6\n3 2 7\n3 4 14\n0 0 0\n",
            "a",
        );
        let mut m = read_sms::<Zp32003>(&a).unwrap();
        reduced_row_echelon(&mut m);
        assert_eq!(rref_digest(3, &m), (3, 0x97e04412b3fff343));

        let b = sms(
            "3 3 M\n1 1 1\n1 2 1\n2 2 1\n2 3 1\n3 1 1\n3 3 1\n0 0 0\n",
            "b",
        );
        let mut m = read_sms::<Zp2>(&b).unwrap();
        reduced_row_echelon(&mut m);
        assert_eq!(rref_digest(3, &m), (2, 0xb201df38ce8d8826));
    }

    // Negative and repeated SMS entries are reduced and summed, as the C readers do.
    #[test]
    fn sms_reader_sums_and_reduces() {
        let path = sms("2 2 M\n1 1 -1\n1 1 3\n2 2 32003\n0 0 0\n", "sum");
        let m = read_sms::<Zp32003>(&path).unwrap();
        assert_eq!(m.rows()[0].entries(), &[(0, Zp32003::new(2))]);
        assert!(m.rows()[1].is_zero());
    }

    // A written matrix and sidecar read back identically.
    #[test]
    fn export_round_trips() {
        let dir = scratch("trip");
        let out = dir.join("x").to_string_lossy().into_owned();
        let matrix = synthetic::<Mersenne31>(false, 20, 30, 4, 2147483647, 7);
        let meta = Meta {
            prime: 2147483647,
            split: 0,
            label: "t".into(),
        };
        write_matrix(&out, &matrix, &meta).unwrap();
        assert_eq!(
            read_sms::<Mersenne31>(Path::new(&format!("{out}.sms"))).unwrap(),
            matrix
        );
        assert_eq!(read_meta(Path::new(&format!("{out}.meta"))).unwrap(), meta);
    }

    fn agree<F: FiniteField + Send + Sync>(matrix: &SparseMatrix<F>, split: usize, arms: &[&str]) {
        let mut reference = matrix.clone();
        reduced_row_echelon(&mut reference);
        let expected = rref_digest(matrix.num_rows(), &reference);
        for arm in arms {
            let r = rref_arm(matrix, split, arm, 1).unwrap();
            assert_eq!((r.rank, r.digest), expected, "arm {arm}");
        }
        let r = rref_arm(matrix, split, "f4", 3).unwrap();
        assert_eq!((r.rank, r.digest), expected, "f4 at three workers");
    }

    // Every arm reaches the same RREF on rank-deficient sparse and dense matrices.
    #[test]
    fn every_arm_agrees_on_synthetic_matrices() {
        let sparse = synthetic::<Zp32003>(false, 60, 50, 3, 32003, 1);
        agree(&sparse, 0, &["f4", "lane", "blocked", "matrix"]);
        let dense = synthetic::<Zp32003>(true, 30, 40, 0, 32003, 2);
        agree(&dense, 0, &["f4", "lane", "blocked", "matrix"]);
        let wide = synthetic::<Mersenne31>(false, 40, 40, 2, 2147483647, 3);
        agree(&wide, 0, &["f4", "lane", "matrix"]);
        let bits = synthetic::<Zp2>(false, 70, 90, 5, 2, 4);
        agree(&bits, 0, &["f4", "gf2", "matrix"]);
    }

    // On a captured corpus batch the arms agree with the split taken as F4 takes it.
    #[test]
    fn every_arm_agrees_on_a_corpus_batch() {
        let dir = scratch("corpus");
        let out = dir.join("c").to_string_lossy().into_owned();
        run(&[
            "export".into(),
            "cyclic-6/grevlex/m31/default".into(),
            out.clone(),
        ])
        .unwrap();
        let meta = read_meta(Path::new(&format!("{out}.meta"))).unwrap();
        assert_eq!(meta.prime, 2147483647);
        assert!(meta.split > 0);
        let matrix = read_sms::<Mersenne31>(Path::new(&format!("{out}.sms"))).unwrap();
        agree(&matrix, meta.split, &["f4", "lane", "matrix"]);
    }

    // The product arms agree with each other and with FLINT's digest of the same product.
    #[test]
    fn product_arms_agree() {
        let (matrix, _) = mul_arm::<Zp32003>(9, 32003, 5, "matrix").unwrap();
        let (blocked, _) = mul_arm::<Zp32003>(9, 32003, 5, "blocked").unwrap();
        assert_eq!(matrix, blocked);
        assert_eq!(matrix, 0x39a70f72a2693d2e);
    }

    fn driver(name: &str) -> std::path::PathBuf {
        let prefix = std::env::var("ZEEBRA_EXT_PREFIX").unwrap_or_else(|_| {
            format!("{}/.local/opt/zeebra-ext", std::env::var("HOME").unwrap())
        });
        Path::new(&prefix)
            .join("bin")
            .join(format!("linalg-{name}"))
    }

    fn driver_rref(name: &str, sms: &Path, prime: u64) -> (usize, u64) {
        let out = std::process::Command::new(driver(name))
            .args(["rref", sms.to_str().unwrap(), &prime.to_string(), "1", "1"])
            .output()
            .unwrap_or_else(|e| panic!("linalg-{name}: {e}"));
        assert!(out.status.success(), "linalg-{name} failed");
        let line = String::from_utf8(out.stdout).unwrap();
        let field = |key: &str| {
            line.split_whitespace()
                .find_map(|t| t.strip_prefix(key))
                .unwrap()
                .to_string()
        };
        (
            field("rank=").parse().unwrap(),
            u64::from_str_radix(&field("digest="), 16).unwrap(),
        )
    }

    // Live agreement with each provisioned driver on a corpus batch and a synthetic matrix.
    #[test]
    #[ignore = "needs tools/external/provision-linalg.sh"]
    fn every_comparand_agrees_with_zeebra() {
        let dir = scratch("live");
        let out = dir.join("s").to_string_lossy().into_owned();
        let matrix = synthetic::<Zp32003>(false, 120, 100, 4, 32003, 9);
        write_matrix(
            &out,
            &matrix,
            &Meta {
                prime: 32003,
                split: 0,
                label: "s".into(),
            },
        )
        .unwrap();
        let expected = rref_arm(&matrix, 0, "f4", 1).unwrap();
        let sms = Path::new(&format!("{out}.sms")).to_path_buf();
        for name in ["flint", "fflas", "spasm"] {
            assert_eq!(
                driver_rref(name, &sms, 32003),
                (expected.rank, expected.digest),
                "{name}"
            );
        }
        let bits = synthetic::<Zp2>(false, 150, 130, 6, 2, 10);
        write_matrix(
            &out,
            &bits,
            &Meta {
                prime: 2,
                split: 0,
                label: "b".into(),
            },
        )
        .unwrap();
        let expected = rref_arm(&bits, 0, "gf2", 1).unwrap();
        for name in ["flint", "m4ri"] {
            assert_eq!(
                driver_rref(name, &sms, 2),
                (expected.rank, expected.digest),
                "{name}"
            );
        }
    }
}
