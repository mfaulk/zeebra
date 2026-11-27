//! Zeebra's side of the per-primitive univariate comparison against FLINT and NTL (#1206).
//!
//! Each side runs as its own process on the same job file and times its own call, so parsing and
//! process start-up are outside every figure. `export` writes the jobs; `run` executes one with
//! Zeebra's default entry point and writes the result in the format the FLINT and NTL drivers
//! write, so the harness can `cmp` the outputs before it times anything.
//!
//! ```text
//! cargo run --release --example univariate_primitives -- export dir=<d> field=<f> primitive=<p> n=<size>
//! cargo run --release --example univariate_primitives -- run path=<job> [reps=3] [out=<file>]
//! ```
//!
//! A job is `modulus <p>`, `primitive <name>`, then operand blocks `vec <len>` followed by `len`
//! decimal residues one per line. Outputs are one line per value: a polynomial is its coefficients
//! low to high, space-separated (the zero polynomial is an empty line); a scalar is itself; roots
//! are one per line, in any order (the harness sorts them). The harness and the operand shapes of
//! each primitive are in `tools/external/univariate-primitives/README.md`.

use std::{
    collections::HashSet,
    fmt::Write as _,
    path::{Path, PathBuf},
    time::{Duration, Instant},
};

use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    compose_mod,
    fields::{Bn254Fr, KoalaBear, Zp18446744069414584321, Zp18446744073709551557},
    gcd, lagrange_interpolate, multipoint_evaluate, pow_mod_limbs_unstable as pow_mod_limbs,
    resultant, roots, xgcd, KnownOrder, Polynomial, UnivariatePolynomial,
};

const KOALABEAR: &str = "2130706433";
const GOLDILOCKS: &str = "18446744069414584321";
const P64_59: &str = "18446744073709551557";
const BN254_FR: &str =
    "21888242871839275222246405745257275088548364400416034343698204186575808495617";

/// Every primitive the comparison covers, in report order.
const PRIMITIVES: [&str; 10] = [
    "mul",
    "divrem",
    "gcd",
    "xgcd",
    "powmod",
    "roots",
    "multieval",
    "interpolate",
    "compose",
    "resultant",
];

/// Little-endian 64-bit limbs of a decimal string.
fn decimal_limbs(decimal: &str) -> Vec<u64> {
    let mut limbs: Vec<u64> = Vec::new();
    for digit in decimal.bytes() {
        assert!(digit.is_ascii_digit(), "not a decimal: {decimal}");
        let mut carry = u128::from(digit - b'0');
        for limb in &mut limbs {
            let wide = u128::from(*limb) * 10 + carry;
            *limb = wide as u64;
            carry = wide >> 64;
        }
        if carry != 0 {
            limbs.push(carry as u64);
        }
    }
    limbs
}

fn check_modulus<F: KnownOrder>(decimal: &str) {
    assert_eq!(
        decimal_limbs(decimal),
        F::order_limbs(),
        "modulus constant {decimal} is not the field order"
    );
}

/// `len` uniform residues.
fn random_vec<F: KnownOrder>(len: usize, rng: &mut StdRng) -> Vec<F> {
    (0..len).map(|_| F::random(rng)).collect()
}

/// A random polynomial of exactly degree `n`; monic when asked.
fn random_poly<F: KnownOrder>(n: usize, monic: bool, rng: &mut StdRng) -> Vec<F> {
    let mut c = random_vec::<F>(n + 1, rng);
    if monic {
        c[n] = F::one();
    }
    while c[n].is_zero() {
        c[n] = F::random(rng);
    }
    c
}

/// `n` distinct random residues.
fn distinct_points<F: KnownOrder>(n: usize, rng: &mut StdRng) -> Vec<F> {
    let mut seen = HashSet::new();
    let mut out = Vec::with_capacity(n);
    while out.len() < n {
        let x = F::random(rng);
        if seen.insert(x.to_string()) {
            out.push(x);
        }
    }
    out
}

/// The operands of `primitive` at size `n`, as `export` writes them.
fn operands<F: KnownOrder>(primitive: &str, n: usize, rng: &mut StdRng) -> Vec<Vec<F>> {
    match primitive {
        "mul" => vec![random_poly(n, false, rng), random_poly(n, false, rng)],
        "divrem" => vec![random_poly(2 * n, false, rng), random_poly(n, false, rng)],
        "gcd" | "xgcd" | "resultant" => {
            vec![random_poly(n, false, rng), random_poly(n - 1, false, rng)]
        }
        "powmod" | "roots" => vec![random_poly(n, true, rng)],
        "multieval" => vec![random_poly(n - 1, false, rng), distinct_points(n, rng)],
        "interpolate" => vec![distinct_points(n, rng), random_vec(n, rng)],
        "compose" => vec![
            random_poly(n - 1, false, rng),
            random_poly(n - 1, false, rng),
            random_poly(n, true, rng),
        ],
        other => panic!("unknown primitive {other}"),
    }
}

/// Writes `<dir>/<field>-<primitive>-<n>.job` and prints its path.
fn write_job<F: KnownOrder>(dir: &Path, field: &str, modulus: &str, primitive: &str, n: usize) {
    check_modulus::<F>(modulus);
    // One seed per (field, primitive, size), so a job is the same bytes whenever it is exported.
    let index = PRIMITIVES
        .iter()
        .position(|p| *p == primitive)
        .unwrap_or_else(|| panic!("unknown primitive {primitive}"));
    let field_index = FIELDS.iter().position(|f| *f == field).unwrap();
    let seed = 0x1206_0000_0000 ^ (n as u64) << 8 ^ (index as u64) << 4 ^ field_index as u64;
    let mut rng = StdRng::seed_from_u64(seed);
    let mut text = format!("modulus {modulus}\nprimitive {primitive}\n");
    for v in operands::<F>(primitive, n, &mut rng) {
        writeln!(text, "vec {}", v.len()).unwrap();
        for c in v {
            writeln!(text, "{c}").unwrap();
        }
    }
    std::fs::create_dir_all(dir).unwrap_or_else(|e| panic!("creating {}: {e}", dir.display()));
    let path = dir.join(format!("{field}-{primitive}-{n}.job"));
    std::fs::write(&path, text).unwrap_or_else(|e| panic!("writing {}: {e}", path.display()));
    println!("{}", path.display());
}

/// The fields, by the names jobs and reports use.
const FIELDS: [&str; 4] = ["koalabear", "goldilocks", "p64m59", "bn254fr"];

/// One job: the files reach hundreds of megabytes at 2^20 over BN254, so the harness exports each
/// just before it runs it and deletes it afterwards.
fn export(dir: &Path, field: &str, primitive: &str, n: usize) {
    match field {
        "koalabear" => write_job::<KoalaBear>(dir, field, KOALABEAR, primitive, n),
        "goldilocks" => write_job::<Zp18446744069414584321>(dir, field, GOLDILOCKS, primitive, n),
        "p64m59" => write_job::<Zp18446744073709551557>(dir, field, P64_59, primitive, n),
        "bn254fr" => write_job::<Bn254Fr>(dir, field, BN254_FR, primitive, n),
        other => panic!("unknown field {other}; expected one of {FIELDS:?}"),
    }
}

fn poly_line<F: KnownOrder>(p: &UnivariatePolynomial<F>) -> String {
    if p.is_zero() {
        return String::new();
    }
    let c = p.coefficients();
    c[..=p.degree() as usize]
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(" ")
}

fn values_line<F: KnownOrder>(v: &[F]) -> String {
    v.iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(" ")
}

/// What one call returns, kept typed so that formatting happens after the timer stops, as it
/// does in the C drivers.
enum Output<F: KnownOrder> {
    Polys(Vec<UnivariatePolynomial<F>>),
    Values(Vec<F>),
    Roots(Vec<F>),
    Scalar(F),
}

impl<F: KnownOrder> Output<F> {
    fn lines(&self) -> Vec<String> {
        match self {
            Output::Polys(ps) => ps.iter().map(poly_line).collect(),
            Output::Values(v) => vec![values_line(v)],
            Output::Roots(r) => r.iter().map(ToString::to_string).collect(),
            Output::Scalar(s) => vec![s.to_string()],
        }
    }
}

/// Runs `primitive` once. `polys[i]` is `ops[i]` as a polynomial, built before the timer.
fn execute<F: KnownOrder>(
    primitive: &str,
    ops: &[Vec<F>],
    polys: &[UnivariatePolynomial<F>],
    rng: &mut StdRng,
) -> Output<F> {
    match primitive {
        "mul" => Output::Polys(vec![&polys[0] * &polys[1]]),
        "divrem" => {
            let (q, r) = polys[0].div_with_remainder(&polys[1]);
            Output::Polys(vec![q, r])
        }
        "gcd" => Output::Polys(vec![gcd(&polys[0], &polys[1])]),
        "xgcd" => {
            let (g, s, t) = xgcd(&polys[0], &polys[1]);
            Output::Polys(vec![g, s, t])
        }
        "powmod" => {
            let x = UnivariatePolynomial::new(&[F::zero(), F::one()]);
            Output::Polys(vec![pow_mod_limbs(&x, F::order_limbs(), &polys[0])])
        }
        "roots" => Output::Roots(roots(&polys[0], rng)),
        "multieval" => Output::Values(multipoint_evaluate(&polys[0], &ops[1])),
        "interpolate" => {
            let points: Vec<(F, F)> = ops[0].iter().copied().zip(ops[1].iter().copied()).collect();
            Output::Polys(vec![lagrange_interpolate(points)])
        }
        "compose" => Output::Polys(vec![compose_mod(&polys[0], &polys[1], &polys[2])]),
        "resultant" => Output::Scalar(resultant(&polys[0], &polys[1])),
        other => panic!("unknown primitive {other}"),
    }
}

/// Times `reps` calls and prints the median and minimum. Parsing, building the operand
/// polynomials and formatting the result are all outside the timer; the call itself, including
/// allocating its result, is inside, as in the C drivers.
fn run_in<F: KnownOrder>(
    modulus: &str,
    primitive: &str,
    blocks: &[Vec<&str>],
    reps: usize,
    out: Option<&Path>,
) {
    check_modulus::<F>(modulus);
    let ops: Vec<Vec<F>> = blocks
        .iter()
        .map(|b| {
            b.iter()
                .map(|c| F::from_str(c).unwrap_or_else(|e| panic!("residue {c}: {e}")))
                .collect()
        })
        .collect();
    let polys: Vec<UnivariatePolynomial<F>> =
        ops.iter().map(|v| UnivariatePolynomial::new(v)).collect();
    let mut rng = StdRng::seed_from_u64(1206);
    let mut times: Vec<Duration> = Vec::with_capacity(reps);
    let mut last = None;
    for _ in 0..reps {
        drop(last.take());
        let start = Instant::now();
        let result = execute(primitive, &ops, &polys, &mut rng);
        times.push(start.elapsed());
        last = Some(std::hint::black_box(result));
    }
    times.sort();
    println!("time_ns {}", times[times.len() / 2].as_nanos());
    println!("min_ns {}", times[0].as_nanos());
    if let Some(out) = out {
        // Every line newline-terminated, so no roots is an empty file, as the drivers write it.
        let lines = last.expect("reps >= 1").lines();
        let text: String = lines.iter().map(|l| format!("{l}\n")).collect();
        std::fs::write(out, text).unwrap_or_else(|e| panic!("writing {}: {e}", out.display()));
    }
}

fn run(path: &Path, reps: usize, out: Option<&Path>) {
    let text =
        std::fs::read_to_string(path).unwrap_or_else(|e| panic!("reading {}: {e}", path.display()));
    let mut lines = text.lines().map(str::trim).filter(|l| !l.is_empty());
    let modulus = lines
        .next()
        .and_then(|l| l.strip_prefix("modulus "))
        .expect("first line: modulus <p>");
    let primitive = lines
        .next()
        .and_then(|l| l.strip_prefix("primitive "))
        .expect("second line: primitive <name>");
    let mut blocks: Vec<Vec<&str>> = Vec::new();
    while let Some(header) = lines.next() {
        let len: usize = header
            .strip_prefix("vec ")
            .and_then(|l| l.parse().ok())
            .unwrap_or_else(|| panic!("expected `vec <len>`, got {header}"));
        blocks.push(
            (0..len)
                .map(|_| lines.next().expect("truncated vec"))
                .collect(),
        );
    }
    match modulus {
        KOALABEAR => run_in::<KoalaBear>(modulus, primitive, &blocks, reps, out),
        GOLDILOCKS => run_in::<Zp18446744069414584321>(modulus, primitive, &blocks, reps, out),
        P64_59 => run_in::<Zp18446744073709551557>(modulus, primitive, &blocks, reps, out),
        BN254_FR => run_in::<Bn254Fr>(modulus, primitive, &blocks, reps, out),
        other => panic!("no field with modulus {other}"),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let value = |key: &str| {
        args.iter()
            .find_map(|a| a.strip_prefix(&format!("{key}=")).map(str::to_owned))
    };
    match args.first().map(String::as_str) {
        Some("export") => export(
            &PathBuf::from(value("dir").expect("export needs dir=<path>")),
            &value("field").expect("export needs field=<name>"),
            &value("primitive").expect("export needs primitive=<name>"),
            value("n")
                .map(|v| v.parse().expect("n"))
                .expect("export needs n=<size>"),
        ),
        Some("run") => run(
            &PathBuf::from(value("path").expect("run needs path=<job>")),
            value("reps").map_or(3, |v| v.parse().expect("reps")),
            value("out").map(PathBuf::from).as_deref(),
        ),
        _ => {
            eprintln!(
                "usage: univariate_primitives export dir=<d> field=<f> primitive=<p> n=<size>"
            );
            eprintln!("       univariate_primitives run path=<job> [reps=3] [out=<file>]");
            std::process::exit(2);
        }
    }
}
