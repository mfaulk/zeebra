//! #1041: Zeebra's measured point-solving pipeline on Fukuoka-shaped dense MQ, and the hybrid
//! branches, one fresh process per measurement.
//!
//! cargo run --release --example point_solving_screen -- --q 31 --n 10 --m 20 --seed 1
//!     [--mode pipeline|branch|calibrate] [--fix K] [--branch correct|wrong] [--wall-s 600]
//!
//! Every generator carries every monomial of degree ≤ 2 with a uniform coefficient in GF(q); over
//! GF(2) the squares are linear terms and are not repeated. The constant is then fixed so that the
//! system vanishes at a seeded point. Over GF(2) the field equations are adjoined to whatever is
//! solved; over GF(31) they are not (`docs/research/boolean-solving.md` §5.1). The solve is
//! `solve_one_reported` under `GrevlexF4ThenFglm`, the opening route of `solve_one_planned`. F4's
//! row and column caps are lifted and its live-entry budget is 512 M entries, so the machine's
//! memory bounds the attempt rather than the shipping budgets. Its forward and symbolic passes are
//! serial, so this is one worker throughout.
//!
//! - `pipeline`: `n ≤ m` solves the system. `n > m` fixes the last `n − m` variables at random
//!   values and solves the square system. A miss retries with new values, and every attempt is
//!   charged.
//! - `branch --fix K`: one hybrid branch. It fixes the last `K` variables of the same instance at
//!   their planted values (`correct`) or at values drawn away from them (`wrong`) and solves the
//!   rest.
//! - `calibrate`: one-core operation rates for the counted methods. A GF(31) multiply-add and a
//!   64-bit AND+XOR, each over an in-cache array, which is the rate most favourable to them.

use std::time::{Duration, Instant};

use rand::{rngs::StdRng, SeedableRng};
use zeebra::{
    fields::PrimeFieldElement32,
    grobner::{
        solve_one_reported, with_field_equations, ParallelForward, ParallelSymbolic, SolveOptions,
        SolveOutcome, SolveStrategy,
    },
    util::Json,
    FiniteField, KnownOrder, Monomial, MultivariatePolynomial,
};

/// F4's live-entry budget: 512 M entries, 8 GiB at 16 bytes, on a 48 GiB machine.
const LIVE_ENTRIES: usize = 512 << 20;

/// One generator as `(coefficient, exponents)` terms over GF(q), coefficients in `[0, q)`.
type Terms = Vec<(u64, Vec<u32>)>;

#[derive(Debug, Clone, PartialEq)]
struct Args {
    q: u64,
    n: usize,
    m: usize,
    seed: u64,
    mode: String,
    fix: usize,
    correct: bool,
    wall: Duration,
}

fn parse_args(raw: &[String]) -> Result<Args, String> {
    let mut a = Args {
        q: 31,
        n: 0,
        m: 0,
        seed: 1,
        mode: "pipeline".into(),
        fix: 0,
        correct: true,
        wall: Duration::from_secs(600),
    };
    let mut it = raw.iter();
    while let Some(arg) = it.next() {
        let value = it.next().ok_or(format!("{arg} needs a value"))?;
        let number = || {
            value
                .parse::<u64>()
                .map_err(|_| format!("{arg}: not a number"))
        };
        match arg.as_str() {
            "--q" => a.q = number()?,
            "--n" => a.n = number()? as usize,
            "--m" => a.m = number()? as usize,
            "--seed" => a.seed = number()?,
            "--fix" => a.fix = number()? as usize,
            "--wall-s" => a.wall = Duration::from_secs(number()?),
            "--mode" => a.mode = value.clone(),
            "--branch" => {
                a.correct = match value.as_str() {
                    "correct" => true,
                    "wrong" => false,
                    _ => return Err("--branch is correct or wrong".into()),
                }
            }
            other => return Err(format!("unknown argument {other}")),
        }
    }
    if a.mode == "calibrate" {
        return Ok(a);
    }
    if ![2, 31].contains(&a.q) || a.n == 0 || a.m == 0 {
        return Err("--q is 2 or 31, and --n and --m are positive".into());
    }
    if !["pipeline", "branch"].contains(&a.mode.as_str()) {
        return Err("--mode is pipeline, branch or calibrate".into());
    }
    if a.mode == "branch" && (a.fix == 0 || a.fix >= a.n) {
        return Err("--fix is between 1 and n − 1".into());
    }
    Ok(a)
}

/// SplitMix64, so an instance depends on nothing but `(q, n, m, seed)`.
struct Rng(u64);

impl Rng {
    fn new(seed: u64, label: u64) -> Self {
        Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ label.wrapping_mul(0xD1B5_4A32_D192_ED03))
    }
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, q: u64) -> u64 {
        self.next() % q
    }
}

fn value(terms: &Terms, point: &[u64], q: u64) -> u64 {
    terms.iter().fold(0, |acc, (c, e)| {
        let mono = e
            .iter()
            .zip(point)
            .fold(1, |v, (&k, &x)| (0..k).fold(v, |v, _| v * x % q));
        (acc + c * mono) % q
    })
}

/// The dense planted system and its point.
fn instance(q: u64, n: usize, m: usize, seed: u64) -> (Vec<Terms>, Vec<u64>) {
    let mut rng = Rng::new(seed, 0);
    let point: Vec<u64> = (0..n).map(|_| rng.below(q)).collect();
    let mut monomials: Vec<Vec<u32>> = Vec::new();
    for i in 0..n {
        // Over GF(2), x_i² = x_i under the field equations, so the square is the linear term.
        let start = if q == 2 { i + 1 } else { i };
        for j in start..n {
            let mut e = vec![0; n];
            e[i] += 1;
            e[j] += 1;
            monomials.push(e);
        }
    }
    for i in 0..n {
        let mut e = vec![0; n];
        e[i] = 1;
        monomials.push(e);
    }
    let system = (0..m)
        .map(|i| {
            let mut rng = Rng::new(seed, 1 + i as u64);
            let mut terms: Terms = monomials
                .iter()
                .map(|e| (rng.below(q), e.clone()))
                .collect();
            let v = value(&terms, &point, q);
            terms.push(((q - v) % q, vec![0; n]));
            terms
        })
        .collect();
    (system, point)
}

/// `system` with its last `values.len()` variables fixed, in the remaining variables.
fn substitute(system: &[Terms], values: &[u64], q: u64) -> Vec<Terms> {
    let keep = system[0][0].1.len() - values.len();
    system
        .iter()
        .map(|terms| {
            let mut merged: std::collections::BTreeMap<Vec<u32>, u64> = Default::default();
            for (c, e) in terms {
                let scale = e[keep..]
                    .iter()
                    .zip(values)
                    .fold(*c, |v, (&k, &x)| (0..k).fold(v, |v, _| v * x % q));
                let entry = merged.entry(e[..keep].to_vec()).or_insert(0);
                *entry = (*entry + scale) % q;
            }
            merged.into_iter().map(|(e, c)| (c, e)).collect()
        })
        .collect()
}

/// One `solve_one` on `terms` in `N` variables: whether it found a point, the point's check against
/// those terms, the wall and the F4 extents.
fn solve<const N: usize, F: FiniteField + KnownOrder>(
    terms: &[Terms],
    q: u64,
    wall: Duration,
) -> (bool, Vec<(&'static str, Json)>) {
    let system: Vec<MultivariatePolynomial<N, F>> = terms
        .iter()
        .map(|t| {
            let t: Vec<(F, Monomial<N>)> = t
                .iter()
                .filter(|(c, _)| *c != 0)
                .map(|(c, e)| (F::new(*c), Monomial::new(e)))
                .collect();
            MultivariatePolynomial::new(&t)
        })
        .collect();
    let mut options = SolveOptions::with_strategy(SolveStrategy::GrevlexF4ThenFglm);
    // The machine's memory, not the shipping row and column caps, bounds the attempt.
    options.f4 = options.f4.with_live_entries::<F>(LIVE_ENTRIES);
    options.f4.max_matrix_rows = usize::MAX;
    options.f4.max_matrix_columns = usize::MAX;
    options.f4.parallel_forward = ParallelForward::Serial;
    options.f4.parallel_symbolic = ParallelSymbolic::Serial;
    options.f4.max_wall_time = Some(wall);
    let solved = if q == 2 {
        with_field_equations(&system).expect("GF(2) field equations")
    } else {
        system
    };
    let mut rng = StdRng::seed_from_u64(0);
    let clock = Instant::now();
    let (outcome, statistics) = solve_one_reported(&solved, &mut rng, &options);
    let call = clock.elapsed();
    let (status, found, verified) = match &outcome {
        Ok(SolveOutcome::Point(p)) => {
            let point: Vec<u64> = p.iter().map(|x| x.to_string().parse().unwrap()).collect();
            let ok = terms.iter().all(|t| value(t, &point, q) == 0);
            ("point", true, Json::Bool(ok))
        }
        Ok(SolveOutcome::NoBaseFieldPoint) => ("no-base-field-point", false, Json::Null),
        Ok(SolveOutcome::Inconsistent) => ("inconsistent", false, Json::Null),
        Err(_) => ("stopped", false, Json::Null),
    };
    let f4 = statistics.f4.as_ref();
    (
        found,
        vec![
            ("status", Json::string(status)),
            (
                "error",
                outcome
                    .as_ref()
                    .err()
                    .map_or(Json::Null, |e| Json::string(format!("{e:?}"))),
            ),
            ("verified", verified),
            ("call_ns", Json::nanos(call)),
            (
                "max_matrix_rows",
                f4.map_or(Json::Null, |s| Json::size(s.max_matrix_rows)),
            ),
            (
                "max_matrix_columns",
                f4.map_or(Json::Null, |s| Json::size(s.max_matrix_columns)),
            ),
            (
                "max_pair_degree",
                f4.map_or(Json::Null, |s| Json::int(s.max_pair_degree)),
            ),
        ],
    )
}

fn solve_in<F: FiniteField + KnownOrder>(
    terms: &[Terms],
    q: u64,
    wall: Duration,
) -> (bool, Vec<(&'static str, Json)>) {
    macro_rules! dispatch {
        ($($n:literal),*) => {
            match terms[0][0].1.len() {
                $($n => solve::<$n, F>(terms, q, wall),)*
                n => (false, vec![
                    ("status", Json::string("refused")),
                    ("error", Json::string(format!("Unsupported: no instantiation for {n} variables"))),
                ]),
            }
        };
    }
    dispatch!(
        2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
        27, 28
    )
}

fn run(terms: &[Terms], q: u64, wall: Duration) -> (bool, Vec<(&'static str, Json)>) {
    if q == 2 {
        solve_in::<PrimeFieldElement32<2>>(terms, q, wall)
    } else {
        solve_in::<PrimeFieldElement32<31>>(terms, q, wall)
    }
}

fn pipeline(a: &Args) -> Vec<(&'static str, Json)> {
    let (system, _) = instance(a.q, a.n, a.m, a.seed);
    if a.n <= a.m {
        return run(&system, a.q, a.wall).1;
    }
    // Underdetermined: fix the last n − m variables, retry on a miss, charge every attempt.
    let clock = Instant::now();
    let mut rng = Rng::new(a.seed, 0xA77E);
    let mut attempts = Vec::new();
    for _ in 0..64 {
        let values: Vec<u64> = (0..a.n - a.m).map(|_| rng.below(a.q)).collect();
        let left = a.wall.saturating_sub(clock.elapsed());
        let (found, fields) = run(&substitute(&system, &values, a.q), a.q, left);
        let stopped = fields.iter().any(|(k, v)| {
            *k == "status" && ["\"stopped\"", "\"refused\""].contains(&v.to_json().as_str())
        });
        attempts.push(Json::object(fields));
        if found || stopped {
            break;
        }
    }
    let last = attempts.last().cloned().unwrap_or(Json::Null);
    vec![
        ("status", Json::string("attempts")),
        ("attempts", Json::size(attempts.len())),
        ("call_ns", Json::nanos(clock.elapsed())),
        ("last", last),
        ("each", Json::Array(attempts)),
    ]
}

fn branch(a: &Args) -> Vec<(&'static str, Json)> {
    let (system, point) = instance(a.q, a.n, a.m, a.seed);
    let mut rng = Rng::new(a.seed, 0xB4A7);
    let values: Vec<u64> = point[a.n - a.fix..]
        .iter()
        .map(|&x| {
            if a.correct {
                x
            } else {
                // A value other than the planted one, so the branch is wrong.
                (x + 1 + rng.below(a.q - 1)) % a.q
            }
        })
        .collect();
    run(&substitute(&system, &values, a.q), a.q, a.wall).1
}

fn calibrate() -> Vec<(&'static str, Json)> {
    const LEN: usize = 4096;
    const ROUNDS: usize = 200_000;
    let mut a: Vec<u32> = (0..LEN as u32).map(|i| i % 31).collect();
    let b: Vec<u32> = (0..LEN as u32).map(|i| (i * 7 + 3) % 31).collect();
    let clock = Instant::now();
    for round in 0..ROUNDS {
        let c = (round % 30 + 1) as u32;
        for (x, y) in a.iter_mut().zip(&b) {
            *x = (*x + c * y) % 31;
        }
        std::hint::black_box(&mut a);
    }
    let gf31 = (LEN * ROUNDS) as f64 / clock.elapsed().as_secs_f64();
    let mut w: Vec<u64> = (0..LEN as u64)
        .map(|i| i.wrapping_mul(0x9E37_79B9))
        .collect();
    let u: Vec<u64> = (0..LEN as u64)
        .map(|i| i.wrapping_mul(0xD1B5_4A32))
        .collect();
    let clock = Instant::now();
    for round in 0..ROUNDS {
        let mask = (round as u64).wrapping_mul(0x94D0_49BB_1331_11EB);
        for (x, y) in w.iter_mut().zip(&u) {
            *x ^= y & mask;
        }
        std::hint::black_box(&mut w);
    }
    let gf2 = (LEN * ROUNDS) as f64 / clock.elapsed().as_secs_f64();
    vec![
        ("gf31_multiply_adds_per_s", Json::int(gf31 as u64)),
        ("gf2_word_ops_per_s", Json::int(gf2 as u64)),
    ]
}

fn main() {
    let raw: Vec<String> = std::env::args().skip(1).collect();
    let a = parse_args(&raw).unwrap_or_else(|e| panic!("{e}"));
    let mut fields = vec![("mode", Json::string(&a.mode))];
    if a.mode != "calibrate" {
        fields.extend([
            ("q", Json::int(a.q)),
            ("n", Json::size(a.n)),
            ("m", Json::size(a.m)),
            ("seed", Json::int(a.seed)),
        ]);
    }
    match a.mode.as_str() {
        "calibrate" => fields.extend(calibrate()),
        "pipeline" => fields.extend(pipeline(&a)),
        _ => {
            fields.push(("fix", Json::size(a.fix)));
            fields.push((
                "branch",
                Json::string(if a.correct { "correct" } else { "wrong" }),
            ));
            fields.extend(branch(&a));
        }
    }
    println!("{}", Json::object(fields).to_json().replace('\n', ""));
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Dense support: C(n+1, 2) quadratic and n linear terms over GF(31), C(n, 2) and n over GF(2),
    /// plus the constant, and every generator vanishes at the planted point.
    #[test]
    fn instances_are_dense_and_planted() {
        for (q, quadratic) in [(31u64, 21usize), (2, 15)] {
            let (system, point) = instance(q, 6, 12, 3);
            assert_eq!(system.len(), 12);
            assert!(system.iter().all(|t| t.len() == quadratic + 6 + 1));
            assert!(system.iter().all(|t| value(t, &point, q) == 0));
        }
    }

    /// Fixing the last variables at their planted values keeps the rest of the point a zero.
    #[test]
    fn substitution_keeps_the_planted_point() {
        for q in [31u64, 2] {
            let (system, point) = instance(q, 7, 14, 5);
            let fixed = substitute(&system, &point[4..], q);
            assert!(fixed.iter().all(|t| t[0].1.len() == 4));
            assert!(fixed.iter().all(|t| value(t, &point[..4], q) == 0));
        }
    }

    /// The pipeline finds a verified point on both fields, determined and underdetermined.
    #[test]
    fn the_pipeline_finds_a_verified_point() {
        for (q, n, m) in [(31u64, 4usize, 8usize), (2, 6, 12), (31, 6, 4), (2, 9, 6)] {
            let a = parse_args(
                &format!("--q {q} --n {n} --m {m} --seed 1 --wall-s 60")
                    .split(' ')
                    .map(String::from)
                    .collect::<Vec<_>>(),
            )
            .unwrap();
            let out = Json::object(pipeline(&a)).to_json();
            assert!(out.contains("\"verified\": true"), "{q} {n} {m}: {out}");
        }
    }

    /// A correct branch keeps the point; a wrong one over an overdetermined system has none.
    #[test]
    fn branches_are_correct_and_wrong_as_asked() {
        let args = |b: &str| {
            parse_args(
                &format!("--q 31 --n 6 --m 12 --mode branch --fix 2 --branch {b}")
                    .split(' ')
                    .map(String::from)
                    .collect::<Vec<_>>(),
            )
            .unwrap()
        };
        assert!(Json::object(branch(&args("correct")))
            .to_json()
            .contains("\"point\""));
        assert!(Json::object(branch(&args("wrong")))
            .to_json()
            .contains("\"inconsistent\""));
    }

    #[test]
    fn arguments_are_validated() {
        let args = |s: &str| parse_args(&s.split(' ').map(String::from).collect::<Vec<_>>());
        assert!(args("--q 31 --n 6 --m 12").is_ok());
        assert!(args("--q 5 --n 6 --m 12").is_err());
        assert!(args("--q 2 --n 6 --m 12 --mode branch --fix 6").is_err());
        assert!(args("--mode calibrate --n 0").is_ok());
    }
}
