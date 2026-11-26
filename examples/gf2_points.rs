//! #1156: the opt-in GF(2) point-solving route on #1041's dense planted instances, one JSON line
//! per solve.
//!
//! cargo run --release --example gf2_points -- --n 28 --m 56 --seed 1
//!     [--method exhaustive|crossbred] [--kept K] [--degree D] [--workers W] [--all]
//!
//! The instance is `point_solving_screen --q 2`'s, bit for bit: the same SplitMix64 streams, every
//! Boolean monomial of degree ≤ 2 with a uniform coefficient, the constant fixed so the system
//! vanishes at the seeded point. Underdetermined shapes (n > m) are solved directly; the walk
//! stops at the first point, so nothing is fixed at random and nothing is retried.
//!
//! The wall covers conversion, preprocessing and enumeration: the complete task the gate on #1156
//! compares with the field-equation pipeline.

use std::time::Instant;

use zeebra::{
    grobner::{BooleanQuadraticSystem, CrossbredParameters, Gf2Method, Gf2PointOptions},
    util::Json,
};

/// SplitMix64, as in `point_solving_screen`.
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
    fn bit(&mut self) -> bool {
        self.next() % 2 == 1
    }
}

/// `point_solving_screen`'s `instance(2, n, m, seed)`, as monomial masks, and its planted point.
fn instance(n: usize, m: usize, seed: u64) -> (Vec<Vec<u64>>, u64) {
    let mut rng = Rng::new(seed, 0);
    let point = (0..n).fold(0u64, |p, i| p | u64::from(rng.bit()) << i);
    let monomials: Vec<u64> = (0..n)
        .flat_map(|i| (i + 1..n).map(move |j| 1u64 << i | 1 << j))
        .chain((0..n).map(|i| 1u64 << i))
        .collect();
    let system = (0..m)
        .map(|i| {
            let mut rng = Rng::new(seed, 1 + i as u64);
            let mut terms: Vec<u64> = monomials.iter().copied().filter(|_| rng.bit()).collect();
            if terms.iter().filter(|&&t| t & point == t).count() % 2 == 1 {
                terms.push(0);
            }
            terms
        })
        .collect();
    (system, point)
}

fn main() {
    let raw: Vec<String> = std::env::args().skip(1).collect();
    let (mut n, mut m, mut seed, mut workers, mut kept, mut degree) = (0, 0, 1, 1, 0, 0);
    let mut method = "exhaustive".to_string();
    let mut all = false;
    let mut it = raw.iter();
    while let Some(arg) = it.next() {
        if arg == "--all" {
            all = true;
            continue;
        }
        let value = it.next().unwrap_or_else(|| panic!("{arg} needs a value"));
        let number = || -> usize {
            value
                .parse()
                .unwrap_or_else(|_| panic!("{arg}: not a number"))
        };
        match arg.as_str() {
            "--n" => n = number(),
            "--m" => m = number(),
            "--seed" => seed = number() as u64,
            "--workers" => workers = number(),
            "--kept" => kept = number(),
            "--degree" => degree = number(),
            "--method" => method = value.clone(),
            other => panic!("unknown argument {other}"),
        }
    }
    assert!(n > 0 && n <= 64 && m > 0, "--n in 1..=64 and --m positive");
    let method = match method.as_str() {
        "exhaustive" => Gf2Method::Exhaustive,
        "crossbred" => Gf2Method::Crossbred(CrossbredParameters { kept, degree }),
        other => panic!("--method is exhaustive or crossbred, not {other}"),
    };
    let options = Gf2PointOptions {
        method,
        workers,
        ..Gf2PointOptions::default()
    };
    let (equations, planted) = instance(n, m, seed);
    let clock = Instant::now();
    let system = BooleanQuadraticSystem::from_monomial_masks(n, &equations).expect("quadratic");
    let result = if all {
        system.all_points(&options)
    } else {
        system
            .solve_one(&options)
            .map(|(x, report)| (x.into_iter().collect(), report))
    };
    let wall = clock.elapsed();
    let mut fields = vec![
        ("n", Json::size(n)),
        ("m", Json::size(m)),
        ("seed", Json::size(seed as usize)),
        ("method", Json::string(format!("{method:?}"))),
        ("workers", Json::size(workers)),
        ("call_ns", Json::nanos(wall)),
    ];
    match result {
        Ok((points, report)) => {
            let verified = points.iter().all(|&x| system.vanishes_at(x));
            fields.extend([
                (
                    "status",
                    Json::string(if points.is_empty() { "none" } else { "point" }),
                ),
                ("points", Json::size(points.len())),
                ("verified", Json::Bool(verified)),
                ("planted_found", Json::Bool(points.contains(&planted))),
                ("chunks", Json::size(report.chunks as usize)),
                ("chunks_walked", Json::size(report.chunks_walked as usize)),
                (
                    "points_per_chunk",
                    Json::size(report.points_per_chunk as usize),
                ),
                ("candidates", Json::size(report.candidates as usize)),
            ]);
            if let Some(p) = report.preprocessing {
                fields.extend([
                    ("macaulay_rows", Json::size(p.rows)),
                    ("macaulay_columns", Json::size(p.columns)),
                    ("high_columns", Json::size(p.high_columns)),
                    ("rank", Json::size(p.rank)),
                    ("polynomials", Json::size(p.polynomials)),
                ]);
            }
        }
        Err(e) => fields.extend([
            ("status", Json::string("refused")),
            ("error", Json::string(e.to_string())),
        ]),
    }
    println!("{}", Json::object(fields).to_json());
}
