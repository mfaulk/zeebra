//! #1035: conventional F4's largest matrix on the overdetermined multihomogeneous shapes of
//! Faugère–Spaenlehauer–Svartz, *Sparse Gröbner bases: the unmixed case* (ISSAC 2014), Tables 1–2.
//!
//! cargo run --release --example sparse_toric_counts -- --nx 2 --ny 4 --m 9 --dx 2
//!     [--perturb 1] [--seed 1] [--wall-s 120]
//!
//! Each of the `m` generators takes a seeded random coefficient on every monomial `x^a y^b` with
//! `|a| ≤ dx` and `|b| ≤ 1`. That is the lattice points of `dx·Δ_{nx} × Δ_{ny}`, the paper's
//! supports for `dx` = 1 (bilinear) and 2 (bidegree (2,1)). The constant is then fixed so that the
//! system vanishes at a seeded point of GF(65521)ⁿ, which gives the paper's "at least one rational
//! solution". `--perturb k` adds `k` distinct products `y_a·y_b` to each generator, which takes the
//! support out of the polytope: these are the controls. The solve is grevlex conventional F4 under
//! shipping options. Every reported figure is a count; `call_ns` is for scale only.

use std::time::{Duration, Instant};
use zeebra::{
    fields::PrimeFieldElement32,
    grobner::{f4_reported, F4Options},
    util::Json,
    FiniteField, Monomial, MonomialOrder, MultivariatePolynomial,
};

type F = PrimeFieldElement32<65521>;
const ORDER: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

#[derive(Debug, Clone, PartialEq)]
struct Shape {
    nx: usize,
    ny: usize,
    m: usize,
    dx: u32,
    perturb: usize,
    seed: u64,
}

fn parse_args(raw: &[String]) -> Result<(Shape, Duration), String> {
    let mut s = Shape {
        nx: 0,
        ny: 0,
        m: 0,
        dx: 1,
        perturb: 0,
        seed: 1,
    };
    let mut wall = Duration::from_secs(120);
    let mut it = raw.iter();
    while let Some(arg) = it.next() {
        let value = it.next().ok_or(format!("{arg} needs a value"))?;
        let number = |v: &str| v.parse::<u64>().map_err(|_| format!("{arg}: not a number"));
        match arg.as_str() {
            "--nx" => s.nx = number(value)? as usize,
            "--ny" => s.ny = number(value)? as usize,
            "--m" => s.m = number(value)? as usize,
            "--dx" => s.dx = number(value)? as u32,
            "--perturb" => s.perturb = number(value)? as usize,
            "--seed" => s.seed = number(value)?,
            "--wall-s" => wall = Duration::from_secs(number(value)?),
            other => return Err(format!("unknown argument {other}")),
        }
    }
    if s.nx == 0 || s.ny == 0 || s.m == 0 || !(1..=2).contains(&s.dx) {
        return Err("--nx, --ny and --m must be positive and --dx 1 or 2".into());
    }
    if s.perturb > s.ny * (s.ny + 1) / 2 {
        return Err("--perturb exceeds the y-block's products".into());
    }
    Ok((s, wall))
}

/// SplitMix64: a fixed stream per (seed, label), so an instance depends on nothing but its shape.
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
    fn nonzero(&mut self) -> u64 {
        1 + self.next() % 65520
    }
}

/// The exponent vectors of `dx·Δ_{nx} × Δ_{ny}`: x-block degree at most `dx`, y-block at most 1.
fn support(nx: usize, ny: usize, dx: u32) -> Vec<Vec<u32>> {
    let mut x_parts: Vec<Vec<u32>> = vec![vec![0; nx]];
    for _ in 0..dx {
        let mut next = x_parts.clone();
        for p in &x_parts {
            // Raise one coordinate at or after the last nonzero one, so each multiset appears once.
            let start = p.iter().rposition(|&e| e > 0).unwrap_or(0);
            for i in start..nx {
                let mut q = p.clone();
                q[i] += 1;
                next.push(q);
            }
        }
        next.sort();
        next.dedup();
        x_parts = next;
    }
    let mut out = Vec::new();
    for x in &x_parts {
        for y in std::iter::once(None).chain((0..ny).map(Some)) {
            let mut e = x.clone();
            e.extend((0..ny).map(|j| u32::from(y == Some(j))));
            out.push(e);
        }
    }
    out
}

/// One generator as `(coefficient, exponents)` terms.
type Terms = Vec<(u64, Vec<u32>)>;

/// The `m` generators of `shape`, and the planted point.
fn instance(shape: &Shape) -> (Vec<Terms>, Vec<u64>) {
    let n = shape.nx + shape.ny;
    let mut rng = Rng::new(shape.seed, 0);
    let point: Vec<u64> = (0..n).map(|_| rng.next() % 65521).collect();
    let base = support(shape.nx, shape.ny, shape.dx);
    let products: Vec<Vec<u32>> = (0..shape.ny)
        .flat_map(|a| (a..shape.ny).map(move |b| (a, b)))
        .map(|(a, b)| {
            let mut e = vec![0; n];
            e[shape.nx + a] += 1;
            e[shape.nx + b] += 1;
            e
        })
        .collect();
    let mut system = Vec::new();
    for i in 0..shape.m {
        let mut rng = Rng::new(shape.seed, 1 + i as u64);
        let mut terms: Terms = base
            .iter()
            .filter(|e| e.iter().any(|&x| x > 0))
            .map(|e| (rng.nonzero(), e.clone()))
            .collect();
        let mut chosen = std::collections::BTreeSet::new();
        while chosen.len() < shape.perturb {
            chosen.insert((rng.next() % products.len() as u64) as usize);
        }
        terms.extend(chosen.iter().map(|&k| (rng.nonzero(), products[k].clone())));
        // The constant makes the generator vanish at the planted point.
        let value = terms.iter().fold(0u64, |acc, (c, e)| {
            let mono = e
                .iter()
                .zip(&point)
                .fold(1u64, |v, (&k, &w)| (0..k).fold(v, |v, _| v * w % 65521));
            (acc + c * mono) % 65521
        });
        terms.push(((65521 - value) % 65521, vec![0; n]));
        system.push(terms);
    }
    (system, point)
}

fn solve<const N: usize>(shape: &Shape, wall: Duration) -> Vec<(&'static str, Json)> {
    let (terms, point) = instance(shape);
    let system: Vec<MultivariatePolynomial<N, F>> = terms
        .iter()
        .map(|t| {
            let t: Vec<(F, Monomial<N>)> = t
                .iter()
                .map(|(c, e)| (F::new(*c), Monomial::new(e)))
                .collect();
            MultivariatePolynomial::new(&t)
        })
        .collect();
    let options = F4Options {
        max_wall_time: Some(wall),
        ..F4Options::default()
    };
    let clock = Instant::now();
    let (result, statistics) = f4_reported(&system, ORDER, &options);
    let call = clock.elapsed();
    // A planted point is a common zero, so a complete basis must vanish there.
    let vanishes = result.as_ref().ok().map(|basis| {
        let at: [F; N] = std::array::from_fn(|i| F::new(point[i]));
        basis.iter().all(|g| g.eval(&at) == F::new(0))
    });
    vec![
        (
            "status",
            Json::string(if result.is_ok() {
                "complete"
            } else {
                "stopped"
            }),
        ),
        (
            "error",
            result
                .as_ref()
                .err()
                .map_or(Json::Null, |e| Json::string(format!("{e:?}"))),
        ),
        (
            "basis_elements",
            result.as_ref().map_or(Json::Null, |b| Json::size(b.len())),
        ),
        (
            "vanishes_at_planted_point",
            vanishes.map_or(Json::Null, Json::Bool),
        ),
        ("batches", Json::size(statistics.batches)),
        ("max_matrix_rows", Json::size(statistics.max_matrix_rows)),
        (
            "max_matrix_columns",
            Json::size(statistics.max_matrix_columns),
        ),
        ("max_pair_degree", Json::int(statistics.max_pair_degree)),
        ("call_ns", Json::nanos(call)),
    ]
}

fn main() {
    let raw: Vec<String> = std::env::args().skip(1).collect();
    let (shape, wall) = parse_args(&raw).unwrap_or_else(|e| panic!("{e}"));
    let mut fields = vec![
        ("nx", Json::size(shape.nx)),
        ("ny", Json::size(shape.ny)),
        ("m", Json::size(shape.m)),
        ("dx", Json::int(shape.dx)),
        ("perturb", Json::size(shape.perturb)),
        ("seed", Json::int(shape.seed)),
    ];
    macro_rules! dispatch {
        ($($n:literal),*) => {
            match shape.nx + shape.ny {
                $($n => solve::<$n>(&shape, wall),)*
                n => vec![
                    ("status", Json::string("refused")),
                    ("error", Json::string(format!("Unsupported: no instantiation for {n} variables"))),
                ],
            }
        };
    }
    fields.extend(dispatch!(
        6, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 25, 27, 31
    ));
    println!("{}", Json::object(fields).to_json().replace('\n', ""));
}

#[cfg(test)]
mod tests {
    use super::*;

    fn shape(nx: usize, ny: usize, m: usize, dx: u32, perturb: usize) -> Shape {
        Shape {
            nx,
            ny,
            m,
            dx,
            perturb,
            seed: 1,
        }
    }

    /// The support is the lattice points of `dx·Δ_{nx} × Δ_{ny}`: C(nx+dx, nx)·(ny+1) of them.
    #[test]
    fn support_is_the_product_polytope() {
        assert_eq!(support(2, 3, 1).len(), 3 * 4);
        assert_eq!(support(2, 3, 2).len(), 6 * 4);
        assert_eq!(support(3, 2, 2).len(), 10 * 3);
        let s = support(2, 3, 2);
        assert!(s
            .iter()
            .all(|e| e[..2].iter().sum::<u32>() <= 2 && e[2..].iter().sum::<u32>() <= 1));
        let mut unique = s.clone();
        unique.sort();
        unique.dedup();
        assert_eq!(unique.len(), s.len());
    }

    /// Every generator vanishes at the planted point; a perturbation adds exactly k y-products.
    #[test]
    fn instances_are_planted_and_perturbed_as_asked() {
        let (system, point) = instance(&shape(2, 3, 6, 2, 2));
        assert_eq!(system.len(), 6);
        for terms in &system {
            let value = terms.iter().fold(0u64, |acc, (c, e)| {
                let mono = e
                    .iter()
                    .zip(&point)
                    .fold(1u64, |v, (&k, &w)| (0..k).fold(v, |v, _| v * w % 65521));
                (acc + c * mono) % 65521
            });
            assert_eq!(value, 0);
            let outside = terms
                .iter()
                .filter(|(_, e)| e[2..].iter().sum::<u32>() == 2);
            assert_eq!(outside.count(), 2);
        }
        assert_eq!(
            instance(&shape(2, 3, 6, 2, 2)),
            instance(&shape(2, 3, 6, 2, 2))
        );
    }

    /// An overdetermined planted bilinear system solves to a basis that vanishes at the point.
    #[test]
    fn a_small_shape_solves() {
        let out = solve::<6>(&shape(2, 4, 9, 2, 0), Duration::from_secs(30));
        let get = |k| out.iter().find(|(key, _)| *key == k).unwrap().1.to_json();
        assert_eq!(get("status"), "\"complete\"");
        assert_eq!(get("vanishes_at_planted_point"), "true");
    }

    #[test]
    fn arguments_are_validated() {
        let args = |s: &str| parse_args(&s.split(' ').map(String::from).collect::<Vec<_>>());
        assert!(args("--nx 2 --ny 4 --m 9 --dx 2").is_ok());
        assert!(args("--nx 2 --ny 4 --m 9 --dx 3").is_err());
        assert!(args("--nx 0 --ny 4 --m 9").is_err());
        assert!(args("--nx 2 --ny 2 --m 9 --perturb 4").is_err());
    }
}
