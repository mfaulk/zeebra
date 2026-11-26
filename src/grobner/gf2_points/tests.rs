use rand::{rngs::StdRng, Rng, SeedableRng};

use super::*;
use crate::{
    grobner::{rational_points_by_enumeration, solve_zero_dimensional, with_field_equations},
    Monomial,
};

/// A dense quadratic system with every Boolean monomial of degree ≤ 2 drawn at random, planted at
/// a random point when `planted`. The shape of #1041's generator.
fn dense(n: usize, m: usize, planted: bool, rng: &mut StdRng) -> (Vec<Vec<u64>>, u64) {
    let point = if n == 0 {
        0
    } else {
        rng.gen::<u64>() >> (64 - n)
    };
    let monomials: Vec<u64> = (0..n)
        .flat_map(|i| (i + 1..n).map(move |j| 1u64 << i | 1 << j))
        .chain((0..n).map(|i| 1u64 << i))
        .collect();
    let equations = (0..m)
        .map(|_| {
            let mut terms: Vec<u64> = monomials.iter().copied().filter(|_| rng.gen()).collect();
            let value = terms.iter().filter(|&&t| t & point == t).count() % 2 == 1;
            let constant = if planted { value } else { rng.gen() };
            if constant {
                terms.push(0);
            }
            terms
        })
        .collect();
    (equations, point)
}

fn crossbred(kept: usize, degree: usize) -> Gf2PointOptions {
    Gf2PointOptions {
        method: Gf2Method::Crossbred(CrossbredParameters { kept, degree }),
        ..Gf2PointOptions::default()
    }
}

fn brute_force(system: &BooleanQuadraticSystem) -> Vec<u64> {
    (0..1u64 << system.variables())
        .filter(|&x| system.vanishes_at(x))
        .collect()
}

/// Exhaustive search and every crossbred `(k, D)` return exactly the brute-force point set, on
/// systems with none, one and many points, including more than 64 equations.
#[test]
fn every_method_returns_exactly_the_brute_force_points() {
    let mut rng = StdRng::seed_from_u64(1156);
    for n in 1..=9 {
        for &m in &[1, n / 2 + 1, n, 2 * n, 70] {
            for planted in [true, false] {
                let (equations, _) = dense(n, m, planted, &mut rng);
                let system = BooleanQuadraticSystem::from_monomial_masks(n, &equations).unwrap();
                let expected = brute_force(&system);
                let (got, _) = system.all_points(&Gf2PointOptions::default()).unwrap();
                assert_eq!(got, expected, "exhaustive, n = {n}, m = {m}");
                for kept in 1..=n {
                    for degree in 2..=n.clamp(2, 4) {
                        let (got, _) = system.all_points(&crossbred(kept, degree)).unwrap();
                        assert_eq!(
                            got, expected,
                            "crossbred ({kept}, {degree}), n = {n}, m = {m}"
                        );
                    }
                }
            }
        }
    }
}

/// `solve_one` finds a planted point's system solvable, and says `None` only when brute force does.
#[test]
fn solve_one_agrees_with_brute_force_on_existence() {
    let mut rng = StdRng::seed_from_u64(42);
    for n in 2..=10 {
        for planted in [true, false] {
            let (equations, _) = dense(n, n + 2, planted, &mut rng);
            let system = BooleanQuadraticSystem::from_monomial_masks(n, &equations).unwrap();
            let any = !brute_force(&system).is_empty();
            for options in [
                Gf2PointOptions::default(),
                crossbred(n.div_ceil(2), 3.min(n)),
            ] {
                let (x, _) = system.solve_one(&options).unwrap();
                assert_eq!(x.is_some(), any, "n = {n}, {options:?}");
                if let Some(x) = x {
                    assert!(system.vanishes_at(x));
                }
            }
        }
    }
}

/// Converted from field polynomials, the answer is `rational_points_by_enumeration`'s, and squares
/// are read as `x_i² = x_i`.
#[test]
fn polynomial_route_agrees_with_rational_points_by_enumeration() {
    const N: usize = 7;
    let mut rng = StdRng::seed_from_u64(9);
    for round in 0..12 {
        let system: Vec<MultivariatePolynomial<N, Zp2>> = (0..5 + round % 4)
            .map(|_| {
                let terms: Vec<(Monomial<N>, Zp2)> = (0..12)
                    .map(|_| {
                        let mut e = [0u32; N];
                        for _ in 0..rng.gen_range(0..=2) {
                            e[rng.gen_range(0..N)] += rng.gen_range(1..=2);
                        }
                        (Monomial::new(&e), Zp2::one())
                    })
                    .collect();
                MultivariatePolynomial::new(&terms)
            })
            .collect();
        // Exponent 2 on one variable is Boolean degree 1; two variables squared is degree 2.
        let mut expected = rational_points_by_enumeration(&system).unwrap();
        let key = |p: &[Zp2; N]| -> u64 {
            (0..N)
                .filter(|&i| !p[i].is_zero())
                .fold(0, |m, i| m | 1 << i)
        };
        expected.sort_by_key(key);
        for options in [Gf2PointOptions::default(), crossbred(3, 3), crossbred(5, 2)] {
            let (points, _) = gf2_all_points(&system, &options).unwrap();
            assert_eq!(points, expected, "round {round}, {options:?}");
            let (one, _) = gf2_solve_one(&system, &options).unwrap();
            assert_eq!(one.is_some(), !expected.is_empty());
        }
    }
}

/// The same point set as Zeebra's field-equation pipeline, on #1041's dense planted shape.
#[test]
fn agrees_with_the_field_equation_pipeline_as_sets() {
    const N: usize = 6;
    let mut rng = StdRng::seed_from_u64(1041);
    for m in [6, 12] {
        let (equations, point) = dense(N, m, true, &mut rng);
        let system: Vec<MultivariatePolynomial<N, Zp2>> = equations
            .iter()
            .map(|terms| {
                let terms: Vec<(Monomial<N>, Zp2)> = terms
                    .iter()
                    .map(|&mask| {
                        let e: [u32; N] = std::array::from_fn(|i| (mask >> i & 1) as u32);
                        (Monomial::new(&e), Zp2::one())
                    })
                    .collect();
                MultivariatePolynomial::new(&terms)
            })
            .collect();
        let extended = with_field_equations(&system).unwrap();
        let mut pipeline: Vec<u64> =
            solve_zero_dimensional(&extended, &mut StdRng::seed_from_u64(1))
                .unwrap()
                .iter()
                .map(|p| {
                    (0..N)
                        .filter(|&i| !p[i].is_zero())
                        .fold(0, |m, i| m | 1 << i)
                })
                .collect();
        pipeline.sort_unstable();
        assert!(pipeline.contains(&point));
        for options in [Gf2PointOptions::default(), crossbred(3, 3)] {
            let boolean = BooleanQuadraticSystem::from_polynomials(&system).unwrap();
            let (points, _) = boolean.all_points(&options).unwrap();
            assert_eq!(points, pipeline, "m = {m}, {options:?}");
        }
    }
}

/// More than one chunk, walked on several threads: the same point as one thread, and every point.
#[test]
fn the_point_returned_does_not_depend_on_workers() {
    let mut rng = StdRng::seed_from_u64(5);
    // n − k = 16 enumerated variables against 14-bit chunks: four crossbred chunks. Exhaustive
    // over 22 variables against 20-bit chunks: four chunks.
    let (equations, point) = dense(22, 30, true, &mut rng);
    let system = BooleanQuadraticSystem::from_monomial_masks(22, &equations).unwrap();
    for method in [
        Gf2Method::Exhaustive,
        Gf2Method::Crossbred(CrossbredParameters { kept: 6, degree: 3 }),
    ] {
        let at = |workers| Gf2PointOptions {
            method,
            workers,
            ..Gf2PointOptions::default()
        };
        let (one, report) = system.solve_one(&at(1)).unwrap();
        assert_eq!(report.chunks, 4, "{method:?}");
        for workers in [2, 3, 8] {
            assert_eq!(system.solve_one(&at(workers)).unwrap().0, one, "{method:?}");
        }
        let (all, _) = system.all_points(&at(4)).unwrap();
        assert!(all.contains(&point), "{method:?}");
        assert_eq!(all, system.all_points(&at(1)).unwrap().0, "{method:?}");
    }
}

/// Retained combinations really are linear in the kept variables, and there are enough of them
/// on an overdetermined system for the linear solve to pin the kept variables down.
#[test]
fn crossbred_preprocessing_shape() {
    let mut rng = StdRng::seed_from_u64(77);
    let (equations, _) = dense(12, 24, true, &mut rng);
    let system = BooleanQuadraticSystem::from_monomial_masks(12, &equations).unwrap();
    let (_, report) = system.solve_one(&crossbred(6, 3)).unwrap();
    let statistics = report.preprocessing.unwrap();
    assert_eq!(statistics.columns, 1 + 12 + 66 + 220);
    assert_eq!(statistics.rows, 24 * 13);
    // deg ≥ 2 in 6 kept variables, total ≤ 3: C(6,2)·(1 + 6) + C(6,3).
    assert_eq!(statistics.high_columns, 15 * 7 + 20);
    assert!(statistics.polynomials >= 6, "{statistics:?}");
    // Each guess is a linear system that is almost always inconsistent or uniquely solved.
    assert!(report.candidates <= 4 * (1 << 6), "{report:?}");
}

#[test]
fn a_system_without_points_returns_none() {
    // x0 = 0 and x0 = 1.
    let system = BooleanQuadraticSystem::from_monomial_masks(3, &[vec![1], vec![1, 0]]).unwrap();
    for options in [Gf2PointOptions::default(), crossbred(1, 2), crossbred(2, 3)] {
        assert_eq!(system.solve_one(&options).unwrap().0, None);
        assert!(system.all_points(&options).unwrap().0.is_empty());
    }
}

#[test]
fn refusals_are_typed() {
    assert_eq!(
        BooleanQuadraticSystem::from_monomial_masks(65, &[]),
        Err(Gf2PointError::TooManyVariables { variables: 65 })
    );
    assert_eq!(
        BooleanQuadraticSystem::from_monomial_masks(4, &[vec![1], vec![0b111]]),
        Err(Gf2PointError::NotQuadratic {
            generator: 1,
            degree: 3
        })
    );
    // x0·x1·x2 over GF(2), as a field polynomial.
    let cubic: MultivariatePolynomial<3, Zp2> =
        MultivariatePolynomial::new(&[(Monomial::new(&[1, 1, 2]), Zp2::one())]);
    assert!(matches!(
        gf2_solve_one(&[cubic], &Gf2PointOptions::default()),
        Err(Gf2PointError::NotQuadratic { degree: 3, .. })
    ));
    let system = BooleanQuadraticSystem::from_monomial_masks(4, &[vec![1]]).unwrap();
    for (kept, degree) in [(0, 2), (5, 2), (2, 1), (2, 5)] {
        assert!(matches!(
            system.solve_one(&crossbred(kept, degree)),
            Err(Gf2PointError::InvalidParameters { .. })
        ));
    }
    let tiny = Gf2PointOptions {
        matrix_budget_bytes: 8,
        ..crossbred(2, 3)
    };
    assert!(matches!(
        system.solve_one(&tiny),
        Err(Gf2PointError::MatrixTooLarge { .. })
    ));
}
