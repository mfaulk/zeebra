use zeebra::{
    fields::{PrimeFieldElement32, Zp32003},
    grobner::{FglmOptions, QuotientAlgebra, SpectralError, SpectralOptions},
    FiniteField, MonomialOrder, MultivariatePolynomial, UnivariatePolynomial,
};
use zeebra::{One, Polynomial, Zero};

fn quotient<F: FiniteField>() -> QuotientAlgebra<2, F> {
    let basis = ["x^2", "y^2"].map(|s| MultivariatePolynomial::parse(s, ["x", "y"]).unwrap());
    QuotientAlgebra::new(
        &basis,
        MonomialOrder::Lexicographic,
        &FglmOptions::default(),
    )
    .unwrap()
}

// Nonseparating nilpotents retain characteristic multiplicity over small and large primes.
#[test]
fn nonradical_spectra() {
    fn check<F: FiniteField>() {
        let algebra = quotient::<F>();
        let options = SpectralOptions::default();
        let (minimal, stats) = algebra.variable_minimal_polynomial(0, &options).unwrap();
        let (characteristic, _) = algebra
            .variable_characteristic_polynomial(0, &options)
            .unwrap();
        assert_eq!(
            minimal,
            UnivariatePolynomial::new(&[F::zero(), F::zero(), F::one()])
        );
        assert_eq!(
            characteristic,
            UnivariatePolynomial::new(&[F::zero(), F::zero(), F::zero(), F::zero(), F::one()])
        );
        assert!(stats.work_units > 0);
        assert_eq!(
            zeebra::grobner::fglm::shape_report(&algebra, 0).minimal_polynomial_degree,
            2
        );
    }
    check::<PrimeFieldElement32<2>>();
    check::<PrimeFieldElement32<3>>();
    check::<Zp32003>();
    check::<zeebra::fields::Gf256>();
    check::<zeebra::fields::Bn254Fr>();
}

// Invalid variables and exhausted resource budgets produce distinct typed refusals.
#[test]
fn spectral_refusals() {
    let algebra = quotient::<Zp32003>();
    let mut options = SpectralOptions::default();
    assert!(matches!(
        algebra.variable_minimal_polynomial(2, &options),
        Err(SpectralError::InvalidVariable { .. })
    ));
    options.max_dimension = 3;
    assert!(matches!(
        algebra.variable_minimal_polynomial(0, &options),
        Err(SpectralError::DimensionExceeded { .. })
    ));
    options = SpectralOptions::default();
    options.max_work_units = 0;
    assert!(matches!(
        algebra.variable_minimal_polynomial(0, &options),
        Err(SpectralError::WorkExceeded { .. })
    ));
    options = SpectralOptions::default();
    options.max_workspace_bytes = 0;
    assert!(matches!(
        algebra.variable_characteristic_polynomial(0, &options),
        Err(SpectralError::WorkspaceExceeded { .. })
    ));
    options = SpectralOptions::default();
    options.max_duration = std::time::Duration::ZERO;
    assert!(matches!(
        algebra.variable_characteristic_polynomial(0, &options),
        Err(SpectralError::DeadlineExceeded)
    ));
}

// A permutation determinant independently checks every coefficient, not just annihilation.
#[test]
fn characteristic_matches_determinant_and_annihilates() {
    fn check<F: FiniteField>() {
        let basis =
            ["x^2-y-1", "y^2-y-1"].map(|s| MultivariatePolynomial::parse(s, ["x", "y"]).unwrap());
        let algebra = QuotientAlgebra::new(
            &basis,
            MonomialOrder::Lexicographic,
            &FglmOptions::default(),
        )
        .unwrap();
        let options = SpectralOptions::default();
        let (minimal, _) = algebra.variable_minimal_polynomial(0, &options).unwrap();
        let (characteristic, stats) = algebra
            .variable_characteristic_polynomial(0, &options)
            .unwrap();
        let d = algebra.dimension();
        assert_eq!(stats.materialized_bytes, d * d * std::mem::size_of::<F>());
        let matrix: Vec<Vec<F>> = (0..d).map(|j| algebra.operator(0).column(j)).collect();
        fn determinant<F: FiniteField>(
            columns: &[Vec<F>],
            row: usize,
            used: &mut [bool],
            permutation: &mut Vec<usize>,
            product: UnivariatePolynomial<F>,
            sum: &mut UnivariatePolynomial<F>,
        ) {
            let d = columns.len();
            if row == d {
                let inversions = (0..d)
                    .flat_map(|i| (i + 1..d).map(move |j| (i, j)))
                    .filter(|(i, j)| permutation[*i] > permutation[*j])
                    .count();
                *sum = sum.clone()
                    + if inversions % 2 == 0 {
                        product
                    } else {
                        -product
                    };
                return;
            }
            for j in 0..d {
                if used[j] {
                    continue;
                }
                used[j] = true;
                permutation.push(j);
                let factor = UnivariatePolynomial::new(&[
                    -columns[j][row],
                    if row == j { F::one() } else { F::zero() },
                ]);
                determinant(
                    columns,
                    row + 1,
                    used,
                    permutation,
                    product.clone() * factor,
                    sum,
                );
                permutation.pop();
                used[j] = false;
            }
        }
        let mut expected = UnivariatePolynomial::new(&[F::zero()]);
        determinant(
            &matrix,
            0,
            &mut vec![false; d],
            &mut Vec::new(),
            UnivariatePolynomial::new(&[F::one()]),
            &mut expected,
        );
        assert_eq!(characteristic, expected);
        for polynomial in [&minimal, &characteristic] {
            for j in 0..d {
                let mut power = vec![F::zero(); d];
                power[j] = F::one();
                let mut total = vec![F::zero(); d];
                for c in polynomial.coefficients() {
                    for (slot, p) in total.iter_mut().zip(&power) {
                        *slot += *c * *p;
                    }
                    power = algebra.multiply_by_variable(0, &power);
                }
                assert!(total.iter().all(|x| x.is_zero()));
            }
        }
        let (_, remainder) = characteristic.div_with_remainder(&minimal);
        assert!(remainder.coefficients().iter().all(|x| x.is_zero()));
    }
    check::<PrimeFieldElement32<2>>();
    check::<PrimeFieldElement32<3>>();
    check::<Zp32003>();
    check::<zeebra::fields::Gf256>();
    check::<zeebra::fields::Bn254Fr>();
}

// Unit, zero-variable multiplication, cyclic nilpotents and field quotients have exact spectra.
#[test]
fn edge_algebras() {
    type F = Zp32003;
    for (relation, expected) in [
        ("x^3", vec![0, 0, 0, 1]),
        ("x", vec![0, 1]),
        ("x^2+1", vec![1, 0, 1]),
        ("1", vec![1]),
    ] {
        let basis = [MultivariatePolynomial::<1, F>::parse(relation, ["x"]).unwrap()];
        let algebra = QuotientAlgebra::new(
            &basis,
            MonomialOrder::Lexicographic,
            &FglmOptions::default(),
        )
        .unwrap();
        let expected =
            UnivariatePolynomial::new(&expected.into_iter().map(F::new).collect::<Vec<_>>());
        assert_eq!(
            algebra
                .variable_minimal_polynomial(0, &SpectralOptions::default())
                .unwrap()
                .0,
            expected
        );
        assert_eq!(
            algebra
                .variable_characteristic_polynomial(0, &SpectralOptions::default())
                .unwrap()
                .0,
            expected
        );
        assert!(matches!(
            algebra.variable_minimal_polynomial(1, &SpectralOptions::default()),
            Err(SpectralError::InvalidVariable { .. })
        ));
    }
    let basis = ["x", "y^4"].map(|s| MultivariatePolynomial::<2, F>::parse(s, ["x", "y"]).unwrap());
    let algebra = QuotientAlgebra::new(
        &basis,
        MonomialOrder::Lexicographic,
        &FglmOptions::default(),
    )
    .unwrap();
    assert_eq!(
        algebra
            .variable_minimal_polynomial(0, &SpectralOptions::default())
            .unwrap()
            .0,
        UnivariatePolynomial::new(&[F::zero(), F::one()])
    );
    assert_eq!(
        algebra
            .variable_characteristic_polynomial(0, &SpectralOptions::default())
            .unwrap()
            .0,
        UnivariatePolynomial::new(&[F::zero(), F::zero(), F::zero(), F::zero(), F::one()])
    );
    assert_eq!(
        QuotientAlgebra::<1, F>::new(&[], MonomialOrder::Lexicographic, &FglmOptions::default())
            .unwrap_err(),
        zeebra::grobner::FglmError::PositiveDimensional
    );
}

// A successful operation fits its reported workspace and work allowances exactly.
#[test]
fn exact_budget_boundary() {
    let algebra = quotient::<Zp32003>();
    for characteristic in [false, true] {
        let run = |options: &SpectralOptions| {
            if characteristic {
                algebra.variable_characteristic_polynomial(0, options)
            } else {
                algebra.variable_minimal_polynomial(0, options)
            }
        };
        let (expected, stats) = run(&SpectralOptions::default()).unwrap();
        let mut options = SpectralOptions {
            max_workspace_bytes: stats.workspace_bytes,
            max_work_units: stats.work_units,
            ..SpectralOptions::default()
        };
        assert_eq!(run(&options).unwrap().0, expected);
        options.max_work_units -= 1;
        assert!(matches!(
            run(&options),
            Err(SpectralError::WorkExceeded { .. })
        ));
        options.max_work_units += 1;
        options.max_workspace_bytes -= 1;
        assert!(matches!(
            run(&options),
            Err(SpectralError::WorkspaceExceeded { .. })
        ));
    }
}
