use std::time::Instant;
use zeebra::FiniteField;
use zeebra::{
    fields::Zp32003 as F,
    grobner::{FglmOptions, QuotientAlgebra, SpectralOptions},
    Monomial, MonomialOrder, MultivariatePolynomial, One, Polynomial,
};

fn peak_rss() -> String {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| {
            s.lines()
                .find(|line| line.starts_with("VmHWM:"))
                .map(str::to_owned)
        })
        .unwrap_or_else(|| "VmHWM unavailable".into())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let dimension: u32 = args.next().unwrap_or_else(|| "4".into()).parse()?;
    let mode = args.next().unwrap_or_else(|| "dense".into());
    if !(1..=128).contains(&dimension)
        || !matches!(mode.as_str(), "sparse" | "dense")
        || args.next().is_some()
    {
        return Err("usage: quotient_spectra [dimension 1..128] [sparse|dense]".into());
    }
    let mut terms = vec![(Monomial::univariate(0, 1), F::one())];
    for degree in 1..=if mode == "dense" { dimension - 1 } else { 1 } {
        terms.push((Monomial::univariate(1, degree), -F::one()));
    }
    let basis = [
        MultivariatePolynomial::new(&terms),
        MultivariatePolynomial::new(&[
            (Monomial::univariate(1, dimension), F::one()),
            (Monomial::univariate(1, 0), -F::one()),
        ]),
    ];
    let start = Instant::now();
    let algebra = QuotientAlgebra::<2, F>::new(
        &basis,
        MonomialOrder::Lexicographic,
        &FglmOptions::default(),
    )?;
    println!(
        "D={} mode={} construction={:?} operator_bytes={} {}",
        algebra.dimension(),
        mode,
        start.elapsed(),
        algebra.operator_bytes(),
        peak_rss()
    );
    let op = algebra.operator(0);
    let nonzeros: usize = (0..algebra.dimension())
        .map(|j| op.column(j).iter().filter(|x| **x != F::new(0)).count())
        .sum();
    println!("operator_nonzeros={nonzeros}");
    let options = SpectralOptions::default();
    let start = Instant::now();
    let (minimal, stats) = algebra.variable_minimal_polynomial(0, &options)?;
    println!(
        "minimal={:?} degree={} stats={stats:?} {}",
        start.elapsed(),
        minimal.degree(),
        peak_rss()
    );
    let start = Instant::now();
    let (characteristic, stats) = algebra.variable_characteristic_polynomial(0, &options)?;
    println!(
        "characteristic={:?} degree={} stats={stats:?} {}",
        start.elapsed(),
        characteristic.degree(),
        peak_rss()
    );
    let (_, remainder) = characteristic.div_with_remainder(&minimal);
    assert!(remainder.coefficients().iter().all(|c| *c == F::new(0)));
    // y^D=1 is separable here. At y=1 the dense h is D-1; at every other
    // Dth root h=-1, giving the characteristic polynomial independently.
    let (expected_minimal, expected_characteristic) = if mode == "sparse" {
        let mut coefficients = vec![F::new(0); dimension as usize + 1];
        coefficients[0] = -F::one();
        coefficients[dimension as usize] = F::one();
        let p = zeebra::UnivariatePolynomial::new(&coefficients);
        (p.clone(), p)
    } else if dimension == 1 {
        let p = zeebra::UnivariatePolynomial::new(&[F::new(0), F::one()]);
        (p.clone(), p)
    } else {
        let root_one =
            zeebra::UnivariatePolynomial::new(&[-F::new(u64::from(dimension - 1)), F::one()]);
        let other_roots = zeebra::UnivariatePolynomial::new(&[F::one(), F::one()]);
        let mut expected = root_one.clone();
        for _ in 1..dimension {
            expected *= other_roots.clone();
        }
        (root_one * other_roots, expected)
    };
    assert_eq!(minimal, expected_minimal);
    assert_eq!(characteristic, expected_characteristic);
    println!("verified against the independent cyclic-algebra formulas");
    if dimension <= 4 {
        println!("minimal coefficients={:?}", minimal.coefficients());
        println!(
            "characteristic coefficients={:?}",
            characteristic.coefficients()
        );
    }
    Ok(())
}
