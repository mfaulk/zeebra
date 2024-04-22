//! Finite Field Fast Fourier Transform (FFT) and Inverse Fast Fourier Transform (IFFT).

mod domain;
mod evaluate;
mod interpolate;

use crate::FiniteField;

pub use domain::FFTDomain;
pub use evaluate::evaluate;
pub use interpolate::interpolate;

/// Split x into its even-indexed and odd-indexed elements.
fn evens_and_odds<T: Clone>(x: &[T]) -> (Vec<T>, Vec<T>) {
    let evens: Vec<T> = x.iter().step_by(2).cloned().collect();
    let odds: Vec<T> = x.iter().skip(1).step_by(2).cloned().collect();
    (evens, odds)
}

/// Compute the powers 1, w, w^2, ..., w^{n-1}
pub fn powers_of<F: FiniteField>(w: &F, n: usize) -> Vec<F> {
    if n == 0 {
        return vec![];
    };

    let mut powers = Vec::with_capacity(n);
    powers.push(F::one());
    // let mut w_i = F::one(); // w^i
    for i in 1..n {
        // w_i = w_i * w;
        powers.push(powers[i - 1] * w);
    }

    powers
}

#[cfg(test)]
mod tests {
    use crate::{
        fft::powers_of, fields::PrimeFieldElement64, poly::UnivariatePolynomial, FiniteField,
    };

    /*
    Performing polynomial evaluations with Sage:

    sage: R.<x>=GF(5)[]
    sage: f=x^2
    sage: f(5)
    0
     */

    /// Creates a polynomial in F whose coefficients are given as u64s.
    pub(crate) fn to_polynomial<F: FiniteField>(coefficients: &[u64]) -> UnivariatePolynomial<F> {
        let coefficients_in_f: Vec<_> = coefficients.iter().map(|c| F::new(*c)).collect();
        UnivariatePolynomial::new(&coefficients_in_f)
    }

    #[test]
    // Should compute w^0, ..., w^{n-1}.
    fn test_get_powers() {
        type F = PrimeFieldElement64<13>;
        let w = F::new(4);
        let powers = powers_of(&w, 16);
        for i in 0..powers.len() {
            assert_eq!(powers[i], w.pow(i as u128));
        }
    }
}
