//! The Finite Field Fast Fourier Transform
//!
//! (See https://www.csee.umbc.edu/~phatak/691a/fft-lnotes/fftnotes.pdf)
//! (See https://www.csa.iisc.ac.in/~chandan/courses/CNT/notes/lec6.pdf)
//!
//! A Fourier Transform is a sequence of n points constituting the evaluation of a polynomial
//! with coefficients {a_0, ..., a_{n-1}} at the points {w^0, ..., w^{n-1}} where w is a primitive
//! nth root of unity.
//!
//!
//!     |    A(1)    |             |  1  1  ...  ...                1     |     |   a_0   |
//!     |    A(w)    |             |  1  w  w^2  ...             w^{n-1}  |     |   a_1   |
//!     |    A(w^2)  |      =      |  1  ...                       ...    |  *  |   a_2   |
//!     |     ...    |             |  1  ...                       ...    |     |   ...   |
//!     | A(w^{n-1}) |             |  1  w^{n-1} w^2(n-1) ... w^{(n-1)^2} |     | a_{n-1} |
//!
//!
//! When n is even, n=2k, we define two polynomials using the even and odd coefficients:
//!
//!     A_even(x) = \sum_0^{k-1} a_{2i} * x^i
//!     
//!     A_odd(x)  = \sum_0^{k-1} a_{2i+1} * x^i
//!
//!     A(x) = A_even(x^2) + x*A_odd(x^2)
//!

use crate::{
    fft::{domain::FFTDomain, evens_and_odds},
    FiniteField, Polynomial, UnivariatePolynomial,
};

/// Evaluate a polynomial at the points w^0, ..., w^{n-1}, where n is a power of 2.
///
/// # Arguments
/// * `p` - A polynomial of degree less than n with coefficients in a finite field F.
/// * `w` - Powers w^0, ..., w^{n-1} of w, a primitive nth root of unity of F.
#[allow(non_snake_case)]
pub fn evaluate<F: FiniteField>(p: &impl Polynomial<F>, w: &FFTDomain<F>) -> Vec<F> {
    let d = p.degree() as usize;
    let n = w.size();
    assert!(d < n, "p has degree {} but must be less than {}", d, n);

    if n == 1 {
        // When n is 1, p must be a constant polynomial.
        // TODO: check this
        return vec![p.eval(&w[0])];
    }

    // w must contain an even number of elements.
    assert_eq!(n % 2, 0, "n is {} but must be a power of 2.", n);

    let (even_coefficients, odd_coefficients) = evens_and_odds(p.coefficients());
    let p_even = UnivariatePolynomial::new(&even_coefficients);
    let p_odd = UnivariatePolynomial::new(&odd_coefficients);

    let (w_even, _w_odd) = w.split();

    // A_even and A_odd are evaluated for 1, w^2, w^4, ...
    let A_even = evaluate(&p_even, &w_even);
    let A_odd = evaluate(&p_odd, &w_even);

    let k = n / 2;
    let mut A: Vec<F> = vec![F::zero(); n];
    //                   |     1   |
    //                   |     w   |
    // A = | A_even | +  |    w^2  | \circ | A_odd |
    //     | A_even |    |   ...   |       | A_odd |
    //                   | w^{n-1} |
    //
    // The terms A_even and A_odd have k elements; this iterates over them twice while iterating
    // over the w terms once.
    for i in 0..n {
        A[i] = A_even[i % k] + w[i] * A_odd[i % k];
    }
    A
}

#[cfg(test)]
mod tests {
    use crate::{
        fft::{domain::FFTDomain, evaluate::evaluate, tests::to_polynomial},
        fields::PrimeFieldElement64,
        identities::Zero,
        FiniteField, Polynomial, UnivariatePolynomial,
    };
    use rand::{prelude::StdRng, SeedableRng};

    #[test]
    // Evaluating the zero polynomial should always produce zero.
    fn test_evaluate_zero_polynomial() {
        let mut rng = StdRng::seed_from_u64(13326);
        type F = PrimeFieldElement64<13>;
        let p = to_polynomial::<F>(&[0]);
        let generator = F::root_of_unity(4, &mut rng);
        let w = FFTDomain::from_generator(generator, 4);
        let evaluations = evaluate(&p, &w);
        assert_eq!(evaluations.len(), 4);
        assert_eq!(evaluations, vec!(F::zero(); 4));
    }

    #[test]
    // Evaluating a constant polynomial should always produce a_0.
    fn test_evaluate_constant_polynomial() {
        let mut rng = StdRng::seed_from_u64(17726);
        type F = PrimeFieldElement64<13>;
        let p = to_polynomial::<F>(&[6]);
        let generator = F::root_of_unity(4, &mut rng);
        let w = FFTDomain::from_generator(generator, 4);
        let evaluations = evaluate(&p, &w);
        // let w = F::root_of_unity(4, &mut rng);
        // let w_powers = powers_of(&w, 4);
        // let evaluations = evaluate(&p, &w_powers);
        assert_eq!(evaluations.len(), 4);
        assert_eq!(evaluations, vec!(F::new(6); 4));
    }

    #[test]
    // Evaluate a degree-1 polynomial.
    fn test_evaluate_linear_polynomial() {
        let mut rng = StdRng::seed_from_u64(179026);
        type F = PrimeFieldElement64<13>;
        // p(x) = 6 + x
        let p = to_polynomial::<F>(&[6, 1]);
        let generator = F::root_of_unity(4, &mut rng);
        let w = FFTDomain::from_generator(generator, 4);
        let evaluations = evaluate(&p, &w);
        assert_eq!(evaluations.len(), 4);
        // p(1) = (6 + 1) mod 13
        // p(w) = (6 + w) mod 13
        // p(w^2) = (6 + w^2) mod 13
        // p(w^3) = (6 + w^3) mod 13
        let expected = [
            F::new(7),
            w[1] + F::new(6),
            w[2] + F::new(6),
            w[3] + F::new(6),
        ];
        assert_eq!(evaluations, expected);
    }

    #[test]
    // Evaluate a degree-2 polynomial.
    fn test_evaluate_quadratic_polynomial() {
        let mut rng = StdRng::seed_from_u64(179026);
        type F = PrimeFieldElement64<13>;
        // p(x) = 6 + 4x^2
        let p = to_polynomial::<F>(&[6, 0, 4]);
        let generator = F::root_of_unity(4, &mut rng);
        let w = FFTDomain::from_generator(generator, 4);
        let evaluations = evaluate(&p, &w);
        assert_eq!(evaluations.len(), 4);
        // p(1) = (6 + 4) mod 13
        // p(w) = (6 + 4w^2) mod 13
        // p(w^2) = (6 + 4w^4) mod 13
        // p(w^3) = (6 + 4w^6) mod 13
        let expected = [
            F::new(10),
            F::new(6) + F::new(4) * w[1].pow(2),
            F::new(6) + F::new(4) * w[2].pow(2),
            F::new(6) + F::new(4) * w[3].pow(2),
        ];
        assert_eq!(evaluations, expected);
    }

    #[test]
    // Evaluate a degree-3 polynomial.
    fn test_evaluate_cubic_polynomial() {
        type F = PrimeFieldElement64<13>;
        // p(x) = 5 + x + 4x^2 + x^3
        let p = to_polynomial::<F>(&[5, 1, 4, 1]);
        let generator = F::new(8); // 8 is a 4th root of unity of F.
        let w = FFTDomain::from_generator(generator, 4);
        let evaluations = evaluate(&p, &w);
        assert_eq!(evaluations.len(), 4);

        // sage: R.<x>=GF(13)[]
        // sage: f = 5 + x + 4*x^2 + x^3
        // sage: f(1)
        // 11
        // etc.

        let expected = [F::new(11), F::new(1), F::new(7), F::new(1)];
        assert_eq!(evaluations, expected);
    }

    #[test]
    #[should_panic]
    #[ignore]
    // When w is not an nth root of unity, ...
    fn test_evaluate_w_not_nth_root_of_unity() {
        todo!()
    }

    #[test]
    #[should_panic]
    // Panics if the degree of p >= n.
    fn test_p_degree_too_high() {
        let mut rng = StdRng::seed_from_u64(17);
        type F = PrimeFieldElement64<97>;
        let n = 16;
        let generator = F::root_of_unity(n, &mut rng);
        let w = FFTDomain::from_generator(generator, n as usize);

        // The degree of p should be less than n.
        let p = UnivariatePolynomial::<F>::rand(n, &mut rng);

        let _evaluations = evaluate(&p, &w);
    }
}
