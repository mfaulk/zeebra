//! Factoring a univariate polynomial over a finite field into irreducibles.
//!
//! For each d, the product of all monic irreducibles whose degree divides d is `x^(q^d) - x`, and
//! that product is squarefree. So `gcd(f, x^(q^d) - x)` is the product of the *distinct*
//! irreducible factors of f whose degree divides d — **whatever the multiplicities in f are**.
//!
//! That is what lets this skip squarefree decomposition altogether. The usual route computes
//! `gcd(f, f')` first, which needs separate handling in characteristic p when a multiplicity is
//! divisible by p, or when f' vanishes entirely as it does for `x^p`. None of that arises here:
//! multiplicities are recovered afterwards by dividing f by each irreducible factor.
//!
//! The distinct factors are collected degree by degree, then each group of equal-degree factors
//! is separated by Cantor–Zassenhaus splitting.
//!
//! # References
//! * A Computational Introduction to Number Theory and Algebra, 20.3 and 21.3
//! * Modern Computer Algebra by von zur Gathen and Gerhard, Ch. 14

use rand::{CryptoRng, RngCore};

use crate::{
    poly::univariate::{gcd, pow_mod, pow_mod::field_order, Polynomial, UnivariatePolynomial},
    FiniteField, KnownOrder,
};

/// Each splitting attempt succeeds with probability near one half, so exhausting this many means
/// a defect rather than bad luck. Failing loudly beats looping forever.
const MAX_SPLIT_ATTEMPTS: usize = 1000;

/// The monic irreducible factors of `f` and their multiplicities, in unspecified order.
///
/// The product of the factors, each raised to its multiplicity, is `f` divided by its leading
/// coefficient. A constant has no factorization, so the result is empty.
///
/// # Panics
/// Panics if `f` is the zero polynomial, which has no factorization.
pub fn factorize<F: KnownOrder, R: RngCore + CryptoRng>(
    f: &UnivariatePolynomial<F>,
    rng: &mut R,
) -> Vec<(UnivariatePolynomial<F>, usize)> {
    assert!(!f.is_zero(), "the zero polynomial has no factorization");

    if f.degree() == 0 {
        return Vec::new();
    }

    let monic = make_monic(f);
    let total_degree = monic.degree();
    let x = variable::<F>();
    let q = field_order::<F>();

    let mut factors: Vec<(UnivariatePolynomial<F>, usize)> = Vec::new();
    let mut accounted = 0u32;

    // Products of the distinct irreducible factors of each degree found so far, indexed by
    // degree minus one. Needed because `gcd(f, x^(q^d) - x)` catches every degree dividing d,
    // so the proper divisors have to be divided back out.
    let mut distinct_of_degree: Vec<UnivariatePolynomial<F>> = Vec::new();

    // x^(q^d), built by applying the Frobenius map repeatedly. Computing q^d as an integer would
    // overflow for even modest q and d.
    let mut x_to_the_q_to_the_d = pow_mod(&x, q, &monic);

    for d in 1..=total_degree {
        // The distinct irreducible factors of f whose degree divides d.
        let dividing_d = gcd(&monic, &(&x_to_the_q_to_the_d - &x));

        let mut exactly_d = dividing_d;
        for e in 1..d {
            if d % e == 0 {
                exactly_d = exactly_d.div(&distinct_of_degree[(e - 1) as usize]).0;
            }
        }
        distinct_of_degree.push(exactly_d.clone());

        if exactly_d.degree() > 0 {
            for irreducible in separate_equal_degree(&exactly_d, d, rng) {
                let multiplicity = multiplicity_in(&monic, &irreducible);
                accounted += d * multiplicity as u32;
                factors.push((irreducible, multiplicity));
            }
        }

        // Every factor is found once the degrees add up, which is usually long before d reaches
        // the degree of f.
        if accounted == total_degree {
            break;
        }

        x_to_the_q_to_the_d = pow_mod(&x_to_the_q_to_the_d, q, &monic);
    }

    debug_assert_eq!(
        accounted, total_degree,
        "factor degrees did not account for all of {}",
        monic
    );
    factors
}

/// True if `f` is irreducible over F.
///
/// Rabin's test: a monic polynomial of degree n is irreducible exactly when `x^(q^n) = x` in
/// F[x]/(f) and `gcd(x^(q^(n/p)) - x, f) = 1` for every prime p dividing n. The first condition
/// says every irreducible factor has degree dividing n; the second rules out a proper divisor.
///
/// # Panics
/// Panics if `f` is the zero polynomial.
pub fn is_irreducible<F: KnownOrder>(f: &UnivariatePolynomial<F>) -> bool {
    assert!(!f.is_zero(), "the zero polynomial is not irreducible");

    let n = f.degree();
    // A constant is a unit, not an irreducible. Degree one is always irreducible.
    if n == 0 {
        return false;
    }
    if n == 1 {
        return true;
    }

    let monic = make_monic(f);
    let x = variable::<F>();
    let q = field_order::<F>();

    if frobenius_iterated(&x, n, q, &monic) != x {
        return false;
    }

    for p in prime_divisors(n) {
        let candidate = frobenius_iterated(&x, n / p, q, &monic);
        if gcd(&monic, &(&candidate - &x)).degree() > 0 {
            return false;
        }
    }
    true
}

/// `base^(q^times) mod modulus`, by applying the Frobenius map `times` times.
///
/// Raising to `q^times` directly would overflow the exponent for all but the smallest inputs.
fn frobenius_iterated<F: KnownOrder>(
    base: &UnivariatePolynomial<F>,
    times: u32,
    q: u128,
    modulus: &UnivariatePolynomial<F>,
) -> UnivariatePolynomial<F> {
    let mut result = base.div(modulus).1;
    for _ in 0..times {
        result = pow_mod(&result, q, modulus);
    }
    result
}

/// Separate a product of distinct monic irreducibles, each of degree `d`, into those factors.
pub(crate) fn separate_equal_degree<F: KnownOrder, R: RngCore + CryptoRng>(
    g: &UnivariatePolynomial<F>,
    d: u32,
    rng: &mut R,
) -> Vec<UnivariatePolynomial<F>> {
    // One factor of degree d means g is already that factor.
    if g.degree() == d {
        return vec![g.clone()];
    }

    let (left, right) = split(g, d, rng);
    let mut factors = separate_equal_degree(&left, d, rng);
    factors.extend(separate_equal_degree(&right, d, rng));
    factors
}

/// Split a product of two or more distinct monic irreducibles of degree `d` into two parts.
fn split<F: KnownOrder, R: RngCore + CryptoRng>(
    g: &UnivariatePolynomial<F>,
    d: u32,
    rng: &mut R,
) -> (UnivariatePolynomial<F>, UnivariatePolynomial<F>) {
    debug_assert!(g.degree() > d);

    for _ in 0..MAX_SPLIT_ATTEMPTS {
        let h = random_element_of_quotient(g, rng);

        // Each irreducible factor of g independently either divides the candidate or does not,
        // so the gcd is a proper factor unless every factor falls on the same side.
        let candidate = if F::characteristic_limbs() == [2] {
            // The role of "half the elements" falls to the trace onto GF(2), there being no
            // (q^d - 1)/2 in characteristic two. The extension F[x]/(factor) has 2^(m*d)
            // elements, so the trace has m*d terms.
            trace_to_gf2(&h, g, d)
        } else {
            // The target is h^((q^d - 1)/2). Writing (q^d - 1)/2 as
            // ((q - 1)/2) * (1 + q + ... + q^(d-1)) turns it into the norm raised to (q - 1)/2,
            // both of which are computable: the exponent itself would overflow.
            &pow_mod(&frobenius_norm(&h, g, d), (field_order::<F>() - 1) / 2, g)
                - &UnivariatePolynomial::one()
        };

        // Correctness rests on this check, not on the candidate: any proper divisor of g is a
        // valid split. An error in the trace or the exponent costs attempts rather than giving a
        // wrong answer.
        let divisor = gcd(g, &candidate);
        if !divisor.is_zero() && divisor.degree() > 0 && divisor.degree() < g.degree() {
            let quotient = g.div(&divisor).0;
            return (divisor, quotient);
        }
    }

    panic!(
        "failed to split {} in {} attempts; it may not be a product of distinct irreducibles of \
         degree {}",
        g, MAX_SPLIT_ATTEMPTS, d
    );
}

/// The norm `h * h^q * h^(q^2) * ... * h^(q^(d-1))` in F[x]/(g).
fn frobenius_norm<F: KnownOrder>(
    h: &UnivariatePolynomial<F>,
    g: &UnivariatePolynomial<F>,
    d: u32,
) -> UnivariatePolynomial<F> {
    let q = field_order::<F>();
    let mut term = h.div(g).1;
    let mut norm = term.clone();
    for _ in 1..d {
        term = pow_mod(&term, q, g);
        norm = (&norm * &term).div(g).1;
    }
    norm
}

/// The absolute trace `h + h^2 + h^4 + ... + h^(2^(m*d - 1))` in F[x]/(g), for q = 2^m.
pub(crate) fn trace_to_gf2<F: KnownOrder>(
    h: &UnivariatePolynomial<F>,
    g: &UnivariatePolynomial<F>,
    d: u32,
) -> UnivariatePolynomial<F> {
    // q = 2^m, so m is the position of its single set bit.
    let m = field_order::<F>().trailing_zeros();
    let mut term = h.div(g).1;
    let mut sum = term.clone();
    for _ in 1..(m * d) {
        term = pow_mod(&term, 2, g);
        sum = &sum + &term;
    }
    sum.div(g).1
}

/// A uniformly random element of F[x]/(g), i.e. a polynomial of degree below `g`.
pub(crate) fn random_element_of_quotient<F: FiniteField, R: RngCore + CryptoRng>(
    g: &UnivariatePolynomial<F>,
    rng: &mut R,
) -> UnivariatePolynomial<F> {
    let coefficients: Vec<F> = (0..g.degree()).map(|_| F::random(rng)).collect();
    UnivariatePolynomial::new(&coefficients)
}

/// How many times `divisor` divides `p`.
fn multiplicity_in<F: FiniteField>(
    p: &UnivariatePolynomial<F>,
    divisor: &UnivariatePolynomial<F>,
) -> usize {
    debug_assert!(divisor.degree() > 0, "a constant divides infinitely often");
    let mut remaining = p.clone();
    let mut multiplicity = 0;
    loop {
        let (quotient, remainder) = remaining.div(divisor);
        if !remainder.is_zero() {
            return multiplicity;
        }
        remaining = quotient;
        multiplicity += 1;
    }
}

/// `p` scaled so that its leading coefficient is one.
pub(crate) fn make_monic<F: FiniteField>(p: &UnivariatePolynomial<F>) -> UnivariatePolynomial<F> {
    let leading = *p
        .coefficients()
        .last()
        .expect("a polynomial has at least one coefficient");
    p.scale(&leading.inverse())
}

/// The polynomial `x`.
pub(crate) fn variable<F: FiniteField>() -> UnivariatePolynomial<F> {
    UnivariatePolynomial::new(&[F::zero(), F::one()])
}

/// The distinct primes dividing `n`.
fn prime_divisors(mut n: u32) -> Vec<u32> {
    let mut divisors = Vec::new();
    let mut d = 2;
    while d * d <= n {
        if n.is_multiple_of(d) {
            divisors.push(d);
            while n.is_multiple_of(d) {
                n /= d;
            }
        }
        d += 1;
    }
    if n > 1 {
        divisors.push(n);
    }
    divisors
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use rand::{prelude::StdRng, SeedableRng};

    use crate::{
        fields::PrimeFieldElement64,
        identities::Zero,
        poly::univariate::{
            factorize::{factorize, is_irreducible},
            roots, Polynomial, UnivariatePolynomial,
        },
        FiniteField,
    };

    fn poly<const P: u64>(coefficients: &[u64]) -> UnivariatePolynomial<PrimeFieldElement64<P>> {
        UnivariatePolynomial::new(
            &coefficients
                .iter()
                .map(|c| PrimeFieldElement64::<P>::new(*c))
                .collect::<Vec<_>>(),
        )
    }

    /// Every monic polynomial of degree `n` over GF(P).
    fn monic_polynomials<const P: u64>(
        n: u32,
    ) -> Vec<UnivariatePolynomial<PrimeFieldElement64<P>>> {
        let mut result = Vec::new();
        let count = P.pow(n);
        for index in 0..count {
            let mut coefficients: Vec<u64> = (0..n).map(|i| index / P.pow(i) % P).collect();
            coefficients.push(1);
            result.push(poly::<P>(&coefficients));
        }
        result
    }

    /// True if no monic polynomial of degree 1..=n/2 divides `f`.
    ///
    /// The definition of irreducibility, applied directly. Shares nothing with Rabin's test: no
    /// modular exponentiation, no gcd.
    fn irreducible_by_trial_division<const P: u64>(
        f: &UnivariatePolynomial<PrimeFieldElement64<P>>,
    ) -> bool {
        let n = f.degree();
        if n == 0 {
            return false;
        }
        for d in 1..=n / 2 {
            for divisor in monic_polynomials::<P>(d) {
                if f.div(&divisor).1.is_zero() {
                    return false;
                }
            }
        }
        true
    }

    /// `is_irreducible` agrees with trial division on every monic polynomial of low degree.
    #[test]
    fn test_is_irreducible_agrees_with_trial_division() {
        fn check<const P: u64>(max_degree: u32) {
            for n in 1..=max_degree {
                for f in monic_polynomials::<P>(n) {
                    assert_eq!(
                        is_irreducible(&f),
                        irreducible_by_trial_division::<P>(&f),
                        "{} over GF({})",
                        f,
                        P
                    );
                }
            }
        }
        check::<2>(6);
        check::<3>(4);
        check::<5>(3);
        check::<7>(3);
    }

    /// A constant is a unit rather than an irreducible.
    #[test]
    fn test_constants_are_not_irreducible() {
        for c in 1..7u64 {
            assert!(!is_irreducible(&poly::<7>(&[c])));
        }
    }

    /// The factors multiply back to the polynomial, and each one is irreducible.
    ///
    /// Taken together these are a complete check rather than a sample: factorization over a field
    /// is unique up to units, so a product of irreducibles that reconstructs f *is* the
    /// factorization.
    #[test]
    fn test_factorize_reconstructs_the_polynomial() {
        fn check<const P: u64>(seed: u64) {
            let mut rng = StdRng::seed_from_u64(seed);
            for n in 1..=5u32 {
                for f in monic_polynomials::<P>(n) {
                    let factors = factorize(&f, &mut rng);
                    assert!(!factors.is_empty(), "{} has no factors", f);

                    let product = factors.iter().fold(
                        UnivariatePolynomial::<PrimeFieldElement64<P>>::one(),
                        |acc, (factor, multiplicity)| acc * factor.pow(*multiplicity as u32),
                    );
                    assert_eq!(product, f, "factors of {} do not multiply back", f);

                    for (factor, multiplicity) in &factors {
                        assert!(is_irreducible(factor), "{} is not irreducible", factor);
                        assert!(*multiplicity >= 1);
                    }
                }
            }
        }
        check::<2>(1);
        check::<3>(2);
        check::<5>(3);
    }

    /// Factors built by hand are recovered exactly, multiplicities included.
    #[test]
    fn test_factorize_recovers_known_factors() {
        const P: u64 = 7;
        let mut rng = StdRng::seed_from_u64(11);

        // x, x + 1, and x^2 + 1 — the last irreducible over GF(7), as asserted below.
        let a = poly::<P>(&[0, 1]);
        let b = poly::<P>(&[1, 1]);
        let c = poly::<P>(&[1, 0, 1]);
        assert!(is_irreducible(&c));

        let expected = [(a.clone(), 3usize), (b.clone(), 1), (c.clone(), 2)];
        let f = a.pow(3) * b.pow(1) * c.pow(2);

        let mut found = factorize(&f, &mut rng);
        found.sort_by_key(|(factor, _)| factor.degree());
        let found: HashSet<(Vec<u64>, usize)> = found
            .into_iter()
            .map(|(factor, m)| (factor.coefficients().iter().map(|c| c.value()).collect(), m))
            .collect();
        let expected: HashSet<(Vec<u64>, usize)> = expected
            .into_iter()
            .map(|(factor, m)| (factor.coefficients().iter().map(|c| c.value()).collect(), m))
            .collect();
        assert_eq!(found, expected);
    }

    /// A pure p-th power in characteristic p, where the derivative vanishes.
    ///
    /// The usual route to factorization starts from `gcd(f, f')`, which gives no information
    /// here: the derivative of x^5 over GF(5) is 5x^4 = 0. Collecting factors by
    /// `gcd(f, x^(q^d) - x)` instead sidesteps that entirely.
    #[test]
    fn test_factorize_a_pure_power_in_characteristic_p() {
        const P: u64 = 5;
        let mut rng = StdRng::seed_from_u64(13);

        // x^5, whose derivative is zero.
        let x = poly::<P>(&[0, 1]);
        assert_eq!(factorize(&x.pow(5), &mut rng), vec![(x.clone(), 5)]);

        // (x + 1)^5, likewise, with a multiplicity divisible by the characteristic.
        let shifted = poly::<P>(&[1, 1]);
        assert_eq!(
            factorize(&shifted.pow(5), &mut rng),
            vec![(shifted.clone(), 5)]
        );

        // And a mixture of a p-th power with another factor.
        let f = x.pow(5) * shifted.pow(2);
        let mut found = factorize(&f, &mut rng);
        found.sort_by_key(|(factor, _)| factor.coefficients()[0].value());
        assert_eq!(found, vec![(x, 5), (shifted, 2)]);
    }

    /// x^q - x splits into every linear factor exactly once.
    #[test]
    fn test_factorize_x_to_the_q_minus_x() {
        const P: u64 = 11;
        let mut rng = StdRng::seed_from_u64(17);
        let mut coefficients = vec![0u64; 12];
        coefficients[11] = 1;
        coefficients[1] = P - 1;
        let f = poly::<P>(&coefficients);

        let factors = factorize(&f, &mut rng);
        assert_eq!(factors.len(), P as usize);
        for (factor, multiplicity) in &factors {
            assert_eq!(factor.degree(), 1);
            assert_eq!(*multiplicity, 1);
        }
    }

    /// An irreducible polynomial factors into itself.
    #[test]
    fn test_factorize_an_irreducible_polynomial() {
        const P: u64 = 7;
        let mut rng = StdRng::seed_from_u64(19);
        let f = poly::<P>(&[1, 0, 1]); // x^2 + 1, irreducible over GF(7)
        assert!(is_irreducible(&f));
        assert_eq!(factorize(&f, &mut rng), vec![(f.clone(), 1)]);
    }

    /// The degree-one factors are exactly the roots.
    #[test]
    fn test_linear_factors_match_the_roots() {
        const P: u64 = 13;
        let mut rng = StdRng::seed_from_u64(23);
        let candidates: Vec<Vec<u64>> = vec![
            vec![P - 1, 0, 1],
            vec![0, 0, 1],
            vec![1, 2, 3, 4],
            vec![P - 1, 0, 0, 1],
            vec![1, 1, 1, 1, 1],
            vec![1, 0, 1],
        ];
        for coefficients in &candidates {
            let f = poly::<P>(coefficients);
            let from_factors: HashSet<_> = factorize(&f, &mut rng)
                .into_iter()
                .filter(|(factor, _)| factor.degree() == 1)
                // monic x - a, so the root is -c_0
                .map(|(factor, _)| PrimeFieldElement64::<P>::zero() - factor.coefficients()[0])
                .collect();
            let from_roots: HashSet<_> = roots(&f, &mut rng).into_iter().collect();
            assert_eq!(from_factors, from_roots, "{:?}", coefficients);
        }
    }

    /// A nonzero constant has no factorization, and zero is rejected.
    #[test]
    fn test_factorize_edge_cases() {
        let mut rng = StdRng::seed_from_u64(29);
        assert!(factorize(&poly::<7>(&[3]), &mut rng).is_empty());
    }

    #[test]
    #[should_panic(expected = "zero polynomial has no factorization")]
    fn test_factorize_zero_panics() {
        let mut rng = StdRng::seed_from_u64(31);
        let _ = factorize(
            &UnivariatePolynomial::<PrimeFieldElement64<7>>::zero(),
            &mut rng,
        );
    }
}
