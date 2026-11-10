//! Power permutations `x -> x^d` of a finite field, which is what an arithmetization-friendly
//! S-box is.
//!
//! The map is a bijection of GF(q) exactly when `gcd(d, q - 1) = 1`: it fixes zero, and on the
//! multiplicative group — cyclic of order `q - 1` — raising to the `d`th power is injective
//! precisely when `d` is invertible modulo the group order. That inverse is the exponent of the
//! **compositional inverse**, since `(x^d)^e = x^{de} = x` when `de = 1 (mod q - 1)`. So the test,
//! the enumeration of admissible exponents, and the inverse map are all the same piece of
//! arithmetic modulo `q - 1`.
//!
//! This is the whole of what the hash work needs: Poseidon's S-box is `x^alpha`, and a model of it
//! carries `alpha` as a parameter whose admissibility needs checking. Which exponents a field admits is also what a parameter sweep over `alpha` has to
//! know before it starts.
//!
//! # What is deliberately not here
//!
//! Deciding whether an *arbitrary* polynomial permutes GF(q) — Hermite's criterion, and families
//! such as the Dickson polynomials — is a much larger subject than the S-box question, and none of
//! it is implemented. [`is_permutation_polynomial`] therefore returns `Option<bool>`, and answers
//! only for the shapes that need no work: monomials and affine polynomials.
//!
//! # Exponents and the `u128` ceiling
//!
//! Exponents are `u128` because [`FiniteField::pow`](crate::FiniteField::pow) takes a `u128`, so a
//! power map over a field whose order exceeds that is not expressible anyway. The 254- and 255-bit
//! prime fields are therefore out of reach here, which [`PowerPermutation::new`] says by panicking
//! and [`is_permutation_polynomial`] by declining to decide.

use std::marker::PhantomData;

use crate::{
    integers::{gcd_u128, mod_inverse_u128},
    poly::univariate::{Polynomial, UnivariatePolynomial},
    KnownOrder,
};

/// Whether `x -> x^d` permutes a field of order `q`.
///
/// # Panics
/// Panics if `q < 2`, which is not the order of a field.
pub fn is_permutation_exponent(d: u128, q: u128) -> bool {
    assert!(q >= 2, "{} is not the order of a finite field", q);

    // `x^0` is the constant 1, and it is the one case the gcd does not catch: gcd(0, q - 1) is
    // q - 1, which is 1 over GF(2).
    d >= 1 && gcd_u128(d, q - 1) == 1
}

/// The exponents `d` for which `x -> x^d` permutes a field of order `q`, ascending.
///
/// One representative per distinct map: `x^d` and `x^{d + (q - 1)}` agree everywhere, so the
/// exponents yielded are the admissible residues in `1..=q-2` — plus the identity exponent when
/// `q = 2`, where that range is empty and `1` is the only residue modulo `q - 1 = 1`.
///
/// Lazy, and `q` may be large: over a 31-bit field the iterator has around `2^31` items, so a
/// caller after the small exponents an S-box would use should stop early rather than collect.
///
/// # Panics
/// Panics if `q < 2`.
pub fn permutation_exponents(q: u128) -> impl Iterator<Item = u128> {
    assert!(q >= 2, "{} is not the order of a finite field", q);
    (1..=(q - 2).max(1)).filter(move |&d| gcd_u128(d, q - 1) == 1)
}

/// The exponent of the compositional inverse of `x -> x^d` over a field of order `q`: the `e` with
/// `x^{de} = x` for every `x`. `None` if `x^d` is not a permutation.
///
/// `e` is the inverse of `d` modulo `q - 1`, taken in `1..=q-1` rather than in `0..q-1`, since a
/// zero exponent would be the constant map and not the inverse. The two differ only over GF(2).
///
/// # Panics
/// Panics if `q < 2`.
pub fn inverse_exponent(d: u128, q: u128) -> Option<u128> {
    if !is_permutation_exponent(d, q) {
        return None;
    }
    let group_order = q - 1;
    let e = mod_inverse_u128(d, group_order)?;
    Some(if e == 0 { group_order } else { e })
}

/// Whether `f` permutes the field, or `None` if that is not decided here.
///
/// Decided for the two shapes whose answer is immediate:
///
/// * `c x^d` with `c != 0` permutes iff `x^d` does, scaling by a nonzero constant being a
///   bijection. Needs the order as a `u128`, so a wider field is undecided.
/// * `a x + b` with `a != 0` permutes every field; a constant (including zero) permutes none.
///
/// Everything else returns `None`. Deciding the general case is a separate subject — see the
/// module documentation — and the absence of a general test is why this is not a `bool`.
pub fn is_permutation_polynomial<F: KnownOrder>(f: &UnivariatePolynomial<F>) -> Option<bool> {
    // The zero polynomial and the nonzero constants are constant maps, and a field has at least
    // two elements.
    if f.is_zero() || f.degree() == 0 {
        return Some(false);
    }

    // Affine with nonzero slope — the leading coefficient of a trimmed polynomial is nonzero.
    if f.degree() == 1 {
        return Some(true);
    }

    let mut exponents = f
        .coefficients()
        .iter()
        .enumerate()
        .filter(|(_i, c)| !c.is_zero())
        .map(|(i, _c)| i as u128);
    let d = exponents.next()?;
    if exponents.next().is_some() {
        // Two or more terms: not a monomial.
        return None;
    }

    Some(is_permutation_exponent(d, F::order_u128()?))
}

/// A power permutation `x -> x^d` of a finite field, with its compositional inverse.
///
/// Constructing one establishes that the exponent is admissible, which is the property the rest of
/// the type assumes: [`Self::invert`] is the inverse map and not an approximation of one.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct PowerPermutation<F> {
    /// The exponent `d`, as given.
    exponent: u128,

    /// `d^-1 mod (q - 1)`, in `1..=q-1`.
    inverse_exponent: u128,

    field: PhantomData<F>,
}

impl<F: KnownOrder> PowerPermutation<F> {
    /// The power permutation `x -> x^exponent`, or `None` if that map is not a permutation of F.
    ///
    /// # Panics
    /// Panics if the order of F does not fit in a `u128`.
    pub fn new(exponent: u128) -> Option<Self> {
        let q = F::order_u128().expect(
            "deciding whether a power map permutes the field needs the order as an integer",
        );
        Some(Self {
            exponent,
            inverse_exponent: inverse_exponent(exponent, q)?,
            field: PhantomData,
        })
    }

    /// The exponent `d`, as it was given to [`Self::new`].
    pub fn exponent(&self) -> u128 {
        self.exponent
    }

    /// The exponent of the compositional inverse. See [`inverse_exponent`].
    pub fn inverse_exponent(&self) -> u128 {
        self.inverse_exponent
    }

    /// `x^d`.
    pub fn apply(&self, x: &F) -> F {
        x.pow(self.exponent)
    }

    /// The `y` preimage: `y^e`, where `e` is the inverse exponent.
    pub fn invert(&self, y: &F) -> F {
        y.pow(self.inverse_exponent)
    }

    /// The compositional inverse, which is itself a power permutation.
    pub fn inverse(&self) -> Self {
        Self {
            exponent: self.inverse_exponent,
            inverse_exponent: self.exponent,
            field: PhantomData,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use rand::{prelude::StdRng, SeedableRng};

    use crate::{
        fields::{BabyBear, Bn254Fr, KoalaBear, Mersenne31, PrimeFieldElement64, Zp7},
        identities::{One, Zero},
        integers::gcd_u128,
        poly::univariate::{
            power_permutation::{
                inverse_exponent, is_permutation_exponent, is_permutation_polynomial,
                permutation_exponents, PowerPermutation,
            },
            Polynomial, UnivariatePolynomial,
        },
        FiniteField, KnownOrder,
    };

    /// Is `x -> x^d` a bijection of GF(P), decided by applying it to every element?
    ///
    /// Shares no code with `is_permutation_exponent`: no gcd, only the field's own arithmetic.
    fn is_bijection<const P: u64>(d: u128) -> bool {
        let images: HashSet<PrimeFieldElement64<P>> = (0..P)
            .map(|x| PrimeFieldElement64::<P>::new(x).pow(d))
            .collect();
        images.len() == P as usize
    }

    fn poly<const P: u64>(coefficients: &[u64]) -> UnivariatePolynomial<PrimeFieldElement64<P>> {
        UnivariatePolynomial::new(
            &coefficients
                .iter()
                .map(|c| PrimeFieldElement64::<P>::new(*c))
                .collect::<Vec<_>>(),
        )
    }

    /// `is_permutation_exponent` agrees with applying `x -> x^d` to every field element, over a
    /// range of exponents that runs past `q - 1` so that reduction modulo the group order is
    /// exercised too.
    #[test]
    fn test_permutation_exponents_agree_with_brute_force() {
        fn check<const P: u64>() {
            for d in 0..(2 * P as u128 + 3) {
                assert_eq!(
                    is_permutation_exponent(d, P as u128),
                    is_bijection::<P>(d),
                    "x^{} over GF({})",
                    d,
                    P
                );
            }
        }
        check::<2>();
        check::<3>();
        check::<5>();
        check::<7>();
        check::<11>();
        check::<13>();
        check::<17>();
    }

    /// The zero exponent is the constant map, including over GF(2), where gcd(0, q - 1) = 1 would
    /// wrongly admit it.
    #[test]
    fn test_the_zero_exponent_is_never_a_permutation() {
        assert!(!is_permutation_exponent(0, 2));
        assert!(!is_permutation_exponent(0, 7));
    }

    /// `permutation_exponents` enumerates exactly the admissible residues in 1..=q-2, which over
    /// GF(7) are 1 and 5.
    #[test]
    fn test_permutation_exponents_enumerates_the_admissible_residues() {
        assert_eq!(permutation_exponents(7).collect::<Vec<_>>(), vec![1, 5]);
        assert_eq!(permutation_exponents(5).collect::<Vec<_>>(), vec![1, 3]);
        // q - 1 = 1, so the only residue is the identity exponent.
        assert_eq!(permutation_exponents(2).collect::<Vec<_>>(), vec![1]);
        assert_eq!(permutation_exponents(3).collect::<Vec<_>>(), vec![1]);
    }

    /// Everything `permutation_exponents` yields is a permutation, and nothing it skips is.
    #[test]
    fn test_permutation_exponents_is_exactly_the_admissible_set() {
        fn check<const P: u64>() {
            let enumerated: HashSet<u128> = permutation_exponents(P as u128).collect();
            for d in 1..=(P as u128 - 2).max(1) {
                assert_eq!(enumerated.contains(&d), is_bijection::<P>(d));
            }
        }
        check::<7>();
        check::<13>();
        check::<17>();
    }

    /// The inverse exponent undoes the power map at every element of the field.
    #[test]
    fn test_inverse_exponent_round_trips_over_every_element() {
        fn check<const P: u64>() {
            for d in permutation_exponents(P as u128) {
                let e = inverse_exponent(d, P as u128).unwrap();
                for x in (0..P).map(PrimeFieldElement64::<P>::new) {
                    assert_eq!(x.pow(d).pow(e), x, "x^({} * {}) over GF({})", d, e, P);
                }
            }
        }
        check::<2>();
        check::<7>();
        check::<13>();
        check::<17>();
    }

    /// An exponent that is not a permutation has no inverse exponent.
    #[test]
    fn test_inverse_exponent_rejects_a_non_permutation() {
        assert_eq!(inverse_exponent(2, 7), None); // gcd(2, 6) = 2
        assert_eq!(inverse_exponent(0, 7), None);
    }

    /// KoalaBear admits the Poseidon challenge's S-box exponent: p - 1 = 2^24 * 127, which 3 does
    /// not divide, and 3 * 1420470955 = 1 (mod p - 1).
    #[test]
    fn test_koalabear_admits_the_poseidon_sbox_exponent() {
        let q = KoalaBear::order_u128().unwrap();
        assert_eq!(q - 1, (1 << 24) * 127);
        assert!(is_permutation_exponent(3, q));
        let e = inverse_exponent(3, q).unwrap();
        assert_eq!(e, 1420470955);
        assert_eq!(3 * e % (q - 1), 1);
        // 127 divides p - 1, so the 127th power map collapses.
        assert!(!is_permutation_exponent(127, q));
    }

    /// BabyBear rejects the cube map — 3 divides p - 1 = 2^27 * 3 * 5 — and the smallest
    /// admissible exponent above 1 is 7.
    #[test]
    fn test_babybear_rejects_the_cube_map() {
        let q = BabyBear::order_u128().unwrap();
        assert_eq!(q - 1, (1 << 27) * 15);
        assert!(!is_permutation_exponent(3, q));
        assert!(!is_permutation_exponent(5, q));
        assert_eq!(
            permutation_exponents(q).find(|&d| d > 1),
            Some(7),
            "the smallest S-box exponent above the identity"
        );
    }

    /// Mersenne31 rejects the cube map and admits the fifth power.
    #[test]
    fn test_mersenne31_rejects_the_cube_map_and_admits_the_fifth_power() {
        let q = Mersenne31::order_u128().unwrap();
        assert_eq!(gcd_u128(3, q - 1), 3);
        assert!(!is_permutation_exponent(3, q));
        assert!(is_permutation_exponent(5, q));
    }

    /// A `PowerPermutation` and its inverse undo each other on random elements of a 31-bit field,
    /// where brute force is out of reach.
    #[test]
    fn test_power_permutation_round_trips_over_koalabear() {
        let mut rng = StdRng::seed_from_u64(0);
        let sbox = PowerPermutation::<KoalaBear>::new(3).unwrap();
        for _ in 0..1000 {
            let x = KoalaBear::random(&mut rng);
            assert_eq!(sbox.invert(&sbox.apply(&x)), x);
            assert_eq!(sbox.apply(&sbox.invert(&x)), x);
        }
    }

    /// A non-permutation exponent yields no `PowerPermutation`.
    #[test]
    fn test_power_permutation_rejects_a_non_permutation_exponent() {
        assert!(PowerPermutation::<BabyBear>::new(3).is_none());
        assert!(PowerPermutation::<BabyBear>::new(7).is_some());
    }

    /// The compositional inverse is itself a power permutation, with the exponents exchanged.
    #[test]
    fn test_power_permutation_inverse_exchanges_the_exponents() {
        let sbox = PowerPermutation::<KoalaBear>::new(3).unwrap();
        let inverse = sbox.inverse();
        assert_eq!(inverse.exponent(), sbox.inverse_exponent());
        assert_eq!(inverse.inverse_exponent(), sbox.exponent());

        let mut rng = StdRng::seed_from_u64(1);
        for _ in 0..100 {
            let x = KoalaBear::random(&mut rng);
            assert_eq!(inverse.apply(&x), sbox.invert(&x));
        }
    }

    /// A field whose order exceeds a `u128` cannot report an exponent's admissibility.
    #[test]
    #[should_panic(expected = "needs the order as an integer")]
    fn test_power_permutation_panics_for_an_order_wider_than_a_u128() {
        let _ = PowerPermutation::<Bn254Fr>::new(5);
    }

    /// A monomial is decided by its exponent, whatever its nonzero leading coefficient.
    #[test]
    fn test_is_permutation_polynomial_decides_monomials() {
        // x^5 over GF(7): gcd(5, 6) = 1.
        assert_eq!(
            is_permutation_polynomial(&poly::<7>(&[0, 0, 0, 0, 0, 1])),
            Some(true)
        );
        // 3x^5 is the same map composed with a nonzero scaling.
        assert_eq!(
            is_permutation_polynomial(&poly::<7>(&[0, 0, 0, 0, 0, 3])),
            Some(true)
        );
        // x^3 over GF(7): gcd(3, 6) = 3.
        assert_eq!(
            is_permutation_polynomial(&poly::<7>(&[0, 0, 0, 1])),
            Some(false)
        );
    }

    /// An affine polynomial with nonzero slope permutes every field, and a constant permutes none.
    #[test]
    fn test_is_permutation_polynomial_decides_affine_polynomials() {
        assert_eq!(is_permutation_polynomial(&poly::<7>(&[3, 2])), Some(true));
        assert_eq!(is_permutation_polynomial(&poly::<7>(&[3])), Some(false));
        assert_eq!(
            is_permutation_polynomial(&UnivariatePolynomial::<Zp7>::zero()),
            Some(false)
        );
        // Affine needs no order, so it is decided even over a 254-bit field.
        let f = UnivariatePolynomial::<Bn254Fr>::new(&[Bn254Fr::new(3), Bn254Fr::new(2)]);
        assert_eq!(is_permutation_polynomial(&f), Some(true));
    }

    /// Nothing outside those two shapes is decided: the general test is deliberately absent.
    #[test]
    fn test_is_permutation_polynomial_declines_the_general_case() {
        // x^2 + x + 1 over GF(7) is in fact not a permutation, but deciding that needs Hermite's
        // criterion or an enumeration, neither of which is here.
        assert_eq!(is_permutation_polynomial(&poly::<7>(&[1, 1, 1])), None);
        // x^3 + x over GF(7), which happens to be a permutation, is equally undecided.
        assert_eq!(is_permutation_polynomial(&poly::<7>(&[0, 1, 0, 1])), None);
    }

    /// The monomial case is undecided when the field's order does not fit in a `u128`.
    #[test]
    fn test_is_permutation_polynomial_declines_a_wide_field() {
        let mut coefficients = vec![Bn254Fr::zero(); 6];
        coefficients[5] = Bn254Fr::one();
        let f = UnivariatePolynomial::<Bn254Fr>::new(&coefficients);
        assert_eq!(is_permutation_polynomial(&f), None);
    }
}
