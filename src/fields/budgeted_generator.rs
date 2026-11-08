//! A generator of a field's multiplicative group, found under an explicit effort budget.
//!
//! [`KnownOrder::try_primitive_element`] has nowhere to put an effort bound, so the fields whose
//! `q - 1` is too wide to factor casually decline to search at all — see
//! `PrimeFieldElement256`'s override, which returns
//! [`RootOfUnityError::NoKnownGenerator`](super::RootOfUnityError::NoKnownGenerator). The
//! factoring half is no longer missing (Lenstra ECM, `integers::prime_factors::ecm`), but the
//! reason for the refusal was never only that it was missing: factoring a 254-bit integer is a
//! computation a caller must *ask* for. So this is a separate entry point that takes an
//! [`EcmBudget`], and that reports a budget which did not finish rather than guessing past it.
//!
//! The search itself is HAC Algorithm 4.80 — the same one
//! [`KnownOrder::try_primitive_element`]'s default runs — lifted off `u128` exponents onto
//! [`crate::FiniteField::pow_limbs`] so that it reaches a field whose order a `u128` cannot hold.

use rand::{CryptoRng, RngCore};
use std::fmt::{Display, Formatter};

use crate::{
    integers::{big_uint::BigUInt, factor_with_budget, EcmBudget},
    KnownOrder,
};

/// How many candidates the random search draws before reporting failure.
///
/// Generators have density `phi(q - 1) / (q - 1)`, which is bounded below by roughly
/// `1 / (e^gamma ln ln (q-1))` — above 1/14 for every order this crate can represent. So 256
/// draws miss with probability under `(13/14)^256 < 2^-26`, and the bound exists to keep the
/// search terminating rather than because it is expected to be reached.
const MAX_CANDIDATES: usize = 256;

/// Why a budgeted generator search did not produce a generator.
///
/// Both variants are honest failures rather than "this field has none": the multiplicative group
/// of a finite field is always cyclic, so a generator always exists.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GeneratorSearchError {
    /// The budget ran out before `q - 1` was fully factored, leaving these composite cofactors.
    ///
    /// Carried rather than discarded because it says what a larger budget would have to split,
    /// and because a partial factorization cannot certify a generator: an untested prime factor
    /// is a divisor of `q - 1` whose quotient the candidate might fix.
    IncompleteFactorization {
        /// The cofactors [`factor_with_budget`] could not split, in increasing order.
        unfactored: Vec<BigUInt>,
    },
    /// `q - 1` was factored, but no generator turned up in [`MAX_CANDIDATES`] draws.
    SearchExhausted {
        /// How many candidates were tested.
        candidates: usize,
    },
}

impl Display for GeneratorSearchError {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IncompleteFactorization { unfactored } => {
                let cofactors: Vec<String> = unfactored.iter().map(BigUInt::to_dec_str).collect();
                write!(
                    formatter,
                    "the effort budget did not finish factoring q - 1; unsplit cofactors: {}",
                    cofactors.join(", ")
                )
            }
            Self::SearchExhausted { candidates } => write!(
                formatter,
                "no generator found in {candidates} candidates, though q - 1 was fully factored"
            ),
        }
    }
}

impl std::error::Error for GeneratorSearchError {}

/// A generator of `F`'s multiplicative group, or the reason the budget could not certify one.
///
/// `q - 1` is factored with [`factor_with_budget`], then candidates are drawn at random and tested
/// against the prime divisors: an element fails to generate exactly when its order is a proper
/// divisor of `q - 1`, and every proper divisor divides `(q - 1) / r` for some prime `r | q - 1`,
/// so those quotients are the only exponents worth testing (HAC Algorithm 4.80).
///
/// The returned element is certified against the **complete** factorization, which is why an
/// exhausted budget is an error and not a weaker guarantee.
///
/// # Cost, and why it is not a function of the field's width
/// One ECM factorization of `q - 1` at `budget`, then about one exponentiation per distinct prime
/// divisor per candidate. The factorization dominates, and what it costs depends on the largest
/// prime factor of `q - 1` rather than on how wide `q` is. The crate's two 255-bit scalar fields
/// are worlds apart on exactly that:
///
/// * **BLS12-381's** `r - 1 = 2^32 * 3 * 11 * 19 * 10177 * 125527 * 859267 * 906349^2 * 2508409 *
///   2529403 * 52437899 * 254760293^2` — nine decimal digits at worst, so
///   `EcmBudget::for_digits(9)` certifies a generator there.
/// * **BN254's** `r - 1` has a 29-digit prime factor, which is past what this ECM reaches in any
///   time worth spending: its inner loop is a [`BigUInt`] multiply and remainder rather than
///   Montgomery arithmetic. That field gets [`GeneratorSearchError::IncompleteFactorization`] and
///   the cofactor it would have to split.
///
/// So the budget is the caller's to choose, and [`EcmBudget::for_digits`] is parameterized by the
/// decimal digits of the largest prime factor expected.
pub fn try_primitive_element_with_budget<F: KnownOrder, R: RngCore + CryptoRng>(
    budget: &EcmBudget,
    rng: &mut R,
) -> Result<F, GeneratorSearchError> {
    let group_order = &BigUInt::new(F::order_limbs()) - &BigUInt::one();
    let factorization = factor_with_budget(&group_order, budget, rng);
    if !factorization.is_complete() {
        return Err(GeneratorSearchError::IncompleteFactorization {
            unfactored: factorization
                .unfactored
                .iter()
                .map(|(cofactor, _power)| cofactor.clone())
                .collect(),
        });
    }

    // One quotient per distinct prime divisor, formed once and reused across candidates: the
    // multiplicities do not matter, since an order dividing `(q-1)/r^e` divides `(q-1)/r` too.
    let exponents: Vec<Vec<u64>> = factorization
        .primes
        .iter()
        .map(|r| (&group_order / r).as_le_words().to_vec())
        .collect();

    // A non-generator's order divides one of the quotients, so each draw is an independent trial.
    for _ in 0..MAX_CANDIDATES {
        let g = F::random(rng);
        if g.is_zero() {
            continue;
        }
        if exponents
            .iter()
            .all(|exponent| g.pow_limbs(exponent) != F::one())
        {
            return Ok(g);
        }
    }

    Err(GeneratorSearchError::SearchExhausted {
        candidates: MAX_CANDIDATES,
    })
}

#[cfg(test)]
mod tests {
    use rand::{prelude::StdRng, SeedableRng};

    use super::{try_primitive_element_with_budget, GeneratorSearchError};
    use crate::{
        fields::{Bls12_381Fr, Bn254Fr, RootOfUnityError, Zp1091, Zp13},
        integers::EcmBudget,
        FiniteField, KnownOrder, One,
    };

    /// Over a small field the budgeted search returns an element whose order is the group order.
    #[test]
    fn test_a_small_field_yields_a_certified_generator() {
        let mut rng = StdRng::seed_from_u64(1);
        let g: Zp13 =
            try_primitive_element_with_budget(&EcmBudget::for_digits(10), &mut rng).unwrap();
        assert!(g.is_generator(&mut rng));
        // Order exactly 12: no proper divisor of 12 is the order.
        assert!(g.pow(12).is_one());
        for e in 1..12 {
            assert!(!g.pow(e).is_one(), "{g:?} has order {e}, not 12");
        }
    }

    /// The budgeted search agrees with the crate's independent generator test over Zp1091.
    #[test]
    fn test_the_budgeted_search_agrees_with_is_generator() {
        let mut rng = StdRng::seed_from_u64(2);
        for _ in 0..8 {
            let g: Zp1091 =
                try_primitive_element_with_budget(&EcmBudget::for_digits(10), &mut rng).unwrap();
            assert!(g.is_generator(&mut rng));
        }
    }

    /// A budget too small to split q - 1 reports the cofactors it could not split, not a guess.
    #[test]
    fn test_an_exhausted_budget_reports_the_unsplit_cofactors() {
        let mut rng = StdRng::seed_from_u64(3);
        // Zero curves cannot split anything trial division misses. Zp1091's group order is
        // 1090 = 2 * 5 * 109, all in the small-prime table, so a field whose q - 1 has a factor
        // past the table is needed: BN254's r - 1 has a 29-digit prime factor.
        let no_effort = EcmBudget {
            b1: 100,
            b2: 0,
            curves: 0,
        };
        let result = try_primitive_element_with_budget::<Bn254Fr, _>(&no_effort, &mut rng);
        match result {
            Err(GeneratorSearchError::IncompleteFactorization { unfactored }) => {
                assert!(!unfactored.is_empty());
            }
            other => panic!("expected an incomplete factorization, got {other:?}"),
        }
    }

    /// BLS12-381's scalar field gets a generator: r - 1 factors into nine-digit primes at worst.
    ///
    /// This is the point of the issue — a 255-bit field that `try_primitive_element` declines, and
    /// that the budgeted entry point can certify.
    #[test]
    fn test_the_bls12_381_scalar_field_gets_a_certified_generator() {
        let mut rng = StdRng::seed_from_u64(5);
        let g: Bls12_381Fr = try_primitive_element_with_budget(&EcmBudget::for_digits(9), &mut rng)
            .expect("r - 1 is 2^32 * small primes, the largest of nine digits");

        // Certified independently of the search: g^((q-1)/2) = -1 is necessary for a generator,
        // and g^(q-1) = 1 is Fermat. `is_generator` is not available here — it needs the order in
        // a u128 — so the two-adic part is checked directly, which is the half a 2^32 factor makes
        // cheap and the half a non-generator is overwhelmingly likely to fail.
        let (two_adicity, odd_part) =
            crate::fields::two_adic::two_adic_decomposition(Bls12_381Fr::order_limbs());
        assert_eq!(two_adicity, 32);
        let mut w = g.pow_limbs(&odd_part);
        for _ in 0..two_adicity - 1 {
            assert!(
                !w.is_one(),
                "g^odd has order below 2^32, so g is no generator"
            );
            w = &w * &w;
        }
        assert!(!w.is_one());
        w = &w * &w;
        assert!(w.is_one(), "g^(q-1) must be one");
    }

    /// `try_primitive_element` still declines, so nothing starts a 254-bit factorization by
    /// accident.
    #[test]
    fn test_the_trait_method_still_declines_to_search() {
        let mut rng = StdRng::seed_from_u64(7);
        assert_eq!(
            Bls12_381Fr::try_primitive_element(&mut rng),
            Err(RootOfUnityError::NoKnownGenerator)
        );
        assert_eq!(
            Bn254Fr::try_primitive_element(&mut rng),
            Err(RootOfUnityError::NoKnownGenerator)
        );
    }
}
