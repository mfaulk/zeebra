/// Run one test body over every field implementation in the crate.
///
/// Coverage was uneven by accident: a trait law tested for `PrimeFieldElement64` was usually not
/// tested for `BinaryFieldElement` unless someone remembered to copy the test. The body is written
/// once, generic over `F: KnownOrder + Arbitrary`, and expands to one `#[test]` per field named after that
/// field, so a failure says which one.
///
/// The list spans every implementation family — the four prime field widths, a binary field and an
/// extension field — and within the prime fields the moduli whose structure differs: a Mersenne
/// prime of two-adicity 1, two NTT-friendly primes, and the two 254-bit fields.
///
/// ```ignore
/// for_each_field!(fn inverse_undoes_multiplication<F>() {
///     let mut rng = StdRng::seed_from_u64(1);
///     let a = F::random(&mut rng);
///     if !a.is_zero() {
///         assert!((a * a.inverse()).is_one());
///     }
/// });
/// ```
///
/// Use [`for_each_small_field!`](crate::for_each_small_field) instead for a body that enumerates the field.
#[macro_export]
macro_rules! for_each_field {
    (fn $name:ident<$type_parameter:ident>() $body:block) => {
        mod $name {
            #[allow(unused_imports)]
            use super::*;

            fn body<$type_parameter: $crate::KnownOrder + ::proptest::arbitrary::Arbitrary>() $body

            $crate::for_each_field_test!(body, zp31, $crate::fields::Zp31);
            $crate::for_each_field_test!(body, koala_bear, $crate::fields::KoalaBear);
            $crate::for_each_field_test!(body, mersenne31, $crate::fields::Mersenne31);
            $crate::for_each_field_test!(body, zp13, $crate::fields::Zp13);
            $crate::for_each_field_test!(body, zp65537, $crate::fields::Zp65537);
            $crate::for_each_field_test!(body, goldilocks, $crate::fields::Zp18446744069414584321);
            // Expanded by hand rather than through `for_each_field_test!` so the deprecation
            // allow sits on this one test alone. `PrimeFieldElement128` is deprecated (#163) but
            // still `pub`, so the field laws must still hold over it.
            #[test]
            #[allow(deprecated)]
            fn prime_field_128() {
                body::<$crate::fields::Zp221360928884514619393>()
            }
            $crate::for_each_field_test!(body, bn254_fr, $crate::fields::Bn254Fr);
            $crate::for_each_field_test!(body, bls12_381_fr, $crate::fields::Bls12_381Fr);
            $crate::for_each_field_test!(body, gf256, $crate::fields::Gf256);
            $crate::for_each_field_test!(body, gf13_pow_4, $crate::fields::Gf13Pow4);
        }
    };
}

/// Run one test body over the fields small enough to enumerate exhaustively.
///
/// The second list [`for_each_field!`]'s documentation refers to: a body that walks every element
/// cannot run over a 254-bit field, and a body that tests a trait law can. Same expansion, same
/// `F: KnownOrder + Arbitrary` bound, fewer fields — all of order below 2^16.
#[macro_export]
macro_rules! for_each_small_field {
    (fn $name:ident<$type_parameter:ident>() $body:block) => {
        mod $name {
            #[allow(unused_imports)]
            use super::*;

            fn body<$type_parameter: $crate::KnownOrder + ::proptest::arbitrary::Arbitrary>() $body

            $crate::for_each_field_test!(body, zp13, $crate::fields::Zp13);
            $crate::for_each_field_test!(body, zp31, $crate::fields::Zp31);
            $crate::for_each_field_test!(body, zp541, $crate::fields::Zp541);
            $crate::for_each_field_test!(body, zp65537, $crate::fields::Zp65537);
            $crate::for_each_field_test!(body, gf256, $crate::fields::Gf256);
            $crate::for_each_field_test!(body, gf32, $crate::fields::Gf32);
        }
    };
}

/// One generated `#[test]`, as its own macro because `macro_rules!` cannot build an identifier
/// from a type path and so needs the test name passed in alongside it.
#[macro_export]
#[doc(hidden)]
macro_rules! for_each_field_test {
    ($body:ident, $name:ident, $field:ty) => {
        #[test]
        fn $name() {
            $body::<$field>()
        }
    };
}

#[cfg(test)]
mod tests {
    #[allow(unused_imports)]
    use proptest::prelude::Arbitrary;
    use rand::{prelude::StdRng, SeedableRng};

    // Consumed by the generated modules through their `use super::*`, which the unused-import
    // lint does not count as a use.
    #[allow(unused_imports)]
    use crate::{FiniteField, KnownOrder, One, Zero};

    // A trait law, over every field: `a * a^-1 = 1` off zero.
    for_each_field!(
        fn inverse_undoes_multiplication<F>() {
            let mut rng = StdRng::seed_from_u64(1);
            for _ in 0..20 {
                let a = F::random(&mut rng);
                if !a.is_zero() {
                    assert!((a * a.inverse()).is_one(), "{a} * {a}^-1 != 1");
                }
            }
        }
    );

    // Fermat's little theorem, over every field: `a^(q-1) = 1` off zero.
    for_each_field!(
        fn fermat_holds<F>() {
            let mut rng = StdRng::seed_from_u64(2);
            let (s, m) = crate::fields::two_adic::two_adic_decomposition(F::order_limbs());
            for _ in 0..10 {
                let a = F::random(&mut rng);
                if !a.is_zero() {
                    // q - 1 = 2^s * m, so a^(q-1) is a^m squared s times.
                    let mut power = a.pow_limbs(&m);
                    for _ in 0..s {
                        power = power * power;
                    }
                    assert!(power.is_one(), "{a}^(q-1) != 1");
                }
            }
        }
    );

    // Equal elements hash equally, and the field's proptest strategy is not degenerate.
    //
    // `src/test_support.rs`'s checks are generic over the type but were invoked by hand, once per
    // field, which is how the coverage became uneven in the first place.
    for_each_field!(
        fn the_strategy_and_hash_contracts_hold<F>() {
            let strategy = F::arbitrary();
            crate::test_support::assert_strategy_is_not_degenerate(&strategy, "a field element");
            let values = crate::test_support::draw(&strategy, 200);
            crate::test_support::assert_hash_agrees_with_eq(&values, "a field element");
        }
    );

    // The ring laws: both operations commute and associate, and multiplication distributes.
    for_each_field!(
        fn the_ring_laws_hold<F>() {
            let mut rng = StdRng::seed_from_u64(4);
            for _ in 0..20 {
                let (a, b, c) = (
                    F::random(&mut rng),
                    F::random(&mut rng),
                    F::random(&mut rng),
                );
                assert_eq!(a + b, b + a, "addition does not commute");
                assert_eq!(a * b, b * a, "multiplication does not commute");
                assert_eq!((a + b) + c, a + (b + c), "addition does not associate");
                assert_eq!(
                    (a * b) * c,
                    a * (b * c),
                    "multiplication does not associate"
                );
                assert_eq!(
                    a * (b + c),
                    a * b + a * c,
                    "multiplication does not distribute"
                );
                assert!((a + a.neg()).is_zero(), "a + (-a) != 0");
            }
        }
    );

    // Every element of a small field has a square root or a character of -1, never neither.
    for_each_small_field!(
        fn every_element_is_classified<F>() {
            let mut rng = StdRng::seed_from_u64(3);
            let order = F::order_u128().expect("a small field");
            let mut elements = vec![F::zero()];
            let generator = F::primitive_element(&mut rng);
            let mut power = F::one();
            for _ in 0..order - 1 {
                elements.push(power);
                power *= generator;
            }

            for x in elements {
                match x.sqrt(&mut rng) {
                    Some(root) => assert_eq!(root * root, x, "sqrt({x})^2 != {x}"),
                    None => assert_eq!(crate::fields::legendre_symbol(&x), -1),
                }
            }
        }
    );
}
