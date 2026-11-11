use std::hash::{DefaultHasher, Hash, Hasher};

use proptest::prelude::*;
use zeebra::Monomial;

// Construction and arithmetic preserve total degrees even when they exceed u32.
#[test]
fn wide_degree_survives_every_constructor() {
    let a = Monomial::<3>::new(&[u32::MAX, u32::MAX, 0]);
    let b = Monomial::<3>::univariate(2, u32::MAX);
    let product = a * b;
    assert_eq!(a.degree(), 2 * u64::from(u32::MAX));
    assert_eq!(b.degree(), u64::from(u32::MAX));
    assert_eq!(product.degree(), 3 * u64::from(u32::MAX));
    assert_eq!(product.checked_div(&b), Some(a));
    assert_eq!(Monomial::lcm(&a, &b), product);
    assert_eq!(Monomial::<0>::one().degree(), 0);
    assert_eq!(Monomial::<3>::default().degree(), 0);
}

// Serialization remains exactly the legacy exponent-only bincode representation.
#[test]
fn legacy_bytes_reconstruct_the_degree() {
    let bytes: Vec<u8> = [u32::MAX, 7, 19]
        .into_iter()
        .flat_map(u32::to_le_bytes)
        .collect();
    let monomial: Monomial<3> = bincode::deserialize(&bytes).unwrap();
    assert_eq!(monomial.degree(), u64::from(u32::MAX) + 26);
    assert_eq!(bincode::serialize(&monomial).unwrap(), bytes);
    assert!(bincode::deserialize::<Monomial<3>>(&bytes[..8]).is_err());
}

// Derived ordering stays lexicographic when degree and exponent order disagree.
#[test]
fn ordering_and_hashing_depend_on_exponents() {
    let small_degree = Monomial::<2>::new(&[2, 0]);
    let large_degree = Monomial::<2>::new(&[1, 100]);
    assert!(small_degree > large_degree);
    let mut monomial_hash = DefaultHasher::new();
    let mut exponent_hash = DefaultHasher::new();
    small_degree.hash(&mut monomial_hash);
    [2u32, 0].hash(&mut exponent_hash);
    assert_eq!(monomial_hash.finish(), exponent_hash.finish());
}

proptest! {
    // Arbitrary monomials and their products, quotients and lcms report the exponent sum.
    #[test]
    fn arithmetic_degrees_match_exponents(a in any::<[u32; 7]>(), b in any::<[u32; 7]>()) {
        let a = Monomial::<7>::new(&a.map(|e| e / 2));
        let b = Monomial::<7>::new(&b.map(|e| e / 2));
        let product = a * b;
        for monomial in [a, b, product, Monomial::lcm(&a, &b), product.checked_div(&b).unwrap()] {
            let expected: u64 = monomial.exponents().iter().map(|&e| u64::from(e)).sum();
            prop_assert_eq!(monomial.degree(), expected);
            let restored: Monomial<7> = bincode::deserialize(&bincode::serialize(&monomial).unwrap()).unwrap();
            prop_assert_eq!(restored.degree(), expected);
        }
        prop_assert_eq!(product.degree(), a.degree() + b.degree());
    }
}
