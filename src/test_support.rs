//! Shared checks for properties that every type in the crate should satisfy, and the oracles they
//! check against.
//!
//! These exist because the same defects kept recurring, all of them invisible in a green test run:
//! a `proptest` strategy that panics or generates a single degenerate value, so every property
//! holds vacuously; a type with more than one representation of a value whose equality is derived
//! over that representation, which only misbehaves once a value reaches a `HashMap`; and — the
//! reason [`schoolbook_product`] is here — an oracle that is the implementation it is supposed to
//! be checking. Each module's tests call these so a regression shows up as a failure rather than
//! as silently weaker coverage.

use std::{
    collections::hash_map::DefaultHasher,
    fmt::Debug,
    hash::{Hash, Hasher},
};

use proptest::{
    strategy::{Strategy, ValueTree},
    test_runner::TestRunner,
};

use crate::{FiniteField, Polynomial, UnivariatePolynomial};

/// The product of two polynomials, by the definition, as the comparand for every faster route.
///
/// Written out here rather than taken from `Mul` because `Mul` stopped being independent of what it
/// was checking: #231 dispatches it to `multiply_dense`, so `karatsuba`'s agreement tests would
/// have compared Karatsuba against Karatsuba and `fft::multiply`'s would have compared the
/// transform against Karatsuba, and all of them would still have passed. This shares code with
/// neither Karatsuba nor the transform — two loops over the coefficients and nothing else — so
/// agreement against it is a real check in a way agreement against `Mul` is no longer.
///
/// Deliberately not generic over a polynomial trait and deliberately not optimized: `&[F]` in,
/// coefficients accumulated at `i + j`, trimmed by `new` exactly as `Mul` used to trim. The whole
/// point is that there is nothing in here to get subtly right.
pub fn schoolbook_product<F: FiniteField>(
    a: &UnivariatePolynomial<F>,
    b: &UnivariatePolynomial<F>,
) -> UnivariatePolynomial<F> {
    let x = a.coefficients();
    let y = b.coefficients();
    let mut product = vec![F::zero(); x.len() + y.len() - 1];
    for (i, p) in x.iter().enumerate() {
        for (j, q) in y.iter().enumerate() {
            product[i + j] += *p * *q;
        }
    }
    UnivariatePolynomial::new(&product)
}

/// Draw `count` values from `strategy`.
///
/// Panics if the strategy itself panics, which is the failure mode of a strategy that indexes into
/// a collection it never filled.
pub fn draw<S: Strategy>(strategy: &S, count: usize) -> Vec<S::Value> {
    let mut runner = TestRunner::deterministic();
    (0..count)
        .map(|_| strategy.new_tree(&mut runner).unwrap().current())
        .collect()
}

/// Assert that a strategy is usable: it does not panic, and it does not collapse to one value.
///
/// A strategy that always returns the same value (typically the type's zero) satisfies every
/// algebraic property trivially, so property tests built on it assert nothing.
pub fn assert_strategy_is_not_degenerate<S>(strategy: &S, label: &str)
where
    S: Strategy,
    S::Value: Debug + PartialEq,
{
    let values = draw(strategy, 64);
    // Compared pairwise rather than collected into a set, so this works for the types in the
    // crate that implement `PartialEq` but not `Hash`.
    let varies = values.iter().any(|v| *v != values[0]);
    assert!(
        varies,
        "the strategy for {} produced only {:?} across 64 draws, so any property over it holds \
         vacuously",
        label, values[0]
    );
}

/// Assert that equal values hash equally, as `Hash`'s contract with `Eq` requires.
///
/// Violated whenever a type admits two representations of one value but derives `PartialEq` or
/// `Hash` over the representation. The consequence is a `HashMap` or `HashSet` that fails to find
/// a key equal to one it stores.
pub fn assert_hash_agrees_with_eq<T: Debug + Eq + Hash>(values: &[T], label: &str) {
    for a in values {
        for b in values {
            if a == b {
                assert_eq!(
                    hash_of(a),
                    hash_of(b),
                    "{}: {:?} == {:?} but their hashes differ",
                    label,
                    a,
                    b
                );
            }
        }
    }
}

/// Assert that `Ord` agrees with `Eq` and is antisymmetric over the sample.
///
/// A manual `cmp` can disagree with a derived `PartialEq` — reporting `Equal` for values that
/// compare unequal, or vice versa — which makes sorting and binary search misbehave.
pub fn assert_ord_agrees_with_eq<T: Debug + Ord>(values: &[T], label: &str) {
    for a in values {
        for b in values {
            assert_eq!(
                a == b,
                a.cmp(b) == std::cmp::Ordering::Equal,
                "{}: equality and ordering disagree for {:?} and {:?}",
                label,
                a,
                b
            );
            assert_eq!(
                a.cmp(b),
                b.cmp(a).reverse(),
                "{}: ordering is not antisymmetric for {:?} and {:?}",
                label,
                a,
                b
            );
        }
    }
}

fn hash_of<T: Hash>(value: &T) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

#[cfg(test)]
mod tests {
    use super::schoolbook_product;
    use crate::{fields::Zp7, FiniteField, Polynomial, UnivariatePolynomial};

    fn poly(coefficients: &[u64]) -> UnivariatePolynomial<Zp7> {
        UnivariatePolynomial::new(
            &coefficients
                .iter()
                .map(|c| Zp7::new(*c))
                .collect::<Vec<_>>(),
        )
    }

    /// The oracle reproduces products computed by hand, so that the thing two modules now check
    /// against is itself pinned rather than trusted.
    #[test]
    fn test_the_oracle_agrees_with_products_computed_by_hand() {
        // (1 + x)(1 + x) = 1 + 2x + x^2
        assert_eq!(
            schoolbook_product(&poly(&[1, 1]), &poly(&[1, 1])),
            poly(&[1, 2, 1])
        );
        // (2 + 3x)(4 + 5x) = 8 + 22x + 15x^2, which over GF(7) is 1 + x + x^2
        assert_eq!(
            schoolbook_product(&poly(&[2, 3]), &poly(&[4, 5])),
            poly(&[1, 1, 1])
        );
        // (1 + x^2)(1 + x) = 1 + x + x^2 + x^3, a gap in one operand
        assert_eq!(
            schoolbook_product(&poly(&[1, 0, 1]), &poly(&[1, 1])),
            poly(&[1, 1, 1, 1])
        );
    }

    /// The oracle trims its result, so the degree it reports is the degree `Mul` reported: a
    /// product whose leading coefficient vanishes modulo the characteristic is shorter than
    /// `deg a + deg b`.
    #[test]
    fn test_the_oracle_trims_a_vanishing_leading_coefficient() {
        // (7x + 1) is (1) over GF(7), so this is degree 0 and not degree 2.
        let product = schoolbook_product(&poly(&[1, 7]), &poly(&[1, 7]));
        assert_eq!(product, poly(&[1]));
        assert_eq!(product.degree(), 0);
    }

    /// Multiplying by zero or one behaves, which is what the empty-coefficient edge would break.
    #[test]
    fn test_the_oracle_handles_the_zero_and_one_polynomials() {
        let f = poly(&[3, 1, 4]);
        let zero = UnivariatePolynomial::<Zp7>::zero();
        let one = UnivariatePolynomial::<Zp7>::one();
        assert!(schoolbook_product(&f, &zero).is_zero());
        assert!(schoolbook_product(&zero, &f).is_zero());
        assert!(schoolbook_product(&zero, &zero).is_zero());
        assert_eq!(schoolbook_product(&f, &one), f);
    }
}
