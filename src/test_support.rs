//! Shared checks for properties that every type in the crate should satisfy.
//!
//! These exist because the same two defects kept recurring: a `proptest` strategy that panics or
//! generates a single degenerate value, and a type with more than one representation of a value
//! whose equality is derived over that representation. Both are invisible in a green test run —
//! a degenerate strategy makes every property hold vacuously, and a duplicate representation only
//! misbehaves once a value reaches a `HashMap`. Each module's tests call these so a regression
//! shows up as a failure rather than as silently weaker coverage.

use std::{
    collections::hash_map::DefaultHasher,
    fmt::Debug,
    hash::{Hash, Hasher},
};

use proptest::{
    strategy::{Strategy, ValueTree},
    test_runner::TestRunner,
};

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
