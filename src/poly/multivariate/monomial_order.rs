//! Monomial orderings on k[x_0, ..., x_{n-1}].
//!
//! Lexicographic order (lex)  first compares exponents of x1 in the monomials, and in case of
//! equality compares exponents of x2, and so on.
//!
//! Graded lexicographic order (grlex) compares by total degree (sum of all exponents), and then
//! "breaks ties" using lexicographic order.
//!
//! Graded reverse lexicographic order (grevlex) compares by total degree (sum of all exponents),
//! and then "breaks ties" by looking at the right-most variable and favoring the monomial with the
//! smaller exponent on that variable.

use crate::Monomial;
use std::cmp::Ordering;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MonomialOrder {
    /// Lexicographic order (lex).
    Lexicographic,

    /// Graded lexicographic order (grlex).
    GradedLexicographic,

    /// Graded reverse lexicographic order (grevlex).
    GradedReverseLexicographic,
}

impl MonomialOrder {
    /// Returns the monomial order's comparison function.
    pub fn cmp<const N: usize>(&self, a: &Monomial<N>, b: &Monomial<N>) -> Ordering {
        match self {
            MonomialOrder::Lexicographic => lex(a, b),
            MonomialOrder::GradedLexicographic => grlex(a, b),
            MonomialOrder::GradedReverseLexicographic => grevlex(a, b),
        }
    }

    /// The greater of two monomials under this order.
    pub fn max<const N: usize>(&self, a: &Monomial<N>, b: &Monomial<N>) -> Monomial<N> {
        // Defers to `cmp` so the two cannot drift apart, which is how grevlex came to be
        // dispatched two different ways.
        match self.cmp(a, b) {
            Ordering::Greater => *a,
            Ordering::Less => *b,
            Ordering::Equal => *a,
        }
    }

    /// Returns the monomial order's name.
    pub fn name(&self) -> &'static str {
        match self {
            MonomialOrder::Lexicographic => "lex",
            MonomialOrder::GradedLexicographic => "grlex",
            MonomialOrder::GradedReverseLexicographic => "grevlex",
        }
    }

    /// Returns the monomial order's description.
    pub fn description(&self) -> &'static str {
        match self {
            MonomialOrder::Lexicographic => "lexicographic",
            MonomialOrder::GradedLexicographic => "graded lexicographic",
            MonomialOrder::GradedReverseLexicographic => "graded reverse lexicographic",
        }
    }
}

/// Lexicographic order.
///
/// Compares exponents of x1 in the monomials, and in case of equality compares exponents of x2, etc.
fn lex<const N: usize>(a: &Monomial<N>, b: &Monomial<N>) -> Ordering {
    a.exponents().cmp(b.exponents())
}

/// Graded lexicographic order.
///
/// Compares by total degree and then "breaks ties" using lexicographic order.
fn grlex<const N: usize>(a: &Monomial<N>, b: &Monomial<N>) -> Ordering {
    match a.degree().cmp(&b.degree()) {
        Ordering::Equal => lex(a, b),
        ord => ord,
    }
}

/// Graded reverse lexicographic order.
///
/// Compares by total degree (sum of all exponents), and then "breaks ties" by looking at the
/// right-most variable and favoring the monomial with the smaller exponent on that variable.
fn grevlex<const N: usize>(a: &Monomial<N>, b: &Monomial<N>) -> Ordering {
    match a.degree().cmp(&b.degree()) {
        Ordering::Equal => {
            for i in (0..N).rev() {
                match a.exponents()[i].cmp(&b.exponents()[i]).reverse() {
                    Ordering::Equal => continue,
                    ord => return ord,
                }
            }
            Ordering::Equal
        }
        ord => ord,
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        poly::multivariate::monomial_order::{grevlex, grlex, lex},
        Monomial, MonomialOrder,
    };
    use proptest::{
        prelude::{any, TestCaseError},
        prop_assert_eq, proptest,
    };
    use std::cmp::Ordering;

    #[test]
    fn spotcheck_lex_ordering() {
        // Equal
        {
            let a = Monomial::<3>::new(&[1, 5, 3]); // xy^5z^3
            assert_eq!(lex(&a, &a), Ordering::Equal); // (1,5,3) =_lex (1,5,3)
        }

        {
            let a = Monomial::<3>::new(&[1, 2, 0]); // y^5
            let b = Monomial::<3>::new(&[0, 3, 4]); // x^5
            assert_eq!(lex(&a, &b), Ordering::Greater); // (1,2,0) >_lex (0,3,4)
            assert_eq!(lex(&b, &a), Ordering::Less);
        }

        {
            let a = Monomial::<3>::new(&[3, 2, 4]); // x^3y^2z^4
            let b = Monomial::<3>::new(&[3, 2, 1]); // x^3y^2z
            assert_eq!(lex(&a, &b), Ordering::Greater); // (3,2,4) >_lex (3,2,1)
            assert_eq!(lex(&b, &a), Ordering::Less);
        }
    }

    #[test]
    fn spotcheck_grlex_ordering() {
        // Equal
        {
            let a = Monomial::<3>::new(&[1, 5, 3]); // xy^5z^3
            assert_eq!(grlex(&a, &a), Ordering::Equal);
        }

        // (1,2,3) >_grlex (3,2,0)
        {
            let a = Monomial::<3>::new(&[1, 2, 3]); // xy^2z^3
            let b = Monomial::<3>::new(&[3, 2, 0]); // x^3yz^0
            assert_eq!(grlex(&a, &b), Ordering::Greater);
            assert_eq!(grlex(&b, &a), Ordering::Less);
        }

        // (1,2,4) >_grlex (1,1,5)
        {
            let a = Monomial::<3>::new(&[1, 2, 4]); // xy^2z^4
            let b = Monomial::<3>::new(&[1, 1, 5]); // xy^1z^5
            assert_eq!(grlex(&a, &b), Ordering::Greater);
            assert_eq!(grlex(&b, &a), Ordering::Less);
        }
    }

    #[test]
    fn spotcheck_grevlex_ordering() {
        // Equal
        {
            let a = Monomial::<3>::new(&[1, 5, 3]); // xy^5z^3
            assert_eq!(grevlex(&a, &a), Ordering::Equal);
        }

        {
            let a = Monomial::<3>::new(&[4, 7, 1]); // x^4y^7z
            let b = Monomial::<3>::new(&[4, 2, 3]); // x^4y^2z^3
            assert_eq!(grevlex(&a, &b), Ordering::Greater); // (4,7,1) >_grlex (4,2,3)
            assert_eq!(grevlex(&b, &a), Ordering::Less);
        }

        {
            let a = Monomial::<3>::new(&[1, 5, 2]); // xy^5z^2
            let b = Monomial::<3>::new(&[4, 1, 3]); // x^4yz^3
            assert_eq!(grevlex(&a, &b), Ordering::Greater); // (1,5,2) >_grevlex (4,1,3)
            assert_eq!(grevlex(&b, &a), Ordering::Less);
        }
    }

    fn order_is_symmetric<const N: usize>(
        a: Monomial<N>,
        b: Monomial<N>,
    ) -> Result<(), TestCaseError> {
        prop_assert_eq!(lex(&a, &b), lex(&b, &a).reverse());
        prop_assert_eq!(grlex(&a, &b), grlex(&b, &a).reverse());
        prop_assert_eq!(grevlex(&a, &b), grevlex(&b, &a).reverse());
        Ok(())
    }

    proptest! {
        #[test]
        fn test_order_is_symmetric(a in any::<Monomial<7>>(), b in any::<Monomial<7>>()) {
            order_is_symmetric(a, b)?;
        }
    }

    /// Every order dispatches `cmp` to its own comparison, not another order's.
    ///
    /// Regression test for a dispatch bug: `GradedReverseLexicographic` routed `cmp` to `grlex`
    /// while `max` routed it to `grevlex`, so grevlex silently behaved as grlex everywhere
    /// `leading_term` was used, and the two functions disagreed with each other.
    #[test]
    fn test_cmp_dispatches_to_the_named_order() {
        // In three variables at degree two, grlex and grevlex disagree on x*z versus y^2:
        // grlex compares exponent vectors left to right, so x*z = (1,0,1) > y^2 = (0,2,0);
        // grevlex compares from the right preferring the smaller, so y^2 > x*z.
        let xz = Monomial::<3>::new(&[1, 0, 1]);
        let y2 = Monomial::<3>::new(&[0, 2, 0]);

        assert_eq!(
            MonomialOrder::GradedLexicographic.cmp(&xz, &y2),
            Ordering::Greater,
            "grlex should rank x*z above y^2"
        );
        assert_eq!(
            MonomialOrder::GradedReverseLexicographic.cmp(&xz, &y2),
            Ordering::Less,
            "grevlex should rank y^2 above x*z"
        );

        // The two orders must therefore not agree on this pair.
        assert_ne!(
            MonomialOrder::GradedLexicographic.cmp(&xz, &y2),
            MonomialOrder::GradedReverseLexicographic.cmp(&xz, &y2)
        );
    }

    /// `cmp` and `max` agree, for every order.
    #[test]
    fn test_cmp_and_max_agree() {
        let monomials = sample_monomials();
        for order in ALL_ORDERS {
            for a in &monomials {
                for b in &monomials {
                    let expected = match order.cmp(a, b) {
                        Ordering::Less => *b,
                        _ => *a,
                    };
                    assert_eq!(
                        order.max(a, b),
                        expected,
                        "{}: max disagrees with cmp on {:?} and {:?}",
                        order.name(),
                        a.exponents(),
                        b.exponents()
                    );
                }
            }
        }
    }

    /// Each order is a total order: antisymmetric, and equal only for equal monomials.
    #[test]
    fn test_orders_are_total() {
        let monomials = sample_monomials();
        for order in ALL_ORDERS {
            for a in &monomials {
                for b in &monomials {
                    assert_eq!(
                        order.cmp(a, b),
                        order.cmp(b, a).reverse(),
                        "{} is not antisymmetric",
                        order.name()
                    );
                    assert_eq!(
                        order.cmp(a, b) == Ordering::Equal,
                        a == b,
                        "{} reports equality for distinct monomials",
                        order.name()
                    );
                }
            }
        }
    }

    /// Each order is transitive.
    #[test]
    fn test_orders_are_transitive() {
        let monomials = sample_monomials();
        for order in ALL_ORDERS {
            for a in &monomials {
                for b in &monomials {
                    for c in &monomials {
                        if order.cmp(a, b) == Ordering::Less && order.cmp(b, c) == Ordering::Less {
                            assert_eq!(
                                order.cmp(a, c),
                                Ordering::Less,
                                "{} is not transitive",
                                order.name()
                            );
                        }
                    }
                }
            }
        }
    }

    /// Each order is multiplicative: a < b implies a*c < b*c.
    ///
    /// This is what makes a monomial order usable for division, and the sorted-merge reduction
    /// relies on it: multiplying a sorted sequence of terms by a monomial preserves the order.
    #[test]
    fn test_orders_are_multiplicative() {
        let monomials = sample_monomials();
        for order in ALL_ORDERS {
            for a in &monomials {
                for b in &monomials {
                    for c in &monomials {
                        let ac = a * c;
                        let bc = b * c;
                        assert_eq!(
                            order.cmp(a, b),
                            order.cmp(&ac, &bc),
                            "{}: multiplying by {:?} changed the order of {:?} and {:?}",
                            order.name(),
                            c.exponents(),
                            a.exponents(),
                            b.exponents()
                        );
                    }
                }
            }
        }
    }

    /// One is the least monomial under every order, so reduction terminates.
    #[test]
    fn test_one_is_minimal() {
        let one = Monomial::<3>::one();
        for order in ALL_ORDERS {
            for m in sample_monomials() {
                if m == one {
                    continue;
                }
                assert_eq!(
                    order.cmp(&one, &m),
                    Ordering::Less,
                    "{} does not rank 1 below {:?}",
                    order.name(),
                    m.exponents()
                );
            }
        }
    }

    /// Each order ranks degree-two monomials in three variables as the textbook does.
    #[test]
    fn test_known_orderings_of_degree_two() {
        let descending = |order: MonomialOrder, mut ms: Vec<Monomial<3>>| {
            ms.sort_by(|a, b| order.cmp(a, b).reverse());
            ms.iter()
                .map(|m| m.exponents().to_vec())
                .collect::<Vec<_>>()
        };
        let degree_two = vec![
            Monomial::<3>::new(&[2, 0, 0]), // x^2
            Monomial::<3>::new(&[1, 1, 0]), // xy
            Monomial::<3>::new(&[1, 0, 1]), // xz
            Monomial::<3>::new(&[0, 2, 0]), // y^2
            Monomial::<3>::new(&[0, 1, 1]), // yz
            Monomial::<3>::new(&[0, 0, 2]), // z^2
        ];

        // lex and grlex coincide within a single degree: x^2 > xy > xz > y^2 > yz > z^2.
        let expected_lex = vec![
            vec![2, 0, 0],
            vec![1, 1, 0],
            vec![1, 0, 1],
            vec![0, 2, 0],
            vec![0, 1, 1],
            vec![0, 0, 2],
        ];
        assert_eq!(
            descending(MonomialOrder::Lexicographic, degree_two.clone()),
            expected_lex
        );
        assert_eq!(
            descending(MonomialOrder::GradedLexicographic, degree_two.clone()),
            expected_lex
        );

        // grevlex differs: x^2 > xy > y^2 > xz > yz > z^2.
        assert_eq!(
            descending(MonomialOrder::GradedReverseLexicographic, degree_two),
            vec![
                vec![2, 0, 0],
                vec![1, 1, 0],
                vec![0, 2, 0],
                vec![1, 0, 1],
                vec![0, 1, 1],
                vec![0, 0, 2],
            ]
        );
    }

    /// Graded orders rank by total degree first; lex does not.
    #[test]
    fn test_graded_orders_rank_by_degree_first() {
        let low = Monomial::<3>::new(&[1, 0, 0]); // x, degree 1
        let high = Monomial::<3>::new(&[0, 0, 3]); // z^3, degree 3

        for order in [
            MonomialOrder::GradedLexicographic,
            MonomialOrder::GradedReverseLexicographic,
        ] {
            assert_eq!(order.cmp(&low, &high), Ordering::Less, "{}", order.name());
        }
        // Under lex, x outranks z^3 despite the lower degree.
        assert_eq!(
            MonomialOrder::Lexicographic.cmp(&low, &high),
            Ordering::Greater
        );
    }

    const ALL_ORDERS: [MonomialOrder; 3] = [
        MonomialOrder::Lexicographic,
        MonomialOrder::GradedLexicographic,
        MonomialOrder::GradedReverseLexicographic,
    ];

    /// Every monomial in three variables with exponents up to two, which covers the cases where
    /// the three orders differ.
    fn sample_monomials() -> Vec<Monomial<3>> {
        let mut out = Vec::new();
        for i in 0..3u32 {
            for j in 0..3u32 {
                for k in 0..3u32 {
                    out.push(Monomial::new(&[i, j, k]));
                }
            }
        }
        out
    }
}
