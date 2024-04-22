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
            MonomialOrder::GradedReverseLexicographic => grlex(a, b),
        }
    }
    pub fn max<const N: usize>(&self, a: &Monomial<N>, b: &Monomial<N>) -> Monomial<N> {
        let ordering = match self {
            MonomialOrder::Lexicographic => lex(a, b),
            MonomialOrder::GradedLexicographic => grlex(a, b),
            MonomialOrder::GradedReverseLexicographic => grevlex(a, b),
        };

        match ordering {
            Ordering::Greater => a.clone(),
            Ordering::Less => b.clone(),
            Ordering::Equal => a.clone(),
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
    a.exponents().cmp(&b.exponents())
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
        Monomial,
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
}
