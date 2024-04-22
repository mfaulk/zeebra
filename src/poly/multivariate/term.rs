//! A term c * monomial

use std::fmt::Display;

use crate::{FiniteField, Monomial};

#[derive(Eq, PartialEq, Copy, Clone, Debug, Hash)]
pub struct Term<const N: usize, F: FiniteField> {
    pub(crate) coefficient: F,
    pub(crate) monomial: Monomial<N>,
}

impl<const N: usize, F: FiniteField> Term<N, F> {
    /// Te term c * monomial
    pub fn new(coefficient: F, monomial: Monomial<N>) -> Self {
        Self {
            coefficient,
            monomial,
        }
    }

    /// The zero term
    pub fn zero() -> Self {
        Self {
            coefficient: F::zero(),
            monomial: Monomial::one(),
        }
    }

    /// The one term
    pub fn one() -> Self {
        Self {
            coefficient: F::one(),
            monomial: Monomial::one(),
        }
    }

    /// Return true if the term is zero.
    pub fn is_zero(&self) -> bool {
        self.coefficient.is_zero()
    }

    /// Return true if the term is one.
    pub fn is_one(&self) -> bool {
        self.coefficient.is_one() && self.monomial.is_one()
    }

    /// The coefficient of the term.
    pub fn coefficient(&self) -> &F {
        &self.coefficient
    }

    /// The monomial of the term.
    pub fn monomial(&self) -> &Monomial<N> {
        &self.monomial
    }

    /// Total degree (sum of exponents) f the term.
    pub fn degree(&self) -> u64 {
        self.monomial.degree()
    }

    /// Evaluate the term at the vector x.
    pub fn eval(&self, x: &[F]) -> F {
        self.coefficient * self.monomial.eval(x)
    }

    /// The least common multiple of two terms.
    pub fn lcm(_a: &Self, _b: &Self) -> Self {
        // let coefficient = a.coefficient.lcm(&b.coefficient);
        // let monomial = a.monomial.lcm(&b.monomial);
        // Self::new(coefficient, monomial)
        unimplemented!()
    }
}

/// Display
impl<const N: usize, F: FiniteField> Display for Term<N, F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.coefficient.is_one() {
            write!(f, "{}", self.monomial)
        } else {
            write!(f, "{} * {}", self.coefficient, self.monomial)
        }
    }
}

/// Term --> (coefficient, monomial)
impl<const N: usize, F: FiniteField> From<Term<N, F>> for (F, Monomial<N>) {
    fn from(term: Term<N, F>) -> Self {
        (term.coefficient, term.monomial)
    }
}

/// (coefficient, monomial) --> Term
impl<const N: usize, F: FiniteField> From<(F, Monomial<N>)> for Term<N, F> {
    fn from((coefficient, monomial): (F, Monomial<N>)) -> Self {
        Self::new(coefficient, monomial)
    }
}

/// (monomial, coefficient) --> Term
impl<const N: usize, F: FiniteField> From<(Monomial<N>, F)> for Term<N, F> {
    fn from((monomial, coefficient): (Monomial<N>, F)) -> Self {
        Self::new(coefficient, monomial)
    }
}

#[cfg(test)]
mod tests {

    // TODO
}
