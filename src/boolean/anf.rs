//! Square-free algebraic normal form: the reference representation and the expanded-ANF route.
//!
//! An element of `GF(2)[x]/<x_i^2 + x_i>` is a set of square-free monomials, each a set of
//! variables. Addition is symmetric difference and the product of two monomials is the union of
//! their variable sets, which is exactly `x·x = x`. Nothing here shares structure, so this is the
//! oracle the ZDD is checked against, and the baseline it has to beat.

use std::collections::HashSet;

use super::ZddError;

/// The most variables a [`Term`] can name.
pub const MAX_VARS: usize = 256;

/// A square-free monomial, as the bitmask of its variables.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Term([u64; MAX_VARS / 64]);

impl Term {
    /// The monomial `1`.
    pub const ONE: Self = Self([0; MAX_VARS / 64]);

    /// The monomial whose variables are `vars`. Repeats collapse, since `x·x = x`.
    pub fn of(vars: &[u32]) -> Self {
        let mut term = Self::ONE;
        for &v in vars {
            term.insert(v);
        }
        term
    }

    /// Whether `v` divides this monomial.
    pub fn contains(&self, v: u32) -> bool {
        let v = v as usize;
        self.0[v / 64] >> (v % 64) & 1 == 1
    }

    /// Multiplies in `v`.
    pub fn insert(&mut self, v: u32) {
        assert!((v as usize) < MAX_VARS, "variable {v} exceeds MAX_VARS");
        self.0[v as usize / 64] |= 1 << (v % 64);
    }

    /// Divides out `v`.
    pub fn remove(&mut self, v: u32) {
        self.0[v as usize / 64] &= !(1 << (v % 64));
    }

    /// The Boolean product: the union of the variable sets.
    pub fn union(&self, other: &Self) -> Self {
        let mut out = *self;
        for (a, b) in out.0.iter_mut().zip(other.0) {
            *a |= b;
        }
        out
    }

    /// The variables, ascending.
    pub fn vars(&self) -> impl Iterator<Item = u32> + '_ {
        (0..MAX_VARS as u32).filter(|&v| self.contains(v))
    }

    /// The number of variables.
    pub fn degree(&self) -> u32 {
        self.0.iter().map(|w| w.count_ones()).sum()
    }
}

/// A Boolean polynomial in algebraic normal form.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Anf {
    terms: HashSet<Term>,
}

/// What the expanded-ANF route did, for the measurements.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct AnfWork {
    /// Monomial products formed.
    pub products: u64,
    /// Largest intermediate polynomial, in terms.
    pub peak_terms: usize,
}

impl Anf {
    /// The zero polynomial.
    pub fn zero() -> Self {
        Self::default()
    }

    /// The constant `1`.
    pub fn one() -> Self {
        Self::from_terms([Term::ONE])
    }

    /// The variable `x_v`.
    pub fn var(v: u32) -> Self {
        Self::from_terms([Term::of(&[v])])
    }

    /// The sum of `terms`; a repeated monomial cancels, since `1 + 1 = 0`.
    pub fn from_terms(terms: impl IntoIterator<Item = Term>) -> Self {
        let mut out = Self::zero();
        for t in terms {
            out.toggle(t);
        }
        out
    }

    /// The Boolean class of an ordinary polynomial over GF(2), given as exponent vectors.
    ///
    /// Every positive exponent becomes 1. This is the quotient map, not an identity: `x^2 + x + 1`
    /// lands on `1`.
    pub fn from_exponents(monomials: &[&[u32]]) -> Self {
        Self::from_terms(monomials.iter().map(|exps| {
            let vars: Vec<u32> = (0..exps.len() as u32)
                .filter(|&v| exps[v as usize] > 0)
                .collect();
            Term::of(&vars)
        }))
    }

    /// Adds the monomial `t` in place.
    pub fn toggle(&mut self, t: Term) {
        if !self.terms.remove(&t) {
            self.terms.insert(t);
        }
    }

    /// The number of terms.
    pub fn len(&self) -> usize {
        self.terms.len()
    }

    /// Whether this is the zero polynomial.
    pub fn is_empty(&self) -> bool {
        self.terms.is_empty()
    }

    /// The monomials, in no particular order.
    pub fn terms(&self) -> impl Iterator<Item = &Term> {
        self.terms.iter()
    }

    /// Whether `v` occurs.
    pub fn mentions(&self, v: u32) -> bool {
        self.terms.iter().any(|t| t.contains(v))
    }

    /// The highest variable index occurring, if any.
    pub fn max_var(&self) -> Option<u32> {
        self.terms.iter().flat_map(|t| t.vars()).max()
    }

    /// Estimated heap bytes held, from the table's capacity.
    pub fn heap_bytes(&self) -> usize {
        self.terms.capacity() * (std::mem::size_of::<Term>() + 1)
    }

    /// The sum.
    pub fn add(&self, other: &Self) -> Self {
        let mut out = self.clone();
        for &t in &other.terms {
            out.toggle(t);
        }
        out
    }

    /// The Boolean product, refused once an intermediate exceeds `term_budget` terms.
    pub fn mul(
        &self,
        other: &Self,
        term_budget: usize,
        work: &mut AnfWork,
    ) -> Result<Self, ZddError> {
        let mut out = Self::zero();
        for a in &self.terms {
            for b in &other.terms {
                out.toggle(a.union(b));
                work.products += 1;
            }
            if out.len() > term_budget {
                return Err(ZddError::TermBudgetExceeded { limit: term_budget });
            }
            work.peak_terms = work.peak_terms.max(out.len());
        }
        Ok(out)
    }

    /// `x_v ← h`: splits `self = x_v·q + r`, returns `h·q + r`.
    pub fn substitute(
        &self,
        v: u32,
        h: &Self,
        term_budget: usize,
        work: &mut AnfWork,
    ) -> Result<Self, ZddError> {
        let mut q = Self::zero();
        let mut r = Self::zero();
        for &t in &self.terms {
            if t.contains(v) {
                let mut t = t;
                t.remove(v);
                q.toggle(t);
            } else {
                r.toggle(t);
            }
        }
        let out = h.mul(&q, term_budget, work)?.add(&r);
        if out.len() > term_budget {
            return Err(ZddError::TermBudgetExceeded { limit: term_budget });
        }
        work.peak_terms = work.peak_terms.max(out.len());
        Ok(out)
    }

    /// The value at the assignment `x_v = assignment(v)`.
    pub fn evaluate(&self, assignment: impl Fn(u32) -> bool) -> bool {
        self.terms
            .iter()
            .filter(|t| t.vars().all(&assignment))
            .count()
            % 2
            == 1
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const BIG: usize = 1 << 20;

    #[test]
    fn x_times_x_is_x_and_x_plus_x_is_zero() {
        let x = Anf::var(3);
        assert_eq!(x.mul(&x, BIG, &mut AnfWork::default()).unwrap(), x);
        assert!(x.add(&x).is_empty());
    }

    #[test]
    fn x_squared_plus_x_plus_one_is_one_in_the_quotient() {
        assert_eq!(Anf::from_exponents(&[&[2], &[1], &[0]]), Anf::one());
    }

    #[test]
    fn substitution_replaces_the_variable() {
        // x0·x1 + x0 with x0 ← x1 + x2 is x1 + x1·x2 + x1 + x2 = x1·x2 + x2.
        let f = Anf::from_terms([Term::of(&[0, 1]), Term::of(&[0])]);
        let h = Anf::from_terms([Term::of(&[1]), Term::of(&[2])]);
        let g = f.substitute(0, &h, BIG, &mut AnfWork::default()).unwrap();
        assert_eq!(g, Anf::from_terms([Term::of(&[1, 2]), Term::of(&[2])]));
    }

    #[test]
    fn a_product_past_the_term_budget_is_refused() {
        let f = Anf::from_terms((0..8).map(|v| Term::of(&[v])));
        let g = Anf::from_terms((8..16).map(|v| Term::of(&[v])));
        let err = f.mul(&g, 10, &mut AnfWork::default()).unwrap_err();
        assert_eq!(err, ZddError::TermBudgetExceeded { limit: 10 });
    }
}
