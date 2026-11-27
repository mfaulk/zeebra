//! Research prototype (#1168): bounded ZDD normal forms in the Boolean quotient ring.
//!
//! The ring here is `GF(2)[x_0, …, x_{n-1}] / <x_i^2 + x_i>`, **not** the polynomial ring the rest
//! of the crate works in: `x^2 + x + 1` is `1` here and irreducible there. The one contract is the
//! exact Boolean normal form of a polynomial with respect to verified triangular rules
//! `x_i + h_i`, where `h_i` mentions only variables after `x_i` in a chosen order. That is not a
//! Gröbner basis, a solver or a backend; `docs/research/boolean-zdd-normal-forms.md` records the
//! measurements and the go/no-go.
//!
//! - [`anf`]: the square-free ANF oracle, and the expanded-ANF route the ZDD is measured against.
//! - [`zdd`]: the bounded manager (unique table, operation cache, budgets, typed refusals).
//! - [`normal_form`]: rule verification and the normal form by both routes.
//! - [`fixtures`]: public structured families, their scrambled orders, and a dense MQ control.
//!
//! Algorithms follow Brickenstein and Dreyer (PolyBoRi, JSC 2009; Dagstuhl 10271, Alg. 1). The
//! code is written independently: PolyBoRi is GPL and is an algorithmic reference only.

use std::fmt::{self, Display, Formatter};

pub mod anf;
pub mod fixtures;
pub mod normal_form;
pub mod zdd;

/// A budget refusal. The operation did not finish; nothing partial is returned.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ZddError {
    /// More decision nodes were needed than the manager allows.
    NodeBudgetExceeded {
        /// The configured limit.
        limit: usize,
    },
    /// More operation-cache entries were needed than the manager allows.
    CacheBudgetExceeded {
        /// The configured limit.
        limit: usize,
    },
    /// An expanded ANF polynomial would exceed this many terms.
    TermBudgetExceeded {
        /// The configured limit.
        limit: usize,
    },
}

impl Display for ZddError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::NodeBudgetExceeded { limit } => write!(f, "node budget of {limit} exceeded"),
            Self::CacheBudgetExceeded { limit } => write!(f, "cache budget of {limit} exceeded"),
            Self::TermBudgetExceeded { limit } => write!(f, "term budget of {limit} exceeded"),
        }
    }
}

impl std::error::Error for ZddError {}

/// Why a variable order or a rule set was refused before use.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RuleError {
    /// The order is not a permutation of `0..n`, or `n` exceeds [`anf::MAX_VARS`].
    InvalidOrder,
    /// A rule's head or tail names a variable outside the order.
    VariableOutOfRange {
        /// The variable.
        var: u32,
    },
    /// Two rules share a head.
    DuplicateHead {
        /// The head.
        head: u32,
    },
    /// A tail mentions a variable at or before its head in the order.
    NotTriangular {
        /// The rule's head.
        head: u32,
        /// The offending tail variable.
        var: u32,
    },
}

impl Display for RuleError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidOrder => write!(f, "the variable order is not a permutation"),
            Self::VariableOutOfRange { var } => write!(f, "variable {var} is outside the order"),
            Self::DuplicateHead { head } => write!(f, "two rules have head x{head}"),
            Self::NotTriangular { head, var } => {
                write!(
                    f,
                    "the rule for x{head} mentions x{var}, which is not after it"
                )
            }
        }
    }
}

impl std::error::Error for RuleError {}

/// A variable order: level 0 is the top of every diagram and the largest variable in lex.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VariableOrder {
    var_at: Vec<u32>,
    level_of: Vec<u32>,
}

impl VariableOrder {
    /// The order whose level `i` holds variable `vars[i]`.
    pub fn new(vars: Vec<u32>) -> Result<Self, RuleError> {
        let n = vars.len();
        if n > anf::MAX_VARS {
            return Err(RuleError::InvalidOrder);
        }
        let mut level_of = vec![u32::MAX; n];
        for (level, &v) in vars.iter().enumerate() {
            match level_of.get_mut(v as usize) {
                Some(slot) if *slot == u32::MAX => *slot = level as u32,
                _ => return Err(RuleError::InvalidOrder),
            }
        }
        Ok(Self {
            var_at: vars,
            level_of,
        })
    }

    /// `x_0` at the top, then `x_1`, and so on.
    pub fn identity(n: u32) -> Self {
        Self::new((0..n).collect()).expect("the identity is a permutation")
    }

    /// The number of variables.
    pub fn len(&self) -> usize {
        self.var_at.len()
    }

    /// Whether the order is empty.
    pub fn is_empty(&self) -> bool {
        self.var_at.is_empty()
    }

    /// The level of `v`.
    pub fn level_of(&self, v: u32) -> u32 {
        self.level_of[v as usize]
    }

    /// The variable at `level`.
    pub fn var_at(&self, level: u32) -> u32 {
        self.var_at[level as usize]
    }

    /// Variables from the top.
    pub fn vars(&self) -> &[u32] {
        &self.var_at
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn an_order_must_be_a_permutation() {
        assert_eq!(VariableOrder::new(vec![0, 0]), Err(RuleError::InvalidOrder));
        assert_eq!(VariableOrder::new(vec![0, 2]), Err(RuleError::InvalidOrder));
        let order = VariableOrder::new(vec![2, 0, 1]).unwrap();
        assert_eq!((order.level_of(2), order.var_at(2)), (0, 1));
    }
}
