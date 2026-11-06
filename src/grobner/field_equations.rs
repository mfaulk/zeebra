//! Field equations `x^q - x`, and when adjoining them is the difference between two problems.
//!
//! A system over `F_q` has two solution sets and they are not the same: the points of the variety
//! over the algebraic closure, which is what an ideal in `F_q[x_0, ..., x_{N-1}]` describes, and
//! the points with coordinates **in `F_q` itself**, which is what a cryptanalytic problem asks
//! for. The second is cut out by adjoining `x_i^q - x_i` for every variable, since that polynomial
//! has exactly the elements of `F_q` as roots and each with multiplicity one.
//!
//! Two consequences, and the second is the one that makes this module worth having:
//!
//! - **The dimension changes.** `I` may be positive-dimensional while `I + <x_i^q - x_i>` is
//!   always zero-dimensional, because the quotient is spanned by the finitely many monomials with
//!   every exponent below `q`.
//! - **The ideal becomes radical.** `x^q - x` is squarefree and splits completely over `F_q`, so
//!   `dim F_q[x]/(I + <x_i^q - x_i>)` is *exactly* the number of `F_q`-rational points — counted
//!   once each, however many times they occur in `I`. That turns a solution count into a
//!   machine-independent invariant, which is what `tests` below checks against brute force.
//!
//! **Whether to adjoin them is a judgement about `q`, not a default.** The generator has degree
//! `q`, so the cost is only acceptable when `q` is below the degree the computation would reach
//! anyway. Over `GF(2)` that is degree 2 and the answer is essentially always yes. Over `GF(31)`
//! — Fukuoka MQ types III and VI — it is degree 31, against measured solving degrees of 4 to 9 on
//! those instances, so the answer is no. Over `GF(65521)`, the Courtois MinRank challenge field,
//! degree 65521 is absurd and the answer is never. Nothing here chooses for the caller.

use std::fmt::{self, Display, Formatter};

use crate::{KnownOrder, Monomial, MultivariatePolynomial};

/// Why field equations could not be constructed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FieldEquationError {
    /// The field order does not fit a monomial exponent, so `x^q` cannot be represented.
    ///
    /// `Monomial` stores exponents as `u32`. This is a representation limit rather than a policy:
    /// a field whose order exceeds it has field equations that no computation here could use, so
    /// refusing is the same answer arrived at sooner.
    OrderNotRepresentable {
        /// The order, where it is known at all. `None` for a field too wide for a `u128`.
        order: Option<u128>,
    },
}

impl Display for FieldEquationError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::OrderNotRepresentable { order: Some(q) } => write!(
                f,
                "the field order {q} exceeds u32::MAX, so x^q is not a representable monomial"
            ),
            Self::OrderNotRepresentable { order: None } => write!(
                f,
                "the field order does not fit a u128, so x^q is not a representable monomial"
            ),
        }
    }
}

impl std::error::Error for FieldEquationError {}

/// The field equations `x_i^q - x_i`, one per variable.
///
/// Returns `Err` when `q` does not fit a monomial exponent; see [`FieldEquationError`].
pub fn field_equations<const N: usize, F: KnownOrder>(
) -> Result<Vec<MultivariatePolynomial<N, F>>, FieldEquationError> {
    let order = F::order_u128();
    let q = match order {
        Some(q) if q <= u32::MAX as u128 => q as u32,
        _ => return Err(FieldEquationError::OrderNotRepresentable { order }),
    };

    Ok((0..N)
        .map(|i| {
            let mut power = [0u32; N];
            power[i] = q;
            let mut linear = [0u32; N];
            linear[i] = 1;
            // `F::zero() - F::one()` rather than a literal -1, because in characteristic two the
            // two coincide and writing the subtraction keeps one expression correct in both cases.
            MultivariatePolynomial::new(&[
                (Monomial::new(&power), F::one()),
                (Monomial::new(&linear), F::zero() - F::one()),
            ])
        })
        .collect())
}

/// `system` with the field equations appended, so its variety is the `F_q`-rational points.
///
/// The simple mechanism: `N` extra generators. The alternative — reducing exponents modulo
/// `x^q - x` inside monomial arithmetic, as PolyBoRi does with a ZDD over `GF(2)` — is faster and
/// changes what `Monomial` means, so it is a separate decision and is deliberately not taken here.
pub fn with_field_equations<const N: usize, F: KnownOrder>(
    system: &[MultivariatePolynomial<N, F>],
) -> Result<Vec<MultivariatePolynomial<N, F>>, FieldEquationError> {
    let mut extended = system.to_vec();
    extended.extend(field_equations::<N, F>()?);
    Ok(extended)
}

/// Every `F_q`-rational point of `system`, by evaluating it at all `q^N` assignments.
///
/// Exponential and deliberately so: this is an oracle, not an algorithm. It exists to check a
/// quotient dimension against a count that cannot be wrong, which is only possible while `q^N` is
/// small. `KnownOrder::enumerate`-style iteration is not available, so the field is enumerated
/// through `F::new` over `0..q`.
pub fn rational_points_by_enumeration<const N: usize, F: KnownOrder>(
    system: &[MultivariatePolynomial<N, F>],
) -> Result<Vec<[F; N]>, FieldEquationError> {
    let order = F::order_u128();
    let q = match order {
        Some(q) if q <= u32::MAX as u128 => q as u64,
        _ => return Err(FieldEquationError::OrderNotRepresentable { order }),
    };

    let total = q
        .checked_pow(N as u32)
        .expect("q^N must fit a u64 to enumerate");
    let mut points = Vec::new();
    for index in 0..total {
        let mut assignment = [F::zero(); N];
        let mut remaining = index;
        for slot in assignment.iter_mut() {
            *slot = F::new(remaining % q);
            remaining /= q;
        }
        if system.iter().all(|p| p.eval(&assignment).is_zero()) {
            points.push(assignment);
        }
    }
    Ok(points)
}

#[cfg(test)]
mod tests {
    use rand::{prelude::StdRng, Rng, SeedableRng};

    use super::*;
    use crate::{
        fields::{Gf256, Zp2, Zp31},
        grobner::{classify_ideal, f4, is_grobner_basis, IdealClass, QuotientBasis},
        FiniteField, MonomialOrder, One, Zero,
    };

    /// Over GF(2) the field equation is `x^2 + x`, since -1 = 1 there.
    #[test]
    fn the_gf2_field_equation_is_x_squared_plus_x() {
        let equations = field_equations::<2, Zp2>().expect("GF(2) has a representable order");
        assert_eq!(equations.len(), 2);

        let expected: MultivariatePolynomial<2, Zp2> = MultivariatePolynomial::new(&[
            (Monomial::new(&[2, 0]), Zp2::one()),
            (Monomial::new(&[1, 0]), Zp2::one()),
        ]);
        assert_eq!(equations[0], expected);
    }

    /// The generator's degree is the field order, which is the whole cost argument.
    #[test]
    fn the_field_equation_has_degree_q() {
        let gf2 = field_equations::<1, Zp2>().expect("representable");
        assert_eq!(gf2[0].degree(), 2);

        let gf31 = field_equations::<1, Zp31>().expect("representable");
        assert_eq!(gf31[0].degree(), 31);

        let gf256 = field_equations::<1, Gf256>().expect("representable");
        assert_eq!(gf256[0].degree(), 256);
    }

    /// A field whose order exceeds a monomial exponent is refused as a value, not a panic.
    #[test]
    fn an_order_above_u32_max_is_refused() {
        use crate::fields::Bn254Fr;

        assert_eq!(
            field_equations::<1, Bn254Fr>(),
            Err(FieldEquationError::OrderNotRepresentable { order: None }),
        );
    }

    /// Field equations are satisfied by exactly the base-field elements.
    #[test]
    fn the_field_equation_vanishes_on_the_whole_field_and_nowhere_else() {
        let equation = &field_equations::<1, Zp31>().expect("representable")[0];
        for value in 0..31u64 {
            assert!(
                equation.eval(&[Zp31::new(value)]).is_zero(),
                "x^31 - x must vanish at {value}"
            );
        }
        // Over GF(31) there is nothing outside the field to test against, so the companion check
        // is that the polynomial is not identically zero as a polynomial.
        assert_eq!(equation.degree(), 31);
    }

    /// **The point of the module.** With field equations the quotient dimension counts the
    /// GF(2)-rational points exactly; without them it does not.
    ///
    /// `n = 8` makes brute force 256 assignments, so the comparand is a complete enumeration and
    /// cannot itself be wrong. The ideal with field equations adjoined is radical — `x^2 - x` is
    /// squarefree and splits over GF(2) — so its quotient dimension *is* the point count.
    #[test]
    fn the_quotient_dimension_counts_gf2_points_only_with_field_equations() {
        let grevlex = MonomialOrder::GradedReverseLexicographic;
        let mut rng = StdRng::seed_from_u64(9);

        // A random quadratic system in 8 Boolean variables with a planted solution, built so that
        // every generator vanishes at the plant by construction rather than by search.
        let plant: [Zp2; 8] = std::array::from_fn(|_| Zp2::new(rng.gen_range(0..2)));
        let mut system: Vec<MultivariatePolynomial<8, Zp2>> = Vec::new();
        for _ in 0..6 {
            let mut terms: Vec<([u32; 8], Zp2)> = Vec::new();
            for i in 0..8 {
                for j in i..8 {
                    if rng.gen_bool(0.3) {
                        let mut exponents = [0u32; 8];
                        exponents[i] += 1;
                        exponents[j] += 1;
                        terms.push((exponents, Zp2::one()));
                    }
                }
            }
            let mut polynomial: MultivariatePolynomial<8, Zp2> = MultivariatePolynomial::new(
                &terms
                    .iter()
                    .map(|(e, c)| (Monomial::new(e), *c))
                    .collect::<Vec<_>>(),
            );
            // Subtract the value at the plant, making the constant term whatever it must be.
            let value = polynomial.eval(&plant);
            polynomial += MultivariatePolynomial::new(&[(Monomial::one(), Zp2::zero() - value)]);
            assert!(polynomial.eval(&plant).is_zero());
            system.push(polynomial);
        }

        let points = rational_points_by_enumeration(&system).expect("GF(2) enumerates");
        assert!(
            points.contains(&plant),
            "the planted point must be among the enumerated solutions"
        );

        let extended = with_field_equations(&system).expect("GF(2) has field equations");
        let basis = f4(&extended, grevlex).expect("within the default budgets");
        assert!(is_grobner_basis(&basis, grevlex));
        assert_eq!(classify_ideal(&basis, grevlex), IdealClass::ZeroDimensional);

        let quotient = QuotientBasis::new(&basis, grevlex, 4096).expect("zero-dimensional");
        assert_eq!(
            quotient.dimension(),
            points.len(),
            "with field equations the ideal is radical, so dim F_2[x]/I is the GF(2)-point count"
        );

        // And without them it is a different ideal. Which way it differs is not fixed in advance
        // — it may stay positive-dimensional, or be zero-dimensional with a larger dimension
        // counting points over extensions and multiplicities — so the claim is that the dimension
        // is not the point count, not a specific alternative value.
        //
        // On this seed it is the former: six quadratics in eight variables are underdetermined,
        // the bare ideal is positive-dimensional, and FGLM does not apply to it at all. The two
        // GF(2) points become a quotient of dimension two once the field equations are adjoined.
        let bare = f4(&system, grevlex).expect("within the default budgets");
        let bare_dimension = match classify_ideal(&bare, grevlex) {
            IdealClass::PositiveDimensional => None,
            _ => Some(
                QuotientBasis::new(&bare, grevlex, 65536)
                    .expect("finite-dimensional")
                    .dimension(),
            ),
        };
        assert_ne!(
            bare_dimension,
            Some(points.len()),
            "if the bare ideal already had the point count as its dimension, the field equations \
             would be inert here and this test would say nothing"
        );
    }
}
