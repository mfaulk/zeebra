//! Full-degree scalar recurrences yield candidates; operator evaluation certifies every relation.

use rand::{rngs::StdRng, SeedableRng};

use super::{
    shape::shape_relations_vanish, ConversionStrategy, FglmOptions, FglmStatistics, QuotientAlgebra,
};
use crate::{
    xgcd, FiniteField, Monomial, MonomialOrder, MultivariatePolynomial, Polynomial,
    UnivariatePolynomial,
};

/// The algorithm that returned a conversion result.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum ConversionRoute {
    /// The complete lex monomial walk.
    #[default]
    Classical,
    /// Scalar Wiedemann with deterministically verified shape relations.
    Wiedemann,
}

/// Why the classical algorithm was used after considering scalar Wiedemann.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum WiedemannFallback {
    /// Adaptive selection avoids quotients smaller than 128 dimensions.
    SmallQuotient,
    /// The last operator's stored cells plus unit columns exceed a quarter of a dense matrix.
    DenseOperator,
    /// The linear workspace allowance exceeds a cell or byte budget.
    WorkspaceBudget,
    /// None of three projections yielded a full-degree recurrence with invertible numerator.
    ///
    /// This can mean a nonseparating variable or unlucky projections; it is not a shape verdict.
    NonCyclicProjection,
    /// Reconstructed shape relations failed deterministic quotient-algebra evaluation.
    VerificationFailed,
}

/// Conservative allowance for moments, Krylov registers, polynomial arithmetic and verification.
/// Output polynomial maps and allocator overhead follow the classical budget's exclusions.
fn workspace_cells<const N: usize>(dimension: usize) -> Option<usize> {
    dimension
        .checked_add(1)?
        .checked_mul(N.checked_mul(4)?.checked_add(64)?)
}

pub(super) fn try_conversion<const N: usize, F: FiniteField>(
    algebra: &QuotientAlgebra<N, F>,
    options: &FglmOptions,
    stats: &mut FglmStatistics,
) -> Option<Vec<MultivariatePolynomial<N, F>>> {
    let d = algebra.dimension();
    if options.conversion_strategy == ConversionStrategy::Classical || N == 0 || d == 0 {
        return None;
    }
    if options.conversion_strategy == ConversionStrategy::Adaptive {
        if d < 128 {
            stats.wiedemann_fallback = Some(WiedemannFallback::SmallQuotient);
            return None;
        }
        let operator = algebra.operator(N - 1);
        let cost = operator
            .stored_cells()
            .saturating_add(operator.standard_columns());
        if cost > d.saturating_mul(d) / 4 {
            stats.wiedemann_fallback = Some(WiedemannFallback::DenseOperator);
            return None;
        }
    }
    let Some((cells, bytes)) = workspace_cells::<N>(d)
        .and_then(|cells| {
            cells
                .checked_mul(std::mem::size_of::<F>() + std::mem::size_of::<usize>())
                .map(|b| (cells, b))
        })
        .filter(|(cells, bytes)| {
            *cells <= options.max_span_entries && *bytes <= options.max_span_bytes
        })
    else {
        stats.wiedemann_fallback = Some(WiedemannFallback::WorkspaceBudget);
        return None;
    };
    stats.memory.krylov_workspace_cells = cells;
    stats.memory.krylov_workspace_bytes = bytes;
    let mut rng = StdRng::seed_from_u64(0x368_f61a);
    for _ in 0..3 {
        stats.wiedemann_attempts += 1;
        let projection: Vec<F> = (0..d).map(|_| F::random(&mut rng)).collect();
        match reconstruct(algebra, projection) {
            Ok(basis) => {
                stats.conversion_route = ConversionRoute::Wiedemann;
                stats.wiedemann_fallback = None;
                return Some(basis);
            }
            Err(reason) => stats.wiedemann_fallback = Some(reason),
        }
    }
    None
}

fn reconstruct<const N: usize, F: FiniteField>(
    algebra: &QuotientAlgebra<N, F>,
    mut projection: Vec<F>,
) -> Result<Vec<MultivariatePolynomial<N, F>>, WiedemannFallback> {
    let d = algebra.dimension();
    let last = N - 1;
    let operator = algebra.operator(last);
    // Sparse coordinate classes make moment queries cheap when variables remain standard.
    let classes: Vec<Vec<(usize, F)>> = std::iter::once(algebra.one())
        .chain((0..last).map(|i| algebra.multiply_by_variable(i, &algebra.one())))
        .map(|v| {
            v.into_iter()
                .enumerate()
                .filter(|(_, c)| !c.is_zero())
                .collect()
        })
        .collect();
    let mut moments: Vec<Vec<F>> = (0..last).map(|_| Vec::with_capacity(d)).collect();
    let mut sequence = Vec::with_capacity(2 * d);
    for k in 0..2 * d {
        let dot = |class: &[(usize, F)]| {
            class
                .iter()
                .map(|(j, c)| projection[*j] * *c)
                .fold(F::zero(), |a, b| a + b)
        };
        sequence.push(dot(&classes[0]));
        if k < d {
            for (values, class) in moments.iter_mut().zip(&classes[1..]) {
                values.push(dot(class));
            }
        }
        if k + 1 < 2 * d {
            projection = operator.apply_transpose(&projection);
        }
    }
    let p = berlekamp_massey(&sequence);
    if p.len() != d + 1 {
        return Err(WiedemannFallback::NonCyclicProjection);
    }
    let modulus = UnivariatePolynomial::new(&p);
    let mut result = vec![shape_relation(last, last, &p)];
    if last > 0 {
        let numerator = numerator_for(&p, &sequence);
        let (gcd, _, inverse) = xgcd(&modulus, &UnivariatePolynomial::new(&numerator));
        if !gcd.is_one() {
            return Err(WiedemannFallback::NonCyclicProjection);
        }
        for (variable, values) in moments.iter().enumerate() {
            let num = UnivariatePolynomial::new(&numerator_for(&p, values));
            let h = &(&num * &inverse) % &modulus;
            let coefficients: Vec<_> = h.coefficients().iter().map(|c| -*c).collect();
            result.push(shape_relation(variable, last, &coefficients));
        }
    }
    if !certify(algebra, &result) {
        return Err(WiedemannFallback::VerificationFailed);
    }
    result.sort_by(|a, b| {
        MonomialOrder::Lexicographic.cmp(
            &b.leading_monomial(MonomialOrder::Lexicographic),
            &a.leading_monomial(MonomialOrder::Lexicographic),
        )
    });
    Ok(result)
}

/// For moments s_k, [p(t) sum s_k t^(-k-1)]_+ has degree below deg(p).
fn numerator_for<F: FiniteField>(p: &[F], moments: &[F]) -> Vec<F> {
    let d = p.len() - 1;
    (0..d)
        .map(|j| {
            (j + 1..=d)
                .map(|i| p[i] * moments[i - j - 1])
                .fold(F::zero(), |a, b| a + b)
        })
        .collect()
}

/// The monic recurrence polynomial in ascending powers, including nilpotent factors.
fn berlekamp_massey<F: FiniteField>(sequence: &[F]) -> Vec<F> {
    let mut c = vec![F::one()];
    let mut b = c.clone();
    let mut degree = 0;
    let mut shift = 1;
    let mut previous = F::one();
    for (n, value) in sequence.iter().enumerate() {
        let discrepancy = *value
            + (1..=degree)
                .map(|i| c.get(i).copied().unwrap_or(F::zero()) * sequence[n - i])
                .fold(F::zero(), |a, b| a + b);
        if discrepancy.is_zero() {
            shift += 1;
            continue;
        }
        let saved = c.clone();
        let factor = discrepancy / previous;
        c.resize(c.len().max(b.len() + shift), F::zero());
        for (i, coefficient) in b.iter().enumerate() {
            c[i + shift] -= factor * *coefficient;
        }
        if 2 * degree <= n {
            degree = n + 1 - degree;
            b = saved;
            previous = discrepancy;
            shift = 1;
        } else {
            shift += 1;
        }
    }
    c.resize(degree + 1, F::zero());
    c.reverse();
    c
}

fn shape_relation<const N: usize, F: FiniteField>(
    variable: usize,
    last: usize,
    coefficients: &[F],
) -> MultivariatePolynomial<N, F> {
    let mut terms: Vec<_> = coefficients
        .iter()
        .enumerate()
        .filter(|(_, c)| !c.is_zero())
        .map(|(k, c)| (Monomial::univariate(last, k as u32), *c))
        .collect();
    if variable != last {
        terms.push((Monomial::univariate(variable, 1), F::one()));
    }
    MultivariatePolynomial::new(&terms)
}

/// Membership plus these leading monomials gives the source quotient dimension, proving a basis.
fn certify<const N: usize, F: FiniteField>(
    algebra: &QuotientAlgebra<N, F>,
    basis: &[MultivariatePolynomial<N, F>],
) -> bool {
    let last = N - 1;
    basis.len() == N
        && basis.iter().enumerate().all(|(at, p)| {
            let (variable, exponent) = if at == 0 {
                (last, algebra.dimension())
            } else {
                (at - 1, 1)
            };
            let lead = Monomial::univariate(variable, exponent as u32);
            p.leading_monomial(MonomialOrder::Lexicographic) == lead
                && p.terms().get(&lead) == Some(&F::one())
        })
        && shape_relations_vanish(algebra, basis, last)
}

#[cfg(test)]
mod tests {
    use super::{berlekamp_massey, certify, numerator_for, reconstruct};
    use crate::{
        fields::Zp13 as F,
        grobner::{
            f4,
            fglm::{FglmOptions, QuotientAlgebra},
        },
        FiniteField, MonomialOrder, MultivariatePolynomial, One, Zero,
    };

    // A finite impulse retains its nilpotent factor instead of collapsing to a squarefree relation.
    #[test]
    fn recurrence_preserves_nilpotents_and_zero_sequences() {
        let sequence = [F::zero(), F::one(), F::zero(), F::zero()];
        assert_eq!(
            berlekamp_massey(&sequence),
            vec![F::zero(), F::zero(), F::one()]
        );
        assert_eq!(berlekamp_massey(&[F::zero(); 6]), vec![F::one()]);
    }

    // Every term of a known order-three recurrence agrees with the recovered ascending polynomial.
    #[test]
    fn recurrence_matches_a_known_polynomial() {
        let p = [F::new(2), F::new(3), F::new(4), F::one()];
        let mut values = vec![F::new(5), F::new(7), F::new(11)];
        for k in 3..12 {
            values.push(
                -(0..3)
                    .map(|i| p[i] * values[k - 3 + i])
                    .fold(F::zero(), |a, b| a + b),
            );
        }
        assert_eq!(berlekamp_massey(&values), p);
    }

    // Rational numerators reconstruct a shifted moment series modulo its recurrence polynomial.
    #[test]
    fn numerator_agrees_with_the_shift_identity() {
        let p = [F::new(2), F::new(3), F::one()];
        let sequence = [
            F::new(5),
            F::new(7),
            -(F::new(2) * F::new(5) + F::new(3) * F::new(7)),
        ];
        assert_eq!(numerator_for(&p, &sequence), vec![F::new(9), F::new(5)]);
        assert_eq!(
            numerator_for(&p, &sequence[1..]),
            vec![-F::new(10), F::new(7)]
        );
    }

    // Certification rejects a corrupted relation even when the leading shape is unchanged.
    #[test]
    fn independent_certification_rejects_tampering() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let source: Vec<MultivariatePolynomial<2, F>> = ["x-y", "y^3-1"]
            .iter()
            .map(|s| MultivariatePolynomial::parse(s, ["x", "y"]).unwrap())
            .collect();
        let source = f4(&source, order).unwrap();
        let algebra = QuotientAlgebra::new(&source, order, &FglmOptions::recommended()).unwrap();
        let mut result = reconstruct(&algebra, vec![F::one(), F::new(2), F::new(3)]).unwrap();
        assert!(certify(&algebra, &{
            let mut v = result.clone();
            v.reverse();
            v
        }));
        let constant = MultivariatePolynomial::parse("1", ["x", "y"]).unwrap();
        result[0] = &result[0] + &constant;
        result.reverse();
        assert!(!certify(&algebra, &result));
        assert!(reconstruct(&algebra, vec![F::zero(); 3]).is_err());
    }
    // Fast conversion and classical FGLM agree across prime, binary, extension and wide fields.
    crate::for_each_field!(
        fn conversion_agrees_in_every_field<K>() {
            use crate::grobner::fglm::{
                fglm_to_lex_with_options, ConversionRoute, ConversionStrategy,
            };
            let order = MonomialOrder::GradedReverseLexicographic;
            let input: Vec<MultivariatePolynomial<2, K>> = ["x-y^2", "y^7-y-1"]
                .iter()
                .map(|s| MultivariatePolynomial::parse(s, ["x", "y"]).unwrap())
                .collect();
            let source = f4(&input, order).unwrap();
            let options = FglmOptions {
                conversion_strategy: ConversionStrategy::Wiedemann,
                ..FglmOptions::recommended()
            };
            let (fast, stats) = fglm_to_lex_with_options(&source, order, &options).unwrap();
            let (classical, _) =
                fglm_to_lex_with_options(&source, order, &FglmOptions::recommended()).unwrap();
            assert_eq!(fast, classical);
            assert_eq!(stats.conversion_route, ConversionRoute::Wiedemann);
            for relation in fast {
                assert!(relation.normal_form(&source, order).is_zero());
            }
        }
    );
}
