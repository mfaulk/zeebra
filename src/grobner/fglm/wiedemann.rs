//! Full-degree scalar recurrences yield candidates; operator evaluation certifies every relation.

use rand::{rngs::StdRng, SeedableRng};

use super::{
    shape::shape_relations_vanish_controlled, ConversionStrategy, FglmControl, FglmError,
    FglmOptions, FglmStage, FglmStatistics, QuotientAlgebra, SAFE_POINT_STRIDE,
};
use crate::{
    berlekamp_massey, poly::PreparedDivisor, xgcd, FiniteField, Monomial, MonomialOrder,
    MultivariatePolynomial, Polynomial, UnivariatePolynomial,
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

/// The largest quotient dimension a conversion under `options` may enumerate.
///
/// `max_quotient_dimension` caps the classical walk, whose dense blocks are `O(D^2)`. A strategy
/// that may attempt Wiedemann can enumerate past it, up to the largest `D` whose linear workspace
/// allowance fits both span budgets — so the enumeration stays bounded by the budgets that bound
/// memory, and a quotient above the cap is only ever converted by Wiedemann (#1111).
pub(crate) fn dimension_ceiling<const N: usize, F: FiniteField>(options: &FglmOptions) -> usize {
    let cap = options.max_quotient_dimension;
    if options.conversion_strategy == ConversionStrategy::Classical || N == 0 {
        return cap;
    }
    let Some(per_dimension) = workspace_cells::<N>(0) else {
        return cap;
    };
    let cell_bytes = std::mem::size_of::<F>() + std::mem::size_of::<usize>();
    let rows = (options.max_span_entries / per_dimension)
        .min(options.max_span_bytes / cell_bytes / per_dimension);
    cap.max(rows.saturating_sub(1))
}

/// A Wiedemann conversion of `algebra`, `Ok(None)` if it was declined or every attempt failed, or
/// the stop `control` ordered at one of the attempts' safe points.
///
/// The control is the caller's and is not reset, so a classical fallback after `Ok(None)` polls
/// the same deadline this spent from.
pub(super) fn try_conversion<const N: usize, F: FiniteField>(
    algebra: &QuotientAlgebra<N, F>,
    options: &FglmOptions,
    control: &FglmControl<'_>,
    stats: &mut FglmStatistics,
) -> Result<Option<Vec<MultivariatePolynomial<N, F>>>, FglmError> {
    let d = algebra.dimension();
    if options.conversion_strategy == ConversionStrategy::Classical || N == 0 || d == 0 {
        return Ok(None);
    }
    if options.conversion_strategy == ConversionStrategy::Adaptive {
        if d < 128 {
            stats.wiedemann_fallback = Some(WiedemannFallback::SmallQuotient);
            return Ok(None);
        }
        let operator = algebra.operator(N - 1);
        let cost = operator
            .stored_cells()
            .saturating_add(operator.standard_columns());
        if cost > d.saturating_mul(d) / 4 {
            stats.wiedemann_fallback = Some(WiedemannFallback::DenseOperator);
            return Ok(None);
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
        return Ok(None);
    };
    stats.memory.krylov_workspace_cells = cells;
    stats.memory.krylov_workspace_bytes = bytes;
    let mut rng = StdRng::seed_from_u64(0x368_f61a);
    for _ in 0..3 {
        control.poll(FglmStage::Wiedemann)?;
        stats.wiedemann_attempts += 1;
        let projection: Vec<F> = (0..d).map(|_| F::random(&mut rng)).collect();
        match reconstruct(algebra, projection, options.measure_stages, control, stats)? {
            Ok(basis) => {
                stats.conversion_route = ConversionRoute::Wiedemann;
                stats.wiedemann_fallback = None;
                return Ok(Some(basis));
            }
            Err(reason) => stats.wiedemann_fallback = Some(reason),
        }
    }
    Ok(None)
}

/// One scalar attempt: the certified shape basis, why it was rejected, or the stop `control`
/// ordered at one of its safe points.
type Attempt<const N: usize, F> =
    Result<Result<Vec<MultivariatePolynomial<N, F>>, WiedemannFallback>, FglmError>;

fn reconstruct<const N: usize, F: FiniteField>(
    algebra: &QuotientAlgebra<N, F>,
    mut projection: Vec<F>,
    measured: bool,
    control: &FglmControl<'_>,
    stats: &mut FglmStatistics,
) -> Attempt<N, F> {
    let mut clock = crate::grobner::f4::StageClock::new(measured);
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
        if k.is_multiple_of(SAFE_POINT_STRIDE) {
            if let Err(stop) = control.poll(FglmStage::Wiedemann) {
                stats.timings.scalar_sequence += clock.lap();
                return Err(stop);
            }
        }
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
    stats.timings.scalar_sequence += clock.lap();
    control.poll(FglmStage::Wiedemann)?;
    let reconstructed = (|| {
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
            // Every product below has fewer than 2d coefficients, so one reciprocal serves them all.
            let reducer = PreparedDivisor::new(&modulus, d);
            for (variable, values) in moments.iter().enumerate() {
                let num = UnivariatePolynomial::new(&numerator_for(&p, values));
                let h = reducer.rem(&(&num * &inverse));
                let coefficients: Vec<_> = h.coefficients().iter().map(|c| -*c).collect();
                result.push(shape_relation(variable, last, &coefficients));
            }
        }
        Ok(result)
    })();
    stats.timings.scalar_reconstruction += clock.lap();
    let mut result = match reconstructed {
        Ok(result) => result,
        Err(reason) => return Ok(Err(reason)),
    };
    control.poll(FglmStage::Wiedemann)?;
    let certified = certify(algebra, &result, control);
    stats.timings.scalar_certificate += clock.lap();
    if !certified? {
        return Ok(Err(WiedemannFallback::VerificationFailed));
    }
    result.sort_by(|a, b| {
        MonomialOrder::Lexicographic.cmp(
            &b.leading_monomial(MonomialOrder::Lexicographic),
            &a.leading_monomial(MonomialOrder::Lexicographic),
        )
    });
    Ok(Ok(result))
}

/// For moments s_k, [p(t) sum s_k t^(-k-1)]_+ has degree below deg(p).
///
/// Coefficient j is `sum_k p[j+1+k] s_k`, a correlation, so it is read off one product of the
/// reversed recurrence with the first `deg p` moments: coefficient `deg p - 1 - j` of that product.
fn numerator_for<F: FiniteField>(p: &[F], moments: &[F]) -> Vec<F> {
    let d = p.len() - 1;
    let reversed: Vec<F> = p.iter().rev().copied().collect();
    let product = &UnivariatePolynomial::new(&reversed) * &UnivariatePolynomial::new(&moments[..d]);
    let coefficients = product.coefficients();
    (0..d)
        .map(|j| coefficients.get(d - 1 - j).copied().unwrap_or(F::zero()))
        .collect()
}

/// The quadratic definition [`numerator_for`] replaces, kept as its differential oracle.
#[cfg(test)]
fn numerator_for_classical<F: FiniteField>(p: &[F], moments: &[F]) -> Vec<F> {
    let d = p.len() - 1;
    (0..d)
        .map(|j| {
            (j + 1..=d)
                .map(|i| p[i] * moments[i - j - 1])
                .fold(F::zero(), |a, b| a + b)
        })
        .collect()
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
    control: &FglmControl<'_>,
) -> Result<bool, FglmError> {
    let last = N - 1;
    let shaped = basis.len() == N
        && basis.iter().enumerate().all(|(at, p)| {
            let (variable, exponent) = if at == 0 {
                (last, algebra.dimension())
            } else {
                (at - 1, 1)
            };
            let lead = Monomial::univariate(variable, exponent as u32);
            p.leading_monomial(MonomialOrder::Lexicographic) == lead
                && p.terms().get(&lead) == Some(&F::one())
        });
    if !shaped {
        return Ok(false);
    }
    shape_relations_vanish_controlled(algebra, basis, last, control, FglmStage::Wiedemann)
}

#[cfg(test)]
mod tests {
    use super::{
        certify, dimension_ceiling, numerator_for, numerator_for_classical, reconstruct,
        ConversionStrategy,
    };
    use crate::grobner::FglmStatistics;
    use crate::{
        fields::Zp13 as F,
        grobner::{
            f4,
            fglm::{FglmControl, FglmOptions, QuotientAlgebra},
        },
        FiniteField, MonomialOrder, MultivariatePolynomial, One, Zero,
    };

    // The enumeration ceiling is the largest D whose linear workspace fits both span budgets.
    #[test]
    fn dimension_ceiling_is_the_workspace_budget_inverse() {
        type P = crate::fields::Zp2147483647;
        let recommended = FglmOptions::recommended();
        // (D + 1) * (4 * 14 + 64) <= 20,000,000 cells, and the 320 MB byte budget at 16 bytes a
        // cell admits the same 20,000,000.
        assert_eq!(dimension_ceiling::<14, P>(&recommended), 166_665);
        let classical = FglmOptions {
            conversion_strategy: ConversionStrategy::Classical,
            ..recommended
        };
        assert_eq!(dimension_ceiling::<14, P>(&classical), 4_096);
        // A cap above what the workspace admits is never lowered.
        let tight = FglmOptions {
            max_span_entries: 1_000,
            ..recommended
        };
        assert_eq!(dimension_ceiling::<14, P>(&tight), 4_096);
        assert_eq!(
            dimension_ceiling::<14, P>(&FglmOptions {
                max_quotient_dimension: 0,
                ..tight
            }),
            7
        );
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

    // The product-based numerator equals the quadratic correlation on both sides of Karatsuba's base case.
    #[test]
    fn numerator_matches_the_classical_correlation() {
        use rand::{rngs::StdRng, SeedableRng};
        type W = crate::fields::Zp2147483647;
        let mut rng = StdRng::seed_from_u64(806);
        for d in [1, 2, 3, 17, 64, 65, 300, 1025] {
            let mut p: Vec<W> = (0..d).map(|_| W::random(&mut rng)).collect();
            p.push(W::one());
            if d % 2 == 1 {
                p[0] = W::zero();
            }
            let moments: Vec<W> = (0..2 * d).map(|_| W::random(&mut rng)).collect();
            assert_eq!(
                numerator_for(&p, &moments),
                numerator_for_classical(&p, &moments),
                "d = {d}"
            );
            let sparse = vec![W::zero(); d];
            assert_eq!(numerator_for(&p, &sparse), vec![W::zero(); d]);
        }
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
        let mut result = reconstruct(
            &algebra,
            vec![F::one(), F::new(2), F::new(3)],
            false,
            &FglmControl::unlimited(),
            &mut FglmStatistics::default(),
        )
        .unwrap()
        .unwrap();
        let unlimited = FglmControl::unlimited();
        assert!(certify(
            &algebra,
            &{
                let mut v = result.clone();
                v.reverse();
                v
            },
            &unlimited
        )
        .unwrap());
        let constant = MultivariatePolynomial::parse("1", ["x", "y"]).unwrap();
        result[0] = &result[0] + &constant;
        result.reverse();
        assert!(!certify(&algebra, &result, &unlimited).unwrap());
        assert!(reconstruct(
            &algebra,
            vec![F::zero(); 3],
            false,
            &unlimited,
            &mut FglmStatistics::default()
        )
        .unwrap()
        .is_err());
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
