//! The `(1,[1])` round skip and the univariate output polynomial it induces.
//!
//! The construction is derived in `docs/research/graeffe-root-finding.md` §9.5.2 from 2026/1254
//! §2.2, for Zeebra's hybrid `permutation_plus_linear` rather than for Poseidon or Poseidon2. Two
//! invariants carry the correctness and both are asserted in this module's tests, because neither
//! is visible in the code: every point of a [`CicoFamily`] lifts to a permutation input whose
//! constrained coordinates hold identically, and [`cico_univariate_family`] agrees with running the
//! permutation on the lifted input.

use std::time::{Duration, Instant};

use rand::SeedableRng;

use crate::{
    fft::{interpolate, FFTDomain},
    grobner::research::poseidon::{CicoInstance, Poseidon, PoseidonError, PoseidonParameters},
    linalg::Matrix,
    poly::{Polynomial, UnivariatePolynomial},
    FiniteField, KnownOrder,
};

/// Degree bound at or below which the univariate is built symbolically rather than by evaluation.
///
/// Straight-line multiplication of dense univariates is cheaper than standing up an FFT domain
/// until the polynomial is a few thousand terms wide. The registered reductions straddle this:
/// `R_F + R_P ≤ 8` stays symbolic, the `3^13` target does not.
pub const SYMBOLIC_CROSSOVER: usize = 4096;

/// Where the degree-`δ` univariate was built.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnivariateRoute {
    /// Straight-line evaluation over `UnivariatePolynomial<F>`.
    Symbolic { degree_bound: usize },
    /// Evaluation at `1 << log_size` points of a two-adic subgroup, recovered by `fft::interpolate`.
    Evaluation { log_size: u32 },
}

/// The route [`cico_univariate_family`] takes at the given degree bound.
#[must_use]
pub fn univariate_route(degree_bound: usize) -> UnivariateRoute {
    if degree_bound <= SYMBOLIC_CROSSOVER {
        UnivariateRoute::Symbolic { degree_bound }
    } else {
        let points = degree_bound.saturating_add(1).next_power_of_two().max(2);
        UnivariateRoute::Evaluation {
            log_size: points.trailing_zeros(),
        }
    }
}

/// A failure to build or use a round-skipping family.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FamilyError {
    Poseidon(PoseidonError),
    /// `gcd(alpha, p - 1) != 1`, so the S-box is not a bijection and `z = y^{1/alpha}` is undefined.
    SboxNotInvertible {
        alpha: u32,
        order: u64,
    },
    /// The two supports must be disjoint for the skipped state to be affine in `Z = X^alpha`.
    SupportsOverlap {
        index: usize,
    },
    /// A support was out of range, had a repeated index, or was the wrong size for `k`.
    BadSupport {
        expected: usize,
        found: usize,
    },
    /// The state is too narrow to hold `k` base and `k + 1` direction coordinates disjointly.
    StateTooNarrow {
        t: usize,
        needed: usize,
    },
    /// A minor of `M^{-1}` that an MDS matrix makes nonsingular came back singular.
    SingularMinor,
    /// The degree bound needs more two-adic points than the field has.
    DomainTooLarge {
        degree_bound: usize,
        two_adicity: u32,
    },
}

impl From<PoseidonError> for FamilyError {
    fn from(error: PoseidonError) -> Self {
        FamilyError::Poseidon(error)
    }
}

impl std::fmt::Display for FamilyError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            FamilyError::Poseidon(error) => write!(f, "{error}"),
            FamilyError::SboxNotInvertible { alpha, order } => write!(
                f,
                "the S-box x^{alpha} is not a bijection: gcd({alpha}, {order} - 1) != 1"
            ),
            FamilyError::SupportsOverlap { index } => {
                write!(
                    f,
                    "index {index} is in both the base and direction supports"
                )
            }
            FamilyError::BadSupport { expected, found } => {
                write!(
                    f,
                    "expected a support of {expected} distinct indices, found {found}"
                )
            }
            FamilyError::StateTooNarrow { t, needed } => {
                write!(
                    f,
                    "a state of width {t} cannot hold {needed} disjoint support indices"
                )
            }
            FamilyError::SingularMinor => {
                write!(f, "a minor of the inverse MDS matrix was singular")
            }
            FamilyError::DomainTooLarge {
                degree_bound,
                two_adicity,
            } => write!(
                f,
                "degree bound {degree_bound} needs more than 2^{two_adicity} two-adic points"
            ),
        }
    }
}

impl std::error::Error for FamilyError {}

/// A one-parameter CICO-preserving family: the `(1,[1])` round skip of 2026/1254 §2.2, derived for
/// `permutation_plus_linear` in `docs/research/graeffe-root-finding.md` §9.5.2.
///
/// The skipped state is affine in the search parameter — `y_i(Z) = base[i] + direction[i] * Z` —
/// which is what buys the factor `alpha` in the final degree, and holds only because the two
/// supports are disjoint.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CicoFamily<F: KnownOrder> {
    /// The base point in root coordinates, `z*`. Supported on `base_support`.
    pub z_star: Vec<F>,
    /// The direction in root coordinates, `v`, normalized so its first supported entry is one.
    pub v: Vec<F>,
    /// `z*_i^alpha`: the constant term of the skipped state.
    pub base: Vec<F>,
    /// `v_i^alpha`: the linear term of the skipped state, in `Z = X^alpha`.
    pub direction: Vec<F>,
    pub base_support: Vec<usize>,
    pub direction_support: Vec<usize>,
    /// `alpha^{-1} mod (p - 1)`, so a search point `Z` can be lifted back through the S-box.
    inverse_alpha: u128,
}

impl<F: KnownOrder> CicoFamily<F> {
    /// The skipped state `y(Z)`, immediately after the first full round's S-box layer and before
    /// that round's MDS.
    #[must_use]
    pub fn skipped_state(&self, z: F) -> Vec<F> {
        self.base
            .iter()
            .zip(&self.direction)
            .map(|(b, d)| *b + *d * z)
            .collect()
    }

    /// The full permutation input that `Z` parametrizes.
    ///
    /// Its first `k` coordinates equal the instance's input constants identically in `Z`; that is
    /// the invariant the family exists to provide and it is asserted, not assumed.
    pub fn lift(&self, instance: &CicoInstance<F>, z: F) -> Result<Vec<F>, FamilyError> {
        let poseidon = &instance.poseidon;
        let x = z.pow(self.inverse_alpha);
        let root: Vec<F> = self
            .z_star
            .iter()
            .zip(&self.v)
            .map(|(zs, v)| *zs + *v * x)
            .collect();
        let shifted: Vec<F> = root
            .iter()
            .zip(&poseidon.round_constants[0])
            .map(|(r, c)| *r - *c)
            .collect();
        let inverse = inverse_mds(poseidon)?;
        Ok(apply(&inverse, &shifted))
    }

    /// The free inputs of the lifted point, ready for [`CicoInstance::is_solution`].
    pub fn lift_free(&self, instance: &CicoInstance<F>, z: F) -> Result<Vec<F>, FamilyError> {
        Ok(self.lift(instance, z)?.split_off(instance.k))
    }
}

/// Build a `(1,[1])` family from a choice of supports.
///
/// `base_support` carries the base point and needs `k` indices — the `k` input constraints are `k`
/// affine equations in the skipped state's root coordinates. `direction_support` needs `k + 1`, one
/// more than the `k` homogeneous equations, so that a nonzero kernel vector exists. The two must be
/// disjoint, which is what makes the skipped state affine in `Z = X^alpha` rather than degree
/// `alpha` in `X`.
pub fn parametrize<F: KnownOrder>(
    instance: &CicoInstance<F>,
    base_support: &[usize],
    direction_support: &[usize],
) -> Result<CicoFamily<F>, FamilyError> {
    let poseidon = &instance.poseidon;
    let parameters = poseidon.parameters;
    let t = parameters.t;
    let k = instance.k;

    if base_support.len() != k {
        return Err(FamilyError::BadSupport {
            expected: k,
            found: base_support.len(),
        });
    }
    if direction_support.len() != k + 1 {
        return Err(FamilyError::BadSupport {
            expected: k + 1,
            found: direction_support.len(),
        });
    }
    if t < 2 * k + 1 {
        return Err(FamilyError::StateTooNarrow {
            t,
            needed: 2 * k + 1,
        });
    }
    check_distinct(base_support, t)?;
    check_distinct(direction_support, t)?;
    for index in base_support {
        if direction_support.contains(index) {
            return Err(FamilyError::SupportsOverlap { index: *index });
        }
    }

    let inverse_alpha = inverse_mod(
        u128::from(parameters.alpha),
        u128::from(parameters.prime) - 1,
    )
    .ok_or(FamilyError::SboxNotInvertible {
        alpha: parameters.alpha,
        order: parameters.prime,
    })?;

    let inverse = inverse_mds(poseidon)?;
    // Rows 0..k of M^{-1}. The constrained inputs sit in coordinates 0..k, because
    // `CicoInstance::is_solution` builds its state as `constants[..k] ++ free`; 2026/1254 §2.2
    // writes the same construction against the *last* k rows for inputs in the last k coordinates,
    // and §3.2 makes exactly this substitution for its own instance.
    let lambda: Vec<Vec<F>> = (0..k).map(|j| inverse.row(j).copied().collect()).collect();

    // The k affine equations. The right-hand sides carry no alpha-th power: the prefix is the
    // initial linear layer plus one full round, so the input constraint reaches the root
    // coordinates through one constant vector and no S-box. See §9.5.2.
    let rhs: Vec<F> = (0..k)
        .map(|j| {
            let correction = lambda[j]
                .iter()
                .zip(&poseidon.round_constants[0])
                .fold(F::zero(), |acc, (l, c)| acc + *l * *c);
            instance.constants[j] + correction
        })
        .collect();

    // Solve for the base point on its support.
    let mut minor_elements: Vec<F> = Vec::with_capacity(k * k);
    for row in &lambda {
        for index in base_support {
            minor_elements.push(row[*index]);
        }
    }
    let minor = Matrix::new(k, k, &minor_elements);
    let solved = minor.inverse().map_err(|_| FamilyError::SingularMinor)?;
    let coordinates = apply(&solved, &rhs);
    let mut z_star = vec![F::zero(); t];
    for (index, value) in base_support.iter().zip(&coordinates) {
        z_star[*index] = *value;
    }

    // The direction is a kernel vector of the k x (k+1) homogeneous minor, built by the generalized
    // cross product: v_m = (-1)^m det(B with column m deleted). Every k x k minor of M^{-1} is
    // nonsingular because the inverse of an MDS matrix is MDS, so every v_m is nonzero and the
    // direction's support is exactly `direction_support`.
    let mut direction_values: Vec<F> = Vec::with_capacity(k + 1);
    for m in 0..=k {
        let kept: Vec<usize> = direction_support
            .iter()
            .enumerate()
            .filter(|(index, _)| *index != m)
            .map(|(_, i)| *i)
            .collect();
        let mut elements: Vec<F> = Vec::with_capacity(k * k);
        for row in &lambda {
            for index in &kept {
                elements.push(row[*index]);
            }
        }
        let cofactor = Matrix::new(k, k, &elements)
            .determinant()
            .map_err(|_| FamilyError::SingularMinor)?;
        direction_values.push(if m % 2 == 0 { cofactor } else { -cofactor });
    }
    let leading = direction_values[0];
    if leading.is_zero() {
        return Err(FamilyError::SingularMinor);
    }
    let normalizer = leading.inverse();
    let mut v = vec![F::zero(); t];
    for (index, value) in direction_support.iter().zip(&direction_values) {
        v[*index] = *value * normalizer;
    }

    let alpha = u128::from(parameters.alpha);
    Ok(CicoFamily {
        base: z_star.iter().map(|z| z.pow(alpha)).collect(),
        direction: v.iter().map(|d| d.pow(alpha)).collect(),
        z_star,
        v,
        base_support: base_support.to_vec(),
        direction_support: direction_support.to_vec(),
        inverse_alpha,
    })
}

/// The constrained output word `P_i(Z)`, with its target subtracted, over a round-skipping family.
///
/// A base-field root of `P_0` is a candidate: it satisfies the first output constraint and the
/// input constraints by construction, and leaves the remaining `k - 1` constraints to be filtered
/// by evaluation. That asymmetry is 2026/1254 §4.2's "common-root strategy" and it is independent
/// filtering, not a coupling — see `docs/research/graeffe-root-finding.md` §9.5.1.
///
/// The degree bound is `alpha^{R_F + R_P - 1}`, one S-box layer below the direct bound, because the
/// skipped state is affine in `Z`.
pub fn cico_univariate_family<F: KnownOrder>(
    instance: &CicoInstance<F>,
    family: &CicoFamily<F>,
    constraint: usize,
) -> Result<(UnivariatePolynomial<F>, UnivariateRoute), FamilyError> {
    let (polynomial, stages) = cico_univariate_family_with_stats(instance, family, constraint)?;
    Ok((polynomial, stages.route))
}

/// What [`cico_univariate_family`] cost, split so that evaluation and interpolation are separate
/// numbers rather than one construction total.
///
/// `interpolation` is zero on the symbolic route, where there is nothing to invert.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FamilyStages {
    pub route: UnivariateRoute,
    pub degree_bound: usize,
    /// Permutation evaluations performed. Zero on the symbolic route.
    pub evaluations: usize,
    /// Straight-line evaluation, or the evaluation-domain sweep.
    pub construction: Duration,
    /// `fft::interpolate` over the evaluation domain.
    pub interpolation: Duration,
}

/// [`cico_univariate_family`], with the construction split into its stages.
pub fn cico_univariate_family_with_stats<F: KnownOrder>(
    instance: &CicoInstance<F>,
    family: &CicoFamily<F>,
    constraint: usize,
) -> Result<(UnivariatePolynomial<F>, FamilyStages), FamilyError> {
    let poseidon = &instance.poseidon;
    let parameters = poseidon.parameters;
    if constraint >= instance.k {
        return Err(FamilyError::BadSupport {
            expected: instance.k,
            found: constraint,
        });
    }
    let target = instance.constants[instance.k + constraint];
    let degree_bound = degree_bound(&parameters);
    let route = univariate_route(degree_bound);

    match route {
        UnivariateRoute::Symbolic { .. } => {
            let at = Instant::now();
            let state: Vec<UnivariatePolynomial<F>> = family
                .base
                .iter()
                .zip(&family.direction)
                .map(|(b, d)| UnivariatePolynomial::new(&[*b, *d]))
                .collect();
            let finished = finish_symbolic(poseidon, &state);
            let polynomial = finished[constraint].clone() - UnivariatePolynomial::lift(&target);
            Ok((
                polynomial,
                FamilyStages {
                    route,
                    degree_bound,
                    evaluations: 0,
                    construction: at.elapsed(),
                    interpolation: Duration::ZERO,
                },
            ))
        }
        UnivariateRoute::Evaluation { log_size } => {
            if log_size > F::two_adicity() {
                return Err(FamilyError::DomainTooLarge {
                    degree_bound,
                    two_adicity: F::two_adicity(),
                });
            }
            let generator = F::two_adic_root_of_unity(
                log_size,
                &mut rand::rngs::StdRng::seed_from_u64(0x1_1C1C0),
            );
            let domain = FFTDomain::from_generator(generator, 1usize << log_size);
            let at = Instant::now();
            let values: Vec<F> = domain
                .iter()
                .map(|z| {
                    let finished = finish_field(poseidon, &family.skipped_state(*z));
                    finished[constraint] - target
                })
                .collect();
            let construction = at.elapsed();
            let at = Instant::now();
            let polynomial = interpolate(&values, &domain);
            Ok((
                polynomial,
                FamilyStages {
                    route,
                    degree_bound,
                    evaluations: values.len(),
                    construction,
                    interpolation: at.elapsed(),
                },
            ))
        }
    }
}

/// The `k = 1` analogue of [`cico_bivariate`](super::resultant::cico_bivariate): one free input left
/// symbolic, the rest fixed, and the first constrained output word returned with its target
/// subtracted.
///
/// This is the plain slice, not the round-skipping family — the input constraints hold because
/// `CicoInstance` writes them into the state, so the degree is the direct `alpha^{R_F + R_P}`. Use
/// [`cico_univariate_family`] for the `(1,[1])` construction and its factor-`alpha` saving.
///
/// # Errors
/// [`PoseidonError::WrongStateWidth`] if `fixed` does not leave exactly one free input symbolic.
pub fn cico_univariate<F: KnownOrder>(
    instance: &CicoInstance<F>,
    fixed: &[F],
) -> Result<UnivariatePolynomial<F>, PoseidonError> {
    let poseidon = &instance.poseidon;
    let t = poseidon.parameters.t;
    let k = instance.k;
    let free = instance.free_inputs();
    if free < 1 || fixed.len() + 1 != free {
        return Err(PoseidonError::WrongStateWidth {
            expected: free.saturating_sub(1),
            found: fixed.len(),
        });
    }

    let mut state: Vec<UnivariatePolynomial<F>> = Vec::with_capacity(t);
    for i in 0..k {
        state.push(UnivariatePolynomial::lift(&instance.constants[i]));
    }
    state.push(UnivariatePolynomial::new(&[F::zero(), F::one()]));
    for value in fixed {
        state.push(UnivariatePolynomial::lift(value));
    }
    debug_assert_eq!(state.len(), t);

    // The CICO verifier applies the MDS before the first round, as `permutation_plus_linear` does.
    state = mds_symbolic(poseidon, &state);
    let finished = rounds_symbolic(poseidon, state, 0);
    Ok(&finished[0] - &UnivariatePolynomial::lift(&instance.constants[k]))
}

/// `alpha^{R_F + R_P - 1}`, the `(1,[1])` output degree bound of 2026/1254 eq. (1).
#[must_use]
pub fn degree_bound(parameters: &PoseidonParameters) -> usize {
    (parameters.alpha as usize).pow((parameters.rounds() - 1) as u32)
}

/// True if round `round` applies the S-box to the whole state.
fn is_full(parameters: &PoseidonParameters, round: usize) -> bool {
    let half = parameters.r_f / 2;
    round < half || round >= half + parameters.r_p
}

/// `M * state`, over the field.
fn apply<F: FiniteField>(matrix: &Matrix<F>, state: &[F]) -> Vec<F> {
    (0..matrix.num_rows())
        .map(|row| {
            matrix
                .row(row)
                .zip(state)
                .fold(F::zero(), |acc, (m, s)| acc + *m * *s)
        })
        .collect()
}

/// `M^{-1}`, rebuilt from the instance's dense MDS.
fn inverse_mds<F: KnownOrder>(poseidon: &Poseidon<F>) -> Result<Matrix<F>, FamilyError> {
    let t = poseidon.parameters.t;
    let elements: Vec<F> = poseidon.mds.iter().flatten().copied().collect();
    Matrix::new(t, t, &elements)
        .inverse()
        .map_err(|_| FamilyError::SingularMinor)
}

/// Finish the permutation over the field, from the skipped state `y` onward: round 0's MDS, then
/// every remaining round.
fn finish_field<F: KnownOrder>(poseidon: &Poseidon<F>, y: &[F]) -> Vec<F> {
    let parameters = poseidon.parameters;
    let mds = |state: &[F]| -> Vec<F> {
        poseidon
            .mds
            .iter()
            .map(|row| {
                row.iter()
                    .zip(state)
                    .fold(F::zero(), |acc, (m, s)| acc + *m * *s)
            })
            .collect()
    };
    let alpha = u128::from(parameters.alpha);
    let mut state = mds(y);
    for round in 1..parameters.rounds() {
        for (word, c) in state.iter_mut().zip(&poseidon.round_constants[round]) {
            *word += *c;
        }
        if is_full(&parameters, round) {
            for word in state.iter_mut() {
                *word = word.pow(alpha);
            }
        } else {
            state[0] = state[0].pow(alpha);
        }
        state = mds(&state);
    }
    state
}

fn mds_symbolic<F: KnownOrder>(
    poseidon: &Poseidon<F>,
    state: &[UnivariatePolynomial<F>],
) -> Vec<UnivariatePolynomial<F>> {
    poseidon
        .mds
        .iter()
        .map(|row| {
            row.iter()
                .zip(state)
                .fold(UnivariatePolynomial::zero(), |acc, (m, word)| {
                    acc + word.scale(m)
                })
        })
        .collect()
}

/// Apply rounds `first..rounds` symbolically to a state that has already had its linear layer.
fn rounds_symbolic<F: KnownOrder>(
    poseidon: &Poseidon<F>,
    mut state: Vec<UnivariatePolynomial<F>>,
    first: usize,
) -> Vec<UnivariatePolynomial<F>> {
    let parameters = poseidon.parameters;
    for round in first..parameters.rounds() {
        for (word, c) in state.iter_mut().zip(&poseidon.round_constants[round]) {
            *word += UnivariatePolynomial::lift(c);
        }
        if is_full(&parameters, round) {
            for word in state.iter_mut() {
                *word = word.pow(parameters.alpha);
            }
        } else {
            state[0] = state[0].pow(parameters.alpha);
        }
        state = mds_symbolic(poseidon, &state);
    }
    state
}

/// The symbolic twin of [`finish_field`].
fn finish_symbolic<F: KnownOrder>(
    poseidon: &Poseidon<F>,
    y: &[UnivariatePolynomial<F>],
) -> Vec<UnivariatePolynomial<F>> {
    let state = mds_symbolic(poseidon, y);
    rounds_symbolic(poseidon, state, 1)
}

fn check_distinct(support: &[usize], t: usize) -> Result<(), FamilyError> {
    for (position, index) in support.iter().enumerate() {
        if *index >= t {
            return Err(FamilyError::StateTooNarrow {
                t,
                needed: *index + 1,
            });
        }
        if support[..position].contains(index) {
            return Err(FamilyError::BadSupport {
                expected: support.len(),
                found: position,
            });
        }
    }
    Ok(())
}

/// `a^{-1} mod m` by the extended Euclidean algorithm, or `None` when `gcd(a, m) != 1`.
fn inverse_mod(a: u128, m: u128) -> Option<u128> {
    let (mut old_r, mut r) = (a % m, m);
    let (mut old_s, mut s) = (1i128, 0i128);
    while r != 0 {
        let quotient = old_r / r;
        let next_r = old_r - quotient * r;
        old_r = r;
        r = next_r;
        let next_s = old_s - (quotient as i128) * s;
        old_s = s;
        s = next_s;
    }
    if old_r != 1 {
        return None;
    }
    Some(old_s.rem_euclid(m as i128) as u128)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        fields::PrimeFieldElement64,
        grobner::research::{challenge, poseidon::KOALABEAR_PRIME},
        identities::Zero,
    };
    use rand::{rngs::StdRng, Rng};

    type K = PrimeFieldElement64<KOALABEAR_PRIME>;

    /// The three reduced rows small enough for a symbolic construction to be checked exhaustively.
    const ROWS: [&str; 3] = [
        "poseidon31-cico-t16-rf2-rp0",
        "poseidon31-cico-t16-rf2-rp2",
        "poseidon31-cico-t16-rf4-rp0",
    ];

    fn instance(id: &str) -> CicoInstance<K> {
        challenge(id)
            .expect("registered")
            .cico_instance::<K>()
            .expect("a CICO row")
    }

    fn family(instance: &CicoInstance<K>) -> CicoFamily<K> {
        let t = instance.poseidon.parameters.t;
        parametrize(instance, &[t - 4, t - 3], &[0, 1, 2]).expect("disjoint supports")
    }

    /// Oracle 1: every point of a parametrized family lifts to an input whose constrained
    /// coordinates equal the instance's input constants, identically in the search parameter.
    #[test]
    fn the_family_holds_the_input_constraints_at_every_point() {
        let mut rng = StdRng::seed_from_u64(0xc1c0_0001);
        for id in ROWS {
            let instance = instance(id);
            let family = family(&instance);
            for _ in 0..64 {
                let z = K::new(rng.gen_range(0..KOALABEAR_PRIME));
                let x = family.lift(&instance, z).expect("a lifted input");
                for j in 0..instance.k {
                    assert_eq!(
                        x[j], instance.constants[j],
                        "{id}: input coordinate {j} is not the constrained value at Z = {z}"
                    );
                }
            }
        }
    }

    /// Oracle 1, restated through the permutation: the lifted input reproduces the family's skipped
    /// state, so the parametrization is faithful to `permutation_plus_linear`'s own round schedule.
    #[test]
    fn the_lifted_input_reproduces_the_skipped_state() {
        let mut rng = StdRng::seed_from_u64(0xc1c0_0002);
        for id in ROWS {
            let instance = instance(id);
            let family = family(&instance);
            let poseidon = &instance.poseidon;
            for _ in 0..32 {
                let z = K::new(rng.gen_range(0..KOALABEAR_PRIME));
                let x = family.lift(&instance, z).expect("a lifted input");
                let trace = poseidon.run(&x, true).expect("the right width");
                let t = poseidon.parameters.t;
                assert_eq!(
                    trace.sbox_outputs[..t],
                    family.skipped_state(z)[..],
                    "{id}: the first round's S-box outputs are not the family's skipped state"
                );
            }
        }
    }

    /// Oracle 2: the family polynomial evaluated at a point equals the constrained output word of
    /// `permutation_plus_linear` on the input that point parametrizes, minus its target.
    #[test]
    fn the_family_polynomial_agrees_with_the_permutation() {
        let mut rng = StdRng::seed_from_u64(0xc1c0_0003);
        for id in ROWS {
            let instance = instance(id);
            let family = family(&instance);
            let k = instance.k;
            for constraint in 0..k {
                let (p, _route) = cico_univariate_family(&instance, &family, constraint)
                    .expect("a constructible family");
                for _ in 0..32 {
                    let z = K::new(rng.gen_range(0..KOALABEAR_PRIME));
                    let x = family.lift(&instance, z).expect("a lifted input");
                    let out = instance
                        .poseidon
                        .permutation_plus_linear(&x)
                        .expect("the right width");
                    assert_eq!(
                        p.eval(&z),
                        out[constraint] - instance.constants[k + constraint],
                        "{id}: P_{constraint} disagrees with the permutation at Z = {z}"
                    );
                }
            }
        }
    }

    /// A base-field root of the family polynomial is a point satisfying that output constraint, and
    /// a root satisfying all of them verifies through `CicoInstance::is_solution`.
    #[test]
    fn a_root_of_the_family_polynomial_satisfies_its_constraint() {
        let instance = instance("poseidon31-cico-t16-rf2-rp0");
        let family = family(&instance);
        let (p, route) =
            cico_univariate_family(&instance, &family, 0).expect("a constructible family");
        assert!(matches!(route, UnivariateRoute::Symbolic { .. }));
        let roots = crate::roots(&p, &mut StdRng::seed_from_u64(0xc1c0_0004));
        for root in &roots {
            let x = family.lift(&instance, *root).expect("a lifted input");
            let out = instance
                .poseidon
                .permutation_plus_linear(&x)
                .expect("the right width");
            assert_eq!(out[0], instance.constants[instance.k]);
            let free = family.lift_free(&instance, *root).expect("a lifted input");
            assert_eq!(
                instance.is_solution(&free).expect("the right width"),
                out[1] == instance.constants[instance.k + 1],
                "is_solution must agree with the second constraint on a root of P_0"
            );
        }
    }

    /// The `(1,[1])` degree bound is one S-box layer below the direct bound, and the symbolic
    /// construction attains it rather than merely respecting it.
    #[test]
    fn the_family_polynomial_has_the_round_skipping_degree() {
        for id in ROWS {
            let instance = instance(id);
            let parameters = instance.poseidon.parameters;
            let bound = degree_bound(&parameters);
            assert_eq!(
                bound,
                (parameters.alpha as usize).pow((parameters.rounds() - 1) as u32)
            );
            let family = family(&instance);
            let (p, _) =
                cico_univariate_family(&instance, &family, 0).expect("a constructible family");
            assert_eq!(p.degree() as usize, bound, "{id}: degree is not the bound");
        }
    }

    /// `cico_univariate` is the plain `k = 1` slice: it agrees with the permutation on the input its
    /// argument fixes, and so carries the direct degree rather than the round-skipping one.
    #[test]
    fn cico_univariate_agrees_with_the_permutation() {
        let mut rng = StdRng::seed_from_u64(0xc1c0_0005);
        let instance = instance("poseidon31-cico-t16-rf2-rp0");
        let k = instance.k;
        let free = instance.free_inputs();
        let fixed: Vec<K> = (0..free - 1)
            .map(|_| K::new(rng.gen_range(0..KOALABEAR_PRIME)))
            .collect();
        let p = cico_univariate(&instance, &fixed).expect("one free input remains");
        for _ in 0..32 {
            let x0 = K::new(rng.gen_range(0..KOALABEAR_PRIME));
            let mut state = instance.constants[..k].to_vec();
            state.push(x0);
            state.extend_from_slice(&fixed);
            let out = instance
                .poseidon
                .permutation_plus_linear(&state)
                .expect("the right width");
            assert_eq!(p.eval(&x0), out[0] - instance.constants[k]);
        }
    }

    /// `cico_univariate` refuses a `fixed` slice that does not leave exactly one free input.
    #[test]
    fn cico_univariate_refuses_the_wrong_number_of_fixed_inputs() {
        let instance = instance("poseidon31-cico-t16-rf2-rp0");
        let free = instance.free_inputs();
        assert!(matches!(
            cico_univariate(&instance, &vec![K::zero(); free]),
            Err(PoseidonError::WrongStateWidth { .. })
        ));
    }

    /// `parametrize` refuses supports that overlap, since disjointness is what makes the skipped
    /// state affine in `Z` rather than degree `alpha` in `X`.
    #[test]
    fn parametrize_refuses_overlapping_supports() {
        let instance = instance("poseidon31-cico-t16-rf2-rp0");
        assert!(matches!(
            parametrize(&instance, &[0, 1], &[1, 2, 3]),
            Err(FamilyError::SupportsOverlap { index: 1 })
        ));
    }

    /// `parametrize` refuses a direction support that is not one wider than the constraint count,
    /// because a `k x k` homogeneous system has no nonzero kernel vector.
    #[test]
    fn parametrize_refuses_a_direction_support_without_slack() {
        let instance = instance("poseidon31-cico-t16-rf2-rp0");
        assert!(matches!(
            parametrize(&instance, &[12, 13], &[0, 1]),
            Err(FamilyError::BadSupport {
                expected: 3,
                found: 2
            })
        ));
    }

    /// Distinct supports give distinct families, which is what makes a family search possible.
    #[test]
    fn distinct_supports_give_distinct_families() {
        let instance = instance("poseidon31-cico-t16-rf2-rp0");
        let a = parametrize(&instance, &[12, 13], &[0, 1, 2]).expect("disjoint");
        let b = parametrize(&instance, &[12, 13], &[3, 4, 5]).expect("disjoint");
        assert_ne!(a.direction, b.direction);
        let (pa, _) = cico_univariate_family(&instance, &a, 0).expect("constructible");
        let (pb, _) = cico_univariate_family(&instance, &b, 0).expect("constructible");
        assert_ne!(pa, pb);
    }

    /// The evaluation route is taken above the crossover and the symbolic route below it, and the
    /// chosen domain is a power of two large enough to determine the polynomial.
    #[test]
    fn the_route_switches_at_the_crossover() {
        assert!(matches!(
            univariate_route(SYMBOLIC_CROSSOVER),
            UnivariateRoute::Symbolic { .. }
        ));
        match univariate_route(SYMBOLIC_CROSSOVER + 1) {
            UnivariateRoute::Evaluation { log_size } => {
                assert!(1usize << log_size > SYMBOLIC_CROSSOVER + 1);
            }
            other => panic!("expected the evaluation route, got {other:?}"),
        }
        // The disclosed CICO-2 target: 3^13 at 2^21, inside KoalaBear's two-adicity of 24.
        assert_eq!(
            univariate_route(3usize.pow(13)),
            UnivariateRoute::Evaluation { log_size: 21 }
        );
        assert!(21 <= K::two_adicity());
    }

    /// The two construction routes agree on a row where both are affordable, which is the only
    /// check that the evaluation-domain build is not a separate construction.
    #[test]
    fn the_two_routes_agree() {
        let instance = instance("poseidon31-cico-t16-rf4-rp0");
        let family = family(&instance);
        let (symbolic, route) =
            cico_univariate_family(&instance, &family, 0).expect("constructible");
        assert!(matches!(route, UnivariateRoute::Symbolic { .. }));

        // Rebuild the same polynomial through the evaluation domain, as the large-degree path does.
        let bound = degree_bound(&instance.poseidon.parameters);
        let log_size = (bound + 1).next_power_of_two().trailing_zeros();
        let generator = K::two_adic_root_of_unity(log_size, &mut StdRng::seed_from_u64(0x1_1C1C0));
        let domain = FFTDomain::from_generator(generator, 1usize << log_size);
        let target = instance.constants[instance.k];
        let values: Vec<K> = domain
            .iter()
            .map(|z| finish_field(&instance.poseidon, &family.skipped_state(*z))[0] - target)
            .collect();
        assert_eq!(interpolate(&values, &domain), symbolic);
    }

    /// The stage split records the route it took, charges no interpolation on the symbolic route,
    /// and returns the same polynomial the unsplit entry point does.
    #[test]
    fn the_stage_split_matches_the_unsplit_construction() {
        let instance = instance("poseidon31-cico-t16-rf4-rp0");
        let family = family(&instance);
        let (split, stages) =
            cico_univariate_family_with_stats(&instance, &family, 0).expect("constructible");
        let (plain, route) = cico_univariate_family(&instance, &family, 0).expect("constructible");
        assert_eq!(split, plain);
        assert_eq!(stages.route, route);
        assert!(matches!(stages.route, UnivariateRoute::Symbolic { .. }));
        assert_eq!(stages.interpolation, Duration::ZERO);
        assert_eq!(stages.evaluations, 0);
        assert_eq!(
            stages.degree_bound,
            degree_bound(&instance.poseidon.parameters)
        );
    }

    /// `inverse_mod` inverts the S-box exponent modulo `p - 1`, which is what lets a search point
    /// in `Z = X^alpha` be lifted back to `X`.
    #[test]
    fn the_sbox_exponent_inverts_modulo_the_group_order() {
        let order = u128::from(KOALABEAR_PRIME) - 1;
        let inverse = inverse_mod(3, order).expect("3 is coprime to p - 1");
        assert_eq!(3 * inverse % order, 1);
        // p - 1 = 127 * 2^24, so an even exponent is not invertible and the S-box would not be a
        // bijection.
        assert_eq!(inverse_mod(2, order), None);
    }
}
