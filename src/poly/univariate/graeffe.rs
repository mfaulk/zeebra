//! Root finding by the Graeffe transform.
//!
//! `GT_l(f)` is the polynomial whose roots are the `l`-th powers of `f`'s. Iterating it over
//! `F_p` does **not** separate roots by magnitude, which is what the real-number original is for:
//! `p - 1 = 2^k * s` means `alpha^(2^k)` lands in the subgroup of order `s` for every
//! `alpha` in `F_p^*`, so `k` transforms drive every base-field root into a subgroup small enough
//! to search outright. That is the whole idea, and it is why the method wants a field whose
//! `p - 1` has a large power of two and a small odd part.
//!
//! # References
//! * `docs/research/graeffe-root-finding.md` — the transcription this follows, with the papers.
//! * [P937] Sanso-Vitto, ePrint 2025/937, §4-§5 (Algorithm 2, the single-root variant).
//! * [PC] Zhao-Sanso-Vitto-Ding, ePrint 2025/1916, §3 (Definition 2, Lemmas 1 and 2,
//!   Algorithms 2 and 3).

use std::time::{Duration, Instant};

use rand::{CryptoRng, RngCore};

use crate::{
    evaluate,
    fft::multiply_over_domain,
    fields::{two_adic::two_adic_decomposition, RootOfUnityError},
    interpolate,
    poly::univariate::{gcd::gcd, roots::roots, Polynomial, UnivariatePolynomial},
    FFTDomain, FiniteField, KnownOrder,
};

/// Why a Graeffe root find could not run.
///
/// One variant, deliberately: everything else about the method degrades in cost rather than in
/// availability, and a cost is reported through [`GraeffeStats`] rather than refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GraeffeError {
    /// An order-2 step at degree `degree` needs a power-of-two domain of `2^log_n >= degree + 1`
    /// points, and this field has no primitive `2^log_n`-th root of unity.
    ///
    /// A fact about the field, so a value rather than a panic. Mersenne-31, whose two-adicity is
    /// 1, is where it bites: no polynomial of degree above one can be transformed over it at all.
    DomainTooLarge {
        degree: u32,
        log_n: u32,
        two_adicity: u32,
    },
}

impl std::fmt::Display for GraeffeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DomainTooLarge {
                degree,
                log_n,
                two_adicity,
            } => write!(
                f,
                "an order-2 Graeffe step at degree {degree} needs a domain of 2^{log_n} points, \
                 and this field's two-adicity is {two_adicity}"
            ),
        }
    }
}

impl std::error::Error for GraeffeError {}

/// How the roots in the final subgroup were found.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SubgroupRoute {
    /// The order-`s` subgroup was enumerated and the polynomial evaluated at every point.
    ///
    /// `O(s * d)`, and the route the method is designed around: it is cheap exactly when the odd
    /// part of `p - 1` is small, which is what makes KoalaBear (`s = 127`) the good case.
    Enumerated { points: u64 },
    /// [`roots`] was called on the reduced polynomial and its output filtered to the subgroup.
    ///
    /// The fallback for a field whose odd part is too large to enumerate — Goldilocks, where
    /// `s = 2^32 - 1`. Exact, but quadratic in the degree, so the Graeffe iteration buys nothing
    /// there: see [`graeffe_root`]'s note on which fields the method actually helps.
    GcdRootFinder { degree: u32 },
}

/// What one [`graeffe_root`] call cost, for a benchmark to report rather than estimate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GraeffeStats {
    /// Order-2 Graeffe steps run, which is the field's two-adicity.
    pub graeffe_steps: u32,
    /// Forward and inverse transforms performed: three per order-2 step.
    pub transforms: usize,
    /// The largest transform size used.
    pub max_transform_size: usize,
    /// The sum of every transform's size, which is what progressive reduction bounds.
    pub total_transform_elements: usize,
    /// Coefficients held live across the whole run: the sum over the retained `G_{2^i}`.
    pub stored_coefficients: usize,
    /// The degree of the fully transformed polynomial, after reduction.
    pub final_degree: u32,
    /// The orders of the odd-order forward steps taken, in the order taken — [PC] Algorithm 3.
    ///
    /// Empty when the order-2 phase already left an enumerable subgroup, which is the KoalaBear
    /// case and every field whose odd part is small. Non-empty is the Goldilocks case: each entry
    /// is a prime dividing the odd part, and their product is what divides the subgroup order the
    /// search would otherwise have faced.
    pub odd_steps: Vec<u64>,
    /// The order of the subgroup the search ran over, after the odd-order steps.
    ///
    /// The odd part of `q - 1` divided by the product of [`Self::odd_steps`], so it is the odd
    /// part exactly when no odd step was taken.
    pub subgroup_order: u128,
    pub subgroup_route: SubgroupRoute,
    /// Candidates the subgroup search produced, each of which the descent then un-squares.
    pub candidates: usize,
    /// Wall time in the order-2 iteration, which is where every transform is.
    pub forward_time: Duration,
    /// Wall time in the subgroup search.
    pub subgroup_time: Duration,
    /// Wall time in the un-squaring descent.
    pub descent_time: Duration,
}

/// The order-2 Graeffe transform of `f`, over a domain the caller supplies.
///
/// With `f(x) = f_e(x^2) + x f_o(x^2)`,
///
/// ```text
/// f(x) f(-x) = f_e(x^2)^2 - x^2 f_o(x^2)^2        so        GT_2(f)(y) = f_e(y)^2 - y f_o(y)^2
/// ```
///
/// which is **three transforms of size `>= deg f + 1`, not of size `2 deg f + 1`**: `f_e` and
/// `f_o` have half the degree, so their squares and the whole result fit in a domain one power of
/// two below what an ordinary product of two degree-`d` polynomials would need. [P937] §5.3
/// records this as a correction the authors make to their own first implementation, which followed
/// Definition 2 literally and paid double.
///
/// The leading `(-1)^d` is [P937] §5.3's normalization and is not cosmetic: `f(x) f(-x)` carries
/// `(-1)^d` from the `d` sign flips, so without it a monic `f` transforms to a polynomial with
/// leading coefficient `-1` at odd degree, and [PC] Lemma 2's `GT_2 . GT_2 = GT_4` holds only up
/// to a unit. With it, `f = prod (x - r_i)` transforms to exactly `prod (x - r_i^2)`.
///
/// # Memory
/// `3 n B` live at the peak, for `n` the domain size: the forward values of `f_e` reused as the
/// combine's output buffer, plus the `2 n B` that `interpolate` holds. Both halves' value vectors
/// are scoped so that only one of them outlives the combine, and the parity-split coefficient
/// vectors are dropped before the inverse transform runs. Worth doing explicitly: since #161 took
/// `evaluate` to `1 n B` and `interpolate` to `2 n B` — their floors — the naive form's live set is
/// this function's own temporaries rather than the kernel's.
///
/// # Panics
/// Panics if the domain holds `deg f` points or fewer, which is a choice the caller made.
pub fn graeffe_2_over_domain<F: FiniteField>(
    f: &UnivariatePolynomial<F>,
    domain: &FFTDomain<F>,
) -> UnivariatePolynomial<F> {
    let degree = f.degree() as usize;
    assert!(
        domain.size() > degree,
        "an order-2 Graeffe step at degree {degree} needs at least {} points, not {}",
        degree + 1,
        domain.size()
    );

    // `values` starts as `f_e` on the domain and becomes `f_e^2 - x f_o^2` in place. The odd half's
    // values and both parity-split coefficient vectors live only inside this block.
    let values = {
        let coefficients = f.coefficients();
        let even =
            UnivariatePolynomial::new(&coefficients.iter().step_by(2).copied().collect::<Vec<F>>());
        let odd = UnivariatePolynomial::new(
            &coefficients
                .iter()
                .skip(1)
                .step_by(2)
                .copied()
                .collect::<Vec<F>>(),
        );
        let mut even_values = evaluate(&even, domain);
        let odd_values = evaluate(&odd, domain);
        for (point, (even_value, odd_value)) in domain
            .powers()
            .iter()
            .zip(even_values.iter_mut().zip(odd_values.iter()))
        {
            *even_value = *even_value * *even_value - *point * (*odd_value * *odd_value);
        }
        even_values
    };

    let transformed = interpolate(&values, domain);
    // `scale` below allocates another `n B`, and the values are spent.
    drop(values);

    if degree % 2 == 1 {
        transformed.scale(&-F::one())
    } else {
        transformed
    }
}

/// The order-2 Graeffe transform of `f`, over a domain built for the occasion.
///
/// Fails if the field's two-adicity cannot host a domain of `deg f + 1` points.
pub fn graeffe_2<F: KnownOrder, R: RngCore + CryptoRng>(
    f: &UnivariatePolynomial<F>,
    rng: &mut R,
) -> Result<UnivariatePolynomial<F>, GraeffeError> {
    if f.is_zero() {
        return Ok(UnivariatePolynomial::zero());
    }

    let degree = f.degree();
    let points = (degree as usize + 1).next_power_of_two().max(2);
    let log_n = points.trailing_zeros();
    let generator =
        F::try_two_adic_root_of_unity(log_n, rng).map_err(|_| GraeffeError::DomainTooLarge {
            degree,
            log_n,
            two_adicity: F::two_adicity(),
        })?;
    let domain = FFTDomain::from_generator(generator, points);
    Ok(graeffe_2_over_domain(f, &domain))
}

/// The order-`l` Graeffe transform of `f`, by [PC] §3.2's product of scaled copies.
///
/// [PC] Definition 2 directly: `GT_l(f)(x^l) = prod_t f(x w_l^t)`, so the `l` scaled copies are
/// multiplied together and every `l`-th coefficient of the degree-`l d` product is read off. The
/// intermediate product is `l` times the size of the output, which is why [PC] applies orders
/// above 2 only to small-degree polynomials in the final steps.
///
/// `l` need not be prime. The normalization matches [`graeffe_2`]'s: `prod_t (x w_l^t - r)` is
/// `w_l^(l(l-1)/2) (x^l - r^l)`, and `w_l^(l(l-1)/2)` is 1 for odd `l` and `-1` for even `l`, so
/// only an even `l` needs the `(-1)^d`. Hence `graeffe_l(f, 2)` agrees with [`graeffe_2`] and
/// odd-order steps need no sign at all.
///
/// Fails if `l` does not divide `q - 1` — no primitive `l`-th root of unity exists then — or if
/// the field cannot host a domain for the degree-`l d` product.
///
/// # Panics
/// Panics if `l < 2`.
pub fn graeffe_l<F: KnownOrder, R: RngCore + CryptoRng>(
    f: &UnivariatePolynomial<F>,
    l: u64,
    rng: &mut R,
) -> Result<UnivariatePolynomial<F>, RootOfUnityError> {
    assert!(l >= 2, "a Graeffe transform needs an order of at least 2");
    if f.is_zero() {
        return Ok(UnivariatePolynomial::zero());
    }

    let degree = f.degree() as usize;
    let omega = F::try_root_of_unity(l, rng)?;

    let mut power = F::one();
    let mut factors: Vec<UnivariatePolynomial<F>> = Vec::with_capacity(l as usize);
    for _ in 0..l {
        factors.push(scale_variable(f, &power));
        power *= omega;
    }

    // A product tree, one domain per level: all the operands of a level have the same degree, so
    // one domain serves the whole level and the sizes rise with the partial products rather than
    // every product paying for the final one.
    while factors.len() > 1 {
        let operand_degree = factors
            .iter()
            .map(|factor| factor.degree() as usize)
            .max()
            .unwrap_or(0);
        let points = (2 * operand_degree + 1).next_power_of_two().max(2);
        let generator = F::try_two_adic_root_of_unity(points.trailing_zeros(), rng)?;
        let domain = FFTDomain::from_generator(generator, points);

        let mut level = Vec::with_capacity(factors.len().div_ceil(2));
        let mut remaining = factors.into_iter();
        while let Some(left) = remaining.next() {
            match remaining.next() {
                Some(right) => level.push(multiply_over_domain(&left, &right, &domain)),
                None => level.push(left),
            }
        }
        factors = level;
    }

    // Only exponents divisible by l survive the product, which is Lemma 1's proof: the product is
    // invariant under `x -> w_l x`.
    let product = factors
        .pop()
        .expect("the product tree leaves one polynomial");
    let coefficients = product.coefficients();
    let mut transformed: Vec<F> = (0..=degree)
        .map(|i| {
            coefficients
                .get(i * l as usize)
                .copied()
                .unwrap_or_else(F::zero)
        })
        .collect();
    if l.is_multiple_of(2) && !degree.is_multiple_of(2) {
        for coefficient in transformed.iter_mut() {
            *coefficient = -*coefficient;
        }
    }
    Ok(UnivariatePolynomial::new(&transformed))
}

/// A root of `f` in F, or `None` if it has none.
///
/// [P937] Algorithm 2 — the single-root variant the authors implemented — with [P937] §5.3's
/// progressive degree reduction and [PC] Algorithm 2's gcd-based descent in place of Algorithm 2's
/// `k` square roots and `r`-way scan. Why the descent rather than the scan: the scan is `O(r)`
/// candidate tests with `r = 2^two_adicity`, which is `2^24` over KoalaBear and `2^32` over
/// Goldilocks, and is only cheap in the setting [P937] §5.2 assumes — where the test is one
/// permutation call. For a standalone root finder the gcd descent costs `k` folds instead, each
/// linear in the degree it folds.
///
/// The four phases, and what each costs:
///
/// 1. **Forward.** `k = two_adicity` order-2 steps, each three transforms of size
///    `>= deg + 1`. After step `i` the polynomial is reduced modulo `x^beta_i - 1` with
///    `beta_i = (q - 1) / 2^i`: every root descended from a base-field root of `f` lies in the
///    order-`beta_i` subgroup, so the reduction loses none of them and caps the degree at
///    `beta_i - 1`. Once `beta_i` falls below the degree it **halves every step**, so the sum of
///    transform sizes is `ceil(log2((q - 1) / d)) + 2` times the largest rather than `k` times it
///    — a real saving, but one that is only large when `(q - 1) / d` is small. [P937] §5.3.
/// 2. **Odd-order forward steps**, [PC] Algorithm 3 — #593. The order-2 phase leaves the roots
///    in the subgroup of order `s`, the odd part of `q - 1`, and when `s` is large that subgroup
///    cannot be enumerated: over Goldilocks `s = 2^32 - 1` exceeds any degree of interest, so the
///    search below degraded to the quadratic route the method exists to replace — 99.6% of the
///    call at degree 4 096, measured in `docs/research/graeffe-root-finding.md` §6.5. An order-`q`
///    step maps the order-`s` subgroup onto the order-`s/q` one, so steps at the small prime
///    factors of `s` shrink the search geometrically. Over Goldilocks that is `3 * 5 * 17 * 257`,
///    leaving **65 537**, which is enumerable. [`plan_odd_steps`] chooses them, and chooses
///    **none** unless they get the residual below the crossover — a step that leaves the search on
///    the gcd route anyway is a transform paid for nothing.
/// 3. **Subgroup search.** Found by enumeration when the residual order is small and by [`roots`]
///    on the reduced polynomial when it is not — see [`SubgroupRoute`]. The crossover is a
///    property of the degree as well as the order: enumerating costs `s (d + 1)` against the gcd
///    route's `log q (d + 1)^2`, so over Goldilocks the odd steps pay from about `d = 1 024` and
///    not below it.
/// 4. **Descent.** The odd steps come off first, by [`un_power`]'s `gcd(g, x^q - mu)` — [PC]
///    Algorithm 3 lines 10-14, and multi-valued, so [`descend_mixed`] branches over the preimages.
///    Then the squares: `mu_k = alpha^(2^k)` is known; `mu_{i-1}` is the common root of
///    `G_{2^(i-1)}` and `x^2 - mu_i`, which is [PC] Algorithm 2 line 8 at `q_i = 2`. **The un-squaring
///    ambiguity is decided by the polynomial, not guessed**: reducing `G_{2^(i-1)}` modulo
///    `x^2 - mu_i` leaves `a x + b`, and `-b/a` is the one of the two square roots of `mu_i` that
///    `G_{2^(i-1)}` vanishes at. Both square roots lie in the right subgroup, so either, when both
///    are roots, descends to a genuine root of `f`.
///
/// # Panics
/// Panics if `f` is the zero polynomial, every element of which is a root.
pub fn graeffe_root<F: KnownOrder, R: RngCore + CryptoRng>(
    f: &UnivariatePolynomial<F>,
    rng: &mut R,
) -> Result<Option<F>, GraeffeError> {
    graeffe_root_with_stats(f, rng).map(|(root, _stats)| root)
}

/// `f / (x - root)` by synthetic division, assuming `root` is a root so the remainder vanishes.
///
/// `O(d)`, which is what makes deflation affordable to repeat: a `div_with_remainder` against a
/// linear divisor would do the same work through a general division.
fn deflate<F: FiniteField>(f: &UnivariatePolynomial<F>, root: F) -> UnivariatePolynomial<F> {
    let coefficients = f.coefficients();
    let degree = coefficients.len() - 1;
    if degree == 0 {
        return UnivariatePolynomial::new(&[F::zero()]);
    }
    // Horner from the top: q[i-1] = c[i] + root * q[i], with q[d-1] = c[d].
    let mut quotient = vec![F::zero(); degree];
    let mut carry = coefficients[degree];
    quotient[degree - 1] = carry;
    for i in (1..degree).rev() {
        carry = coefficients[i] + root * carry;
        quotient[i - 1] = carry;
    }
    UnivariatePolynomial::new(&quotient)
}

/// Every base-field root of `f`, **with multiplicity**, by [`graeffe_root`] and deflation.
///
/// [`graeffe_root`] returns *one* root, where an elimination route needs every candidate. This is
/// the bridge: take a root, divide it out in `O(d)`, repeat until the deflated polynomial has none.
/// A root of multiplicity `m` survives `m - 1` deflations and is therefore reported `m` times,
/// which is why this returns a `Vec` rather than a set — the caller that wants distinct values can
/// collect, and the caller pricing a search wants the iteration count.
///
/// **Whether this beats [`roots`](super::roots::roots) is a property of the root count, not of the
/// degree.** Each iteration costs one `graeffe_root`, so the total is `(roots + 1)` searches: cheap
/// when the base-field roots are `O(1)`, and worse than a gcd-based finder when they are `O(d)`.
/// #351 is the measurement.
///
/// # Errors
/// [`GraeffeError`], from the first search that cannot be made to apply — the field's two-adic
/// structure is a property of `F`, so a failure here fails for every degree alike.
///
/// # Panics
/// Panics if `f` is the zero polynomial, every element of which is a root.
pub fn graeffe_all_roots<F: KnownOrder, R: RngCore + CryptoRng>(
    f: &UnivariatePolynomial<F>,
    rng: &mut R,
) -> Result<Vec<F>, GraeffeError> {
    assert!(
        !f.is_zero(),
        "every element is a root of the zero polynomial"
    );

    let mut remaining = f.clone();
    let mut found = Vec::new();
    // A linear factor leaves at most `degree` of them, which bounds the loop independently of
    // whatever the search returns.
    while remaining.degree() >= 1 {
        match graeffe_root(&remaining, rng)? {
            Some(root) => {
                remaining = deflate(&remaining, root);
                found.push(root);
            }
            None => break,
        }
    }
    Ok(found)
}

/// [`graeffe_root`], with what the run cost.
///
/// # Panics
/// Panics if `f` is the zero polynomial.
pub fn graeffe_root_with_stats<F: KnownOrder, R: RngCore + CryptoRng>(
    f: &UnivariatePolynomial<F>,
    rng: &mut R,
) -> Result<(Option<F>, GraeffeStats), GraeffeError> {
    assert!(
        !f.is_zero(),
        "every element is a root of the zero polynomial"
    );

    let (two_adicity, odd_part) = two_adic_decomposition(F::order_limbs());
    let subgroup_order = limbs_to_u128(&odd_part).unwrap_or(u128::MAX);
    let mut stats = GraeffeStats {
        graeffe_steps: 0,
        transforms: 0,
        max_transform_size: 0,
        total_transform_elements: 0,
        stored_coefficients: 0,
        final_degree: f.degree(),
        odd_steps: Vec::new(),
        subgroup_order,
        subgroup_route: SubgroupRoute::GcdRootFinder { degree: 0 },
        candidates: 0,
        forward_time: Duration::ZERO,
        subgroup_time: Duration::ZERO,
        descent_time: Duration::ZERO,
    };

    // A nonzero constant has no roots, and zero is a root exactly when the constant term is.
    if f.degree() == 0 {
        return Ok((None, stats));
    }
    if f.coefficients()[0].is_zero() {
        return Ok((Some(F::zero()), stats));
    }

    // === forward: k order-2 steps, each followed by the reduction that caps the degree ===

    // `beta_0 = q - 1`. The fold is a no-op at every degree this is called at, and is here so the
    // induction the descent relies on starts where [PC] Algorithm 2 line 1 puts it.
    //
    // Every `G_(2^i)` is moved into `retained` rather than cloned into it, and the next step reads
    // the vector's last element. One full-degree copy per step would otherwise be live alongside
    // the transform's own buffers, which since #161 took the kernel to its `1 n B` floor is the
    // larger of the two.
    let base_fold = fold_if_needed(f, cyclic_modulus(&odd_part, two_adicity, 0));
    let base: &UnivariatePolynomial<F> = base_fold.as_ref().unwrap_or(f);
    let mut retained: Vec<UnivariatePolynomial<F>> = Vec::with_capacity(two_adicity as usize);

    let forward_start = Instant::now();
    let mut domain: Option<FFTDomain<F>> = None;
    for step in 1..=two_adicity {
        let degree = retained.last().unwrap_or(base).degree();
        let points = (degree as usize + 1).next_power_of_two().max(2);
        let log_n = points.trailing_zeros();
        if log_n > two_adicity {
            return Err(GraeffeError::DomainTooLarge {
                degree,
                log_n,
                two_adicity,
            });
        }
        if domain.as_ref().map(FFTDomain::size) != Some(points) {
            let generator = F::try_two_adic_root_of_unity(log_n, rng).map_err(|_| {
                GraeffeError::DomainTooLarge {
                    degree,
                    log_n,
                    two_adicity,
                }
            })?;
            domain = Some(FFTDomain::from_generator(generator, points));
        }

        let transformed = graeffe_2_over_domain(
            retained.last().unwrap_or(base),
            domain.as_ref().expect("built above"),
        );
        let beta = cyclic_modulus(&odd_part, two_adicity, step);
        match fold_if_needed(&transformed, beta) {
            Some(folded) => retained.push(folded),
            None => retained.push(transformed),
        }

        stats.graeffe_steps += 1;
        stats.transforms += 3;
        stats.max_transform_size = stats.max_transform_size.max(points);
        stats.total_transform_elements += 3 * points;
    }
    // === forward: odd-order steps, [PC] Algorithm 3 ===
    //
    // The order-2 phase above leaves every base-field root in the subgroup of order `odd_part`.
    // Where that is small the search below enumerates it and this phase is empty; where it is not,
    // each order-`q` step maps the order-`s` subgroup onto the order-`s/q` one and so divides the
    // work the search faces. The polynomial *before* each step is retained, because inverting the
    // step needs it: `gcd(before, x^q - mu)` is what identifies which of `mu`'s `q` preimages the
    // polynomial vanishes at.
    let (odd_steps, _planned_residual) =
        plan_odd_steps::<F>(subgroup_order, retained.last().unwrap_or(base).degree());
    let mut odd_retained: Vec<(u64, UnivariatePolynomial<F>)> = Vec::with_capacity(odd_steps.len());
    let mut odd_residual = subgroup_order;
    let mut taken: Vec<u64> = Vec::with_capacity(odd_steps.len());
    for &q in &odd_steps {
        let current = odd_retained
            .last()
            .map(|(_, polynomial)| polynomial)
            .unwrap_or_else(|| retained.last().unwrap_or(base));
        // A transform this field cannot host is a **cost** and not a refusal: the search below
        // still works at whatever order the steps reached, so the phase stops here rather than
        // failing a call that the order-2 route alone would have answered. `graeffe_l` needs a
        // primitive `q`-th root and a domain for the degree-`q d` product, and a field that has
        // neither is one this phase cannot help.
        let Ok(transformed) = graeffe_l(current, q, rng) else {
            break;
        };
        taken.push(q);
        odd_residual /= q as u128;
        // The roots now lie in the subgroup of order `odd_residual`, so exponents may be reduced
        // modulo it — the same identity the order-2 phase folds on, at the orders this phase
        // leaves. A no-op at every degree Goldilocks is called at, and correct where it is not.
        let folded = usize::try_from(odd_residual)
            .ok()
            .and_then(|beta| fold_if_needed(&transformed, Some(beta)));
        odd_retained.push((q, folded.unwrap_or(transformed)));
        stats.transforms += 1;
    }
    // `odd_residual` rather than the plan's `residual_order`, so a phase that stopped early
    // reports the order the search will actually face.
    let residual_order = odd_residual;
    stats.odd_steps = taken;
    stats.subgroup_order = residual_order;

    stats.forward_time = forward_start.elapsed();
    let fully_transformed = odd_retained
        .last()
        .map(|(_, polynomial)| polynomial)
        .unwrap_or_else(|| retained.last().unwrap_or(base));
    stats.final_degree = fully_transformed.degree();
    // What this call holds, which excludes the caller's `f`: the retained `G_(2^i)` for
    // `i = 1..=k`, plus the folded `G_(2^0)` only when the fold actually materialized one.
    stats.stored_coefficients = retained
        .iter()
        .chain(base_fold.as_ref())
        .map(|polynomial| polynomial.coefficients().len())
        .sum();

    // === the subgroup search ===

    let subgroup_start = Instant::now();
    let residual_limbs = [residual_order as u64, (residual_order >> 64) as u64];
    let candidates = subgroup_roots(
        fully_transformed,
        &residual_limbs,
        residual_order,
        &mut stats,
        rng,
    );
    stats.subgroup_time = subgroup_start.elapsed();
    stats.candidates = candidates.len();

    // === the descent, [PC] Algorithm 2 lines 7-9 ===

    let descent_start = Instant::now();
    for candidate in candidates {
        if let Some(root) = descend_mixed(f, base, &retained, &odd_retained, candidate, rng) {
            stats.descent_time = descent_start.elapsed();
            return Ok((Some(root), stats));
        }
    }
    stats.descent_time = descent_start.elapsed();
    Ok((None, stats))
}

/// `f(c x)`: the coefficients scaled by the powers of `c`.
fn scale_variable<F: FiniteField>(f: &UnivariatePolynomial<F>, c: &F) -> UnivariatePolynomial<F> {
    let mut power = F::one();
    let scaled: Vec<F> = f
        .coefficients()
        .iter()
        .map(|coefficient| {
            let value = *coefficient * power;
            power *= *c;
            value
        })
        .collect();
    UnivariatePolynomial::new(&scaled)
}

/// `f mod (x^beta - 1)`, by folding coefficient `i` onto `i mod beta`, or `None` if the caller
/// should keep `f` as it stands.
///
/// `max(deg f + 1 - beta, 0)` additions and no division, which is [P937] §5.2's point about
/// Algorithm 2 line 6. A `beta` of `None` is a modulus too wide to index with, where the fold is
/// likewise a no-op.
///
/// Three cases return `None`, and the third is a correctness condition rather than a saving. `f`
/// of degree below `beta` needs no reduction, and a `beta` too wide to index cannot be applied —
/// but **a fold that lands on the zero polynomial is refused**, because it is the one outcome the
/// reduction must not be allowed to report. `fold = 0` means `x^beta - 1` divides `f`, so every
/// `beta`-th root of unity is a root of `f`: the roots the reduction exists to expose are *all*
/// of them, and the zero polynomial records that as indistinguishable from none. `x^127 - 1` over
/// KoalaBear is the smallest instance — fixed by the order-two transform, 127 roots, and `beta_k`
/// is exactly 127. Keeping `f` unreduced carries its degree into the subgroup search, which costs
/// more than the fold would have but reports the roots.
fn fold_if_needed<F: FiniteField>(
    f: &UnivariatePolynomial<F>,
    beta: Option<usize>,
) -> Option<UnivariatePolynomial<F>> {
    let coefficients = f.coefficients();
    let beta = match beta {
        Some(beta) if beta >= 1 && coefficients.len() > beta => beta,
        // `None` rather than a clone: the caller keeps what it already has, so a step whose
        // modulus is above the degree costs nothing instead of one full-degree copy.
        _ => return None,
    };

    let mut folded = vec![F::zero(); beta];
    for (index, coefficient) in coefficients.iter().enumerate() {
        folded[index % beta] += *coefficient;
    }
    let folded = UnivariatePolynomial::new(&folded);
    if folded.is_zero() {
        return None;
    }
    Some(folded)
}

/// `beta_i = (q - 1) / 2^i = 2^(two_adicity - i) * odd_part`, as a `usize` if it fits.
///
/// `None` means the modulus exceeds any degree that could be reduced by it, so the fold is a
/// no-op — which is the only thing the caller does with it.
fn cyclic_modulus(odd_part: &[u64], two_adicity: u32, step: u32) -> Option<usize> {
    let odd = limbs_to_u128(odd_part)?;
    odd.checked_shl(two_adicity - step)
        .and_then(|beta| usize::try_from(beta).ok())
}

/// The roots of `g` that lie in the subgroup of order `s`, by whichever route is cheaper.
///
/// Both routes are exact. Enumeration evaluates `g` at all `s` points by Horner, `O(s * deg g)`;
/// the fallback asks [`roots`] for every base-field root and keeps those of order dividing `s`,
/// which is `O(log q * (deg g)^2)`. The estimate decides, and the choice is recorded.
fn subgroup_roots<F: KnownOrder, R: RngCore + CryptoRng>(
    g: &UnivariatePolynomial<F>,
    odd_part: &[u64],
    subgroup_order: u128,
    stats: &mut GraeffeStats,
    rng: &mut R,
) -> Vec<F> {
    let degree = g.degree();
    let terms = degree as f64 + 1.0;
    let enumeration_cost = subgroup_order as f64 * terms;
    let order_bits = 64.0 * F::order_limbs().len() as f64;
    let gcd_cost = order_bits * terms * terms;

    let generator = u64::try_from(subgroup_order)
        .ok()
        .and_then(|s| F::try_root_of_unity(s, rng).ok());

    if let (true, Some(generator)) = (enumeration_cost <= gcd_cost, generator) {
        stats.subgroup_route = SubgroupRoute::Enumerated {
            points: subgroup_order as u64,
        };
        let mut found = Vec::new();
        let mut point = F::one();
        for _ in 0..subgroup_order {
            if g.eval(&point).is_zero() {
                found.push(point);
            }
            point *= generator;
        }
        return found;
    }

    stats.subgroup_route = SubgroupRoute::GcdRootFinder { degree };
    if g.degree() == 0 {
        // A nonzero constant has no roots; `roots` would return an empty vector anyway, but a
        // folded polynomial can reach degree zero and this says so without the modular
        // exponentiation.
        //
        // `degree() == 0` is also what the *zero* polynomial reports, for which the opposite
        // holds — every element is a root. [`fold_if_needed`] is what keeps it from arriving
        // here, so the two cannot be confused at this point.
        return Vec::new();
    }
    roots(g, rng)
        .into_iter()
        .filter(|candidate| candidate.pow_limbs(odd_part).is_one())
        .collect()
}

/// The prime factors of `s` below `bound`, smallest first, with multiplicity.
///
/// Trial division, which is the right algorithm here for a reason rather than for simplicity:
/// what the caller needs is the factors small enough to be worth a Graeffe step, and a factor
/// above `bound` is one whose transform would cost more than the subgroup search it saves. So the
/// bound is the point and a general factorization would be work thrown away. Over Goldilocks
/// `s = 2^32 - 1` this returns `[3, 5, 17, 257]` and leaves 65 537 behind — that last factor is
/// prime and above the bound, which is exactly the residue [PC] Algorithm 3 enumerates.
fn small_odd_factors(mut s: u128, bound: u64) -> Vec<u64> {
    let mut factors = Vec::new();
    let mut candidate: u128 = 3;
    while candidate <= bound as u128 && candidate * candidate <= s {
        while s.is_multiple_of(candidate) {
            factors.push(candidate as u64);
            s /= candidate;
        }
        candidate += 2;
    }
    // What is left is prime, so it is a factor too — but only report it if it is small enough to
    // be worth a step, which is the same test the loop applied to the others.
    if s > 1 && s <= bound as u128 {
        factors.push(s as u64);
    }
    factors
}

/// Whether a subgroup of `order` is cheaper to enumerate than to hand to the gcd root finder.
///
/// The one place this comparison is written down, so [`plan_odd_steps`] and [`subgroup_roots`]
/// cannot disagree about which route a given order takes — a planner that chose steps against a
/// different rule than the search applies would take steps that buy nothing.
fn enumeration_is_cheaper<F: KnownOrder>(order: u128, degree: u32) -> bool {
    let terms = degree as f64 + 1.0;
    let order_bits = 64.0 * F::order_limbs().len() as f64;
    order as f64 * terms <= order_bits * terms * terms
}

/// Odd-order steps that leave a subgroup worth enumerating, and the order they leave — Algorithm 3.
///
/// The order-2 phase drives every base-field root into the subgroup of order `s`, the odd part of
/// `q - 1`. When `s` is small that subgroup is enumerable and nothing more is needed; when it is
/// not, the search degrades to the quadratic root finder on a polynomial of the input's degree,
/// which `docs/research/graeffe-root-finding.md` §6.5 measures at **99.6% of the call** over
/// Goldilocks. An order-`q` step maps the order-`s` subgroup onto the order-`s/q` one, so taking
/// steps at the small prime factors of `s` shrinks the search geometrically.
///
/// Factors are taken smallest first and only while the residual is still not worth enumerating, so
/// a field that needs one step pays for one. Nothing is taken when the subgroup is already
/// enumerable, which keeps KoalaBear on exactly the route it had.
fn plan_odd_steps<F: KnownOrder>(subgroup_order: u128, degree: u32) -> (Vec<u64>, u128) {
    if enumeration_is_cheaper::<F>(subgroup_order, degree) {
        return (Vec::new(), subgroup_order);
    }

    // The bound on a factor worth a step. An order-`q` transform multiplies `q` scaled copies of
    // the polynomial, so its cost grows with `q` while the subgroup it removes shrinks by the same
    // factor — and a step is worth taking while the first is the smaller. `1 << 16` keeps every
    // factor of a 64-bit field's odd part that is worth one and excludes Goldilocks' 65 537, whose
    // step would cost more than enumerating it.
    const STEP_ORDER_BOUND: u64 = 1 << 16;

    let mut residual = subgroup_order;
    let mut steps = Vec::new();
    for factor in small_odd_factors(subgroup_order, STEP_ORDER_BOUND) {
        if enumeration_is_cheaper::<F>(residual, degree) {
            break;
        }
        residual /= factor as u128;
        steps.push(factor);
    }

    // **All or nothing.** If the factors available do not get the residual down to something worth
    // enumerating, the steps buy nothing: the search still takes the gcd route, on a polynomial of
    // the same degree, and the transforms are pure overhead on top of it — which is precisely the
    // criticism §6.5 makes of the order-2 iteration over Goldilocks. Over Goldilocks at degree 256
    // this is the live case: the residual floor is 65 537 and enumerating it only becomes cheaper
    // than the gcd route around degree 1 024, so a smaller instance stays on exactly the route it
    // had before #593.
    if !enumeration_is_cheaper::<F>(residual, degree) {
        return (Vec::new(), subgroup_order);
    }
    (steps, residual)
}

/// The roots of `g` that are `q`-th roots of `mu`: `gcd(g, x^q - mu)` — [PC] Algorithm 3 lines 10-14.
///
/// The order-2 descent has a shortcut — reduce `g` modulo `x^2 - mu` in one pass, since `x^2 = mu`
/// — and that shortcut is what [`un_square`] is. It does not generalize: at order `q` the quotient
/// has `q` preimages and reading off a linear remainder no longer identifies one, so this runs the
/// gcd that [`un_square`] exists to avoid.
///
/// **Multi-valued, and that is why it returns a vector.** `mu` has up to `q` preimages in the
/// field and `g` may vanish at more than one of them; which one continues to a root of the
/// original polynomial is not decidable here, so every one is returned and the caller branches.
/// The gcd's degree bounds the breadth and is in practice one.
fn un_power<F: KnownOrder, R: RngCore + CryptoRng>(
    g: &UnivariatePolynomial<F>,
    mu: &F,
    q: u64,
    rng: &mut R,
) -> Vec<F> {
    let mut coefficients = vec![F::zero(); q as usize + 1];
    coefficients[0] = -*mu;
    coefficients[q as usize] = F::one();
    let shifted = UnivariatePolynomial::new(&coefficients);

    let common = gcd(g, &shifted);
    if common.degree() == 0 {
        return Vec::new();
    }
    roots(&common, rng)
}

/// A root of `f` from a candidate in the final subgroup, inverting the odd steps then the squares.
///
/// Two phases, because the two kinds of step invert differently: the odd-order steps come off with
/// [`un_power`]'s gcd and the order-2 steps with [`un_square`]'s one-pass reduction.
///
/// **Depth-first over the odd steps, because [`un_power`] is multi-valued.** An order-`q` step has
/// up to `q` preimages and the polynomial may vanish at several; which one descends to a root of
/// `f` is not decidable at that level, so every branch is tried. The order-2 phase needs no
/// branching — [`un_square`] identifies its preimage from the polynomial — so it runs once per
/// leaf, and the verification against `f` is what decides the leaf.
///
/// The breadth is bounded by the gcd's degree and is one in every case measured; the depth is the
/// number of odd steps, four over Goldilocks. With no odd steps this is the order-2 descent and a
/// single verification, which is what it was before #593.
fn descend_mixed<F: KnownOrder, R: RngCore + CryptoRng>(
    f: &UnivariatePolynomial<F>,
    base: &UnivariatePolynomial<F>,
    retained: &[UnivariatePolynomial<F>],
    odd_retained: &[(u64, UnivariatePolynomial<F>)],
    mu: F,
    rng: &mut R,
) -> Option<F> {
    match odd_retained.split_last() {
        // Every odd step inverted: finish through the squares and let `f` decide.
        None => {
            let root = descend(base, retained, mu, rng)?;
            f.eval(&root).is_zero().then_some(root)
        }
        // `polynomial` is the input to this step, so its roots are the preimages to choose from.
        Some(((q, _), earlier)) => {
            let polynomial = earlier
                .last()
                .map(|(_, p)| p)
                .unwrap_or_else(|| retained.last().unwrap_or(base));
            for preimage in un_power(polynomial, &mu, *q, rng) {
                if let Some(root) = descend_mixed(f, base, retained, earlier, preimage, rng) {
                    return Some(root);
                }
            }
            None
        }
    }
}

/// `alpha` from `alpha^(2^k)`, by un-squaring against each retained `G_{2^i}` in turn.
///
/// `retained[j]` is `G_{2^(j+1)}` reduced and `base` is `G_{2^0}`, which is `f` itself unless the
/// `beta_0` fold materialized one — `base` is not kept in `retained` so that the common case holds
/// no copy of the input. The loop runs from the top down. [PC] Algorithm 2 line 8 at `q_i = 2`.
fn descend<F: KnownOrder, R: RngCore + CryptoRng>(
    base: &UnivariatePolynomial<F>,
    retained: &[UnivariatePolynomial<F>],
    mut mu: F,
    rng: &mut R,
) -> Option<F> {
    for level in (1..=retained.len()).rev() {
        let g = if level == 1 {
            base
        } else {
            &retained[level - 2]
        };
        mu = un_square(g, &mu, rng)?;
    }
    Some(mu)
}

/// The common root of `g` and `x^2 - mu`, or `None` if they share none.
///
/// `gcd(g, x^2 - mu)` without running a gcd, which is [PC]'s own advice on Algorithm 2 line 8:
/// reduce `g` modulo `x^2 - mu` — one pass over the coefficients, since `x^2 = mu` — to get
/// `a x + b`, whose root `-b / a` is the one of `mu`'s two square roots that `g` vanishes at. So
/// **the sign is decided by the polynomial**; there is nothing to guess and no convention to carry
/// through the descent.
///
/// Two degenerate cases. `a = b = 0` means `x^2 - mu` divides `g`, so both square roots are roots
/// of `g`; both also lie in the subgroup one level down, so either continues a valid descent and
/// Tonelli-Shanks picks one. It is not a rare case — it is what `f = x^2 - a^2` produces at the
/// first level. `a = 0` with `b` nonzero means the two share no root.
fn un_square<F: KnownOrder, R: RngCore + CryptoRng>(
    g: &UnivariatePolynomial<F>,
    mu: &F,
    rng: &mut R,
) -> Option<F> {
    let mut even = F::zero();
    let mut odd = F::zero();
    let mut power = F::one();
    for pair in g.coefficients().chunks(2) {
        even += pair[0] * power;
        if let Some(upper) = pair.get(1) {
            odd += *upper * power;
        }
        power *= *mu;
    }

    if !odd.is_zero() {
        let root = -even / odd;
        return (root * root == *mu).then_some(root);
    }
    if !even.is_zero() {
        return None;
    }
    mu.sqrt(rng)
}

/// `limbs` as a `u128`, or `None` if it is wider than that.
fn limbs_to_u128(limbs: &[u64]) -> Option<u128> {
    if limbs.len() > 2 {
        return None;
    }
    let low = *limbs.first().unwrap_or(&0) as u128;
    let high = *limbs.get(1).unwrap_or(&0) as u128;
    Some(low | (high << 64))
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use rand::{prelude::StdRng, Rng, SeedableRng};

    use super::{
        fold_if_needed, graeffe_2, graeffe_2_over_domain, graeffe_all_roots, graeffe_l,
        graeffe_root, graeffe_root_with_stats, GraeffeError, SubgroupRoute,
    };
    use crate::{
        fields::{KoalaBear, Mersenne31, Zp18446744069414584321, Zp2147483647, Zp65537},
        poly::univariate::{roots::roots, Polynomial, UnivariatePolynomial},
        FFTDomain, FiniteField, KnownOrder, One, Zero,
    };

    /// KoalaBear in a `u32`, the field the registered 2026 Poseidon challenges are over.
    type Koala = KoalaBear;
    /// Goldilocks, `2^64 - 2^32 + 1`, whose odd part is `2^32 - 1`.
    type Goldilocks = Zp18446744069414584321;

    /// `prod (x - r_i)` from the given roots, and `prod (x - r_i^power)` beside it.
    fn planted<F: FiniteField>(roots: &[F], power: u32) -> UnivariatePolynomial<F> {
        let raised: Vec<F> = roots.iter().map(|r| r.pow(power as u128)).collect();
        UnivariatePolynomial::from_zeros(&raised)
    }

    /// `count` distinct nonzero field elements.
    fn distinct_nonzero<F: FiniteField, R: Rng>(count: usize, rng: &mut R) -> Vec<F> {
        let mut seen: Vec<F> = Vec::with_capacity(count);
        while seen.len() < count {
            let candidate = F::new(rng.gen::<u32>() as u64);
            if !candidate.is_zero() && !seen.contains(&candidate) {
                seen.push(candidate);
            }
        }
        seen
    }

    /// A polynomial of exactly `degree` with the given roots planted and a random cofactor.
    ///
    /// Building `prod (x - r_i)` over `degree` roots would be quadratic and would also measure the
    /// construction rather than the root finder; a handful of planted roots in a random cofactor
    /// is the shape a resultant or an interpolated output coordinate leaves behind.
    fn with_planted_roots<F: FiniteField, R: Rng>(
        degree: usize,
        planted_roots: &[F],
        rng: &mut R,
    ) -> UnivariatePolynomial<F> {
        let cofactor_degree = degree - planted_roots.len();
        let mut coefficients: Vec<F> = (0..=cofactor_degree)
            .map(|_| F::new(rng.gen::<u32>() as u64))
            .collect();
        while coefficients[cofactor_degree].is_zero() {
            coefficients[cofactor_degree] = F::new(rng.gen::<u32>() as u64);
        }
        &UnivariatePolynomial::new(&coefficients) * &UnivariatePolynomial::from_zeros(planted_roots)
    }

    /// `GT_2` on a degree-16 polynomial with known roots is the polynomial of their squares.
    #[test]
    fn test_the_order_two_transform_squares_the_roots() {
        let mut rng = StdRng::seed_from_u64(1);
        let planted_roots = distinct_nonzero::<Zp65537, _>(16, &mut rng);
        let f = UnivariatePolynomial::from_zeros(&planted_roots);
        assert_eq!(f.degree(), 16);
        assert_eq!(
            graeffe_2(&f, &mut rng).expect("65537 has two-adicity 16"),
            planted(&planted_roots, 2)
        );
    }

    /// The same oracle at odd degree, where the `(-1)^d` normalization is the whole difference.
    #[test]
    fn test_the_sign_convention_holds_at_odd_degree() {
        let mut rng = StdRng::seed_from_u64(2);
        let planted_roots = distinct_nonzero::<Koala, _>(15, &mut rng);
        let f = UnivariatePolynomial::from_zeros(&planted_roots);
        assert_eq!(f.degree(), 15);
        let transformed = graeffe_2(&f, &mut rng).expect("KoalaBear has two-adicity 24");
        assert_eq!(transformed, planted(&planted_roots, 2));
        // Without the normalization the result would be the negation, so this is not vacuous.
        assert_ne!(
            transformed.scale(&-Koala::one()),
            planted(&planted_roots, 2)
        );
    }

    /// Two order-2 steps are one order-4 step, which is [PC] Lemma 2.
    #[test]
    fn test_two_order_two_steps_are_one_order_four_step() {
        let mut rng = StdRng::seed_from_u64(3);
        for degree in [7usize, 16] {
            let planted_roots = distinct_nonzero::<Zp65537, _>(degree, &mut rng);
            let f = UnivariatePolynomial::from_zeros(&planted_roots);
            let once = graeffe_2(&f, &mut rng).expect("a domain exists");
            let twice = graeffe_2(&once, &mut rng).expect("a domain exists");
            assert_eq!(twice, graeffe_l(&f, 4, &mut rng).expect("4 divides 65536"));
            assert_eq!(twice, planted(&planted_roots, 4), "degree {degree}");
        }
    }

    /// `GT_l` preserves the degree, which is [PC] Lemma 1.
    #[test]
    fn test_the_transform_preserves_the_degree() {
        let mut rng = StdRng::seed_from_u64(4);
        for degree in [1usize, 2, 5, 16, 17, 64] {
            let f = with_planted_roots::<Zp65537, _>(degree, &[Zp65537::one()], &mut rng);
            assert_eq!(f.degree() as usize, degree);
            assert_eq!(
                graeffe_2(&f, &mut rng).expect("a domain exists").degree() as usize,
                degree,
                "GT_2 changed the degree at {degree}"
            );
            assert_eq!(
                graeffe_l(&f, 2, &mut rng)
                    .expect("2 divides 65536")
                    .degree() as usize,
                degree
            );
        }
    }

    /// The three-NTT form agrees with [PC] Definition 2's product of scaled copies.
    #[test]
    fn test_the_three_transform_form_agrees_with_the_product_definition() {
        let mut rng = StdRng::seed_from_u64(5);
        for degree in [3usize, 8, 9] {
            let f = with_planted_roots::<Zp65537, _>(degree, &[Zp65537::new(3)], &mut rng);
            assert_eq!(
                graeffe_2(&f, &mut rng).expect("a domain exists"),
                graeffe_l(&f, 2, &mut rng).expect("2 divides 65536"),
                "degree {degree}"
            );
        }
    }

    /// An odd-order transform raises the roots to that power and needs no sign correction.
    #[test]
    fn test_an_odd_order_transform_raises_the_roots_to_that_power() {
        let mut rng = StdRng::seed_from_u64(6);
        // 2130706432 = 2^24 * 127, so 127 is the only odd prime order available over KoalaBear.
        for order in [127u64] {
            for degree in [4usize, 7] {
                let planted_roots = distinct_nonzero::<Koala, _>(degree, &mut rng);
                let f = UnivariatePolynomial::from_zeros(&planted_roots);
                assert_eq!(
                    graeffe_l(&f, order, &mut rng).expect("127 divides q - 1"),
                    planted(&planted_roots, order as u32),
                    "order {order} at degree {degree}"
                );
            }
        }
        // 65536 = 2^16 and 18446744069414584320 = 2^32 * 3 * 5 * 17 * 257 * 65537, so the odd
        // orders have to come from Goldilocks.
        for order in [3u64, 5, 17] {
            let planted_roots = distinct_nonzero::<Goldilocks, _>(5, &mut rng);
            let f = UnivariatePolynomial::from_zeros(&planted_roots);
            assert_eq!(
                graeffe_l(&f, order, &mut rng).expect("the order divides q - 1"),
                planted(&planted_roots, order as u32),
                "order {order}"
            );
        }
    }

    /// Lemma 2 across two different odd orders: `GT_3 . GT_5 = GT_15`.
    #[test]
    fn test_odd_orders_compose() {
        let mut rng = StdRng::seed_from_u64(7);
        let planted_roots = distinct_nonzero::<Goldilocks, _>(4, &mut rng);
        let f = UnivariatePolynomial::from_zeros(&planted_roots);
        let composed = graeffe_l(
            &graeffe_l(&f, 3, &mut rng).expect("3 divides q - 1"),
            5,
            &mut rng,
        )
        .expect("5 divides q - 1");
        assert_eq!(composed, graeffe_l(&f, 15, &mut rng).expect("15 divides"));
        assert_eq!(composed, planted(&planted_roots, 15));
    }

    /// An order that does not divide `q - 1` has no root of unity, so the transform is refused.
    #[test]
    fn test_an_order_that_does_not_divide_the_group_order_is_refused() {
        let mut rng = StdRng::seed_from_u64(8);
        let f = UnivariatePolynomial::<Koala>::from_zeros(&[Koala::one(), Koala::new(5)]);
        // q - 1 = 2^24 * 127, so 3 does not divide it.
        assert!(graeffe_l(&f, 3, &mut rng).is_err());
    }

    /// A domain with exactly `deg f + 1` points suffices, so the step is three transforms of that
    /// size rather than of twice it.
    #[test]
    fn test_a_domain_of_one_more_than_the_degree_suffices() {
        let mut rng = StdRng::seed_from_u64(9);
        let planted_roots = distinct_nonzero::<Zp65537, _>(15, &mut rng);
        let f = UnivariatePolynomial::from_zeros(&planted_roots);
        assert_eq!(f.degree(), 15);
        let generator = Zp65537::two_adic_root_of_unity(4, &mut rng);
        let domain = FFTDomain::from_generator(generator, 16);
        assert_eq!(domain.size(), 16);
        assert_eq!(
            graeffe_2_over_domain(&f, &domain),
            planted(&planted_roots, 2)
        );
    }

    /// A domain too small for the degree is a programmer error, since the caller chose it.
    #[test]
    #[should_panic(expected = "needs at least")]
    fn test_a_domain_smaller_than_the_degree_is_refused() {
        let mut rng = StdRng::seed_from_u64(10);
        let f = UnivariatePolynomial::<Zp65537>::from_zeros(&distinct_nonzero(15, &mut rng));
        let generator = Zp65537::two_adic_root_of_unity(3, &mut rng);
        let domain = FFTDomain::from_generator(generator, 8);
        let _ = graeffe_2_over_domain(&f, &domain);
    }

    /// Planted roots are recovered, and the root returned is one `roots` also reports.
    fn planted_roots_are_recovered<F: KnownOrder>(degrees: &[usize], seed: u64) {
        let mut rng = StdRng::seed_from_u64(seed);
        for &degree in degrees {
            let planted_roots = distinct_nonzero::<F, _>(4, &mut rng);
            let f = with_planted_roots::<F, _>(degree, &planted_roots, &mut rng);
            assert_eq!(f.degree() as usize, degree);

            let found = graeffe_root(&f, &mut rng)
                .expect("the field hosts a domain for this degree")
                .unwrap_or_else(|| panic!("degree {degree} has four planted roots"));
            assert!(
                f.eval(&found).is_zero(),
                "degree {degree}: {found} is not a root"
            );
            let expected: HashSet<F> = roots(&f, &mut rng).into_iter().collect();
            assert!(
                expected.contains(&found),
                "degree {degree}: {found} is not among the roots the gcd finder reports"
            );
        }
    }

    /// Over KoalaBear, the registered challenge's field, at the degrees the gcd finder reaches.
    #[test]
    fn test_planted_roots_are_recovered_over_koala_bear() {
        planted_roots_are_recovered::<Koala>(&[256, 512, 1024, 2048, 4096], 11);
    }

    /// Over Goldilocks, where the odd part of `q - 1` is `2^32 - 1` and the subgroup search falls
    /// back to the gcd route.
    #[test]
    fn test_planted_roots_are_recovered_over_goldilocks() {
        planted_roots_are_recovered::<Goldilocks>(&[256, 512], 13);
    }

    /// The same at the degrees a release build reaches, up to `2^16`.
    #[test]
    #[ignore] // Slow: 24 order-2 steps at degree 2^16 and a gcd cross-check at that degree.
    fn test_planted_roots_are_recovered_at_larger_degrees() {
        planted_roots_are_recovered::<Koala>(&[8192, 16384, 32768, 65536], 17);
        planted_roots_are_recovered::<Goldilocks>(&[1024, 2048, 4096], 19);
    }

    /// A polynomial with no base-field root returns none rather than a wrong root.
    #[test]
    fn test_no_base_field_root_returns_none() {
        let mut rng = StdRng::seed_from_u64(23);
        // x^2 - 3 over KoalaBear: 3 is a quadratic non-residue there, checked by the character.
        let f = UnivariatePolynomial::<Koala>::new(&[-Koala::new(3), Koala::zero(), Koala::one()]);
        assert_eq!(crate::fields::legendre_symbol(&Koala::new(3)), -1);
        assert_eq!(graeffe_root(&f, &mut rng), Ok(None));
        assert!(roots(&f, &mut rng).is_empty());
    }

    /// An irreducible factor of high degree with no base-field root also returns none.
    #[test]
    fn test_a_polynomial_whose_roots_lie_only_in_an_extension_returns_none() {
        let mut rng = StdRng::seed_from_u64(29);
        // x^q - x vanishes on every element, so dividing it out of a random polynomial leaves one
        // with no base-field root. Cheaper: search for one, which takes a handful of draws.
        for _ in 0..40 {
            let f = UnivariatePolynomial::<Koala>::new(&[
                Koala::new(rng.gen::<u32>() as u64),
                Koala::new(rng.gen::<u32>() as u64),
                Koala::one(),
            ]);
            if roots(&f, &mut rng).is_empty() {
                assert_eq!(graeffe_root(&f, &mut rng), Ok(None));
                return;
            }
        }
        panic!("no rootless quadratic was drawn");
    }

    /// A repeated root is found, and so is the root of a perfect square.
    #[test]
    fn test_repeated_roots_and_perfect_squares() {
        let mut rng = StdRng::seed_from_u64(31);
        let a = Koala::new(7);
        let linear = UnivariatePolynomial::<Koala>::from_zeros(&[a]);

        // (x - 7)^8, a single root of multiplicity eight.
        let repeated = linear.pow(8);
        assert_eq!(graeffe_root(&repeated, &mut rng), Ok(Some(a)));

        // A perfect square, whose every root is repeated.
        let base = with_planted_roots::<Koala, _>(32, &[a, Koala::new(11)], &mut rng);
        let square = &base * &base;
        let found = graeffe_root(&square, &mut rng)
            .expect("a domain exists")
            .expect("the square of a polynomial with roots has roots");
        assert!(square.eval(&found).is_zero());
        assert!(base.eval(&found).is_zero());

        // x^2 - a^2, where both square roots of the transform's root are roots of the input and
        // the un-squaring hits its degenerate branch.
        let pair = UnivariatePolynomial::<Koala>::from_zeros(&[a, -a]);
        let found = graeffe_root(&pair, &mut rng)
            .expect("a domain exists")
            .expect("x^2 - a^2 has two roots");
        assert!(found == a || found == -a);
    }

    /// Zero is reported when the constant term vanishes, before any transform runs.
    #[test]
    fn test_a_vanishing_constant_term_gives_zero() {
        let mut rng = StdRng::seed_from_u64(37);
        let f = UnivariatePolynomial::<Koala>::new(&[Koala::zero(), Koala::one(), Koala::one()]);
        let (root, stats) = graeffe_root_with_stats(&f, &mut rng).expect("no transform needed");
        assert_eq!(root, Some(Koala::zero()));
        assert_eq!(stats.graeffe_steps, 0);
    }

    /// `x^s - 1`, whose fold to zero must not be read as "no roots in the subgroup".
    ///
    /// The odd part of KoalaBear's `q - 1` is 127, so `x^127 - 1` splits into 127 distinct base
    /// field roots and is also fixed by the degree-normalized order-two transform. Every element
    /// of the order-127 subgroup is therefore a root of the fully transformed polynomial, and the
    /// final reduction modulo `x^127 - 1` sends it to zero — the one case where a zero reduced
    /// polynomial means *every* candidate rather than none.
    #[test]
    fn test_a_subgroup_vanishing_polynomial_still_yields_a_root() {
        let mut rng = StdRng::seed_from_u64(97);
        let subgroup_order = 127u128;
        let mut coefficients = vec![Koala::zero(); subgroup_order as usize + 1];
        coefficients[0] = -Koala::one();
        coefficients[subgroup_order as usize] = Koala::one();
        let f = UnivariatePolynomial::<Koala>::new(&coefficients);

        let (root, stats) = graeffe_root_with_stats(&f, &mut rng).expect("KoalaBear carries 128");
        let root = root.expect("x^127 - 1 has 127 roots in the base field");
        assert!(f.eval(&root).is_zero());
        assert!(root.pow(subgroup_order).is_one());
        assert_eq!(stats.subgroup_order, subgroup_order);
    }

    /// The same vanishing factor inside a larger polynomial still descends to a root.
    ///
    /// `(x^127 - 1) * cofactor` folds to zero just as the bare factor does, but at a degree above
    /// the subgroup, so the retained polynomial the descent un-squares against is the unreduced
    /// transform rather than something of degree below 127.
    #[test]
    fn test_a_vanishing_factor_in_a_larger_polynomial_still_descends() {
        let mut rng = StdRng::seed_from_u64(101);
        let mut vanishing = vec![Koala::zero(); 128];
        vanishing[0] = -Koala::one();
        vanishing[127] = Koala::one();
        let cofactor = distinct_nonzero::<Koala, _>(4, &mut rng);
        let f = &UnivariatePolynomial::<Koala>::new(&vanishing)
            * &UnivariatePolynomial::from_zeros(&cofactor);
        assert_eq!(f.degree(), 131);

        let root = graeffe_root(&f, &mut rng)
            .expect("KoalaBear carries 256")
            .expect("131 roots, all of them in the base field");
        assert!(f.eval(&root).is_zero());
    }

    /// A fold that lands on zero is refused, so the caller keeps the polynomial it had.
    #[test]
    fn test_a_fold_onto_the_zero_polynomial_is_refused() {
        let mut coefficients = vec![Koala::zero(); 128];
        coefficients[0] = -Koala::one();
        coefficients[127] = Koala::one();
        let f = UnivariatePolynomial::<Koala>::new(&coefficients);

        // `f mod (x^127 - 1)` is zero, which would lose all 127 of its roots.
        assert_eq!(fold_if_needed(&f, Some(127)), None);
        // A fold onto a nonzero remainder is still performed: 127 mod 126 is 1, so the leading
        // term lands on the linear one and `f mod (x^126 - 1)` is `x - 1`.
        let folded = fold_if_needed(&f, Some(126)).expect("x - 1 is nonzero");
        assert_eq!(
            folded,
            UnivariatePolynomial::new(&[-Koala::one(), Koala::one()])
        );
    }

    /// A nonzero constant has no root.
    #[test]
    fn test_a_nonzero_constant_has_no_root() {
        let mut rng = StdRng::seed_from_u64(41);
        let f = UnivariatePolynomial::<Koala>::new(&[Koala::new(5)]);
        assert_eq!(graeffe_root(&f, &mut rng), Ok(None));
    }

    /// The zero polynomial has no meaningful root set.
    #[test]
    #[should_panic(expected = "every element is a root of the zero polynomial")]
    fn test_the_zero_polynomial_panics() {
        let mut rng = StdRng::seed_from_u64(43);
        let _ = graeffe_root(&UnivariatePolynomial::<Koala>::zero(), &mut rng);
    }

    /// A field whose two-adicity cannot host the domain fails as a typed value, not a wrong root.
    ///
    /// Mersenne-31 is where this bites: `2^31 - 1` is prime so `q - 1 = 2 * (2^30 - 1)` and the
    /// largest power-of-two domain has two points, which carries degree one and nothing above it.
    #[test]
    fn test_a_field_without_the_two_adicity_refuses() {
        let mut rng = StdRng::seed_from_u64(47);
        assert_eq!(Mersenne31::two_adicity(), 1);
        assert_eq!(Zp2147483647::two_adicity(), 1);

        let planted_roots = distinct_nonzero::<Mersenne31, _>(2, &mut rng);
        let f = UnivariatePolynomial::from_zeros(&planted_roots);
        assert_eq!(
            graeffe_root(&f, &mut rng),
            Err(GraeffeError::DomainTooLarge {
                degree: 2,
                log_n: 2,
                two_adicity: 1,
            })
        );
        assert!(graeffe_2(&f, &mut rng).is_err());

        // Degree one still works: one point per coefficient, and a domain of two exists.
        let linear = UnivariatePolynomial::<Mersenne31>::from_zeros(&planted_roots[..1]);
        assert_eq!(graeffe_root(&linear, &mut rng), Ok(Some(planted_roots[0])));
    }

    /// Progressive reduction cuts the transform work, and by exactly the schedule it implies.
    ///
    /// The lever is `beta_i = (q - 1) / 2^i`, so the degree stays full until `2^i` passes
    /// `(q - 1) / d` and halves thereafter. At `d = 4096` over KoalaBear, `(q - 1) / d = 520 192`,
    /// so 19 steps run at 8 192 points and the last five at 4 096, 2 048, 1 024, 512 and 256 —
    /// `3 * 163 584 = 490 752` elements against `3 * 24 * 8 192 = 589 824` with no reduction.
    ///
    /// The exact figure is asserted because the inequality alone is weak: **the saving is a factor
    /// of 1.2 here, not an order**, since `ceil(log2((q - 1) / d)) = 19` of the 24 steps are at
    /// full size. §3.6's "a small constant times the largest one" is that constant, and it is
    /// `ceil(log2((q - 1) / d)) + 2` rather than something near one.
    #[test]
    fn test_progressive_reduction_bounds_the_total_transform_work() {
        let mut rng = StdRng::seed_from_u64(53);
        let degree = 4096;
        let planted_roots = distinct_nonzero::<Koala, _>(2, &mut rng);
        let f = with_planted_roots::<Koala, _>(degree, &planted_roots, &mut rng);
        let (_root, stats) = graeffe_root_with_stats(&f, &mut rng).expect("a domain exists");

        assert_eq!(stats.graeffe_steps, 24);
        assert_eq!(stats.transforms, 72);
        assert_eq!(stats.max_transform_size, 8192);
        assert_eq!(stats.subgroup_order, 127);
        assert_eq!(
            stats.subgroup_route,
            SubgroupRoute::Enumerated { points: 127 }
        );
        assert!(
            stats.final_degree <= 126,
            "the reduction left degree {} above the subgroup order",
            stats.final_degree
        );
        assert_eq!(stats.total_transform_elements, 490_752);
        assert!(
            stats.total_transform_elements
                < 3 * stats.graeffe_steps as usize * stats.max_transform_size,
            "the reduction saved nothing: {} elements against {} with no reduction",
            stats.total_transform_elements,
            3 * stats.graeffe_steps as usize * stats.max_transform_size
        );
    }

    /// Over Goldilocks the two-adic reduction never bites, and the odd-order steps are what make
    /// the subgroup enumerable — #593, [PC] Algorithm 3.
    ///
    /// The odd part of `q - 1` is `2^32 - 1 = 3 * 5 * 17 * 257 * 65537`, above any degree of
    /// interest, so all 32 order-2 steps run at the input degree and leave a subgroup of
    /// 4 294 967 295 elements that cannot be enumerated. Driving `beta` through `3 * 5 * 17 * 257`
    /// leaves **65 537**, which can, and that is the whole of what Algorithm 3 buys here.
    #[test]
    fn test_the_odd_steps_make_the_goldilocks_subgroup_enumerable() {
        let mut rng = StdRng::seed_from_u64(59);
        // 1 024 and not 256, because the crossover is a property of the degree. Enumerating the
        // 65 537-element residue costs `65537 (d+1)` and the gcd route `64 (d+1)^2`, so the first
        // is cheaper only from `d + 1 >= 1024` — below that the steps would buy nothing and
        // `plan_odd_steps` declines to take them. §6.5's 256-row staying on the old route is
        // therefore correct rather than a miss, and `test_small_goldilocks_instances_keep_the_old_route`
        // is the other side of it.
        let degree = 1024;
        let f = with_planted_roots::<Goldilocks, _>(degree, &[Goldilocks::one()], &mut rng);
        let (root, stats) = graeffe_root_with_stats(&f, &mut rng).expect("a domain exists");

        assert_eq!(stats.graeffe_steps, 32, "the order-2 phase is unchanged");
        assert_eq!(
            stats.odd_steps,
            vec![3, 5, 17, 257],
            "the small factors of the odd part, smallest first"
        );
        assert_eq!(
            stats.subgroup_order, 65_537,
            "the residual order the search actually runs over"
        );
        assert_eq!(
            stats.subgroup_route,
            SubgroupRoute::Enumerated { points: 65_537 },
            "which is the point: the quadratic fallback is gone"
        );
        assert!(
            stats.transforms >= 3 * 32 + 4,
            "three transforms per order-2 step and one per odd step: {}",
            stats.transforms
        );
        // *A* root, not *the* planted one: `with_planted_roots` multiplies the planted factors
        // into a random cofactor, which has roots of its own, and `graeffe_root` returns whichever
        // candidate descends first. What must hold is that it is a root.
        let root = root.expect("the mixed-order descent returned a root");
        assert!(f.eval(&root).is_zero(), "{root:?} is not a root of f");
    }

    /// Below the crossover the odd steps are declined, so a small instance keeps the old route.
    ///
    /// The steps are worth taking only when they make the residual subgroup cheaper to enumerate
    /// than the gcd route is to run, and at degree 256 over Goldilocks they do not: the residual
    /// floor is 65 537 and the gcd route on a degree-256 polynomial is cheaper than 65 537
    /// evaluations of it. Taking them anyway would be four transforms of pure overhead on top of
    /// the same search — which is exactly the criticism §6.5 makes of the order-2 iteration here,
    /// and it would be dishonest to repeat it one phase later.
    #[test]
    fn test_small_goldilocks_instances_keep_the_old_route() {
        let mut rng = StdRng::seed_from_u64(59);
        let f = with_planted_roots::<Goldilocks, _>(256, &[Goldilocks::one()], &mut rng);
        let (root, stats) = graeffe_root_with_stats(&f, &mut rng).expect("a domain exists");

        assert!(stats.odd_steps.is_empty(), "{:?}", stats.odd_steps);
        assert_eq!(stats.subgroup_order, 4_294_967_295);
        assert_eq!(
            stats.subgroup_route,
            SubgroupRoute::GcdRootFinder { degree: 256 }
        );
        assert_eq!(stats.transforms, 3 * 32, "no odd transform was paid for");
        let root = root.expect("the order-2 route returned a root");
        assert!(f.eval(&root).is_zero(), "{root:?} is not a root of f");
    }

    /// The descent inverts an odd-order step, which is the half of Algorithm 3 that was missing.
    ///
    /// `graeffe_l` landed without a caller in the descent because inverting an order-`q` step
    /// needs `gcd(g, x^q - mu)` rather than the order-2 trick of reducing mod `x^2 - mu`. This
    /// drives the whole mixed-order route over Goldilocks at three degrees and checks the root
    /// against the polynomial, which is the only thing that cannot pass vacuously.
    #[test]
    fn test_planted_roots_are_recovered_over_goldilocks_through_odd_steps() {
        planted_roots_are_recovered::<Goldilocks>(&[256, 512, 1024], 29);
    }

    /// Every root of a product of distinct known linear factors is recovered by deflation.
    #[test]
    fn deflation_recovers_every_distinct_root() {
        type F = KoalaBear;
        let mut rng = StdRng::seed_from_u64(0xdef1_a7e0 + 1);
        let planted: Vec<F> = (1..=6u64).map(F::new).collect();
        let mut f = UnivariatePolynomial::new(&[F::one()]);
        for root in &planted {
            f = &f * &UnivariatePolynomial::new(&[-*root, F::one()]);
        }
        let found = graeffe_all_roots(&f, &mut rng).expect("koalabear is two-adic enough");
        assert_eq!(
            found.len(),
            planted.len(),
            "six distinct roots, six reported"
        );
        let found: HashSet<F> = found.into_iter().collect();
        let expected: HashSet<F> = planted.into_iter().collect();
        assert_eq!(found, expected);
    }

    /// Deflation returns a repeated root once per multiplicity, not once per value.
    #[test]
    fn deflation_returns_a_repeated_root_with_its_multiplicity() {
        type F = KoalaBear;
        let mut rng = StdRng::seed_from_u64(0xdef1_a7e0 + 2);
        let root = F::new(7);
        let linear = UnivariatePolynomial::new(&[-root, F::one()]);
        // (x - 7)^3
        let f = &(&linear * &linear) * &linear;
        let found = graeffe_all_roots(&f, &mut rng).expect("two-adic");
        assert_eq!(found.len(), 3, "a triple root is three roots");
        assert!(found.iter().all(|r| *r == root));
    }

    /// A polynomial with no base-field root deflates to nothing rather than looping.
    #[test]
    fn deflation_terminates_with_no_base_field_roots() {
        type F = KoalaBear;
        let mut rng = StdRng::seed_from_u64(0xdef1_a7e0 + 3);
        // x^2 - g for a non-square g has no root in the base field.
        let mut f = UnivariatePolynomial::new(&[F::zero(), F::zero(), F::one()]);
        for candidate in 2..200u64 {
            let g = F::new(candidate);
            if roots(
                &UnivariatePolynomial::new(&[-g, F::zero(), F::one()]),
                &mut rng,
            )
            .is_empty()
            {
                f = UnivariatePolynomial::new(&[-g, F::zero(), F::one()]);
                break;
            }
        }
        let found = graeffe_all_roots(&f, &mut rng).expect("two-adic");
        assert!(found.is_empty(), "no base-field roots, so none reported");
    }

    /// Deflation and the gcd-based finder agree as multisets on random polynomials.
    #[test]
    fn deflation_agrees_with_the_gcd_finder_on_random_polynomials() {
        type F = KoalaBear;
        let mut rng = StdRng::seed_from_u64(0xdef1_a7e0 + 4);
        for degree in [4usize, 7, 12, 20] {
            let coefficients: Vec<F> = (0..=degree)
                .map(|_| F::new(rng.gen_range(0..1000)))
                .collect();
            let f = UnivariatePolynomial::new(&coefficients);
            if f.is_zero() {
                continue;
            }
            let by_deflation = graeffe_all_roots(&f, &mut rng).expect("two-adic");
            // `roots` reports distinct roots, so compare the deflation result as a set.
            let as_set: HashSet<F> = by_deflation.iter().copied().collect();
            let by_gcd: HashSet<F> = roots(&f, &mut rng).into_iter().collect();
            assert_eq!(as_set, by_gcd, "degree {degree}");
            // And every reported root really is one.
            for root in &as_set {
                assert!(f.eval(root).is_zero(), "degree {degree}, root {root:?}");
            }
        }
    }
}
