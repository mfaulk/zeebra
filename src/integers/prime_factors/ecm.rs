//! Lenstra's elliptic curve method of factorization.
//!
//! ECM's expected cost depends on the size of the *factor* it finds, not on the size of `n`, which
//! is what makes it the right complement to Pollard rho rather than a replacement: rho costs
//! `O(p^(1/2))` group operations in the smallest prime factor `p`, ECM costs
//! `L(p) = exp((sqrt(2) + o(1)) sqrt(ln p ln ln p))`. The workload this exists to serve is the
//! factorization of `q - 1` for a wide prime field `q`, so that a generator can be found by
//! testing candidate orders. Such a number is semi-smooth — a few small primes and a handful of
//! moderate ones — which is exactly ECM's shape, and not a hard semiprime.
//!
//! Arithmetic is on Montgomery curves `B y^2 = x^3 + A x^2 + x` in `XZ`-only projective
//! coordinates. `B` never appears in the `x`-only formulas, and no step needs a modular inverse,
//! which matters here because [`BigUInt`] has no inversion: the curve constant `(A + 2) / 4` is
//! carried as an unreduced fraction and cleared projectively instead.
//!
//! # References
//! * H. W. Lenstra Jr., "Factoring Integers with Elliptic Curves", Annals of Mathematics 126 (1987).
//! * P. L. Montgomery, "Speeding the Pollard and Elliptic Curve Methods of Factorization",
//!   Mathematics of Computation 48 (1987).

use crate::integers::{
    big_integers::big_uint::BigUInt, gcd_u64, prime_factors::miller_rabin::is_prime,
    prime_factors::SMALL_PRIMES, roots::perfect_power,
};
use rand::{CryptoRng, RngCore};
use std::collections::BTreeMap;

/// Number of Miller-Rabin iterations used to decide whether a cofactor is already prime.
const NUM_ITERATIONS_MR: usize = 5;

/// How much work the elliptic curve method may spend before admitting it found nothing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EcmBudget {
    /// Stage-1 bound: a prime factor `p` is found in stage 1 when the curve order modulo `p` is
    /// `b1`-smooth.
    pub b1: u64,
    /// Stage-2 bound: stage 2 additionally catches a curve order that is `b1`-smooth apart from
    /// one prime in `(b1, b2]`. Stage 2 is skipped when `b2 <= b1`.
    pub b2: u64,
    /// Number of curves to try before giving up. Each curve is an independent trial.
    pub curves: usize,
}

impl EcmBudget {
    /// The standard parameters for finding a factor of about `digits` decimal digits.
    ///
    /// `b1` and the curve count follow the usual ECM parameter table; `b2` is the customary
    /// `100 * b1` for a standard continuation. These are the asymptotically motivated choices,
    /// not measurements of this implementation — the constant factor here is a [`BigUInt`]
    /// multiply and remainder, so the wall-clock cost of a given budget is much higher than a
    /// Montgomery-arithmetic implementation would pay.
    ///
    /// Digit levels above 30 are expensive enough that [`factor_with_budget`] is better driven by
    /// a hand-chosen budget.
    pub fn for_digits(digits: u32) -> Self {
        let (b1, curves) = match digits {
            0..=10 => (500, 10),
            11..=15 => (2_000, 30),
            16..=20 => (11_000, 90),
            21..=25 => (50_000, 240),
            26..=30 => (250_000, 500),
            _ => (1_000_000, 1_100),
        };
        EcmBudget {
            b1,
            b2: b1 * 100,
            curves,
        }
    }
}

/// A factorization carried as far as the effort budget allowed.
///
/// The point of the type is that it can say "I did not finish". An unbounded factorization of a
/// wide integer is a computation a caller must opt into, so the bounded call has to have an honest
/// way to report a cofactor it could not split.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartialFactorization {
    /// The prime factors found, in increasing order.
    pub primes: Vec<BigUInt>,
    /// `powers[i]` is the multiplicity of `primes[i]` in `n`.
    pub powers: Vec<u128>,
    /// Composite factors the budget could not split, each with its multiplicity in `n`.
    pub unfactored: Vec<(BigUInt, u128)>,
}

impl PartialFactorization {
    /// Whether every factor was resolved to a prime.
    pub fn is_complete(&self) -> bool {
        self.unfactored.is_empty()
    }

    /// The number this factorization describes, which always equals the input.
    pub fn product(&self) -> BigUInt {
        let mut product = BigUInt::one();
        for (base, power) in self
            .primes
            .iter()
            .zip(self.powers.iter())
            .chain(self.unfactored.iter().map(|(base, power)| (base, power)))
        {
            product = &product * &base.pow(&BigUInt::new_from_u128(*power));
        }
        product
    }
}

/// A non-trivial factor of `n`, or `None` if the budget was exhausted without finding one.
///
/// Small primes are not what this is for: the curve constant's denominator happens to expose a
/// factor of two, but anything reachable by trial division is far cheaper to strip first, which is
/// what [`factor_with_budget`] does. Inputs below four return `None` because they have no proper
/// divisor to find, not because the search failed.
///
/// Returning `None` is a real outcome rather than an error, which is the property that keeps an
/// unbounded factorization something a caller opts into.
pub fn ecm_find_factor<R: RngCore + CryptoRng>(
    n: &BigUInt,
    budget: &EcmBudget,
    rng: &mut R,
) -> Option<BigUInt> {
    if *n < BigUInt::new_from_u64(4) || budget.curves == 0 {
        return None;
    }

    // Shared by every curve, and the sieve is the expensive part for a wide stage-1 bound.
    let stage_one_primes = primes_up_to(budget.b1);

    for _attempt in 0..budget.curves {
        // `sigma` is reduced modulo `n`, and the gcd check inside the construction rejects the
        // choices that degenerate, so no condition on the sampled value is needed here.
        let sigma = BigUInt::new_from_u64(rng.next_u64());
        let (curve, point) = match suyama_curve(n, &sigma) {
            CurveChoice::Curve(curve, point) => (curve, point),
            CurveChoice::Factor(factor) => return Some(factor),
            CurveChoice::Degenerate => continue,
        };

        let reached = stage_one(&curve, &point, &stage_one_primes, budget.b1);
        if let Some(factor) = non_trivial_gcd(n, &reached.z) {
            return Some(factor);
        }

        // A `Z` of zero means stage 1 drove the point to the identity modulo all of `n`, so every
        // stage-2 multiple of it is the identity too and the continuation has nothing to find.
        if budget.b2 > budget.b1 && !reached.z.is_zero() {
            let accumulated = stage_two(&curve, &reached, budget.b1, budget.b2);
            if let Some(factor) = non_trivial_gcd(n, &accumulated) {
                return Some(factor);
            }
        }
        // Otherwise this curve's order was not smooth enough modulo any factor of `n`, or it was
        // smooth modulo all of them at once and the gcd came back as `n`. Either way the next
        // curve is an independent trial.
    }
    None
}

/// Factor `n` as far as `budget` allows, using trial division, the perfect-power test, and ECM.
///
/// Anything the budget could not split is reported in
/// [`PartialFactorization::unfactored`] rather than dropped, so the result always multiplies back
/// out to `n`.
pub fn factor_with_budget<R: RngCore + CryptoRng>(
    n: &BigUInt,
    budget: &EcmBudget,
    rng: &mut R,
) -> PartialFactorization {
    // Zero has no factorization: every prime divides it, to no finite power.
    if n.is_zero() {
        return PartialFactorization {
            primes: Vec::new(),
            powers: Vec::new(),
            unfactored: vec![(BigUInt::zero(), 1)],
        };
    }

    let mut prime_powers: BTreeMap<BigUInt, u128> = BTreeMap::new();
    let mut unfactored: Vec<(BigUInt, u128)> = Vec::new();

    // Trial division first: a factor the table can reach costs one remainder, not a curve.
    let mut remaining = n.clone();
    for small in SMALL_PRIMES.iter().copied().map(BigUInt::new_from_u64) {
        if remaining.is_one() {
            break;
        }
        let mut power = 0u128;
        while (&remaining % &small).is_zero() {
            remaining = &remaining / &small;
            power += 1;
        }
        if power > 0 {
            prime_powers.insert(small, power);
        }
    }

    // Each entry is a cofactor of `n` together with its multiplicity in `n`.
    let mut cofactors: Vec<(BigUInt, u128)> = if remaining.is_one() {
        Vec::new()
    } else {
        vec![(remaining, 1)]
    };

    while let Some((cofactor, multiplicity)) = cofactors.pop() {
        if is_prime(&cofactor, NUM_ITERATIONS_MR, rng) {
            *prime_powers.entry(cofactor).or_insert(0) += multiplicity;
            continue;
        }
        // A perfect power first: ECM on `m^k` spends its whole budget on a number whose only
        // factors are `m`'s, and splitting the power off hands it the smaller base instead.
        if let Some((base, exponent)) = perfect_power(&cofactor) {
            cofactors.push((base, multiplicity * exponent as u128));
            continue;
        }
        match ecm_find_factor(&cofactor, budget, rng) {
            Some(factor) => {
                let complement = &cofactor / &factor;
                cofactors.push((factor, multiplicity));
                cofactors.push((complement, multiplicity));
            }
            None => unfactored.push((cofactor, multiplicity)),
        }
    }

    // A `BTreeMap` yields the primes in increasing order, which the other factoring entry points
    // also promise.
    let (primes, powers) = prime_powers.into_iter().unzip();
    unfactored.sort();
    PartialFactorization {
        primes,
        powers,
        unfactored,
    }
}

/// `gcd(n, value)` when that is a proper non-trivial divisor of `n`, else `None`.
///
/// A gcd of `n` is the "found everything at once" failure: the curve order was smooth modulo
/// every prime factor, so the gcd names no single one of them.
fn non_trivial_gcd(n: &BigUInt, value: &BigUInt) -> Option<BigUInt> {
    let shared = n.gcd(value);
    if shared.is_one() || shared == *n {
        None
    } else {
        Some(shared)
    }
}

/// The primes up to `bound`, from [`SMALL_PRIMES`] when the table reaches far enough.
///
/// The sieve beyond the table allocates one byte per candidate, so a stage-1 bound far above
/// `10^8` is a memory decision as well as a time one.
fn primes_up_to(bound: u64) -> Vec<u64> {
    let largest_tabulated = *SMALL_PRIMES.last().expect("the table is not empty");
    if bound <= largest_tabulated {
        return SMALL_PRIMES
            .iter()
            .copied()
            .take_while(|prime| *prime <= bound)
            .collect();
    }

    let bound = bound as usize;
    let mut is_composite = vec![false; bound + 1];
    let mut primes = Vec::new();
    for candidate in 2..=bound {
        if is_composite[candidate] {
            continue;
        }
        primes.push(candidate as u64);
        // `saturating_mul` rather than a product that would overflow for a candidate near `bound`.
        let mut multiple = candidate.saturating_mul(candidate);
        while multiple <= bound {
            is_composite[multiple] = true;
            multiple += candidate;
        }
    }
    primes
}

// ---------------------------------------------------------------------------
// Modular arithmetic. Every value below is a representative in `0..n`, which is what lets the
// additions and subtractions be a conditional offset rather than a division.
// ---------------------------------------------------------------------------

fn add_mod(a: &BigUInt, b: &BigUInt, n: &BigUInt) -> BigUInt {
    let sum = a + b;
    if sum >= *n {
        sum - n
    } else {
        sum
    }
}

/// `a - b` modulo `n`, branching because [`BigUInt`] is unsigned and its subtraction panics on a
/// borrow rather than wrapping.
fn sub_mod(a: &BigUInt, b: &BigUInt, n: &BigUInt) -> BigUInt {
    if a >= b {
        a - b
    } else {
        n - &(b - a)
    }
}

fn mul_mod(a: &BigUInt, b: &BigUInt, n: &BigUInt) -> BigUInt {
    &(a * b) % n
}

// ---------------------------------------------------------------------------
// Montgomery curve arithmetic in XZ-only projective coordinates.
// ---------------------------------------------------------------------------

/// A point on a Montgomery curve, carrying only `X` and `Z`. `z == 0` is the identity.
///
/// The `y`-coordinate is never needed: the curve coefficient `B` drops out of the `x`-only
/// formulas, so any `A` and any `x` describe a curve with a point on it, and a point's `x`
/// determines `[k]x` up to the sign of `y` — which is enough, because a factor shows up as a
/// vanishing `Z`.
#[derive(Clone, Debug)]
struct PointXz {
    x: BigUInt,
    z: BigUInt,
}

impl PointXz {
    /// The identity, which has `z == 0`.
    fn identity() -> Self {
        PointXz {
            x: BigUInt::one(),
            z: BigUInt::zero(),
        }
    }
}

/// A Montgomery curve `B y^2 = x^3 + A x^2 + x` modulo `n`.
///
/// `(A + 2) / 4` is held as the unreduced fraction `a24_num / a24_den`. Dividing it out would
/// need a modular inverse, which [`BigUInt`] does not have and which would in any case fail
/// exactly when the denominator shares a factor with `n`. Scaling both output coordinates of the
/// doubling by the denominator clears the fraction projectively instead, at the cost of one
/// multiply per doubling.
struct Curve {
    n: BigUInt,
    a24_num: BigUInt,
    a24_den: BigUInt,
}

impl Curve {
    /// `[2] p`.
    fn double(&self, p: &PointXz) -> PointXz {
        let n = &self.n;
        let sum = add_mod(&p.x, &p.z, n);
        let difference = sub_mod(&p.x, &p.z, n);
        let sum_squared = mul_mod(&sum, &sum, n);
        let difference_squared = mul_mod(&difference, &difference, n);
        // (X+Z)^2 - (X-Z)^2 = 4 X Z.
        let cross = sub_mod(&sum_squared, &difference_squared, n);

        // X' = den * (X+Z)^2 (X-Z)^2 and Z' = 4XZ * (den (X-Z)^2 + num * 4XZ), which is the
        // standard doubling with both coordinates scaled by `a24_den`.
        PointXz {
            x: mul_mod(
                &self.a24_den,
                &mul_mod(&sum_squared, &difference_squared, n),
                n,
            ),
            z: mul_mod(
                &cross,
                &add_mod(
                    &mul_mod(&self.a24_den, &difference_squared, n),
                    &mul_mod(&self.a24_num, &cross, n),
                    n,
                ),
                n,
            ),
        }
    }

    /// `p + q`, given `difference = p - q`.
    ///
    /// Differential addition: without a `y`-coordinate the sum of two points is only determined
    /// once their difference is known. The caller is responsible for that difference being right,
    /// and for it not being the identity — which would mean `p == q` and call for a doubling.
    fn add(&self, p: &PointXz, q: &PointXz, difference: &PointXz) -> PointXz {
        let n = &self.n;
        let u = mul_mod(&sub_mod(&p.x, &p.z, n), &add_mod(&q.x, &q.z, n), n);
        let v = mul_mod(&add_mod(&p.x, &p.z, n), &sub_mod(&q.x, &q.z, n), n);
        let sum = add_mod(&u, &v, n);
        let delta = sub_mod(&u, &v, n);
        PointXz {
            x: mul_mod(&difference.z, &mul_mod(&sum, &sum, n), n),
            z: mul_mod(&difference.x, &mul_mod(&delta, &delta, n), n),
        }
    }

    /// `[k] p`, by the Montgomery ladder.
    ///
    /// The ladder holds `r1 - r0 = p` throughout, which is exactly the difference each
    /// differential addition needs, so no extra point has to be tracked.
    fn multiply(&self, p: &PointXz, k: u64) -> PointXz {
        if k == 0 {
            return PointXz::identity();
        }
        if k == 1 {
            return p.clone();
        }

        let mut r0 = p.clone();
        let mut r1 = self.double(p);
        let highest_bit = 63 - k.leading_zeros();
        for index in (0..highest_bit).rev() {
            if k >> index & 1 == 0 {
                r1 = self.add(&r1, &r0, p);
                r0 = self.double(&r0);
            } else {
                r0 = self.add(&r0, &r1, p);
                r1 = self.double(&r1);
            }
        }
        r0
    }
}

/// The outcome of trying to build a curve from one `sigma`.
enum CurveChoice {
    Curve(Curve, PointXz),
    /// The construction's denominator shares a proper non-trivial factor with `n`. The curve is
    /// unusable, but the shared factor is the answer anyway.
    Factor(BigUInt),
    /// Degenerate for this `sigma`; another one is an independent trial.
    Degenerate,
}

/// A curve and starting point from Suyama's parameterization.
///
/// Suyama's construction forces the curve order to be divisible by twelve, which raises the chance
/// that it is smooth enough for stage 1 to find a factor — the reason to prefer it over picking
/// `A` and `x` at random.
fn suyama_curve(n: &BigUInt, sigma: &BigUInt) -> CurveChoice {
    let sigma = sigma % n;
    let sigma_squared = mul_mod(&sigma, &sigma, n);
    let u = sub_mod(&sigma_squared, &(&BigUInt::new_from_u64(5) % n), n);
    let v = mul_mod(&BigUInt::new_from_u64(4), &sigma, n);

    let u_cubed = mul_mod(&mul_mod(&u, &u, n), &u, n);
    let v_cubed = mul_mod(&mul_mod(&v, &v, n), &v, n);

    // (A + 2) / 4 = (v - u)^3 (3u + v) / (16 u^3 v).
    let v_minus_u = sub_mod(&v, &u, n);
    let a24_num = mul_mod(
        &mul_mod(&mul_mod(&v_minus_u, &v_minus_u, n), &v_minus_u, n),
        &add_mod(&mul_mod(&BigUInt::new_from_u64(3), &u, n), &v, n),
        n,
    );
    let a24_den = mul_mod(&BigUInt::new_from_u64(16), &mul_mod(&u_cubed, &v, n), n);

    // The denominator must be invertible in each quotient the curve is really working in. Where it
    // is not, its gcd with `n` is a factor of `n` — the outcome the whole search is after.
    let shared = n.gcd(&a24_den);
    if shared == *n {
        return CurveChoice::Degenerate;
    }
    if !shared.is_one() {
        return CurveChoice::Factor(shared);
    }

    CurveChoice::Curve(
        Curve {
            n: n.clone(),
            a24_num,
            a24_den,
        },
        PointXz {
            x: u_cubed,
            z: v_cubed,
        },
    )
}

/// Stage 1: multiply the point by every prime power up to the stage-1 bound.
///
/// If the curve order modulo some prime factor `q` of `n` divides that product — which is to say
/// the order is `b1`-smooth — the point reaches the identity modulo `q`, and `q` divides the `Z`
/// of the result while `n` does not.
fn stage_one(curve: &Curve, point: &PointXz, primes: &[u64], b1: u64) -> PointXz {
    let mut reached = point.clone();
    for &prime in primes {
        // Multiply by `prime` once per power of it that still fits under the bound, so that the
        // product covers `prime^e` and not just `prime`.
        let mut power = prime;
        loop {
            reached = curve.multiply(&reached, prime);
            match power.checked_mul(prime) {
                Some(next) if next <= b1 => power = next,
                _ => break,
            }
        }
    }
    reached
}

/// The giant-step stride for the standard continuation.
///
/// `210 = 2 * 3 * 5 * 7`, which leaves only the `phi(210) / 2 = 24` residues below `105` coprime
/// to it, so the baby-step table is small and every prime above seven is `v * 210 +- u` for one of
/// them.
const STAGE_TWO_STRIDE: u64 = 210;

/// Stage 2, the standard continuation: the product whose gcd with `n` exposes a factor whose curve
/// order is `b1`-smooth apart from one prime in `(b1, b2]`.
///
/// For such a prime `p`, `[p] q` is the identity modulo that factor of `n`, so writing
/// `p = v D +- u` the points `[v D] q` and `[u] q` share an `x`-coordinate there — whichever sign
/// `p` took, since `[-u] q` and `[u] q` have the same `x`. Sharing an `x` means
/// `X_vD Z_u - X_u Z_vD` vanishes modulo that factor. The differences are accumulated into one
/// product so the whole stage costs a single gcd rather than one per pair.
///
/// Coverage starts at `D / 2`, so a `b1` below about `105` leaves the primes between `b1` and
/// `105` to neither stage. Any realistic stage-1 bound is far above that.
fn stage_two(curve: &Curve, q: &PointXz, b1: u64, b2: u64) -> BigUInt {
    let n = &curve.n;

    // Baby steps: the multiples `[u] q` for the residues coprime to the stride below half of it.
    let babies: Vec<PointXz> = (1..STAGE_TWO_STRIDE / 2)
        .filter(|u| gcd_u64(*u, STAGE_TWO_STRIDE) == 1)
        .map(|u| curve.multiply(q, u))
        .collect();

    let stride_point = curve.multiply(q, STAGE_TWO_STRIDE);
    // `v == 0` would make the chain's difference the identity, which a differential addition
    // cannot use.
    let first = (b1 / STAGE_TWO_STRIDE).max(1);
    let last = b2 / STAGE_TWO_STRIDE + 1;

    // Both ends of the chain are computed directly; from there each giant step is one addition,
    // because `[(v+1) D] q - [D] q` is the `[v D] q` already in hand.
    let mut current = curve.multiply(q, first * STAGE_TWO_STRIDE);
    let mut next = curve.multiply(q, (first + 1) * STAGE_TWO_STRIDE);

    let mut accumulator = BigUInt::one();
    for _v in first..=last {
        for baby in &babies {
            let difference = sub_mod(
                &mul_mod(&current.x, &baby.z, n),
                &mul_mod(&baby.x, &current.z, n),
                n,
            );
            // A difference of zero means the two `x`-coordinates agree modulo all of `n`, so its
            // gcd is `n` and it names no factor. Multiplying it in would erase what every other
            // pair found, so it is skipped rather than accumulated.
            if !difference.is_zero() {
                accumulator = mul_mod(&accumulator, &difference, n);
            }
        }
        let advanced = curve.add(&next, &stride_point, &current);
        current = next;
        next = advanced;
    }
    accumulator
}

#[cfg(test)]
mod tests {
    use super::{ecm_find_factor, factor_with_budget, EcmBudget};
    use crate::integers::{
        big_integers::big_uint::{BigUInt, ZERO},
        prime_factors::miller_rabin::is_prime,
    };
    use proptest::proptest;
    use rand::{prelude::StdRng, SeedableRng};

    fn big(value: u64) -> BigUInt {
        BigUInt::new_from_u64(value)
    }

    /// A budget small enough to keep the suite fast, sized for factors of a few digits.
    fn small_budget() -> EcmBudget {
        EcmBudget {
            b1: 200,
            b2: 20_000,
            curves: 40,
        }
    }

    /// Asserts `factor` is a divisor of `n` strictly between one and `n`.
    fn assert_non_trivial_divisor(factor: &BigUInt, n: &BigUInt) {
        assert!(*factor > BigUInt::one(), "factor {factor} is trivial");
        assert!(factor < n, "factor {factor} is not proper");
        assert_eq!(n % factor, *ZERO, "{factor} does not divide {n}");
    }

    /// A semiprime with two factors of similar size is split into a genuine non-trivial divisor.
    #[test]
    fn test_ecm_splits_a_balanced_semiprime() {
        let mut rng = StdRng::seed_from_u64(20260131);
        // 10_007 * 10_009, both prime and above the small-prime table's reach for this budget.
        let n = big(10_007) * &big(10_009);
        let factor = ecm_find_factor(&n, &small_budget(), &mut rng).expect("a factor");
        assert_non_trivial_divisor(&factor, &n);
    }

    /// A prime input reports no factor and terminates, rather than searching forever.
    #[test]
    fn test_ecm_reports_no_factor_for_a_prime() {
        let mut rng = StdRng::seed_from_u64(7);
        for prime in [big(1_000_003), big(2_147_483_647)] {
            assert_eq!(ecm_find_factor(&prime, &small_budget(), &mut rng), None);
        }
    }

    /// Inputs with no non-trivial divisor at all return `None` without touching curve arithmetic.
    #[test]
    fn test_ecm_rejects_inputs_below_four() {
        let mut rng = StdRng::seed_from_u64(1);
        for n in [0u64, 1, 2, 3] {
            assert_eq!(ecm_find_factor(&big(n), &small_budget(), &mut rng), None);
        }
    }

    /// An even input is split, because the curve constant's denominator carries a factor of 16 and
    /// so cannot be invertible modulo an even `n`.
    #[test]
    fn test_ecm_splits_an_even_input() {
        let mut rng = StdRng::seed_from_u64(5);
        for n in [big(1 << 20), big(2) * &big(1_000_003)] {
            let factor = ecm_find_factor(&n, &small_budget(), &mut rng).expect("a factor");
            assert_non_trivial_divisor(&factor, &n);
        }
    }

    /// Whatever a prime power or a tiny input returns is a real divisor; ECM is not obliged to
    /// find one, and modulo four the curve constant's denominator is always zero.
    #[test]
    fn test_ecm_returns_only_real_divisors_for_prime_powers_and_tiny_inputs() {
        let mut rng = StdRng::seed_from_u64(11);
        for n in [big(4), big(8), big(9), big(1_000_003).pow(&big(2))] {
            if let Some(factor) = ecm_find_factor(&n, &small_budget(), &mut rng) {
                assert_non_trivial_divisor(&factor, &n);
            }
        }
    }

    /// One curve is not enough for this input and seed, while sixty are: the curve-change path is
    /// what turns the first curve's failure into a success. Both runs share a seed, so the failing
    /// first curve is the same one in each.
    #[test]
    fn test_ecm_retries_on_a_new_curve_after_a_failure() {
        let n = big(10_007) * &big(10_009);
        let one_curve = EcmBudget {
            b1: 200,
            b2: 0,
            curves: 1,
        };
        let mut rng = StdRng::seed_from_u64(1);
        assert_eq!(ecm_find_factor(&n, &one_curve, &mut rng), None);

        let many_curves = EcmBudget {
            curves: 60,
            ..one_curve
        };
        let mut rng = StdRng::seed_from_u64(1);
        let factor = ecm_find_factor(&n, &many_curves, &mut rng).expect("a factor");
        assert_non_trivial_divisor(&factor, &n);
    }

    /// Stage 2 finds a factor that stage 1 alone misses: on this curve the order needs one prime
    /// above the stage-1 bound. Both runs share a seed and a curve count, so stage 2 is the only
    /// difference between them.
    #[test]
    fn test_stage_two_extends_the_reach_of_stage_one() {
        let n = big(10_007) * &big(10_009);
        let stage_one_only = EcmBudget {
            b1: 30,
            b2: 0,
            curves: 1,
        };
        let mut rng = StdRng::seed_from_u64(34);
        assert_eq!(ecm_find_factor(&n, &stage_one_only, &mut rng), None);

        let with_stage_two = EcmBudget {
            b2: 20_000,
            ..stage_one_only
        };
        let mut rng = StdRng::seed_from_u64(34);
        let factor = ecm_find_factor(&n, &with_stage_two, &mut rng).expect("a factor");
        assert_non_trivial_divisor(&factor, &n);
    }

    /// A zero budget finds nothing, which is the property that keeps an unbounded factorization
    /// something a caller opts into.
    #[test]
    fn test_a_zero_budget_finds_nothing() {
        let mut rng = StdRng::seed_from_u64(3);
        let budget = EcmBudget {
            b1: 200,
            b2: 20_000,
            curves: 0,
        };
        let n = big(10_007) * &big(10_009);
        assert_eq!(ecm_find_factor(&n, &budget, &mut rng), None);
    }

    /// The driver factors a number of small primes completely, in increasing order.
    #[test]
    fn test_factor_with_budget_on_small_primes() {
        let mut rng = StdRng::seed_from_u64(3883);
        let n = big(1_290_159_361_801_237); // 4409^3 * 15053
        let factorization = factor_with_budget(&n, &small_budget(), &mut rng);
        assert!(factorization.is_complete());
        assert_eq!(factorization.primes, vec![big(4409), big(15053)]);
        assert_eq!(factorization.powers, vec![3, 1]);
        assert_eq!(factorization.product(), n);
    }

    /// The driver splits a semiprime that trial division cannot reach, and reports it as prime.
    #[test]
    fn test_factor_with_budget_splits_a_semiprime() {
        let mut rng = StdRng::seed_from_u64(20260131);
        let n = big(10_007) * &big(10_009);
        let factorization = factor_with_budget(&n, &small_budget(), &mut rng);
        assert!(factorization.is_complete());
        assert_eq!(factorization.primes, vec![big(10_007), big(10_009)]);
        assert_eq!(factorization.powers, vec![1, 1]);
        assert_eq!(factorization.product(), n);
    }

    /// A prime power beyond trial division is resolved by the perfect-power test, not by ECM.
    #[test]
    fn test_factor_with_budget_on_a_prime_power() {
        let mut rng = StdRng::seed_from_u64(7);
        let p = big(1_000_003);
        let factorization = factor_with_budget(&p.pow(&big(4)), &small_budget(), &mut rng);
        assert!(factorization.is_complete());
        assert_eq!(factorization.primes, vec![p]);
        assert_eq!(factorization.powers, vec![4]);
    }

    /// A cofactor the budget cannot split is reported as unfactored rather than dropped, and the
    /// factorization still multiplies back out to the input.
    #[test]
    fn test_factor_with_budget_reports_an_unsplit_cofactor() {
        let mut rng = StdRng::seed_from_u64(13);
        let budget = EcmBudget {
            b1: 100,
            b2: 0,
            curves: 1,
        };
        // 2^2 * 3 times a semiprime of two distinct 19-digit primes, which this budget cannot
        // touch. A prime *power* would not do: the perfect-power test resolves that without ECM.
        let hard = BigUInt::from_dec_str("1000000000000000003").unwrap()
            * &BigUInt::from_dec_str("1000000000000000009").unwrap();
        let n = big(12) * &hard;
        let factorization = factor_with_budget(&n, &budget, &mut rng);
        assert!(!factorization.is_complete());
        assert_eq!(factorization.primes, vec![big(2), big(3)]);
        assert_eq!(factorization.powers, vec![2, 1]);
        assert_eq!(factorization.product(), n);
    }

    /// Zero and one are degenerate: one is the empty product, and zero has no factorization.
    #[test]
    fn test_factor_with_budget_on_zero_and_one() {
        let mut rng = StdRng::seed_from_u64(1);
        let one = factor_with_budget(&BigUInt::one(), &small_budget(), &mut rng);
        assert!(one.is_complete());
        assert!(one.primes.is_empty());
        assert_eq!(one.product(), BigUInt::one());

        let zero = factor_with_budget(&BigUInt::zero(), &small_budget(), &mut rng);
        assert!(!zero.is_complete());
        assert_eq!(zero.product(), BigUInt::zero());
    }

    /// Every prime reported really is prime, and the product is the input: the invariants that
    /// must hold whatever the probabilistic search happens to find.
    #[test]
    fn test_factor_with_budget_invariants_over_a_range() {
        let mut rng = StdRng::seed_from_u64(424242);
        for n in [
            big(2),
            big(4),
            big(97),
            big(10_403),        // 101 * 103
            big(100_000_007),   // prime
            big(1_522_605_027), // 3 * 139 * 151 * 24181
        ] {
            let factorization = factor_with_budget(&n, &small_budget(), &mut rng);
            assert_eq!(factorization.product(), n, "product mismatch for {n}");
            for prime in &factorization.primes {
                assert!(is_prime(prime, 20, &mut rng), "{prime} is not prime");
            }
            for (composite, _) in &factorization.unfactored {
                assert!(
                    !is_prime(composite, 20, &mut rng),
                    "{composite} was reported unfactored but is prime"
                );
            }
        }
    }

    /// The standard digit-level budgets are monotone in the digit count they target.
    #[test]
    fn test_for_digits_is_monotone() {
        let levels: Vec<EcmBudget> = [10, 15, 20, 25, 30, 35]
            .iter()
            .map(|d| EcmBudget::for_digits(*d))
            .collect();
        for pair in levels.windows(2) {
            assert!(pair[1].b1 >= pair[0].b1);
            assert!(pair[1].b2 >= pair[0].b2);
            assert!(pair[1].curves >= pair[0].curves);
        }
    }

    proptest! {
        #[test]
        /// Whatever `ecm_find_factor` returns for an arbitrary input is a proper non-trivial
        /// divisor of it. The search may find nothing; it may never be wrong.
        fn ecm_only_ever_returns_a_real_divisor(value in 0u64..200_000) {
            let n = BigUInt::new_from_u64(value);
            let budget = EcmBudget { b1: 50, b2: 0, curves: 2 };
            let mut rng = StdRng::seed_from_u64(value);
            if let Some(factor) = ecm_find_factor(&n, &budget, &mut rng) {
                assert!(factor > BigUInt::one(), "{factor} is trivial");
                assert!(factor < n, "{factor} is not a proper divisor of {n}");
                assert_eq!(&n % &factor, *ZERO, "{factor} does not divide {n}");
            }
        }

        #[test]
        /// A partial factorization always multiplies back out to its input, and never reports a
        /// composite among its primes — whatever the budget managed to split.
        fn factor_with_budget_accounts_for_every_factor(value in 1u64..200_000) {
            let n = BigUInt::new_from_u64(value);
            let budget = EcmBudget { b1: 50, b2: 0, curves: 2 };
            let mut rng = StdRng::seed_from_u64(value);
            let factorization = factor_with_budget(&n, &budget, &mut rng);
            assert_eq!(factorization.product(), n);
            assert_eq!(factorization.primes.len(), factorization.powers.len());
            for prime in &factorization.primes {
                assert!(is_prime(prime, 10, &mut rng), "{prime} is not prime");
            }
        }
    }

    /// The reason ECM is here: a semiprime of two 15-digit primes is factored completely, where
    /// Pollard rho would need about `p^(1/2)` — some `10^7` — iterations per factor.
    #[test]
    // A full digit-level budget is many curves of BigUInt arithmetic, which is slow enough in a
    // debug build to be a tax on the default suite. Release mode finishes it promptly.
    #[ignore]
    fn test_factors_a_semiprime_beyond_the_reach_of_pollard_rho() {
        let mut rng = StdRng::seed_from_u64(20260131);
        let p = BigUInt::from_dec_str("100000000000031").unwrap();
        let q = BigUInt::from_dec_str("100000000000067").unwrap();
        let factorization = factor_with_budget(&(&p * &q), &EcmBudget::for_digits(15), &mut rng);
        assert!(factorization.is_complete());
        assert_eq!(factorization.primes, vec![p.clone(), q.clone()]);
        assert_eq!(factorization.powers, vec![1, 1]);
        assert_eq!(factorization.product(), &p * &q);
    }
}
