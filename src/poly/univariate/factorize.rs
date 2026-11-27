//! Factoring a univariate polynomial over a finite field into irreducibles.
//!
//! For each d, the product of all monic irreducibles whose degree divides d is `x^(q^d) - x`, and
//! that product is squarefree. So `gcd(f, x^(q^d) - x)` is the product of the *distinct*
//! irreducible factors of f whose degree divides d — **whatever the multiplicities in f are**.
//!
//! That is what lets this skip squarefree decomposition altogether. The usual route computes
//! `gcd(f, f')` first, which needs separate handling in characteristic p when a multiplicity is
//! divisible by p, or when f' vanishes entirely as it does for `x^p`. None of that arises here:
//! multiplicities are recovered afterwards by dividing f by each irreducible factor.
//!
//! The distinct factors are collected degree by degree, then each group of equal-degree factors
//! is separated by Cantor–Zassenhaus splitting.
//!
//! Both stages apply the Frobenius map `p ↦ p^q` repeatedly. After `x^q` itself, that is a modular
//! composition with `x^q`, which beats `pow_mod` once enough applications follow to repay building
//! the composer; [`FrobeniusRoute::Auto`] decides when (`docs/research/modular-composition.md`).
//!
//! # References
//! * A Computational Introduction to Number Theory and Algebra, 20.3 and 21.3
//! * Modern Computer Algebra by von zur Gathen and Gerhard, Ch. 14

use rand::{CryptoRng, RngCore};

use crate::{
    integers::highest_set_bit,
    poly::univariate::{
        compose_mod, gcd, pow_mod, pow_mod::pow_mod_limbs, subproduct_tree::derivative,
        ModularComposer, Polynomial, UnivariatePolynomial,
    },
    FiniteField, KnownOrder,
};

/// `(q - 1) / 2`, as little-endian limbs.
///
/// The exponent equal-degree splitting raises to in odd characteristic. `q` is odd there, so
/// `q - 1` is even and the halving is exact — a shift, not a division.
///
/// # Panics
/// Panics in characteristic two, where `(q - 1) / 2` is not an integer and the splitter uses the
/// trace instead.
fn half_of_q_minus_one<F: KnownOrder>() -> Vec<u64> {
    let mut limbs = F::order_limbs().to_vec();
    assert_eq!(limbs[0] & 1, 1, "q must be odd for (q - 1) / 2 to be exact");
    limbs[0] -= 1;

    // One right shift across the limbs, high to low.
    let mut carry = 0u64;
    for limb in limbs.iter_mut().rev() {
        let next_carry = *limb & 1;
        *limb = (*limb >> 1) | (carry << 63);
        carry = next_carry;
    }
    limbs
}

/// `m` where `q = 2^m`, for a field of characteristic two.
///
/// The limb walk is defensive rather than exercised: every characteristic-two field in this crate
/// is a `BinaryFieldElement`, whose modulus is a `u64`, so `m <= 63` and the order occupies one
/// limb. A wider one would still be read correctly.
fn characteristic_two_degree<F: KnownOrder>() -> u32 {
    let limbs = F::order_limbs();
    let position = limbs
        .iter()
        .position(|&limb| limb != 0)
        .expect("a field order is at least two");
    position as u32 * 64 + limbs[position].trailing_zeros()
}

/// Each splitting attempt succeeds with probability near one half, so exhausting this many means
/// a defect rather than bad luck. Failing loudly beats looping forever.
pub(crate) const MAX_SPLIT_ATTEMPTS: usize = 1000;

/// The monic irreducible factors of `f` and their multiplicities, in unspecified order.
///
/// The product of the factors, each raised to its multiplicity, is `f` divided by its leading
/// coefficient. A constant has no factorization, so the result is empty.
///
/// # Panics
/// Panics if `f` is the zero polynomial, which has no factorization.
pub fn factorize<F: KnownOrder, R: RngCore + CryptoRng>(
    f: &UnivariatePolynomial<F>,
    rng: &mut R,
) -> Vec<(UnivariatePolynomial<F>, usize)> {
    factorize_with_routes(
        f,
        rng,
        FrobeniusRoute::default(),
        DistinctDegreeRoute::default(),
    )
}

/// How the Frobenius map `p ↦ p^q mod h` is applied after the first `x^q`.
///
/// Over F_q, `p(x)^q = p(x^q)`, so once `x^q mod h` is known every further application is a
/// modular composition with that fixed inner argument rather than `log2 q` squarings.
#[doc(hidden)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum FrobeniusRoute {
    /// `pow_mod` by `q` every time: `~1.5·log2 q` modular multiplications per application.
    PowMod,
    /// Brent–Kung composition with `x^q mod h` from the first application: `~sqrt(deg h)` modular
    /// multiplications and one dense matrix product per application, the baby steps growing as
    /// the applications accumulate.
    Composition,
    /// `pow_mod` until its accumulated cost reaches the cost of a composer that would beat it per
    /// application, then composition. Bounds the loss when only a few applications follow, which
    /// is where a narrow field at high degree would otherwise pay for a composer it never repays.
    #[default]
    Auto,
}

/// How `factorize` finds the degrees of the irreducible factors.
#[doc(hidden)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum DistinctDegreeRoute {
    /// One Frobenius application and one gcd per degree, until half the degree of what remains.
    Iterated,
    /// Shoup's baby-step/giant-step from degree one: `l ≈ sqrt(n/2)` baby steps `x^(q^i)`, then
    /// one gcd per interval of `l` degrees against `∏ (x^(q^(lj)) - x^(q^i))`. Squarefree inputs
    /// only; anything else takes the iterated route.
    BabyStepGiantStep,
    /// Iterated until the degree reaches `sqrt(deg r / 2)` for what remains `r`, then
    /// baby-step/giant-step with the powers already computed as its baby steps. The iterated
    /// phase is the rent: an input whose factors are all of low degree — the root-finding shape —
    /// finishes inside it and never pays for giant steps.
    #[default]
    Auto,
}

impl DistinctDegreeRoute {
    #[cfg(test)]
    pub(crate) const ALL: [Self; 3] = [Self::Iterated, Self::BabyStepGiantStep, Self::Auto];
}

/// [`factorize`] with the Frobenius route forced. Measurement and differential-testing hook.
#[doc(hidden)]
pub fn factorize_with_route<F: KnownOrder, R: RngCore + CryptoRng>(
    f: &UnivariatePolynomial<F>,
    rng: &mut R,
    route: FrobeniusRoute,
) -> Vec<(UnivariatePolynomial<F>, usize)> {
    factorize_with_routes(f, rng, route, DistinctDegreeRoute::default())
}

/// [`factorize`] with both routes forced. Measurement and differential-testing hook.
#[doc(hidden)]
pub fn factorize_with_routes<F: KnownOrder, R: RngCore + CryptoRng>(
    f: &UnivariatePolynomial<F>,
    rng: &mut R,
    route: FrobeniusRoute,
    distinct_degree: DistinctDegreeRoute,
) -> Vec<(UnivariatePolynomial<F>, usize)> {
    assert!(!f.is_zero(), "the zero polynomial has no factorization");

    if f.degree() == 0 {
        return Vec::new();
    }
    let monic = make_monic(f);
    if monic.degree() == 1 {
        return vec![(monic, 1)];
    }

    let x = variable::<F>();
    let x_to_the_q = pow_mod_limbs(&x, F::order_limbs(), &monic);
    let mut search = DegreeSearch {
        remaining: monic.clone(),
        factors: Vec::new(),
        split_route: SplitRoute {
            route,
            x_to_the_q: Some(&x_to_the_q),
        },
        squarefree_checked_at: None,
    };

    // `powers[d]` is x^(q^d) mod f. Kept only while they may become baby steps; x^(q^(d+1)) is
    // x^(q^d) under one more Frobenius application, since q^d would overflow as an exponent.
    let keep_powers = distinct_degree != DistinctDegreeRoute::Iterated;
    let max_baby_steps = ceil_sqrt(monic.degree() as usize / 2 + 1) + 1;
    let mut powers = vec![x.clone(), x_to_the_q.clone()];
    let mut frobenius = Frobenius::new(route, &x_to_the_q, &monic);

    if distinct_degree == DistinctDegreeRoute::BabyStepGiantStep && search.is_squarefree() {
        let baby_steps = ceil_sqrt(search.remaining.degree() as usize / 2).max(1);
        while powers.len() <= baby_steps {
            let next = frobenius.apply(powers.last().expect("x is always present"));
            powers.push(next);
        }
        search.baby_step_giant_step(&powers, &monic, 0, rng);
        return search.factors;
    }

    // Invariant at the top of each pass: no factor of degree d or less divides `remaining`.
    let mut x_to_the_q_to_the_d = x_to_the_q.clone();
    let mut d = 1u32;
    loop {
        // The distinct irreducible factors of what remains whose degree divides d are those of
        // degree exactly d, everything smaller having been divided out already.
        let exactly_d = gcd(&search.remaining, &(&x_to_the_q_to_the_d - &x));
        if exactly_d.degree() > 0 {
            search.take(&exactly_d, d, rng);
        }
        if search.finished(d) {
            return search.factors;
        }

        // The rent is paid once d reaches the baby-step count baby-step/giant-step would choose
        // for what remains: the powers so far are its baby steps, and x^(q^d) its giant stride.
        let wanted = ceil_sqrt(search.remaining.degree() as usize / 2);
        if distinct_degree == DistinctDegreeRoute::Auto
            && d as usize >= wanted
            && powers.len() == d as usize + 1
            && search.is_squarefree()
        {
            search.baby_step_giant_step(&powers, &monic, 1, rng);
            return search.factors;
        }

        x_to_the_q_to_the_d = frobenius.apply(&x_to_the_q_to_the_d);
        d += 1;
        if keep_powers && powers.len() == d as usize && powers.len() <= max_baby_steps {
            powers.push(x_to_the_q_to_the_d.clone());
        }
    }
}

/// The state of the distinct-degree stage: what is left of `f` and the factors taken from it.
struct DegreeSearch<'a, F: FiniteField> {
    /// `f` with every factor found so far divided out to its full multiplicity.
    remaining: UnivariatePolynomial<F>,
    factors: Vec<(UnivariatePolynomial<F>, usize)>,
    split_route: SplitRoute<'a, F>,
    /// The degree of `remaining` when it was last found not to be squarefree.
    squarefree_checked_at: Option<u32>,
}

impl<F: KnownOrder> DegreeSearch<'_, F> {
    /// Split `product`, a product of distinct irreducibles of degree `d` dividing `remaining`, and
    /// divide each factor out of `remaining` as often as it divides.
    fn take<R: RngCore + CryptoRng>(
        &mut self,
        product: &UnivariatePolynomial<F>,
        d: u32,
        rng: &mut R,
    ) {
        for irreducible in separate_equal_degree_by(product, d, rng, &self.split_route) {
            let mut multiplicity = 0;
            loop {
                let (quotient, remainder) = self.remaining.div_with_remainder(&irreducible);
                if !remainder.is_zero() {
                    break;
                }
                self.remaining = quotient;
                multiplicity += 1;
            }
            debug_assert!(multiplicity > 0, "{irreducible} does not divide f");
            self.factors.push((irreducible, multiplicity));
        }
    }

    /// True, and `remaining` recorded as a factor if it is not one, once no factor of degree `d` or
    /// less divides `remaining` and that settles the rest. A reducible `remaining` would have a
    /// factor of degree at most half its own, and every one of those is gone.
    fn finished(&mut self, d: u32) -> bool {
        let degree = self.remaining.degree();
        if degree == 0 {
            return true;
        }
        if degree < 2 * (d + 1) {
            let last = std::mem::replace(&mut self.remaining, UnivariatePolynomial::one());
            self.factors.push((last, 1));
            return true;
        }
        false
    }

    /// True if `remaining` is squarefree, by `gcd(r, r') = 1`. A vanishing derivative — a p-th
    /// power — gives `gcd(r, 0) = r`, so is not squarefree, as it should not be.
    fn is_squarefree(&mut self) -> bool {
        let degree = self.remaining.degree();
        if self.squarefree_checked_at == Some(degree) {
            return false;
        }
        let squarefree = gcd(&self.remaining, &derivative(&self.remaining)).degree() == 0;
        if !squarefree {
            self.squarefree_checked_at = Some(degree);
        }
        squarefree
    }

    /// Shoup's interval distinct-degree factorization of a squarefree `remaining`.
    ///
    /// `powers` holds `x^(q^i) mod f` for `i = 0..=l`. Interval `j` covers the degrees
    /// `l·j + 1 ..= l·(j + 1)`: with `H = x^(q^(l(j+1)))`, an irreducible of degree `e` divides
    /// `H - x^(q^i)` exactly when `e` divides `l(j+1) - i`, so one gcd against
    /// `∏_{i<l} (H - x^(q^i))` collects every factor in the interval, and a gcd per `i`, ascending
    /// in degree, separates them. Factors of degree `l·first_interval` or less must already be
    /// gone from `remaining`.
    fn baby_step_giant_step<R: RngCore + CryptoRng>(
        &mut self,
        powers: &[UnivariatePolynomial<F>],
        f: &UnivariatePolynomial<F>,
        first_interval: u32,
        rng: &mut R,
    ) {
        debug_assert!(self.is_squarefree());
        let l = powers.len() - 1;
        let stride = l as u32;
        // x^(q^(l(j+1))) = x^(q^(lj)) ∘ x^(q^l) mod f: one composition per interval, always with
        // the same inner argument, which is the case `Frobenius`'s composer is for. `pow_mod` by
        // q^l is never the cheaper route.
        let mut giant = Frobenius::new(FrobeniusRoute::Composition, &powers[l], f);
        let mut stride_power = powers[l].clone();
        for _ in 0..first_interval {
            stride_power = giant.apply(&stride_power);
        }

        let mut baby_steps: Vec<UnivariatePolynomial<F>> = Vec::new();
        let mut reduced_for = None;
        let mut j = first_interval;
        loop {
            if self.finished(stride * j) {
                return;
            }
            if j > first_interval {
                stride_power = giant.apply(&stride_power);
            }
            let degree = self.remaining.degree();
            if reduced_for != Some(degree) {
                baby_steps = powers[..l].iter().map(|p| p % &self.remaining).collect();
                reduced_for = Some(degree);
            }
            let h = &stride_power % &self.remaining;

            let mut interval = UnivariatePolynomial::one();
            for baby in &baby_steps {
                interval = &(&interval * &(&h - baby)) % &self.remaining;
            }
            let mut in_interval = gcd(&self.remaining, &interval);
            for i in (0..l).rev() {
                if in_interval.degree() == 0 {
                    break;
                }
                let exactly = gcd(&in_interval, &(&h - &baby_steps[i]));
                if exactly.degree() > 0 {
                    in_interval = &in_interval / &exactly;
                    self.take(&exactly, stride * (j + 1) - i as u32, rng);
                }
            }

            j += 1;
        }
    }
}

/// How `is_irreducible` reaches the Frobenius powers Rabin's test needs.
#[doc(hidden)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum IrreducibilityRoute {
    /// `x^(q^k)` for k = 1, 2, … in one pass, one Frobenius application each by the given route,
    /// reading off `x^(q^(n/p))` on the way to `x^(q^n)`.
    Iterate(FrobeniusRoute),
    /// `x^(q^k)` by an addition chain on k: `x^(q^(2a)) = x^(q^a) ∘ x^(q^a)`, one one-shot
    /// composition per doubling, and `x^(q^(a+1))` by one Frobenius application. About
    /// `2·log2 n` compositions per power instead of n applications.
    #[default]
    Doubling,
}

impl IrreducibilityRoute {
    #[cfg(test)]
    pub(crate) const ALL: [Self; 4] = [
        Self::Iterate(FrobeniusRoute::PowMod),
        Self::Iterate(FrobeniusRoute::Composition),
        Self::Iterate(FrobeniusRoute::Auto),
        Self::Doubling,
    ];
}

/// True if `f` is irreducible over F.
///
/// Rabin's test: a monic polynomial of degree n is irreducible exactly when `x^(q^n) = x` in
/// F\[x\]/(f) and `gcd(x^(q^(n/p)) - x, f) = 1` for every prime p dividing n. The first condition
/// says every irreducible factor has degree dividing n; the second rules out a proper divisor.
///
/// # Panics
/// Panics if `f` is the zero polynomial.
pub fn is_irreducible<F: KnownOrder>(f: &UnivariatePolynomial<F>) -> bool {
    is_irreducible_with_route(f, IrreducibilityRoute::default())
}

/// [`is_irreducible`] with the route forced. Measurement and differential-testing hook.
#[doc(hidden)]
pub fn is_irreducible_with_route<F: KnownOrder>(
    f: &UnivariatePolynomial<F>,
    route: IrreducibilityRoute,
) -> bool {
    assert!(!f.is_zero(), "the zero polynomial is not irreducible");

    let n = f.degree();
    // A constant is a unit, not an irreducible. Degree one is always irreducible.
    if n == 0 {
        return false;
    }
    if n == 1 {
        return true;
    }

    let monic = make_monic(f);
    let x = variable::<F>();
    let x_to_the_q = pow_mod_limbs(&x, F::order_limbs(), &monic);
    let divisors = prime_divisors(n);
    let shows_a_proper_factor = |x_to_the_q_to_the_k: &UnivariatePolynomial<F>| -> bool {
        gcd(&monic, &(x_to_the_q_to_the_k - &x)).degree() > 0
    };

    match route {
        IrreducibilityRoute::Iterate(route) => {
            let mut frobenius = Frobenius::new(route, &x_to_the_q, &monic);
            let mut power = x_to_the_q.clone();
            for k in 1..n {
                if divisors.iter().any(|p| n / p == k) && shows_a_proper_factor(&power) {
                    return false;
                }
                power = frobenius.apply(&power);
            }
            power == x
        }
        IrreducibilityRoute::Doubling => {
            let mut frobenius = Frobenius::new(FrobeniusRoute::Auto, &x_to_the_q, &monic);
            // Most reducible inputs fail the cheaper-to-state test first.
            if frobenius_power(n, &x_to_the_q, &monic, &mut frobenius) != x {
                return false;
            }
            divisors.iter().all(|p| {
                !shows_a_proper_factor(&frobenius_power(n / p, &x_to_the_q, &monic, &mut frobenius))
            })
        }
    }
}

/// `x^(q^k) mod f` for `k >= 1`, left to right over the bits of k: doubling the exponent of q is a
/// composition of the power so far with itself, and adding one is a Frobenius application.
fn frobenius_power<F: KnownOrder>(
    k: u32,
    x_to_the_q: &UnivariatePolynomial<F>,
    f: &UnivariatePolynomial<F>,
    frobenius: &mut Frobenius<F>,
) -> UnivariatePolynomial<F> {
    debug_assert!(k >= 1);
    let mut power = x_to_the_q.clone();
    for bit in (0..31 - k.leading_zeros()).rev() {
        power = compose_mod(&power, &power, f);
        if (k >> bit) & 1 == 1 {
            power = frobenius.apply(&power);
        }
    }
    power
}

/// Separate a product of distinct monic irreducibles, each of degree `d`, into those factors.
pub(crate) fn separate_equal_degree<F: KnownOrder, R: RngCore + CryptoRng>(
    g: &UnivariatePolynomial<F>,
    d: u32,
    rng: &mut R,
) -> Vec<UnivariatePolynomial<F>> {
    separate_equal_degree_by(g, d, rng, &SplitRoute::default())
}

/// The Frobenius route for equal-degree splitting, with `x^q` modulo some multiple of every `g`
/// it will be asked to split, when the route needs it.
#[derive(Default)]
struct SplitRoute<'a, F: FiniteField> {
    route: FrobeniusRoute,
    x_to_the_q: Option<&'a UnivariatePolynomial<F>>,
}

fn separate_equal_degree_by<F: KnownOrder, R: RngCore + CryptoRng>(
    g: &UnivariatePolynomial<F>,
    d: u32,
    rng: &mut R,
    route: &SplitRoute<'_, F>,
) -> Vec<UnivariatePolynomial<F>> {
    // One factor of degree d means g is already that factor.
    if g.degree() == d {
        return vec![g.clone()];
    }

    let (left, right) = split(g, d, rng, route);
    let mut factors = separate_equal_degree_by(&left, d, rng, route);
    factors.extend(separate_equal_degree_by(&right, d, rng, route));
    factors
}

/// Split a product of two or more distinct monic irreducibles of degree `d` into two parts.
fn split<F: KnownOrder, R: RngCore + CryptoRng>(
    g: &UnivariatePolynomial<F>,
    d: u32,
    rng: &mut R,
    route: &SplitRoute<'_, F>,
) -> (UnivariatePolynomial<F>, UnivariatePolynomial<F>) {
    let (parts, _) = try_split(g, d, rng, route, MAX_SPLIT_ATTEMPTS);
    parts.unwrap_or_else(|| {
        panic!(
            "failed to split {} in {} attempts; it may not be a product of distinct irreducibles \
             of degree {}",
            g, MAX_SPLIT_ATTEMPTS, d
        )
    })
}

/// The two parts of a split, if one was found, and the attempts spent either way.
pub(crate) type SplitAttempt<F> = (
    Option<(UnivariatePolynomial<F>, UnivariatePolynomial<F>)>,
    usize,
);

/// Split a squarefree product of two or more distinct monic linear factors into two parts, in at
/// most `max_attempts` random tries.
///
/// The fallible form of the degree-one split, for a caller that must report exhaustion rather than
/// panic.
pub(crate) fn try_split_linear<F: KnownOrder, R: RngCore + CryptoRng>(
    g: &UnivariatePolynomial<F>,
    rng: &mut R,
    max_attempts: usize,
) -> SplitAttempt<F> {
    try_split(g, 1, rng, &SplitRoute::default(), max_attempts)
}

fn try_split<F: KnownOrder, R: RngCore + CryptoRng>(
    g: &UnivariatePolynomial<F>,
    d: u32,
    rng: &mut R,
    route: &SplitRoute<'_, F>,
    max_attempts: usize,
) -> SplitAttempt<F> {
    debug_assert!(g.degree() > d);

    // Only the norm of a degree d > 1 split applies the Frobenius map, so only then is a composer
    // worth building. g divides the polynomial `x_to_the_q` was reduced by, so reducing it again
    // modulo g gives x^q mod g without a fresh exponentiation.
    let odd_characteristic = F::characteristic_limbs() != [2];
    let mut frobenius = match route.x_to_the_q {
        Some(x_to_the_q) if odd_characteristic && d > 1 => {
            Frobenius::new(route.route, &(x_to_the_q % g), g)
        }
        _ => Frobenius::new(FrobeniusRoute::PowMod, g, g),
    };

    for attempt in 0..max_attempts {
        let h = random_element_of_quotient(g, rng);

        // Each irreducible factor of g independently either divides the candidate or does not,
        // so the gcd is a proper factor unless every factor falls on the same side.
        let candidate = if F::characteristic_limbs() == [2] {
            // The role of "half the elements" falls to the trace onto GF(2), there being no
            // (q^d - 1)/2 in characteristic two. The extension F[x]/(factor) has 2^(m*d)
            // elements, so the trace has m*d terms.
            trace_to_gf2(&h, g, d)
        } else {
            // The target is h^((q^d - 1)/2). Writing (q^d - 1)/2 as
            // ((q - 1)/2) * (1 + q + ... + q^(d-1)) turns it into the norm raised to (q - 1)/2,
            // both of which are computable: the exponent itself would overflow.
            &pow_mod_limbs(
                &frobenius_norm(&h, g, d, &mut frobenius),
                &half_of_q_minus_one::<F>(),
                g,
            ) - &UnivariatePolynomial::one()
        };

        // Correctness rests on this check, not on the candidate: any proper divisor of g is a
        // valid split. An error in the trace or the exponent costs attempts rather than giving a
        // wrong answer.
        let divisor = gcd(g, &candidate);
        if !divisor.is_zero() && divisor.degree() > 0 && divisor.degree() < g.degree() {
            let quotient = g / &divisor;
            return (Some((divisor, quotient)), attempt + 1);
        }
    }

    (None, max_attempts)
}

/// The norm `h * h^q * h^(q^2) * ... * h^(q^(d-1))` in F[x]/(g).
fn frobenius_norm<F: KnownOrder>(
    h: &UnivariatePolynomial<F>,
    g: &UnivariatePolynomial<F>,
    d: u32,
    frobenius: &mut Frobenius<F>,
) -> UnivariatePolynomial<F> {
    let mut term = h % g;
    let mut norm = term.clone();
    for _ in 1..d {
        term = frobenius.apply(&term);
        norm = &(&norm * &term) % g;
    }
    norm
}

/// `p ↦ p^q mod h` for one fixed `h`, by the chosen route — or, with `inner = x^(q^l) mod h` and
/// the `Composition` route, `p ↦ p^(q^l)`.
struct Frobenius<F: FiniteField> {
    route: FrobeniusRoute,
    modulus: UnivariatePolynomial<F>,
    inner: UnivariatePolynomial<F>,
    /// Built on first need, so a loop that stops before applying the map pays nothing for it.
    composer: Option<ModularComposer<F>>,
    uses: usize,
}

/// The composer's baby-step table is not grown past this many bytes.
const MAX_BABY_STEP_BYTES: usize = 64 << 20;

impl<F: KnownOrder> Frobenius<F> {
    fn new(
        route: FrobeniusRoute,
        inner: &UnivariatePolynomial<F>,
        modulus: &UnivariatePolynomial<F>,
    ) -> Self {
        Self {
            route,
            modulus: modulus.clone(),
            inner: inner.clone(),
            composer: None,
            uses: 0,
        }
    }

    fn apply(&mut self, p: &UnivariatePolynomial<F>) -> UnivariatePolynomial<F> {
        let n = self.modulus.degree() as usize;
        let uses = self.uses;
        self.uses += 1;

        if self.composer.is_none() {
            let block = match self.route {
                FrobeniusRoute::PowMod => None,
                FrobeniusRoute::Composition => Some(block_cap::<F>(n, ceil_sqrt(n))),
                FrobeniusRoute::Auto => {
                    // Every unit below is one modular multiplication. A composer with m baby steps
                    // costs m to build and about n/m per application, against `pow_cost` per
                    // application by `pow_mod`; sized so that n/m is at most half of `pow_cost`,
                    // it wins per application. Renting (`pow_mod`) until the rent paid, this
                    // application's included, would reach the purchase price, then buying, costs
                    // at most about twice whichever would have been cheaper in hindsight. A
                    // composer cheaper than one `pow_mod` — every wide field — is bought at once.
                    let pow_cost = square_and_multiply_cost(F::order_limbs());
                    let block = block_cap::<F>(n, ceil_sqrt(n).max((2 * n).div_ceil(pow_cost)));
                    ((uses + 1) * pow_cost >= block).then_some(block)
                }
            };
            match block {
                Some(block) => {
                    self.composer = Some(ModularComposer::with_block(
                        &self.inner,
                        &self.modulus,
                        block,
                    ))
                }
                None => return pow_mod_limbs(p, F::order_limbs(), &self.modulus),
            }
        }

        let composer = self.composer.as_mut().expect("built above");
        // With m baby steps a composition pays about n/m modular multiplications, and doubling m
        // costs m of them once and saves n/(2m) per use thereafter. Taking the uses so far as the
        // forecast of the uses to come, doubling pays once they reach 2m²/n. The number of uses is
        // not known up front — the distinct-degree loop stops as soon as the factor degrees add up
        // — hence growing rather than sizing.
        let m = composer.block();
        if 2 * m <= block_cap::<F>(n, 2 * m) && uses * n >= 2 * m * m {
            composer.grow_to(2 * m);
        }
        composer.compose(p)
    }
}

/// `block` baby steps, but no more than `n` of them and none past `MAX_BABY_STEP_BYTES`.
fn block_cap<F>(n: usize, block: usize) -> usize {
    let by_memory = MAX_BABY_STEP_BYTES / (n.max(1) * std::mem::size_of::<F>()).max(1);
    block.min(n).min(by_memory).max(1)
}

fn ceil_sqrt(n: usize) -> usize {
    let mut m = (n as f64).sqrt() as usize;
    while m * m < n {
        m += 1;
    }
    m
}

/// Modular multiplications `pow_mod` spends on the exponent `limbs`: one squaring per bit after
/// the first, one multiplication per set bit after the first.
fn square_and_multiply_cost(limbs: &[u64]) -> usize {
    let bits = highest_set_bit(limbs).map_or(0, |b| b + 1);
    let ones: usize = limbs.iter().map(|l| l.count_ones() as usize).sum();
    (bits + ones).saturating_sub(2).max(1)
}

/// The absolute trace `h + h^2 + h^4 + ... + h^(2^(m*d - 1))` in F[x]/(g), for q = 2^m.
pub(crate) fn trace_to_gf2<F: KnownOrder>(
    h: &UnivariatePolynomial<F>,
    g: &UnivariatePolynomial<F>,
    d: u32,
) -> UnivariatePolynomial<F> {
    // q = 2^m, so m is the position of its single set bit.
    let m = characteristic_two_degree::<F>();
    let mut term = h % g;
    let mut sum = term.clone();
    for _ in 1..(m * d) {
        term = pow_mod(&term, 2, g);
        sum = &sum + &term;
    }
    &sum % g
}

/// A uniformly random element of F[x]/(g), i.e. a polynomial of degree below `g`.
pub(crate) fn random_element_of_quotient<F: FiniteField, R: RngCore + CryptoRng>(
    g: &UnivariatePolynomial<F>,
    rng: &mut R,
) -> UnivariatePolynomial<F> {
    let coefficients: Vec<F> = (0..g.degree()).map(|_| F::random(rng)).collect();
    UnivariatePolynomial::new(&coefficients)
}

/// `p` scaled so that its leading coefficient is one.
pub(crate) fn make_monic<F: FiniteField>(p: &UnivariatePolynomial<F>) -> UnivariatePolynomial<F> {
    let leading = *p
        .coefficients()
        .last()
        .expect("a polynomial has at least one coefficient");
    p.scale(&leading.inverse())
}

/// The polynomial `x`.
pub(crate) fn variable<F: FiniteField>() -> UnivariatePolynomial<F> {
    UnivariatePolynomial::new(&[F::zero(), F::one()])
}

/// The distinct primes dividing `n`.
fn prime_divisors(mut n: u32) -> Vec<u32> {
    let mut divisors = Vec::new();
    let mut d = 2;
    while d * d <= n {
        if n.is_multiple_of(d) {
            divisors.push(d);
            while n.is_multiple_of(d) {
                n /= d;
            }
        }
        d += 1;
    }
    if n > 1 {
        divisors.push(n);
    }
    divisors
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use rand::{prelude::StdRng, SeedableRng};

    use crate::{
        fields::PrimeFieldElement64,
        identities::Zero,
        poly::univariate::{
            factorize::{
                characteristic_two_degree, factorize, half_of_q_minus_one, is_irreducible,
            },
            roots, Polynomial, UnivariatePolynomial,
        },
        FiniteField,
    };

    fn poly<const P: u64>(coefficients: &[u64]) -> UnivariatePolynomial<PrimeFieldElement64<P>> {
        UnivariatePolynomial::new(
            &coefficients
                .iter()
                .map(|c| PrimeFieldElement64::<P>::new(*c))
                .collect::<Vec<_>>(),
        )
    }

    /// Every monic polynomial of degree `n` over GF(P).
    fn monic_polynomials<const P: u64>(
        n: u32,
    ) -> Vec<UnivariatePolynomial<PrimeFieldElement64<P>>> {
        let mut result = Vec::new();
        let count = P.pow(n);
        for index in 0..count {
            let mut coefficients: Vec<u64> = (0..n).map(|i| index / P.pow(i) % P).collect();
            coefficients.push(1);
            result.push(poly::<P>(&coefficients));
        }
        result
    }

    /// True if no monic polynomial of degree 1..=n/2 divides `f`.
    ///
    /// The definition of irreducibility, applied directly. Shares nothing with Rabin's test: no
    /// modular exponentiation, no gcd.
    fn irreducible_by_trial_division<const P: u64>(
        f: &UnivariatePolynomial<PrimeFieldElement64<P>>,
    ) -> bool {
        let n = f.degree();
        if n == 0 {
            return false;
        }
        for d in 1..=n / 2 {
            for divisor in monic_polynomials::<P>(d) {
                if (f % &divisor).is_zero() {
                    return false;
                }
            }
        }
        true
    }

    /// `is_irreducible` agrees with trial division on every monic polynomial of low degree.
    #[test]
    fn test_is_irreducible_agrees_with_trial_division() {
        fn check<const P: u64>(max_degree: u32) {
            for n in 1..=max_degree {
                for f in monic_polynomials::<P>(n) {
                    assert_eq!(
                        is_irreducible(&f),
                        irreducible_by_trial_division::<P>(&f),
                        "{} over GF({})",
                        f,
                        P
                    );
                }
            }
        }
        check::<2>(6);
        check::<3>(4);
        check::<5>(3);
        check::<7>(3);
    }

    /// A constant is a unit rather than an irreducible.
    #[test]
    fn test_constants_are_not_irreducible() {
        for c in 1..7u64 {
            assert!(!is_irreducible(&poly::<7>(&[c])));
        }
    }

    /// The factors multiply back to the polynomial, and each one is irreducible.
    ///
    /// Taken together these are a complete check rather than a sample: factorization over a field
    /// is unique up to units, so a product of irreducibles that reconstructs f *is* the
    /// factorization.
    #[test]
    fn test_factorize_reconstructs_the_polynomial() {
        fn check<const P: u64>(seed: u64) {
            let mut rng = StdRng::seed_from_u64(seed);
            for n in 1..=5u32 {
                for f in monic_polynomials::<P>(n) {
                    let factors = factorize(&f, &mut rng);
                    assert!(!factors.is_empty(), "{} has no factors", f);

                    let product = factors.iter().fold(
                        UnivariatePolynomial::<PrimeFieldElement64<P>>::one(),
                        |acc, (factor, multiplicity)| acc * factor.pow(*multiplicity as u32),
                    );
                    assert_eq!(product, f, "factors of {} do not multiply back", f);

                    for (factor, multiplicity) in &factors {
                        assert!(is_irreducible(factor), "{} is not irreducible", factor);
                        assert!(*multiplicity >= 1);
                    }
                }
            }
        }
        check::<2>(1);
        check::<3>(2);
        check::<5>(3);
    }

    /// Factors built by hand are recovered exactly, multiplicities included.
    #[test]
    fn test_factorize_recovers_known_factors() {
        const P: u64 = 7;
        let mut rng = StdRng::seed_from_u64(11);

        // x, x + 1, and x^2 + 1 — the last irreducible over GF(7), as asserted below.
        let a = poly::<P>(&[0, 1]);
        let b = poly::<P>(&[1, 1]);
        let c = poly::<P>(&[1, 0, 1]);
        assert!(is_irreducible(&c));

        let expected = [(a.clone(), 3usize), (b.clone(), 1), (c.clone(), 2)];
        let f = a.pow(3) * b.pow(1) * c.pow(2);

        let mut found = factorize(&f, &mut rng);
        found.sort_by_key(|(factor, _)| factor.degree());
        let found: HashSet<(Vec<u64>, usize)> = found
            .into_iter()
            .map(|(factor, m)| (factor.coefficients().iter().map(|c| c.value()).collect(), m))
            .collect();
        let expected: HashSet<(Vec<u64>, usize)> = expected
            .into_iter()
            .map(|(factor, m)| (factor.coefficients().iter().map(|c| c.value()).collect(), m))
            .collect();
        assert_eq!(found, expected);
    }

    /// A pure p-th power in characteristic p, where the derivative vanishes.
    ///
    /// The usual route to factorization starts from `gcd(f, f')`, which gives no information
    /// here: the derivative of x^5 over GF(5) is 5x^4 = 0. Collecting factors by
    /// `gcd(f, x^(q^d) - x)` instead sidesteps that entirely.
    #[test]
    fn test_factorize_a_pure_power_in_characteristic_p() {
        const P: u64 = 5;
        let mut rng = StdRng::seed_from_u64(13);

        // x^5, whose derivative is zero.
        let x = poly::<P>(&[0, 1]);
        assert_eq!(factorize(&x.pow(5), &mut rng), vec![(x.clone(), 5)]);

        // (x + 1)^5, likewise, with a multiplicity divisible by the characteristic.
        let shifted = poly::<P>(&[1, 1]);
        assert_eq!(
            factorize(&shifted.pow(5), &mut rng),
            vec![(shifted.clone(), 5)]
        );

        // And a mixture of a p-th power with another factor.
        let f = x.pow(5) * shifted.pow(2);
        let mut found = factorize(&f, &mut rng);
        found.sort_by_key(|(factor, _)| factor.coefficients()[0].value());
        assert_eq!(found, vec![(x, 5), (shifted, 2)]);
    }

    /// x^q - x splits into every linear factor exactly once.
    #[test]
    fn test_factorize_x_to_the_q_minus_x() {
        const P: u64 = 11;
        let mut rng = StdRng::seed_from_u64(17);
        let mut coefficients = vec![0u64; 12];
        coefficients[11] = 1;
        coefficients[1] = P - 1;
        let f = poly::<P>(&coefficients);

        let factors = factorize(&f, &mut rng);
        assert_eq!(factors.len(), P as usize);
        for (factor, multiplicity) in &factors {
            assert_eq!(factor.degree(), 1);
            assert_eq!(*multiplicity, 1);
        }
    }

    /// An irreducible polynomial factors into itself.
    #[test]
    fn test_factorize_an_irreducible_polynomial() {
        const P: u64 = 7;
        let mut rng = StdRng::seed_from_u64(19);
        let f = poly::<P>(&[1, 0, 1]); // x^2 + 1, irreducible over GF(7)
        assert!(is_irreducible(&f));
        assert_eq!(factorize(&f, &mut rng), vec![(f.clone(), 1)]);
    }

    /// The degree-one factors are exactly the roots.
    #[test]
    fn test_linear_factors_match_the_roots() {
        const P: u64 = 13;
        let mut rng = StdRng::seed_from_u64(23);
        let candidates: Vec<Vec<u64>> = vec![
            vec![P - 1, 0, 1],
            vec![0, 0, 1],
            vec![1, 2, 3, 4],
            vec![P - 1, 0, 0, 1],
            vec![1, 1, 1, 1, 1],
            vec![1, 0, 1],
        ];
        for coefficients in &candidates {
            let f = poly::<P>(coefficients);
            let from_factors: HashSet<_> = factorize(&f, &mut rng)
                .into_iter()
                .filter(|(factor, _)| factor.degree() == 1)
                // monic x - a, so the root is -c_0
                .map(|(factor, _)| PrimeFieldElement64::<P>::zero() - factor.coefficients()[0])
                .collect();
            let from_roots: HashSet<_> = roots(&f, &mut rng).into_iter().collect();
            assert_eq!(from_factors, from_roots, "{:?}", coefficients);
        }
    }

    /// A nonzero constant has no factorization, and zero is rejected.
    #[test]
    fn test_factorize_edge_cases() {
        let mut rng = StdRng::seed_from_u64(29);
        assert!(factorize(&poly::<7>(&[3]), &mut rng).is_empty());
    }

    #[test]
    #[should_panic(expected = "zero polynomial has no factorization")]
    fn test_factorize_zero_panics() {
        let mut rng = StdRng::seed_from_u64(31);
        let _ = factorize(
            &UnivariatePolynomial::<PrimeFieldElement64<7>>::zero(),
            &mut rng,
        );
    }

    /// `(q - 1) / 2` is right for a one-limb order, where it is checkable by hand.
    #[test]
    fn test_half_of_q_minus_one_on_a_narrow_order() {
        assert_eq!(half_of_q_minus_one::<PrimeFieldElement64<7>>(), vec![3]);
        assert_eq!(half_of_q_minus_one::<PrimeFieldElement64<13>>(), vec![6]);
        assert_eq!(
            half_of_q_minus_one::<PrimeFieldElement64<2147483647>>(),
            vec![1073741823]
        );
    }

    /// `(q - 1) / 2` shifts across the limb boundary rather than within one limb.
    ///
    /// For BN254, `(p - 1) / 2` has a low limb that can only be right if the bit carried down
    /// from the second limb was shifted in.
    #[test]
    fn test_half_of_q_minus_one_shifts_across_limbs() {
        use crate::fields::{Bn254Fr, Bn254FrModulus, PrimeModulus256};

        let halved = half_of_q_minus_one::<Bn254Fr>();

        // Reconstruct 2 * halved + 1 and check it is the modulus.
        let mut doubled = [0u64; 4];
        let mut carry = 0u64;
        for (i, limb) in halved.iter().enumerate() {
            doubled[i] = (limb << 1) | carry;
            carry = limb >> 63;
        }
        assert_eq!(carry, 0, "(p - 1) / 2 must double without overflow");
        doubled[0] |= 1;
        assert_eq!(doubled, Bn254FrModulus::MODULUS);
    }

    /// `(q - 1) / 2` refuses an even order, where the halving would not be exact.
    #[test]
    #[should_panic(expected = "q must be odd")]
    fn test_half_of_q_minus_one_rejects_characteristic_two() {
        let _ = half_of_q_minus_one::<PrimeFieldElement64<2>>();
    }

    /// `m` is recovered from `q = 2^m`.
    ///
    /// GF(2) is the only characteristic-two field reachable from here — `BinaryFieldElement` and
    /// `ExtensionFieldElement` are both crate-private to `fields` — so the cross-limb arithmetic
    /// is covered by `half_of_q_minus_one`'s test instead. See the function's own note on why it
    /// cannot arise for a characteristic-two field in this crate anyway.
    #[test]
    fn test_characteristic_two_degree_reads_the_single_set_bit() {
        assert_eq!(characteristic_two_degree::<PrimeFieldElement64<2>>(), 1);
    }

    /// The square-and-multiply cost counts squarings after the top bit and multiplications after
    /// the first set bit.
    #[test]
    fn test_square_and_multiply_cost() {
        use crate::poly::univariate::factorize::square_and_multiply_cost;
        assert_eq!(square_and_multiply_cost(&[7]), 4);
        assert_eq!(square_and_multiply_cost(&[8]), 3);
        assert_eq!(square_and_multiply_cost(&[1]), 1);
        // 2^64 + 1: 64 squarings and one multiplication.
        assert_eq!(square_and_multiply_cost(&[1, 1]), 65);
    }

    /// The composition and automatic Frobenius routes return the same factorization as `pow_mod`.
    #[test]
    fn test_composition_route_agrees_with_pow_mod_route() {
        use crate::{
            fields::{Bn254Fr, Gf256, KoalaBear},
            poly::univariate::factorize::{factorize_with_route, FrobeniusRoute},
            KnownOrder,
        };

        fn sorted<F: KnownOrder>(
            factors: Vec<(UnivariatePolynomial<F>, usize)>,
        ) -> Vec<(String, usize)> {
            let mut keyed: Vec<_> = factors
                .into_iter()
                .map(|(factor, multiplicity)| (format!("{factor:?}"), multiplicity))
                .collect();
            keyed.sort();
            keyed
        }

        fn check<F: KnownOrder>(seed: u64, degrees: &[u64]) {
            let mut rng = StdRng::seed_from_u64(seed);
            for &degree in degrees {
                let random = UnivariatePolynomial::<F>::rand(degree, &mut rng);
                // A repeated factor and a planted product of two quadratics, so multiplicities
                // and an equal-degree split above degree one are both exercised.
                let quadratic = UnivariatePolynomial::<F>::rand(2, &mut rng);
                let f = &(&random * &quadratic) * &quadratic;
                let by_pow_mod = factorize_with_route(&f, &mut rng, FrobeniusRoute::PowMod);
                let by_composition =
                    factorize_with_route(&f, &mut rng, FrobeniusRoute::Composition);
                assert_eq!(
                    sorted(by_pow_mod),
                    sorted(by_composition),
                    "degree {degree}"
                );
            }
        }

        check::<PrimeFieldElement64<5>>(31, &[1, 3, 8, 20]);
        check::<KoalaBear>(32, &[1, 6, 25]);
        check::<Bn254Fr>(33, &[4, 10]);
        check::<Gf256>(34, &[5, 12]);
    }

    /// Factorization works over a 254-bit field, with the factors recovered as planted.
    ///
    /// Exercises the odd-characteristic splitter at a width where `(q - 1) / 2` and `q^d` are
    /// both beyond a `u128`, which is the whole point of the limb exponents.
    #[test]
    fn test_factorize_over_bn254_fr() {
        use crate::{fields::Bn254Fr, identities::One};

        // (x - 3)(x - a)(x^2 + x + 1), with `a` wide. The quadratic is irreducible over GF(p)
        // exactly when p is not 1 mod 3; whichever it is, the product of the degrees must come
        // back to the total degree and the product of the factors must be the input.
        let a = <Bn254Fr as FiniteField>::from_str("31415926535897932384626433832795028841")
            .expect("valid decimal");
        let linear_three =
            UnivariatePolynomial::new(&[Bn254Fr::zero() - Bn254Fr::new(3), Bn254Fr::one()]);
        let linear_a = UnivariatePolynomial::new(&[Bn254Fr::zero() - a, Bn254Fr::one()]);
        let quadratic =
            UnivariatePolynomial::new(&[Bn254Fr::one(), Bn254Fr::one(), Bn254Fr::one()]);
        let f = &(&linear_three * &linear_a) * &quadratic;

        let mut rng = StdRng::seed_from_u64(21);
        let factors = factorize(&f, &mut rng);

        // Every factor is irreducible, and their product with multiplicity is f.
        let mut product = UnivariatePolynomial::<Bn254Fr>::one();
        let mut total_degree = 0;
        for (factor, multiplicity) in &factors {
            assert!(is_irreducible(factor), "{factor} must be irreducible");
            for _ in 0..*multiplicity {
                product = &product * factor;
                total_degree += factor.degree();
            }
        }
        assert_eq!(total_degree, f.degree());
        assert_eq!(product, f, "the factors must multiply back to f");

        // The two planted linear factors are among them.
        let found: Vec<&UnivariatePolynomial<Bn254Fr>> =
            factors.iter().map(|(factor, _)| factor).collect();
        assert!(found.contains(&&linear_three), "x - 3 must be a factor");
        assert!(found.contains(&&linear_a), "x - a must be a factor");
    }

    /// Factors keyed by their debug form and sorted, so two factorizations compare as multisets.
    fn keyed<F: crate::KnownOrder>(
        factors: Vec<(UnivariatePolynomial<F>, usize)>,
    ) -> Vec<(u32, String, usize)> {
        let mut keyed: Vec<_> = factors
            .into_iter()
            .map(|(factor, multiplicity)| (factor.degree(), format!("{factor:?}"), multiplicity))
            .collect();
        keyed.sort();
        keyed
    }

    /// A random irreducible of degree `d`, by rejection on `is_irreducible`'s `pow_mod` route.
    fn irreducible_of_degree<F: crate::KnownOrder>(
        d: u64,
        rng: &mut StdRng,
    ) -> UnivariatePolynomial<F> {
        use crate::poly::univariate::factorize::{
            is_irreducible_with_route, FrobeniusRoute, IrreducibilityRoute,
        };
        loop {
            let candidate = UnivariatePolynomial::<F>::rand(d, rng);
            if is_irreducible_with_route(
                &candidate,
                IrreducibilityRoute::Iterate(FrobeniusRoute::PowMod),
            ) {
                return candidate;
            }
        }
    }

    /// Every `is_irreducible` route agrees with trial division on all low-degree monic polynomials.
    #[test]
    fn test_is_irreducible_routes_agree_with_trial_division() {
        use crate::poly::univariate::factorize::{is_irreducible_with_route, IrreducibilityRoute};
        fn check<const P: u64>(max_degree: u32) {
            for n in 1..=max_degree {
                for f in monic_polynomials::<P>(n) {
                    let expected = irreducible_by_trial_division::<P>(&f);
                    for route in IrreducibilityRoute::ALL {
                        assert_eq!(
                            is_irreducible_with_route(&f, route),
                            expected,
                            "{f} over GF({P}) by {route:?}"
                        );
                    }
                }
            }
        }
        check::<2>(6);
        check::<3>(4);
        check::<5>(3);
    }

    /// Every `is_irreducible` route returns the same verdict on random, planted-irreducible and
    /// planted-reducible inputs over wide and narrow fields.
    #[test]
    fn test_is_irreducible_routes_agree_on_wide_fields() {
        use crate::{
            fields::{Bn254Fr, Gf256, KoalaBear},
            poly::univariate::factorize::{is_irreducible_with_route, IrreducibilityRoute},
            KnownOrder,
        };
        type Goldilocks = PrimeFieldElement64<18_446_744_069_414_584_321>;

        fn check<F: KnownOrder>(seed: u64, degrees: &[u64]) {
            let mut rng = StdRng::seed_from_u64(seed);
            for &d in degrees {
                let irreducible = irreducible_of_degree::<F>(d, &mut rng);
                let other = irreducible_of_degree::<F>(d.div_ceil(2), &mut rng);
                let random = UnivariatePolynomial::<F>::rand(d, &mut rng);
                let cases = [
                    (irreducible.clone(), Some(true)),
                    (&irreducible * &other, Some(false)),
                    (&other * &other, Some(false)),
                    // A nonmonic irreducible is still irreducible.
                    (irreducible.scale(&F::new(3)), Some(true)),
                    (random, None),
                ];
                for (f, expected) in cases {
                    let verdicts: Vec<bool> = IrreducibilityRoute::ALL
                        .iter()
                        .map(|route| is_irreducible_with_route(&f, *route))
                        .collect();
                    assert!(
                        verdicts.iter().all(|v| *v == verdicts[0]),
                        "routes disagree on degree {d}: {verdicts:?}"
                    );
                    if let Some(expected) = expected {
                        assert_eq!(verdicts[0], expected, "degree {d}");
                    }
                }
            }
        }

        check::<PrimeFieldElement64<5>>(41, &[2, 6, 12, 30]);
        check::<KoalaBear>(42, &[1, 2, 9, 16, 27]);
        check::<Goldilocks>(43, &[3, 8, 20]);
        check::<Bn254Fr>(44, &[2, 5, 12]);
        check::<Gf256>(45, &[4, 9, 15]);
    }

    /// Every distinct-degree route returns the same factorization as the iterated one, on random,
    /// squarefree-planted, repeated-factor and root-finding-shaped inputs.
    #[test]
    fn test_distinct_degree_routes_agree() {
        use crate::{
            fields::{Bn254Fr, Gf256, KoalaBear},
            poly::univariate::factorize::{
                factorize_with_routes, DistinctDegreeRoute, FrobeniusRoute,
            },
            KnownOrder,
        };
        type Goldilocks = PrimeFieldElement64<18_446_744_069_414_584_321>;

        fn agree<F: KnownOrder>(f: &UnivariatePolynomial<F>, rng: &mut StdRng, label: &str) {
            let reference = keyed(factorize_with_routes(
                f,
                rng,
                FrobeniusRoute::PowMod,
                DistinctDegreeRoute::Iterated,
            ));
            let total = reference
                .iter()
                .map(|(degree, _, multiplicity)| *degree as usize * multiplicity)
                .sum::<usize>();
            assert_eq!(total, f.degree() as usize, "{label}: degrees do not add up");
            for ddf in DistinctDegreeRoute::ALL {
                for route in [FrobeniusRoute::PowMod, FrobeniusRoute::Auto] {
                    let other = keyed(factorize_with_routes(f, rng, route, ddf));
                    assert_eq!(reference, other, "{label}: {ddf:?} with {route:?}");
                }
            }
        }

        fn check<F: KnownOrder>(seed: u64, degrees: &[u64]) {
            let mut rng = StdRng::seed_from_u64(seed);
            for &n in degrees {
                let random = UnivariatePolynomial::<F>::rand(n, &mut rng);
                agree(&random, &mut rng, &format!("random of degree {n}"));

                // Distinct irreducibles of several degrees, two of them equal, so the interval
                // gcds and their fine split both see more than one degree per interval.
                let mut planted = UnivariatePolynomial::<F>::one();
                for d in [1, 1, 2, 3, 3, n.max(4), n / 2 + 1] {
                    planted = &planted * &irreducible_of_degree::<F>(d, &mut rng);
                }
                agree(&planted, &mut rng, &format!("planted around {n}"));

                // A repeated factor above the degrees the iterated phase covers keeps the input
                // off the squarefree-only baby-step route.
                let high = irreducible_of_degree::<F>(n.max(3), &mut rng);
                let repeated = &(&high * &high) * &UnivariatePolynomial::<F>::rand(3, &mut rng);
                agree(&repeated, &mut rng, &format!("square of degree {n}"));

                // Linear factors times one irreducible quadratic: the root-finding shape.
                let zeros: Vec<F> = (0..n).map(|_| F::random(&mut rng)).collect();
                let roots = &UnivariatePolynomial::from_zeros(&zeros)
                    * &irreducible_of_degree::<F>(2, &mut rng);
                agree(&roots, &mut rng, &format!("{n} linear x quadratic"));
            }
            agree(
                &UnivariatePolynomial::<F>::rand(1, &mut rng),
                &mut rng,
                "degree 1",
            );
            agree(
                &irreducible_of_degree::<F>(17, &mut rng),
                &mut rng,
                "irreducible of degree 17",
            );
        }

        check::<PrimeFieldElement64<3>>(51, &[4, 9, 24]);
        check::<PrimeFieldElement64<5>>(52, &[6, 20, 40]);
        check::<KoalaBear>(53, &[5, 30, 60]);
        check::<Goldilocks>(54, &[8, 40]);
        check::<Bn254Fr>(55, &[6, 18]);
        check::<Gf256>(56, &[7, 25]);
    }

    /// Every distinct-degree route finds the 3 linear, 3 quadratic and 18 quartic monic
    /// irreducibles of `x^81 - x` over GF(3), each once.
    #[test]
    fn test_distinct_degree_routes_on_x_to_the_q_to_the_k_minus_x() {
        use crate::poly::univariate::factorize::{
            factorize_with_routes, DistinctDegreeRoute, FrobeniusRoute,
        };
        let mut coefficients = vec![0u64; 82];
        coefficients[81] = 1;
        coefficients[1] = 2;
        let f = poly::<3>(&coefficients);
        let mut rng = StdRng::seed_from_u64(57);
        for ddf in DistinctDegreeRoute::ALL {
            let factors = factorize_with_routes(&f, &mut rng, FrobeniusRoute::Auto, ddf);
            let mut by_degree = [0usize; 5];
            for (factor, multiplicity) in &factors {
                assert_eq!(*multiplicity, 1);
                by_degree[factor.degree() as usize] += 1;
            }
            assert_eq!(by_degree, [0, 3, 3, 0, 18], "{ddf:?}");
        }
    }
}
