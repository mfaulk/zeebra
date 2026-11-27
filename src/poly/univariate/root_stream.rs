//! The roots of a univariate polynomial in a finite field, one at a time.
//!
//! [`roots`](super::roots) splits the whole linear part `gcd(f, x^q - x)` before returning any
//! root. A caller that stops at the first root that works — first-point solving, which tries a
//! root, descends, and comes back only if the branch dies — pays for splitting all the others
//! anyway. [`RootStream`] computes the linear part once and splits only as far as the next root
//! needs, keeping the unsplit factors for later requests.
//!
//! Every way the stream can stop is a distinct, typed outcome: `Ok(None)` (every base-field root
//! has been emitted, and the only outcome that means "no more roots"),
//! [`RootStreamError::RetryExhausted`] and [`RootStreamError::Interrupted`] (neither of which says
//! anything about the remaining roots), and [`RootStreamError::EveryElementIsARoot`] for the zero
//! polynomial. A caller that stops asking is the fourth, and needs no variant.
//!
//! # References
//! * A Computational Introduction to Number Theory and Algebra, 20.2 and 21.3

use rand::{CryptoRng, RngCore};

use crate::{
    poly::univariate::{
        factorize::{try_split_linear, MAX_SPLIT_ATTEMPTS},
        gcd,
        pow_mod::pow_mod_limbs,
        Polynomial, UnivariatePolynomial,
    },
    KnownOrder,
};

/// Why a [`RootStream`] could not produce its next root.
///
/// None of these means "no more roots". That is `Ok(None)` from [`RootStream::next_root`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RootStreamError {
    /// The polynomial is zero, so every element of the field is a root.
    EveryElementIsARoot,

    /// A split of a product of `degree` distinct linear factors failed in `attempts` random tries.
    ///
    /// Each try succeeds with probability near one half, so with the default bound this means a
    /// defect, and with a small caller-chosen bound it means the bound. The roots inside that
    /// product are still there.
    RetryExhausted { degree: u32, attempts: usize },

    /// The caller's control asked the stream to stop before its next split.
    Interrupted,
}

impl std::fmt::Display for RootStreamError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EveryElementIsARoot => {
                write!(f, "every element is a root of the zero polynomial")
            }
            Self::RetryExhausted { degree, attempts } => write!(
                f,
                "a product of {} distinct linear factors did not split in {} attempts",
                degree, attempts
            ),
            Self::Interrupted => write!(f, "root extraction was interrupted between splits"),
        }
    }
}

impl std::error::Error for RootStreamError {}

/// The work a [`RootStream`] has done, in the units that dominate its cost.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct RootStreamCounters {
    /// Modular exponentiations: the one `x^q mod f`, plus one per splitting attempt in odd
    /// characteristic, where each attempt raises to `(q - 1) / 2`.
    pub pow_mods: usize,

    /// Absolute traces onto GF(2), the characteristic-two splitter's counterpart of `pow_mods`.
    pub traces: usize,

    /// Polynomial gcds: the linear part, any gcd across constraints, and one per attempt.
    pub gcds: usize,

    /// Random splitting attempts, successful or not.
    pub split_attempts: usize,

    /// Successful splits.
    pub splits: usize,

    /// Distinct base-field roots, known from the linear part's degree before any split.
    pub roots_available: usize,

    /// Roots emitted so far.
    pub roots_emitted: usize,
}

/// The distinct roots of a polynomial in its base field, produced on demand.
///
/// Each root is emitted once and checked by evaluation before it is. The order is unspecified but
/// fixed for a fixed random number generator.
pub struct RootStream<F: KnownOrder> {
    /// The polynomial every emitted value is checked against.
    f: UnivariatePolynomial<F>,
    /// Unsplit squarefree products of distinct linear factors, whose roots are exactly the ones
    /// not yet emitted. The next one split is on top.
    pending: Vec<UnivariatePolynomial<F>>,
    max_split_attempts: usize,
    counters: RootStreamCounters,
}

impl<F: KnownOrder> RootStream<F> {
    /// A stream over the distinct roots of `f` in F.
    ///
    /// Costs one modular exponentiation and one gcd, and no splitting.
    ///
    /// # Errors
    /// [`RootStreamError::EveryElementIsARoot`] if `f` is zero.
    pub fn new(f: &UnivariatePolynomial<F>) -> Result<Self, RootStreamError> {
        Self::of_common_roots(std::slice::from_ref(f))
    }

    /// A stream over the values that are roots of **every** polynomial in `constraints`.
    ///
    /// Takes their gcd first, and the linear part of that, so the one exponentiation is reduced
    /// modulo the smallest polynomial there is. Zero polynomials constrain nothing and are
    /// skipped.
    ///
    /// # Errors
    /// [`RootStreamError::EveryElementIsARoot`] if every constraint is zero, or there are none.
    pub fn of_common_roots(
        constraints: &[UnivariatePolynomial<F>],
    ) -> Result<Self, RootStreamError> {
        let mut counters = RootStreamCounters::default();
        let mut nonzero = constraints.iter().filter(|c| !c.is_zero());
        let mut common = nonzero
            .next()
            .ok_or(RootStreamError::EveryElementIsARoot)?
            .clone();
        for c in nonzero {
            counters.gcds += 1;
            common = gcd(&common, c);
        }

        let mut stream = Self {
            f: common.clone(),
            pending: Vec::new(),
            max_split_attempts: MAX_SPLIT_ATTEMPTS,
            counters,
        };

        // A nonzero constant has no roots, and needs no exponentiation to say so.
        if common.degree() == 0 {
            return Ok(stream);
        }

        // gcd(f, x^q - x) keeps exactly the distinct roots of f that lie in F; see `roots`.
        let x = UnivariatePolynomial::new(&[F::zero(), F::one()]);
        let x_to_the_q = pow_mod_limbs(&x, F::order_limbs(), &common);
        let linear_part = gcd(&common, &(&x_to_the_q - &x));
        stream.counters.pow_mods += 1;
        stream.counters.gcds += 1;

        if !linear_part.is_zero() && linear_part.degree() > 0 {
            stream.counters.roots_available = linear_part.degree() as usize;
            stream.pending.push(linear_part);
        }
        Ok(stream)
    }

    /// The same stream, with each split allowed at most `attempts` random tries.
    pub fn with_max_split_attempts(mut self, attempts: usize) -> Self {
        self.max_split_attempts = attempts;
        self
    }

    /// What the stream has spent so far.
    pub fn counters(&self) -> RootStreamCounters {
        self.counters
    }

    /// Roots not yet emitted. Exact, since it is the degree left unsplit.
    pub fn remaining(&self) -> usize {
        self.pending.iter().map(|p| p.degree() as usize).sum()
    }

    /// The next root, or `Ok(None)` once every base-field root has been emitted.
    ///
    /// # Errors
    /// [`RootStreamError::RetryExhausted`] if a split ran out of attempts. The product it failed on
    /// is kept, so a later call tries it again with fresh randomness.
    pub fn next_root<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
    ) -> Result<Option<F>, RootStreamError> {
        self.next_root_with(rng, &mut || false)
    }

    /// As [`next_root`](Self::next_root), asking `interrupt` before each split whether to stop.
    ///
    /// # Errors
    /// As [`next_root`](Self::next_root), plus [`RootStreamError::Interrupted`] when `interrupt`
    /// returns true. Nothing is lost: the stream resumes where it stopped.
    pub fn next_root_with<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        interrupt: &mut dyn FnMut() -> bool,
    ) -> Result<Option<F>, RootStreamError> {
        let odd_characteristic = F::characteristic_limbs() != [2];
        loop {
            let Some(g) = self.pending.pop() else {
                return Ok(None);
            };

            if g.degree() == 1 {
                let c = g.coefficients();
                let root = F::zero() - c[0] / c[1];
                assert!(
                    self.f.eval(&root).is_zero(),
                    "{} was split out of the linear part of {} and is not a root of it",
                    root,
                    self.f
                );
                self.counters.roots_emitted += 1;
                return Ok(Some(root));
            }

            if interrupt() {
                self.pending.push(g);
                return Err(RootStreamError::Interrupted);
            }

            let (parts, attempts) = try_split_linear(&g, rng, self.max_split_attempts);
            self.counters.split_attempts += attempts;
            self.counters.gcds += attempts;
            if odd_characteristic {
                self.counters.pow_mods += attempts;
            } else {
                self.counters.traces += attempts;
            }

            let Some((left, right)) = parts else {
                let degree = g.degree();
                self.pending.push(g);
                return Err(RootStreamError::RetryExhausted { degree, attempts });
            };
            self.counters.splits += 1;

            // The smaller part on top: it reaches a single root in fewer splits, each cheaper.
            let (small, large) = if left.degree() <= right.degree() {
                (left, right)
            } else {
                (right, left)
            };
            self.pending.push(large);
            self.pending.push(small);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use rand::{prelude::StdRng, SeedableRng};

    use super::{RootStream, RootStreamError};
    use crate::{
        fields::{Bn254Fr, Gf256, PrimeFieldElement64, Zp2147483647},
        identities::{One, Zero},
        poly::univariate::{roots, Polynomial, UnivariatePolynomial},
        FiniteField, KnownOrder,
    };

    /// The product of `(x - a)` over `values`.
    fn product_of_linear<F: FiniteField>(values: &[F]) -> UnivariatePolynomial<F> {
        values.iter().fold(UnivariatePolynomial::one(), |acc, a| {
            &acc * &UnivariatePolynomial::new(&[F::zero() - *a, F::one()])
        })
    }

    /// Every root the stream produces, draining it.
    fn drain<F: KnownOrder>(stream: &mut RootStream<F>, rng: &mut StdRng) -> Vec<F> {
        let mut found = Vec::new();
        while let Some(root) = stream.next_root(rng).expect("default bound") {
            found.push(root);
        }
        found
    }

    fn poly<const P: u64>(coefficients: &[u64]) -> UnivariatePolynomial<PrimeFieldElement64<P>> {
        UnivariatePolynomial::new(
            &coefficients
                .iter()
                .map(|c| PrimeFieldElement64::<P>::new(*c))
                .collect::<Vec<_>>(),
        )
    }

    /// The emitted set equals the planted set for a product of known linear factors.
    #[test]
    fn test_planted_linear_factors_are_recovered() {
        let mut rng = StdRng::seed_from_u64(1);
        let planted: Vec<Zp2147483647> = [3u64, 17, 99, 12345, 2_000_000_000]
            .iter()
            .map(|v| Zp2147483647::new(*v))
            .collect();
        let f = product_of_linear(&planted);
        let mut stream = RootStream::new(&f).unwrap();
        assert_eq!(stream.counters().roots_available, planted.len());
        let found = drain(&mut stream, &mut rng);
        assert_eq!(found.len(), planted.len(), "each root once");
        assert_eq!(
            found.into_iter().collect::<HashSet<_>>(),
            planted.into_iter().collect::<HashSet<_>>()
        );
    }

    /// A root of multiplicity four is emitted exactly once.
    #[test]
    fn test_repeated_factors_give_each_root_once() {
        let mut rng = StdRng::seed_from_u64(2);
        let a = Zp2147483647::new(7);
        let b = Zp2147483647::new(11);
        let f = product_of_linear(&[a, a, a, a, b, b]);
        let found = drain(&mut RootStream::new(&f).unwrap(), &mut rng);
        assert_eq!(found.len(), 2);
        assert_eq!(
            found.into_iter().collect::<HashSet<_>>(),
            HashSet::from([a, b])
        );
    }

    /// An irreducible quadratic has roots only in an extension, so the stream is exhausted at once.
    #[test]
    fn test_roots_only_in_an_extension_exhaust_immediately() {
        let mut rng = StdRng::seed_from_u64(3);
        // x^2 + 1 over GF(7): -1 is not a square mod 7.
        let mut stream = RootStream::new(&poly::<7>(&[1, 0, 1])).unwrap();
        assert_eq!(stream.counters().roots_available, 0);
        assert_eq!(stream.next_root(&mut rng), Ok(None));
        // A nonzero constant has no roots either, and costs no exponentiation.
        let mut constant = RootStream::new(&poly::<7>(&[5])).unwrap();
        assert_eq!(constant.counters().pow_mods, 0);
        assert_eq!(constant.next_root(&mut rng), Ok(None));
    }

    /// Draining the stream agrees with exhaustive evaluation and with `roots`, over small fields
    /// of both characteristics.
    #[test]
    fn test_complete_consumption_agrees_with_evaluation_and_roots() {
        fn check<const P: u64>(seed: u64) {
            let mut rng = StdRng::seed_from_u64(seed);
            let polynomials: Vec<Vec<u64>> = vec![
                vec![1, 1],
                vec![0, 1],
                vec![P - 1, 0, 1],
                vec![1, 0, 1],
                vec![0, 0, 1],
                vec![P - 1, 0, 0, 1],
                vec![1, 2, 3, 4],
                vec![1, 1, 1, 1, 1],
            ];
            for coefficients in &polynomials {
                let f = poly::<P>(coefficients);
                let by_evaluation: HashSet<_> = (0..P)
                    .map(PrimeFieldElement64::<P>::new)
                    .filter(|a| f.eval(a).is_zero())
                    .collect();
                let found = drain(&mut RootStream::new(&f).unwrap(), &mut rng);
                assert_eq!(
                    found.len(),
                    by_evaluation.len(),
                    "duplicates in {:?}",
                    found
                );
                let found: HashSet<_> = found.into_iter().collect();
                assert_eq!(found, by_evaluation, "{:?} over GF({})", coefficients, P);
                let eager: HashSet<_> = roots(&f, &mut rng).into_iter().collect();
                assert_eq!(found, eager);
            }
        }
        check::<2>(10);
        check::<3>(11);
        check::<13>(12);
        check::<31>(13);
    }

    /// x^q - x over GF(2^8) splits completely into all 256 elements, via the trace splitter.
    #[test]
    fn test_characteristic_two_extension_field() {
        let mut rng = StdRng::seed_from_u64(4);
        let mut coefficients = vec![Gf256::zero(); 257];
        coefficients[256] = Gf256::one();
        coefficients[1] = Gf256::one(); // -1 = 1 in characteristic two
        let f = UnivariatePolynomial::new(&coefficients);
        let mut stream = RootStream::new(&f).unwrap();
        let found = drain(&mut stream, &mut rng);
        assert_eq!(found.len(), 256);
        assert_eq!(found.iter().collect::<HashSet<_>>().len(), 256);
        assert!(stream.counters().traces > 0);
        assert_eq!(stream.counters().pow_mods, 1, "only x^q, no odd-q exponent");
    }

    /// Planted roots over BN254's 254-bit scalar field are recovered.
    #[test]
    fn test_wide_prime_field() {
        let mut rng = StdRng::seed_from_u64(5);
        let planted: Vec<Bn254Fr> = ["1", "7", "123456789012345678901234567890123456789"]
            .iter()
            .map(|d| <Bn254Fr as FiniteField>::from_str(d).unwrap())
            .collect();
        let found = drain(
            &mut RootStream::new(&product_of_linear(&planted)).unwrap(),
            &mut rng,
        );
        assert_eq!(
            found.into_iter().collect::<HashSet<_>>(),
            planted.into_iter().collect::<HashSet<_>>()
        );
    }

    /// Stopping after one root leaves most of the splitting undone, which is the point.
    #[test]
    fn test_early_stop_leaves_unsplit_work() {
        let mut rng = StdRng::seed_from_u64(6);
        let planted: Vec<Zp2147483647> = (1..=64).map(Zp2147483647::new).collect();
        let f = product_of_linear(&planted);

        let mut lazy = RootStream::new(&f).unwrap();
        let first = lazy.next_root(&mut rng).unwrap().unwrap();
        assert!(planted.contains(&first));
        let after_one = lazy.counters();
        assert_eq!(lazy.remaining(), 63);

        let mut full = RootStream::new(&f).unwrap();
        drain(&mut full, &mut rng);
        let complete = full.counters();
        assert_eq!(
            complete.splits, 63,
            "a binary tree over 64 leaves has 63 inner nodes"
        );
        // Only the splits on one root-to-leaf path: about log2(64) of them, not 63.
        assert!(
            after_one.splits <= 16,
            "{} splits to reach the first root",
            after_one.splits
        );
    }

    /// The zero polynomial is a typed outcome rather than an empty stream or a panic.
    #[test]
    fn test_zero_polynomial_is_a_typed_outcome() {
        let zero = UnivariatePolynomial::<Zp2147483647>::zero();
        assert_eq!(
            RootStream::new(&zero).err(),
            Some(RootStreamError::EveryElementIsARoot)
        );
        assert_eq!(
            RootStream::<Zp2147483647>::of_common_roots(&[]).err(),
            Some(RootStreamError::EveryElementIsARoot)
        );
    }

    /// A split bound of zero is reported as retry exhaustion, and the roots stay available.
    #[test]
    fn test_forced_retry_exhaustion_is_typed_and_resumable() {
        let mut rng = StdRng::seed_from_u64(7);
        let planted: Vec<Zp2147483647> = (1..=4).map(Zp2147483647::new).collect();
        let mut stream = RootStream::new(&product_of_linear(&planted))
            .unwrap()
            .with_max_split_attempts(0);
        assert_eq!(
            stream.next_root(&mut rng),
            Err(RootStreamError::RetryExhausted {
                degree: 4,
                attempts: 0
            })
        );
        assert_eq!(stream.remaining(), 4, "exhaustion is not 'no root'");
        let mut stream = stream.with_max_split_attempts(1000);
        assert_eq!(drain(&mut stream, &mut rng).len(), 4);
    }

    /// An interrupt between splits stops the stream, and it resumes losing nothing.
    #[test]
    fn test_interruption_between_splits() {
        let mut rng = StdRng::seed_from_u64(8);
        let planted: Vec<Zp2147483647> = (1..=8).map(Zp2147483647::new).collect();
        let mut stream = RootStream::new(&product_of_linear(&planted)).unwrap();
        assert_eq!(
            stream.next_root_with(&mut rng, &mut || true),
            Err(RootStreamError::Interrupted)
        );
        assert_eq!(stream.counters().split_attempts, 0);
        let found: HashSet<_> = drain(&mut stream, &mut rng).into_iter().collect();
        assert_eq!(found, planted.into_iter().collect::<HashSet<_>>());
    }

    /// The common roots of several constraints are those of their gcd.
    #[test]
    fn test_common_roots_of_several_constraints() {
        let mut rng = StdRng::seed_from_u64(9);
        let v = |n: u64| Zp2147483647::new(n);
        let f = product_of_linear(&[v(1), v(2), v(3), v(4)]);
        let g = product_of_linear(&[v(3), v(4), v(5)]);
        let zero = UnivariatePolynomial::zero();
        let mut stream = RootStream::of_common_roots(&[f, zero, g]).unwrap();
        let found: HashSet<_> = drain(&mut stream, &mut rng).into_iter().collect();
        assert_eq!(found, HashSet::from([v(3), v(4)]));
    }
}
