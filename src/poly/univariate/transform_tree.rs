//! A research arm for #606: the subproduct tree with its large node products and remainders moved
//! onto a power-of-two transform, kept beside [`super::subproduct_tree`] rather than replacing it.
//!
//! Not dispatched to. `multipoint_evaluate` and `lagrange_interpolate` are bounded on
//! [`FiniteField`] alone and cannot reach a root of unity, and Mersenne-31 (two-adicity 1) has no
//! large domain at all, so the shipped path stays the Karatsuba tree. This module exists so the
//! A/B in `examples/transform_tree_ab.rs` runs both arithmetics through **one** tree: a
//! [`TransformKernel`] whose threshold is `usize::MAX` takes the Karatsuba / long-division /
//! Karatsuba-Newton route at every node, which is the control arm, and any finite threshold sends
//! products of at least that degree through the transform.
//!
//! Three transform-specific savings are taken, because a specialization would take them and the
//! measurement would otherwise understate the arm:
//!
//! - the twiddle tables are built once, from one root, for every power-of-two size up to the root
//!   product's domain;
//! - a monic product of degree exactly `m = 2^j` is formed cyclically on `m` points and unwrapped,
//!   instead of on `2m`;
//! - a remainder is recovered as `f - q g mod (x^m - 1)` with `m >= deg g`, on half the points the
//!   full `q g` product would need, and `combine`'s two products share one inverse transform.

use rand::{CryptoRng, RngCore};

use crate::{
    fft::transform::transform_in_place,
    fields::{batch_invert, RootOfUnityError},
    poly::univariate::{
        div_with_remainder::{divide_long, newton_is_cheaper},
        karatsuba::multiply_karatsuba,
        subproduct_tree::derivative,
        Polynomial, UnivariatePolynomial,
    },
    FiniteField, KnownOrder,
};

/// Twiddles for one power-of-two size.
struct Table<F> {
    forward: Vec<F>,
    inverse: Vec<F>,
    scale: F,
}

/// Products and remainders, through the transform at and above a product degree, Karatsuba below.
#[doc(hidden)]
pub struct TransformKernel<F> {
    /// `tables[j]` serves size `2^j`; empty when the threshold can never be reached.
    tables: Vec<Table<F>>,
    threshold: usize,
}

impl<F: KnownOrder> TransformKernel<F> {
    /// A kernel serving products of up to `max_len` coefficients, sending a product of degree at
    /// least `threshold` through the transform.
    ///
    /// `usize::MAX` builds no tables and samples no root: that kernel is the Karatsuba control.
    ///
    /// # Errors
    /// If the field's two-adicity cannot host a domain of `max_len` points.
    pub fn new<R: RngCore + CryptoRng>(
        max_len: usize,
        threshold: usize,
        rng: &mut R,
    ) -> Result<Self, RootOfUnityError> {
        if threshold >= max_len {
            return Ok(Self {
                tables: Vec::new(),
                threshold: usize::MAX,
            });
        }
        let size = max_len.next_power_of_two();
        let log = size.trailing_zeros();
        let root = F::try_two_adic_root_of_unity(log, rng)?;
        let powers = crate::fft::powers_of(&root, size);
        let tables = (0..=log)
            .map(|j| {
                let m = 1usize << j;
                let stride = size >> j;
                Table {
                    forward: (0..m).map(|i| powers[i * stride]).collect(),
                    inverse: (0..m).map(|i| powers[((m - i) % m) * stride]).collect(),
                    scale: F::new(m as u64).inverse(),
                }
            })
            .collect();
        Ok(Self { tables, threshold })
    }
}

impl<F: FiniteField> TransformKernel<F> {
    fn uses_transform(&self, product_len: usize) -> bool {
        product_len > self.threshold
    }

    fn table(&self, m: usize) -> &Table<F> {
        &self.tables[m.trailing_zeros() as usize]
    }

    /// `v` reduced modulo `x^m - 1`, zero-padded to `m`, then transformed.
    fn forward(&self, v: &[F], m: usize) -> Vec<F> {
        let mut values = vec![F::zero(); m];
        for (i, c) in v.iter().enumerate() {
            values[i % m] += *c;
        }
        transform_in_place(&mut values, &self.table(m).forward);
        values
    }

    fn inverse(&self, mut values: Vec<F>) -> Vec<F> {
        let m = values.len();
        let table = self.table(m);
        transform_in_place(&mut values, &table.inverse);
        for c in values.iter_mut() {
            *c *= table.scale;
        }
        values
    }

    /// `a * b`.
    pub fn mul(&self, a: &[F], b: &[F]) -> Vec<F> {
        if a.is_empty() || b.is_empty() {
            return Vec::new();
        }
        let len = a.len() + b.len() - 1;
        if !self.uses_transform(len) {
            return multiply_karatsuba(a, b);
        }
        let m = len.next_power_of_two();
        let mut product = self.forward(a, m);
        for (x, y) in product.iter_mut().zip(self.forward(b, m)) {
            *x *= y;
        }
        let mut product = self.inverse(product);
        product.truncate(len);
        product
    }

    /// `a * b` for monic `a` and `b`, cyclically on `deg(ab)` points when that is a power of two.
    ///
    /// The product's only coefficient past `x^(m-1)` is its leading 1, which wraps onto the
    /// constant term; subtracting it back out recovers the product exactly.
    fn mul_monic(&self, a: &[F], b: &[F]) -> Vec<F> {
        let degree = a.len() + b.len() - 2;
        if !self.uses_transform(degree + 1) || !degree.is_power_of_two() {
            return self.mul(a, b);
        }
        let mut product = self.forward(a, degree);
        for (x, y) in product.iter_mut().zip(self.forward(b, degree)) {
            *x *= y;
        }
        let mut product = self.inverse(product);
        product[0] -= F::one();
        product.push(F::one());
        product
    }

    /// `a1 * b1 + a2 * b2`, with one inverse transform for both.
    fn mul_add(&self, a1: &[F], b1: &[F], a2: &[F], b2: &[F]) -> Vec<F> {
        let len = (a1.len() + b1.len()).max(a2.len() + b2.len()) - 1;
        if !self.uses_transform(len) {
            let mut sum = multiply_karatsuba(a1, b1);
            let other = multiply_karatsuba(a2, b2);
            if other.len() > sum.len() {
                sum.resize(other.len(), F::zero());
            }
            for (s, o) in sum.iter_mut().zip(other) {
                *s += o;
            }
            return sum;
        }
        let m = len.next_power_of_two();
        let mut sum = self.forward(a1, m);
        for (x, y) in sum.iter_mut().zip(self.forward(b1, m)) {
            *x *= y;
        }
        let left = self.forward(a2, m);
        for ((s, x), y) in sum.iter_mut().zip(left).zip(self.forward(b2, m)) {
            *s += x * y;
        }
        let mut sum = self.inverse(sum);
        sum.truncate(len);
        sum
    }

    /// `a * b mod x^k`, of length exactly `k`.
    fn mul_truncated(&self, a: &[F], b: &[F], k: usize) -> Vec<F> {
        let mut product = self.mul(&a[..a.len().min(k)], &b[..b.len().min(k)]);
        product.resize(k, F::zero());
        product
    }

    /// `1/g mod x^k` by Newton iteration, the same recurrence as #193's.
    fn invert_mod_xk(&self, g: &[F], k: usize) -> Vec<F> {
        let mut h = vec![g[0].inverse()];
        let mut precision = 1;
        while precision < k {
            let next = (2 * precision).min(k);
            let mut error = self.mul_truncated(g, &h, next);
            for c in error.iter_mut() {
                *c = c.neg();
            }
            error[0] += F::one() + F::one();
            h = self.mul_truncated(&h, &error, next);
            precision = next;
        }
        h
    }

    /// `f mod g`, of length `deg g`, for `g` with a non-zero leading coefficient.
    ///
    /// The route choice is #193's own `newton_is_cheaper`, unchanged, so below the transform
    /// threshold this is exactly the shipped division.
    pub fn rem(&self, f: &[F], g: &[F]) -> Vec<F> {
        let out_len = g.len() - 1;
        if f.len() < g.len() {
            let mut r = f.to_vec();
            r.resize(out_len, F::zero());
            return r;
        }
        let k = f.len() - g.len() + 1;
        if !newton_is_cheaper::<F>(k, g.len()) {
            let (_q, mut r) = divide_long(f, g);
            r.truncate(out_len);
            r.resize(out_len, F::zero());
            return r;
        }

        let reversed_divisor: Vec<F> = g.iter().rev().copied().collect();
        let inverse = self.invert_mod_xk(&reversed_divisor, k);
        let reversed_dividend: Vec<F> = f.iter().rev().take(k).copied().collect();
        let mut q = self.mul_truncated(&reversed_dividend, &inverse, k);
        q.reverse();

        if !self.uses_transform(f.len()) {
            let qg = multiply_karatsuba(&q, g);
            return f[..out_len].iter().zip(&qg).map(|(a, b)| *a - *b).collect();
        }
        // `f - q g` has degree below `deg g`, so it survives reduction mod `x^m - 1` for any
        // `m >= deg g` intact: the product is taken on `m` points rather than on `len f`.
        let m = out_len.next_power_of_two();
        let mut qg = self.forward(&q, m);
        for (x, y) in qg.iter_mut().zip(self.forward(g, m)) {
            *x *= y;
        }
        let qg = self.inverse(qg);
        let mut r = vec![F::zero(); m];
        for (i, c) in f.iter().enumerate() {
            r[i % m] += *c;
        }
        for (slot, c) in r.iter_mut().zip(qg) {
            *slot -= c;
        }
        r.truncate(out_len);
        r
    }
}

/// The subproduct tree of [`super::subproduct_tree`], over coefficient vectors and a kernel.
#[doc(hidden)]
pub struct TransformTree<'k, F> {
    kernel: &'k TransformKernel<F>,
    levels: Vec<Vec<Vec<F>>>,
}

impl<'k, F: FiniteField> TransformTree<'k, F> {
    /// Build the tree over `points`, which must be non-empty.
    pub fn build(points: &[F], kernel: &'k TransformKernel<F>) -> Self {
        assert!(
            !points.is_empty(),
            "a subproduct tree needs at least one point"
        );
        let mut levels = vec![points
            .iter()
            .map(|x| vec![x.neg(), F::one()])
            .collect::<Vec<_>>()];
        while levels.last().expect("pushed above").len() > 1 {
            let below = levels.last().expect("pushed above");
            let above = below
                .chunks(2)
                .map(|pair| match pair {
                    [left, right] => kernel.mul_monic(left, right),
                    [only] => only.clone(),
                    _ => unreachable!("chunks(2)"),
                })
                .collect();
            levels.push(above);
        }
        Self { kernel, levels }
    }

    /// `M = prod (x - x_i)`.
    pub fn root(&self) -> &[F] {
        &self.levels.last().expect("a tree has a leaf level")[0]
    }

    /// `f` at every abscissa, for `deg f < n`.
    pub fn evaluate(&self, f: &[F]) -> Vec<F> {
        let top = self.levels.len() - 1;
        let mut current = vec![self.kernel.rem(f, self.root())];
        for level in (0..top).rev() {
            let below = &self.levels[level];
            let mut next = Vec::with_capacity(below.len());
            for (node, remainder) in current.iter().enumerate() {
                let left = 2 * node;
                next.push(self.kernel.rem(remainder, &below[left]));
                if let Some(right) = below.get(left + 1) {
                    next.push(self.kernel.rem(remainder, right));
                }
            }
            current = next;
        }
        current.iter().map(|r| r[0]).collect()
    }

    /// `sum_i c_i * M/(x - x_i)`.
    pub fn combine(&self, scaled: &[F]) -> Vec<F> {
        assert_eq!(scaled.len(), self.levels[0].len());
        let mut current: Vec<Vec<F>> = scaled.iter().map(|c| vec![*c]).collect();
        for below in &self.levels[..self.levels.len() - 1] {
            let mut above = Vec::with_capacity(current.len().div_ceil(2));
            let mut index = 0;
            while index < current.len() {
                match current.get(index + 1) {
                    Some(right) => above.push(self.kernel.mul_add(
                        &current[index],
                        &below[index + 1],
                        right,
                        &below[index],
                    )),
                    None => above.push(current[index].clone()),
                }
                index += 2;
            }
            current = above;
        }
        current.pop().expect("the root's single node")
    }

    /// `M'(x_i)` for every abscissa.
    pub fn derivative_values(&self) -> Vec<F> {
        let root = UnivariatePolynomial::new(self.root());
        self.evaluate(derivative(&root).coefficients())
    }
}

/// The interpolant through `points`, which must be non-empty with distinct abscissae.
#[doc(hidden)]
pub fn transform_tree_interpolate_unstable<F: FiniteField>(
    points: &[(F, F)],
    kernel: &TransformKernel<F>,
) -> UnivariatePolynomial<F> {
    super::lagrange_interpolation::assert_distinct_abscissae(points);
    let abscissae: Vec<F> = points.iter().map(|(x, _)| *x).collect();
    let tree = TransformTree::build(&abscissae, kernel);
    let mut denominators = tree.derivative_values();
    batch_invert(&mut denominators);
    let scaled: Vec<F> = points
        .iter()
        .zip(&denominators)
        .map(|((_, y), inverse)| *y * *inverse)
        .collect();
    UnivariatePolynomial::new(&tree.combine(&scaled))
}

#[cfg(test)]
mod tests {
    use super::{transform_tree_interpolate_unstable, TransformKernel, TransformTree};
    use crate::{
        fields::{Bn254Fr, KoalaBear, Mersenne31, PrimeFieldElement64},
        multipoint_evaluate,
        poly::univariate::subproduct_tree::interpolate as karatsuba_interpolate,
        FiniteField, KnownOrder, Polynomial, UnivariatePolynomial,
    };
    use rand::{prelude::StdRng, SeedableRng};

    type Goldilocks = PrimeFieldElement64<18_446_744_069_414_584_321>;

    fn random_points<F: FiniteField>(n: usize, rng: &mut StdRng) -> Vec<(F, F)> {
        let mut seen = std::collections::HashSet::new();
        let mut points = Vec::with_capacity(n);
        while points.len() < n {
            let x = F::random(rng);
            if seen.insert(x) {
                points.push((x, F::random(rng)));
            }
        }
        points
    }

    /// The transform arm interpolates to the shipped Karatsuba tree's polynomial, at every threshold.
    fn agrees_with_shipped_tree<F: KnownOrder>(seed: u64) {
        let mut rng = StdRng::seed_from_u64(seed);
        for n in [1usize, 2, 3, 7, 64, 65, 129, 257, 300, 513, 1000] {
            let points = random_points::<F>(n, &mut rng);
            let expected = karatsuba_interpolate(&points);
            for threshold in [0usize, 1, 4, 16, 63, 64, 100, usize::MAX] {
                let kernel = TransformKernel::<F>::new(n + 1, threshold, &mut rng).unwrap();
                assert_eq!(
                    transform_tree_interpolate_unstable(&points, &kernel),
                    expected,
                    "n = {n}, threshold = {threshold}"
                );
            }
        }
    }

    #[test]
    // KoalaBear: the transform tree's interpolant equals the Karatsuba tree's at every threshold.
    fn test_interpolation_agrees_over_koalabear() {
        agrees_with_shipped_tree::<KoalaBear>(606);
    }

    #[test]
    // Goldilocks: the transform tree's interpolant equals the Karatsuba tree's at every threshold.
    fn test_interpolation_agrees_over_goldilocks() {
        agrees_with_shipped_tree::<Goldilocks>(607);
    }

    #[test]
    // BN254 Fr: the transform tree's interpolant equals the Karatsuba tree's at every threshold.
    fn test_interpolation_agrees_over_bn254() {
        agrees_with_shipped_tree::<Bn254Fr>(608);
    }

    #[test]
    // Multipoint evaluation down the transform tree matches the shipped `multipoint_evaluate`.
    fn test_evaluation_agrees_with_multipoint_evaluate() {
        let mut rng = StdRng::seed_from_u64(609);
        for n in [5usize, 200, 777] {
            let xs: Vec<KoalaBear> = random_points::<KoalaBear>(n, &mut rng)
                .into_iter()
                .map(|(x, _)| x)
                .collect();
            let f = UnivariatePolynomial::new(
                &(0..n)
                    .map(|_| KoalaBear::random(&mut rng))
                    .collect::<Vec<_>>(),
            );
            let expected = multipoint_evaluate(&f, &xs);
            for threshold in [0usize, 32, usize::MAX] {
                let kernel = TransformKernel::<KoalaBear>::new(n + 1, threshold, &mut rng).unwrap();
                let tree = TransformTree::build(&xs, &kernel);
                assert_eq!(tree.evaluate(f.coefficients()), expected, "n = {n}");
            }
        }
    }

    #[test]
    // The cyclic monic product on exactly `deg` points unwraps to the true product.
    fn test_monic_wrapped_product_is_exact() {
        let mut rng = StdRng::seed_from_u64(610);
        let kernel = TransformKernel::<KoalaBear>::new(257, 0, &mut rng).unwrap();
        for (da, db) in [(1usize, 1usize), (3, 5), (64, 64), (100, 156), (128, 128)] {
            let mut a: Vec<KoalaBear> = (0..da).map(|_| KoalaBear::random(&mut rng)).collect();
            a.push(KoalaBear::new(1));
            let mut b: Vec<KoalaBear> = (0..db).map(|_| KoalaBear::random(&mut rng)).collect();
            b.push(KoalaBear::new(1));
            let expected = &UnivariatePolynomial::new(&a) * &UnivariatePolynomial::new(&b);
            assert_eq!(
                UnivariatePolynomial::new(&kernel.mul_monic(&a, &b)),
                expected,
                "{da} x {db}"
            );
        }
    }

    #[test]
    // A field whose two-adicity cannot host the domain is refused, and the control kernel is not.
    fn test_mersenne31_cannot_host_a_transform_kernel() {
        let mut rng = StdRng::seed_from_u64(611);
        assert!(TransformKernel::<Mersenne31>::new(1024, 0, &mut rng).is_err());
        assert!(TransformKernel::<Mersenne31>::new(1024, usize::MAX, &mut rng).is_ok());
    }
}
