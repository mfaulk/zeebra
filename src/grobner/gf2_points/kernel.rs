//! Bitsliced `GF(2)` evaluation kernels, kept apart from the algorithms that call them (#1156), so
//! that a measured gap can be split between representation (#218) and algorithm.
//!
//! Both kernels are bitsliced across *polynomials*: bit `e` of a lane word belongs to polynomial
//! `e`, so one `u64` operation advances up to 64 polynomials at once. A point is a `u64` mask, bit
//! `i` the value of variable `i`.

/// Up to 64 quadratic Boolean polynomials in `t ≤ 63` variables, one lane bit per polynomial.
///
/// `pair[i * t + j]` (`i ≠ j`, stored both ways) is the lane mask of `x_i x_j`, `linear[i]` that of
/// `x_i` and `constant` that of `1`.
#[derive(Clone, Debug)]
pub(crate) struct QuadraticLanes {
    pub(crate) vars: usize,
    pub(crate) pair: Vec<u64>,
    pub(crate) linear: Vec<u64>,
    pub(crate) constant: u64,
}

impl QuadraticLanes {
    /// Every polynomial's value at `x`, as a lane mask. The slow path, for tests and candidates.
    #[cfg(test)]
    pub(crate) fn evaluate(&self, x: u64) -> u64 {
        let t = self.vars;
        let mut value = self.constant;
        for i in (0..t).filter(|&i| x >> i & 1 == 1) {
            value ^= self.linear[i];
            for j in (i + 1..t).filter(|&j| x >> j & 1 == 1) {
                value ^= self.pair[i * t + j];
            }
        }
        value
    }

    /// Walks all `2^t` points in Gray-code order and calls `zero(x)` at every point where every
    /// lane is zero. `zero` returns `false` to stop the walk early.
    ///
    /// This is the fast exhaustive search of Bouillaguet et al. (CHES 2010): two word `xor`s per
    /// point. Step `i` flips variable `k1 = ctz(i)`, and `f(x ⊕ e_k1) = f(x) ⊕ D_k1 f(x)`, where the
    /// first derivative `D_k f(x) = b_k ⊕ Σ_j a_kj x_j` is affine. Between two flips of `k1` the
    /// variables below it flip an even number of times each and exactly one above it flips, namely
    /// `k2 = ctz(i & (i − 1))`, so `D_k1 f` changes by the one constant `a_k1k2`. Before its first
    /// flip at `i = 2^k`, the walk stands at `e_(k−1)`, which fixes the initial derivative.
    pub(crate) fn gray_code_zeros(&self, mut zero: impl FnMut(u64) -> bool) {
        let t = self.vars;
        assert!(t < 64, "{t} variables do not fit the walk's counter");
        let mut y = self.constant;
        if y == 0 && !zero(0) {
            return;
        }
        let mut derivative: Vec<u64> = (0..t)
            .map(|k| self.linear[k] ^ if k > 0 { self.pair[k * t + k - 1] } else { 0 })
            .collect();
        let mut x = 0u64;
        for i in 1u64..1 << t {
            let k1 = i.trailing_zeros() as usize;
            let rest = i & (i - 1);
            if rest != 0 {
                derivative[k1] ^= self.pair[k1 * t + rest.trailing_zeros() as usize];
            }
            y ^= derivative[k1];
            x ^= 1 << k1;
            if y == 0 && !zero(x) {
                return;
            }
        }
    }
}

/// Evaluates bitsliced multilinear polynomials at every point of a `c`-cube, in place.
///
/// `table` holds `2^c` blocks of `width` lane words. On entry, block `u` holds the coefficient of
/// the monomial `Π_{i ∈ u} x_i` (as lane masks, one word per output slot). On exit, block `x`
/// holds the value at `x`. This is the binary Möbius (zeta) transform over subsets: `c·2^(c−1)`
/// block `xor`s, so `c/2` word operations per point and slot — against a Gray-code walk's `D`,
/// for degree `D`, which is the faster kernel this one stands in for.
pub(crate) fn mobius_in_place(table: &mut [u64], c: usize, width: usize) {
    assert_eq!(
        table.len(),
        width << c,
        "table is not 2^c blocks of {width}"
    );
    for bit in 0..c {
        let half = 1usize << bit;
        for base in (0..1usize << c).step_by(half << 1) {
            for low in base..base + half {
                let (source, target) = (low * width, (low + half) * width);
                let (head, tail) = table.split_at_mut(target);
                for (t, s) in tail[..width].iter_mut().zip(&head[source..source + width]) {
                    *t ^= *s;
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use rand::{rngs::StdRng, Rng, SeedableRng};

    use super::*;

    fn random_lanes(t: usize, rng: &mut StdRng) -> QuadraticLanes {
        let mut pair = vec![0u64; t * t];
        for i in 0..t {
            for j in i + 1..t {
                let a = rng.gen::<u64>();
                pair[i * t + j] = a;
                pair[j * t + i] = a;
            }
        }
        QuadraticLanes {
            vars: t,
            pair,
            linear: (0..t).map(|_| rng.gen()).collect(),
            constant: rng.gen(),
        }
    }

    /// The walk's running value agrees with direct evaluation at every point it visits, and it
    /// visits each of the `2^t` points once.
    #[test]
    fn gray_code_walk_matches_direct_evaluation_at_every_point() {
        let mut rng = StdRng::seed_from_u64(1156);
        for t in 0..=10 {
            let mut lanes = random_lanes(t, &mut rng);
            // Shift the constant so that `target` is a common zero, then the walk must report it.
            let mut seen = vec![false; 1 << t];
            for target in 0..1u64 << t {
                lanes.constant ^= lanes.evaluate(target);
                let mut hits = Vec::new();
                lanes.gray_code_zeros(|x| {
                    hits.push(x);
                    true
                });
                for &x in &hits {
                    assert_eq!(lanes.evaluate(x), 0, "t = {t}: reported zero at {x:#b}");
                }
                assert!(hits.contains(&target), "t = {t}: missed {target:#b}");
                seen[target as usize] = true;
            }
            assert!(seen.iter().all(|&s| s));
        }
    }

    /// Lanes are independent: a zero is reported only when all 64 vanish at once.
    #[test]
    fn gray_code_walk_reports_exactly_the_common_zeros() {
        let mut rng = StdRng::seed_from_u64(7);
        for t in 1..=12 {
            let mut lanes = random_lanes(t, &mut rng);
            // Keep 4 lanes so common zeros exist.
            let keep = 0b1111;
            lanes.pair.iter_mut().for_each(|w| *w &= keep);
            lanes.linear.iter_mut().for_each(|w| *w &= keep);
            lanes.constant &= keep;
            let expected: Vec<u64> = (0..1u64 << t).filter(|&x| lanes.evaluate(x) == 0).collect();
            let mut got = Vec::new();
            lanes.gray_code_zeros(|x| {
                got.push(x);
                true
            });
            got.sort_unstable();
            assert_eq!(got, expected, "t = {t}");
        }
    }

    #[test]
    fn gray_code_walk_stops_when_asked() {
        let lanes = QuadraticLanes {
            vars: 3,
            pair: vec![0; 9],
            linear: vec![0; 3],
            constant: 0,
        };
        let mut calls = 0;
        lanes.gray_code_zeros(|_| {
            calls += 1;
            calls < 3
        });
        assert_eq!(calls, 3);
    }

    /// The transform turns coefficients into values: compare with summing every submonomial.
    #[test]
    fn mobius_transform_evaluates_multilinear_polynomials() {
        let mut rng = StdRng::seed_from_u64(3);
        for c in 0..=8 {
            let width = 3;
            let coefficients: Vec<u64> = (0..width << c).map(|_| rng.gen()).collect();
            let mut table = coefficients.clone();
            mobius_in_place(&mut table, c, width);
            for x in 0..1usize << c {
                for slot in 0..width {
                    let direct = (0..1usize << c)
                        .filter(|&u| u & !x == 0)
                        .fold(0, |acc, u| acc ^ coefficients[u * width + slot]);
                    assert_eq!(table[x * width + slot], direct, "c = {c}, x = {x:#b}");
                }
            }
        }
    }
}
