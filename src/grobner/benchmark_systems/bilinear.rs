//! The seeded bilinear family of #1007, for #1034's feasibility study.
//!
//! The variables split into `x = (x_0 … x_{k−1})` and `y = (x_k … x_{N−1})`, and each generator is
//!
//! ```text
//! f_i = xᵀ A_i y  +  b_iᵀ x  +  c_iᵀ y  +  d_i        (affine)
//! f_i = xᵀ A_i y                                     (homogeneous of bidegree (1, 1))
//! ```
//!
//! [`BilinearSpec`] fixes the block balance (`k`), the equation count, the support density of the
//! `A_i`, and a **perturbation**: extra `x_i x_j` or `y_i y_j` terms per generator. A perturbed
//! system is the nearby control #1034 requires: the same support plus a few terms that break
//! bilinearity, which [`multigrading`](fn@crate::grobner::planning::multigrading) must refuse.
//!
//! What is known about the generated ideal, and what is not:
//!
//! - **Known, by construction.** Every unperturbed affine generator is within bidegree `(1, 1)`,
//!   every unperturbed homogeneous one is bihomogeneous of `(1, 1)`, and every chosen coefficient
//!   is nonzero, so each generator's support is exactly the drawn one. A planted system vanishes at
//!   [`BilinearSystem::point`].
//! - **Not known.** Dimension, radicality and the number of solutions. Faugère, Safey El Din and
//!   Spaenlehauer's bounds (arXiv:1001.4004) hold for *generic* systems with `m = n_x + n_y`
//!   (affine), a sparse support or a perturbation may leave their hypotheses, and no seed is
//!   checked against them here. Measure, do not assume.

use rand::{rngs::StdRng, Rng, SeedableRng};

use crate::{FiniteField, Monomial, MultivariatePolynomial};

/// The parameters of one bilinear instance. `N = x_variables + n_y`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BilinearSpec {
    /// Variables in the `x` block, `k`. The `y` block holds the other `N − k`; both are nonempty.
    pub x_variables: usize,

    /// Generators, `m`. A zero-dimensional affine system needs `m ≥ N` generically.
    pub equations: usize,

    /// Add `b_iᵀx + c_iᵀy + d_i`. Without it every generator is bihomogeneous of `(1, 1)`.
    pub affine: bool,

    /// Parts per thousand of the `k · (N − k)` products `x_a y_b` each generator keeps, drawn
    /// independently per generator. `1000` is the full support. A generator whose draw keeps none
    /// keeps one, so no generator loses its bilinear part.
    pub support_per_mille: u32,

    /// Distinct same-block products `x_a x_b` or `y_a y_b` (`a ≤ b`) added to each generator.
    /// Zero for a bilinear system; positive for a perturbed control.
    pub perturbation: usize,

    /// Choose each `d_i` so the system vanishes at a seeded point. Affine only.
    pub planted: bool,

    /// The seed. Equal specs give equal systems.
    pub seed: u64,
}

/// A generated bilinear system and the point it was planted at, if any.
#[derive(Clone, Debug)]
pub struct BilinearSystem<const N: usize, F: FiniteField> {
    pub generators: Vec<MultivariatePolynomial<N, F>>,
    pub point: Option<[F; N]>,
}

fn nonzero<F: FiniteField>(rng: &mut StdRng) -> F {
    loop {
        let c = F::random(rng);
        if c != F::zero() {
            return c;
        }
    }
}

fn product<const N: usize>(a: usize, b: usize) -> Monomial<N> {
    let mut exponents = [0u32; N];
    exponents[a] += 1;
    exponents[b] += 1;
    Monomial::new(&exponents)
}

/// The bilinear system `spec` describes, over `F`, in `N` variables.
///
/// Draws come from one `StdRng` seeded with [`BilinearSpec::seed`], in this order: the planted
/// point; then per generator, the support mask, the `A_i` coefficients, `b_i`, `c_i`, the
/// perturbation monomials and their coefficients, and `d_i` (affine and unplanted only). The
/// order is part of the family's definition: changing it changes every instance.
///
/// # Panics
/// If either block is empty, `support_per_mille > 1000`, `planted` without `affine`, or
/// `perturbation` exceeds the same-block products available.
pub fn bilinear<const N: usize, F: FiniteField>(spec: &BilinearSpec) -> BilinearSystem<N, F> {
    let k = spec.x_variables;
    assert!(0 < k && k < N, "both blocks must be nonempty");
    assert!(spec.support_per_mille <= 1000);
    assert!(
        !spec.planted || spec.affine,
        "a homogeneous system has no constant to plant with"
    );
    let same_block: Vec<(usize, usize)> = (0..N)
        .flat_map(|a| (a..N).map(move |b| (a, b)))
        .filter(|&(a, b)| (a < k) == (b < k))
        .collect();
    assert!(
        spec.perturbation <= same_block.len(),
        "only {} same-block products exist",
        same_block.len()
    );

    let mut rng = StdRng::seed_from_u64(spec.seed);
    let point: Option<[F; N]> = spec.planted.then(|| {
        let mut p = [F::zero(); N];
        for v in &mut p {
            *v = F::random(&mut rng);
        }
        p
    });

    let generators = (0..spec.equations)
        .map(|_| {
            let mut keep: Vec<(usize, usize)> = (0..k)
                .flat_map(|a| (k..N).map(move |b| (a, b)))
                .filter(|_| rng.gen_range(0..1000) < spec.support_per_mille)
                .collect();
            if keep.is_empty() {
                let a = rng.gen_range(0..k);
                let b = rng.gen_range(k..N);
                keep.push((a, b));
            }
            let mut terms: Vec<(Monomial<N>, F)> = keep
                .into_iter()
                .map(|(a, b)| (product(a, b), nonzero(&mut rng)))
                .collect();
            if spec.affine {
                for v in 0..N {
                    terms.push((Monomial::univariate(v, 1), nonzero(&mut rng)));
                }
            }
            let mut pool = same_block.clone();
            for _ in 0..spec.perturbation {
                let (a, b) = pool.swap_remove(rng.gen_range(0..pool.len()));
                terms.push((product(a, b), nonzero(&mut rng)));
            }
            if spec.affine {
                let constant = match &point {
                    Some(p) => F::zero() - MultivariatePolynomial::<N, F>::new(&terms).eval(p),
                    None => nonzero(&mut rng),
                };
                terms.push((Monomial::one(), constant));
            }
            MultivariatePolynomial::new(&terms)
        })
        .collect();

    BilinearSystem { generators, point }
}

#[cfg(test)]
mod tests {
    use super::{bilinear, BilinearSpec};
    use crate::{
        fields::{Zp2147483647, Zp31, Zp32003},
        grobner::planning::{multigrading, BlockSplit},
        identities::Zero,
    };

    fn spec(x_variables: usize, equations: usize) -> BilinearSpec {
        BilinearSpec {
            x_variables,
            equations,
            affine: true,
            support_per_mille: 1000,
            perturbation: 0,
            planted: false,
            seed: 7,
        }
    }

    #[test]
    fn test_affine_full_support_is_bilinear_with_exact_term_counts() {
        let s = spec(2, 5);
        let system = bilinear::<5, Zp32003>(&s);
        assert!(system.point.is_none());
        let split = BlockSplit::two_blocks(5, 2).unwrap();
        let g = multigrading(&system.generators, &split).unwrap();
        assert!(g.within(&[1, 1]));
        assert!(!g.is_multihomogeneous());
        for p in &g.generators {
            // 2 × 3 products, 5 linear terms, 1 nonzero constant: every coefficient is nonzero.
            assert_eq!((p.top_terms, p.lower_terms), (6, 6));
        }
        assert_eq!(g.generators.len(), 5);
    }

    #[test]
    fn test_homogeneous_is_bihomogeneous_of_one_one() {
        let s = BilinearSpec {
            affine: false,
            support_per_mille: 500,
            ..spec(3, 4)
        };
        let system = bilinear::<6, Zp31>(&s);
        let split = BlockSplit::two_blocks(6, 3).unwrap();
        let g = multigrading(&system.generators, &split).unwrap();
        assert!(g.all_homogeneous_of(&[1, 1]));
        assert_eq!(g.generators.len(), 4);
    }

    #[test]
    fn test_sparse_support_keeps_a_bilinear_term() {
        let s = BilinearSpec {
            support_per_mille: 0,
            ..spec(1, 3)
        };
        let system = bilinear::<3, Zp32003>(&s);
        let split = BlockSplit::two_blocks(3, 1).unwrap();
        let g = multigrading(&system.generators, &split).unwrap();
        assert!(g.generators.iter().all(|p| p.top_terms == 1));
    }

    #[test]
    fn test_planted_system_vanishes_at_its_point() {
        let s = BilinearSpec {
            planted: true,
            support_per_mille: 600,
            ..spec(3, 7)
        };
        let system = bilinear::<7, Zp2147483647>(&s);
        let point = system.point.expect("planted");
        for p in &system.generators {
            assert_eq!(p.eval(&point), Zp2147483647::zero());
        }
    }

    /// The control differs from its base only by the perturbation, and the verifier refuses every
    /// perturbed generator.
    #[test]
    fn test_perturbed_control_is_refused_by_the_verifier() {
        let s = BilinearSpec {
            perturbation: 2,
            ..spec(3, 6)
        };
        let system = bilinear::<6, Zp32003>(&s);
        let split = BlockSplit::two_blocks(6, 3).unwrap();
        let g = multigrading(&system.generators, &split).unwrap();
        assert_eq!(g.violations(&[1, 1]), (0..6).collect::<Vec<_>>());
        for p in &g.generators {
            assert_eq!(p.bound.iter().max(), Some(&2));
        }
    }

    #[test]
    fn test_seed_determines_the_system() {
        let a = bilinear::<4, Zp32003>(&spec(2, 4)).generators;
        let b = bilinear::<4, Zp32003>(&spec(2, 4)).generators;
        let c = bilinear::<4, Zp32003>(&BilinearSpec {
            seed: 8,
            ..spec(2, 4)
        })
        .generators;
        assert_eq!(a, b);
        assert_ne!(a, c);
    }

    #[test]
    #[should_panic(expected = "no constant to plant")]
    fn test_homogeneous_cannot_be_planted() {
        let s = BilinearSpec {
            affine: false,
            planted: true,
            ..spec(1, 2)
        };
        let _ = bilinear::<2, Zp31>(&s);
    }
}
