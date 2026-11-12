//! Canonical mathematical benchmark families shared by tests, solvers and measurements.
//! Dimension and degeneracy depend on the family and field; a square system need not be finite.

use crate::{FiniteField, Monomial, MultivariatePolynomial};

/// The cyclic-n roots system, in n variables.
///
/// ```text
/// e_i = sum over j of (x_j * x_{j+1} * ... * x_{j+i-1}),  indices mod n,  for i = 1 .. n-1
/// e_n = x_0 * x_1 * ... * x_{n-1} - 1
/// ```
///
/// The first n-1 equations are the elementary symmetric polynomials in a cyclic arrangement; the
/// last fixes the product. For n = 3 this is `{x+y+z, xy+xz+yz, xyz-1}`.
pub fn cyclic<const N: usize, F: FiniteField>() -> Vec<MultivariatePolynomial<N, F>> {
    let mut system = Vec::with_capacity(N);

    for window in 1..N {
        let terms: Vec<(Monomial<N>, F)> = (0..N)
            .map(|start| {
                let mut exponents = [0u32; N];
                for offset in 0..window {
                    exponents[(start + offset) % N] += 1;
                }
                (Monomial::new(&exponents), F::one())
            })
            .collect();
        system.push(MultivariatePolynomial::new(&terms));
    }

    // The product of every variable, less one.
    let product = Monomial::new(&[1u32; N]);
    system.push(MultivariatePolynomial::new(&[
        (product, F::one()),
        (Monomial::one(), F::zero() - F::one()),
    ]));

    system
}

/// The Katsura-n system, in N = n + 1 variables.
///
/// ```text
/// for l = 0 .. n-1:   sum over i = -n..n of  u_{|i|} * u_{|l-i|}   -   u_l
/// and:                sum over i = -n..n of  u_{|i|}               -   1
/// ```
///
/// with `u_j = 0` whenever `j > n`. The final equation expands to
/// `u_0 + 2*(u_1 + ... + u_n) - 1`.
///
/// For n = 2 this is
/// `{u0^2 + 2u1^2 + 2u2^2 - u0,  2u0u1 + 2u1u2 - u1,  u0 + 2u1 + 2u2 - 1}`.
pub fn katsura<const N: usize, F: FiniteField>() -> Vec<MultivariatePolynomial<N, F>> {
    assert!(N >= 2, "Katsura needs at least two variables");
    let n = (N - 1) as i64;
    let mut system = Vec::with_capacity(N);

    for l in 0..n {
        let mut terms: Vec<(Monomial<N>, F)> = Vec::new();
        for i in -n..=n {
            let left = i.unsigned_abs() as usize;
            let right = (l - i).unsigned_abs() as usize;
            // u_j is zero beyond the last variable, so such a product contributes nothing.
            if left > n as usize || right > n as usize {
                continue;
            }
            let mut exponents = [0u32; N];
            exponents[left] += 1;
            exponents[right] += 1;
            terms.push((Monomial::new(&exponents), F::one()));
        }
        // Subtract u_l.
        let mut u_l = [0u32; N];
        u_l[l as usize] = 1;
        terms.push((Monomial::new(&u_l), F::zero() - F::one()));
        system.push(MultivariatePolynomial::new(&terms));
    }

    // sum over i = -n..n of u_{|i|} - 1, i.e. u_0 + 2*(u_1 + ... + u_n) - 1.
    let mut terms: Vec<(Monomial<N>, F)> = Vec::new();
    for i in -n..=n {
        let mut exponents = [0u32; N];
        exponents[i.unsigned_abs() as usize] = 1;
        terms.push((Monomial::new(&exponents), F::one()));
    }
    terms.push((Monomial::one(), F::zero() - F::one()));
    system.push(MultivariatePolynomial::new(&terms));

    system
}

/// A zero-dimensional system with a known solution, in which the nonlinear equations matter.
///
/// Variables are taken in consecutive pairs. Each pair (x, y) with planted values (a, b) gets
///
/// ```text
/// x^2 + y^2 - (a^2 + b^2)
/// x*y - a*b
/// ```
///
/// Both vanish at the planted point, neither follows from the other, and neither is linear, so
/// solving genuinely requires nonlinear reduction. Each pair contributes the four solutions
/// (a,b), (b,a), (-a,-b), (-b,-a), so the system is zero-dimensional with the planted point among
/// them. An odd final variable gets the linear equation `x - a`.
///
/// Planting the answer in nonlinear equations is the point: a system of `x_i - a_i` is already a
/// Gröbner basis under every order and so measures nothing.
pub fn planted<const N: usize, F: FiniteField>(point: &[F]) -> Vec<MultivariatePolynomial<N, F>> {
    assert_eq!(
        point.len(),
        N,
        "the planted point needs one value per variable"
    );
    let mut system: Vec<MultivariatePolynomial<N, F>> = Vec::with_capacity(N);

    let mut i = 0;
    while i + 1 < N {
        let (a, b) = (point[i], point[i + 1]);

        // x_i^2 + x_{i+1}^2 - (a^2 + b^2)
        let mut x_squared = [0u32; N];
        x_squared[i] = 2;
        let mut y_squared = [0u32; N];
        y_squared[i + 1] = 2;
        system.push(MultivariatePolynomial::new(&[
            (Monomial::new(&x_squared), F::one()),
            (Monomial::new(&y_squared), F::one()),
            (Monomial::one(), F::zero() - (a * a + b * b)),
        ]));

        // x_i * x_{i+1} - a*b
        let mut product = [0u32; N];
        product[i] = 1;
        product[i + 1] = 1;
        system.push(MultivariatePolynomial::new(&[
            (Monomial::new(&product), F::one()),
            (Monomial::one(), F::zero() - a * b),
        ]));

        i += 2;
    }

    // An odd trailing variable is pinned linearly, so the system stays square.
    if i < N {
        let mut exponents = [0u32; N];
        exponents[i] = 1;
        system.push(MultivariatePolynomial::new(&[
            (Monomial::new(&exponents), F::one()),
            (Monomial::one(), F::zero() - point[i]),
        ]));
    }

    system
}

/// Morgan's Eco system in N variables; equations are ordered by increasing lag.
pub fn eco<const N: usize, F: FiniteField>() -> Vec<MultivariatePolynomial<N, F>> {
    assert!(N >= 2, "Eco needs at least two variables");
    let mut system = Vec::with_capacity(N);
    for lag in 1..N {
        let mut exponent = [0; N];
        exponent[lag - 1] = 1;
        exponent[N - 1] = 1;
        let mut terms = vec![
            (Monomial::new(&exponent), F::one()),
            (Monomial::one(), -F::new(lag as u64)),
        ];
        for j in 0..N - lag - 1 {
            let mut exponent = [0; N];
            exponent[j] += 1;
            exponent[j + lag] += 1;
            exponent[N - 1] += 1;
            terms.push((Monomial::new(&exponent), F::one()));
        }
        system.push(MultivariatePolynomial::new(&terms));
    }
    let mut terms = vec![(Monomial::one(), F::one())];
    for j in 0..N - 1 {
        let mut exponent = [0; N];
        exponent[j] = 1;
        terms.push((Monomial::new(&exponent), F::one()));
    }
    system.push(MultivariatePolynomial::new(&terms));
    system
}

/// Noonburg's system with parameter 11/10, with every equation multiplied by 10.
/// Panics when N < 2 or the field characteristic divides 10.
pub fn noon<const N: usize, F: FiniteField>() -> Vec<MultivariatePolynomial<N, F>> {
    assert!(N >= 2, "Noon needs at least two variables");
    assert!(!F::new(10).is_zero(), "Noon characteristic divides 10");
    (0..N)
        .map(|i| {
            let mut linear = [0; N];
            linear[i] = 1;
            let mut terms = vec![
                (Monomial::one(), F::new(10)),
                (Monomial::new(&linear), -F::new(11)),
            ];
            for j in 0..N {
                if j != i {
                    let mut exponent = [0; N];
                    exponent[i] = 1;
                    exponent[j] = 2;
                    terms.push((Monomial::new(&exponent), F::new(10)));
                }
            }
            MultivariatePolynomial::new(&terms)
        })
        .collect()
}

/// Reimer's alternating power sums, with degrees 2 through N + 1.
pub fn reimer<const N: usize, F: FiniteField>() -> Vec<MultivariatePolynomial<N, F>> {
    assert!(N >= 2, "Reimer needs at least two variables");
    (2..=N.checked_add(1).expect("Reimer degree overflow"))
        .map(|degree| {
            let degree = u32::try_from(degree).expect("Reimer degree exceeds u32");
            let mut terms = vec![(Monomial::one(), -F::one())];
            for j in 0..N {
                let mut exponent = [0; N];
                exponent[j] = degree;
                terms.push((
                    Monomial::new(&exponent),
                    if j % 2 == 0 { F::new(2) } else { -F::new(2) },
                ));
            }
            MultivariatePolynomial::new(&terms)
        })
        .collect()
}

#[cfg(test)]
mod public_family_tests {
    use super::{eco, noon, reimer};
    use crate::{
        fields::{Zp13, Zp2},
        MultivariatePolynomial,
    };

    fn parsed<const N: usize>(
        text: &[&str],
        names: [&str; N],
    ) -> Vec<MultivariatePolynomial<N, Zp13>> {
        text.iter()
            .map(|s| MultivariatePolynomial::parse(s, names).unwrap())
            .collect()
    }

    // Eco's lag equations and closing affine equation match the published three-variable definition.
    #[test]
    fn eco_three_matches_the_independent_definition() {
        assert_eq!(
            eco::<3, Zp13>(),
            parsed(&["x*y*z+x*z-1", "y*z-2", "x+y+1"], ["x", "y", "z"])
        );
    }

    // Multiplication by 10 clears Noon's rational parameter without changing the ideal at p=13.
    #[test]
    fn noon_three_matches_the_independent_definition() {
        assert_eq!(
            noon::<3, Zp13>(),
            parsed(
                &[
                    "10*x*y^2+10*x*z^2-11*x+10",
                    "10*x^2*y+10*y*z^2-11*y+10",
                    "10*x^2*z+10*y^2*z-11*z+10"
                ],
                ["x", "y", "z"]
            )
        );
    }

    // Reimer uses alternating signs and increasing powers rather than elementary symmetric sums.
    #[test]
    fn reimer_three_matches_the_independent_definition() {
        assert_eq!(
            reimer::<3, Zp13>(),
            parsed(
                &[
                    "2*x^2-2*y^2+2*z^2-1",
                    "2*x^3-2*y^3+2*z^3-1",
                    "2*x^4-2*y^4+2*z^4-1"
                ],
                ["x", "y", "z"]
            )
        );
    }

    // The rational Noon model is rejected where clearing its denominator is not invertible.
    #[test]
    #[should_panic(expected = "characteristic divides 10")]
    fn noon_rejects_a_denominator_divisor() {
        noon::<3, Zp2>();
    }
}

#[cfg(test)]
mod tests {
    use super::{cyclic, katsura, planted};
    use rand::{prelude::StdRng, SeedableRng};

    use crate::{
        fields::Zp2147483647, grobner::f4, FiniteField, MonomialOrder, MultivariatePolynomial, Zero,
    };

    type F = Zp2147483647;

    /// Whether every variable has a positive pure power among the basis's leading monomials,
    /// which for a proper ideal is equivalent to its quotient algebra being finite-dimensional.
    fn has_a_pure_power_of_every_variable<const N: usize>(
        basis: &[MultivariatePolynomial<N, F>],
        order: MonomialOrder,
    ) -> bool {
        let leading: Vec<_> = basis.iter().map(|p| p.leading_monomial(order)).collect();
        (0..N).all(|i| {
            leading.iter().any(|m| {
                let e = m.exponents();
                e[i] > 0 && e.iter().enumerate().all(|(j, v)| j == i || *v == 0)
            })
        })
    }

    /// Cyclic-3 is the symmetric system `{x+y+z, xy+xz+yz, xyz-1}`.
    #[test]
    fn test_cyclic_3_matches_its_definition() {
        let vars = ["x", "y", "z"];
        let expected: Vec<MultivariatePolynomial<3, F>> =
            ["x + y + z", "x*y + y*z + x*z", "x*y*z - 1"]
                .iter()
                .map(|s| MultivariatePolynomial::parse(s, vars).unwrap())
                .collect();
        assert_eq!(cyclic::<3, F>(), expected);
    }

    /// Cyclic-4, written out independently.
    #[test]
    fn test_cyclic_4_matches_its_definition() {
        let vars = ["w", "x", "y", "z"];
        let expected: Vec<MultivariatePolynomial<4, F>> = [
            "w + x + y + z",
            "w*x + x*y + y*z + z*w",
            "w*x*y + x*y*z + y*z*w + z*w*x",
            "w*x*y*z - 1",
        ]
        .iter()
        .map(|s| MultivariatePolynomial::parse(s, vars).unwrap())
        .collect();
        assert_eq!(cyclic::<4, F>(), expected);
    }

    /// Katsura-2, written out independently from the formulation in the doc comment.
    #[test]
    fn test_katsura_2_matches_its_definition() {
        let vars = ["a", "b", "c"];
        let expected: Vec<MultivariatePolynomial<3, F>> = [
            "a^2 + 2*b^2 + 2*c^2 - a",
            "2*a*b + 2*b*c - b",
            "a + 2*b + 2*c - 1",
        ]
        .iter()
        .map(|s| MultivariatePolynomial::parse(s, vars).unwrap())
        .collect();
        assert_eq!(katsura::<3, F>(), expected);
    }

    /// Each family has as many equations as variables, so both are square systems.
    #[test]
    fn test_system_sizes() {
        assert_eq!(cyclic::<3, F>().len(), 3);
        assert_eq!(cyclic::<4, F>().len(), 4);
        assert_eq!(cyclic::<5, F>().len(), 5);
        assert_eq!(katsura::<3, F>().len(), 3);
        assert_eq!(katsura::<4, F>().len(), 4);
        assert_eq!(katsura::<5, F>().len(), 5);
    }

    /// The planted point is a root of every generator, so the advertised solution really solves it.
    #[test]
    fn test_planted_point_is_a_root() {
        let point: Vec<F> = [3u64, 5, 7, 11].iter().map(|v| F::new(*v)).collect();
        let system = planted::<4, F>(&point);
        for p in &system {
            assert!(
                p.eval(&point).is_zero(),
                "{} does not vanish at the planted point",
                p
            );
        }
    }

    /// The planted system is genuinely nonlinear, which is the property the benchmark needs.
    ///
    /// A system of `x_i - a_i` is already a Gröbner basis under every order, so it would measure
    /// nothing. This asserts the generators are not all linear.
    #[test]
    fn test_planted_system_is_nonlinear() {
        let point: Vec<F> = [3u64, 5, 7, 11].iter().map(|v| F::new(*v)).collect();
        let system = planted::<4, F>(&point);
        let quadratics = system
            .iter()
            .filter(|p| p.terms().keys().any(|m| m.degree() == 2))
            .count();
        assert_eq!(
            quadratics, 4,
            "every generator of an even-sized system is quadratic"
        );
    }

    /// An odd variable count still yields one equation per variable.
    #[test]
    fn test_planted_system_is_square_for_an_odd_variable_count() {
        let point: Vec<F> = [3u64, 5, 7].iter().map(|v| F::new(*v)).collect();
        let system = planted::<3, F>(&point);
        assert_eq!(system.len(), 3);
        for p in &system {
            assert!(p.eval(&point).is_zero(), "{} does not vanish", p);
        }
    }

    /// The planted point is recovered by solving, so the system is zero-dimensional as claimed.
    #[test]
    fn test_planted_point_is_among_the_solutions() {
        let point: Vec<F> = [3u64, 5].iter().map(|v| F::new(*v)).collect();
        let system = planted::<2, F>(&point);
        let mut rng = StdRng::seed_from_u64(7);
        let solutions = crate::grobner::solve(&system, &mut rng);
        assert!(
            solutions.contains(&[point[0], point[1]]),
            "the planted point is not among {:?}",
            solutions
        );
    }

    /// Cyclic-4 is positive-dimensional, which the module doc comment used to deny.
    ///
    /// Asserted from the leading monomials of its grevlex basis rather than cited: cyclic-n is
    /// zero-dimensional only for squarefree n, and 4 is the first exception. Anything that needs a
    /// finite quotient algebra, FGLM included, must reject this instance rather than assume it.
    #[test]
    fn test_cyclic_4_is_positive_dimensional() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let basis = f4(&cyclic::<4, F>(), order).expect("within limits");
        assert!(
            !has_a_pure_power_of_every_variable(&basis, order),
            "cyclic-4's leading-term ideal contains a pure power of every variable, so it would \
             be zero-dimensional after all"
        );
    }

    /// Cyclic-3, cyclic-5, and katsura-3 through -5 are zero-dimensional.
    ///
    /// The complement of the test above: the families are not uniformly one thing or the other,
    /// so both halves of the claim are checked.
    #[test]
    fn test_the_zero_dimensional_instances_are_zero_dimensional() {
        let order = MonomialOrder::GradedReverseLexicographic;
        macro_rules! assert_zero_dimensional {
            ($system:expr, $name:literal) => {{
                let basis = f4(&$system, order).expect("within limits");
                assert!(
                    has_a_pure_power_of_every_variable(&basis, order),
                    "{} has no pure power of some variable, so it is not zero-dimensional",
                    $name
                );
            }};
        }
        assert_zero_dimensional!(cyclic::<3, F>(), "cyclic-3");
        assert_zero_dimensional!(cyclic::<5, F>(), "cyclic-5");
        assert_zero_dimensional!(katsura::<3, F>(), "katsura-3");
        assert_zero_dimensional!(katsura::<4, F>(), "katsura-4");
        assert_zero_dimensional!(katsura::<5, F>(), "katsura-5");
    }

    /// No generator is zero or constant, which would make a family trivially degenerate.
    #[test]
    fn test_generators_are_nontrivial() {
        for p in cyclic::<5, F>().iter().chain(katsura::<5, F>().iter()) {
            assert!(!p.is_zero());
            assert!(!p.is_constant(), "{} is constant", p);
        }
    }
}
