//! Standard polynomial system families, for benchmarking and for cross-checking implementations.
//!
//! These are the families conventionally used to compare Gröbner basis engines. Having them in
//! the library rather than in `benches/` lets the benchmarks and the tests that compare the
//! optimized engine against the reference one work from a single definition.
//!
//! Both families are zero-dimensional, and both are stated explicitly below so a reader can check
//! the formulation rather than trust it.

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

#[cfg(test)]
mod tests {
    use super::{cyclic, katsura};
    use crate::{fields::Zp2147483647, MultivariatePolynomial};

    type F = Zp2147483647;

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

    /// No generator is zero or constant, which would make a family trivially degenerate.
    #[test]
    fn test_generators_are_nontrivial() {
        for p in cyclic::<5, F>().iter().chain(katsura::<5, F>().iter()) {
            assert!(!p.is_zero());
            assert!(!p.is_constant(), "{} is constant", p);
        }
    }
}
