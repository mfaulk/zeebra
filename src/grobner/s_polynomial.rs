use crate::{poly::MonomialOrder, FiniteField, Monomial, MultivariatePolynomial};

/// Computes the S-polynomial of two polynomials.
///
/// S(f,g) = x_gamma / lt(f) * f - x_gamma / lt(g) * g, where x_gamma = lcm(lm(f), lm(g)).
pub fn s_polynomial<const N: usize, F: FiniteField>(
    p: &MultivariatePolynomial<N, F>,
    q: &MultivariatePolynomial<N, F>,
    order: MonomialOrder,
) -> MultivariatePolynomial<N, F> {
    // Leading coefficient and monomial of p and q.
    let (lc_p, lm_p): (F, Monomial<N>) = p.leading_term(order).into();
    let (lc_q, lm_q): (F, Monomial<N>) = q.leading_term(order).into();

    // x_gamma = lcm(lm(p), lm(q))
    let x_gamma = Monomial::lcm(&lm_p, &lm_q);

    // (x_gamma / lm(p)) * (1 / lc_p) * p
    let left_part: MultivariatePolynomial<N, F> = {
        let mut exponents = [0u32; N];
        for i in 0..N {
            exponents[i] = x_gamma.exponents()[i] - lm_p.exponents()[i];
        }
        let monomial = Monomial::new(&exponents);
        MultivariatePolynomial::new(&[(F::one(), monomial)]) * p.scale(&lc_p.inverse())
    };

    // (x_gamma / lm(q)) * (1 / lc_q) * q
    let right_part: MultivariatePolynomial<N, F> = {
        let mut exponents = [0u32; N];
        for i in 0..N {
            exponents[i] = x_gamma.exponents()[i] - lm_q.exponents()[i];
        }
        let monomial = Monomial::new(&exponents);
        MultivariatePolynomial::new(&[(F::one(), monomial)]) * q.scale(&lc_q.inverse())
    };

    left_part - right_part
}

#[cfg(test)]
mod tests {
    use crate::{
        fields::Zp13, grobner::s_polynomial::s_polynomial, poly::MonomialOrder,
        MultivariatePolynomial,
    };

    type F = Zp13;
    const VARS: [&str; 3] = ["x", "y", "z"];
    const ORDER: MonomialOrder = MonomialOrder::Lexicographic;

    fn parse(s: &str) -> MultivariatePolynomial<3, F> {
        MultivariatePolynomial::parse(s, VARS).unwrap()
    }

    /// S(f,g) multiplies each operand by its own cofactor x^gamma / LT, cancelling both leading
    /// terms.
    #[test]
    fn test_s_polynomial_cancels_the_leading_terms() {
        // LM(f) = x^2, LM(g) = x, so x^gamma = x^2 and S = f - x*g.
        let f = parse("x^2 + y^2 - 1");
        let g = parse("x - y");
        assert_eq!(s_polynomial(&f, &g, ORDER), parse("x*y + y^2 - 1"));
    }

    /// Each operand is divided by its leading coefficient, not multiplied by it.
    #[test]
    fn test_s_polynomial_divides_by_the_leading_coefficient() {
        // Over GF(13): 1/2 = 7 and 1/3 = 9, so
        //   S(2x^2 + y, 3x + 1) = 7*(2x^2 + y) - 9x*(3x + 1) = (x^2 + 7y) - (x^2 + 9x) = 4x + 7y.
        let f = parse("2*x^2 + y");
        let g = parse("3*x + 1");
        assert_eq!(s_polynomial(&f, &g, ORDER), parse("4*x + 7*y"));
    }

    /// Swapping the operands negates the result.
    #[test]
    fn test_s_polynomial_is_antisymmetric() {
        let pairs = [
            ("x^2 + y^2 - 1", "x - y"),
            ("2*x^2 + y", "3*x + 1"),
            ("x*y*z - 1", "x*y - z"),
            ("x^3 - 2*x*y", "x^2*y - 2*y^2 + x"),
        ];
        for (a, b) in pairs {
            let (f, g) = (parse(a), parse(b));
            let forward = s_polynomial(&f, &g, ORDER);
            let backward = s_polynomial(&g, &f, ORDER);
            assert_eq!(forward, -backward, "S({}, {})", a, b);
        }
    }

    /// A polynomial against itself cancels completely.
    #[test]
    fn test_s_polynomial_with_itself_is_zero() {
        for s in ["x^2 + y^2 - 1", "2*x^2 + y", "x*y*z - 1"] {
            let f = parse(s);
            assert!(s_polynomial(&f, &f, ORDER).is_zero(), "S({0}, {0})", s);
        }
    }

    /// The result's leading monomial is strictly below x^gamma, since x^gamma cancels.
    #[test]
    fn test_s_polynomial_drops_below_the_lcm() {
        use crate::Monomial;
        let pairs = [("x^2 + y^2 - 1", "x - y"), ("x*y*z - 1", "x*y - z")];
        for (a, b) in pairs {
            let (f, g) = (parse(a), parse(b));
            let x_gamma = Monomial::lcm(&f.leading_monomial(ORDER), &g.leading_monomial(ORDER));
            let s = s_polynomial(&f, &g, ORDER);
            assert!(!s.is_zero());
            assert_eq!(
                ORDER.cmp(&s.leading_monomial(ORDER), &x_gamma),
                std::cmp::Ordering::Less,
                "S({}, {}) = {} did not drop below the lcm",
                a,
                b,
                s
            );
        }
    }
}
