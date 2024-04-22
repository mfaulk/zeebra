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
    let (lc_p, lm_p): (F, Monomial<N>) = q.leading_term(order).into();
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
        MultivariatePolynomial::new(&[(F::one(), monomial)]) * p.scale(&lc_p)
    };

    // (x_gamma / lm(q)) * (1 / lc_q) * q
    let right_part: MultivariatePolynomial<N, F> = {
        let mut exponents = [0u32; N];
        for i in 0..N {
            exponents[i] = x_gamma.exponents()[i] - lm_q.exponents()[i];
        }
        let monomial = Monomial::new(&exponents);
        MultivariatePolynomial::new(&[(F::one(), monomial)]) * q.scale(&lc_q)
    };

    left_part - right_part
}

#[cfg(test)]
mod tests {
    // TODO: S(f,g) = -S(g,f)
}
