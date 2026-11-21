// `m33-basis-v1` (plan §11.3): the digest `tools/external/basis_digest.py` computes from any solver's
// text, taken here from the basis itself so the timed region renders nothing. Elements must be monic,
// as a reduced basis is; the Python side normalizes and would expose one that is not.

use std::fmt::Write;
use zeebra::{util::sha256_hex, FiniteField, MultivariatePolynomial};

pub fn basis_digest<const N: usize, F: FiniteField>(
    basis: &[MultivariatePolynomial<N, F>],
    modulus: u128,
) -> String {
    let mut lines: Vec<String> = basis
        .iter()
        .filter(|p| !p.is_zero())
        .map(|p| {
            let mut terms: Vec<_> = p.terms().iter().collect();
            terms.sort_unstable_by(|a, b| a.0.exponents().cmp(b.0.exponents()));
            let mut line = String::new();
            for (i, (monomial, coefficient)) in terms.iter().enumerate() {
                if i > 0 {
                    line.push(' ');
                }
                for (j, e) in monomial.exponents().iter().enumerate() {
                    if j > 0 {
                        line.push(',');
                    }
                    write!(line, "{e}").unwrap();
                }
                write!(line, ":{coefficient}").unwrap();
            }
            line
        })
        .collect();
    lines.sort_unstable();
    sha256_hex(format!("m33-basis-v1 {modulus} {N}\n{}", lines.join("\n")).as_bytes())
}

#[cfg(test)]
mod basis_digest_tests {
    use super::basis_digest;
    use zeebra::{fields::Zp32003, MultivariatePolynomial};

    /// The digest equals `basis_digest.py`'s on the same basis, given in a different element order.
    #[test]
    fn matches_the_python_digest() {
        let basis: Vec<MultivariatePolynomial<2, Zp32003>> = ["x2^2+32002", "x1*x2+2", "x1^2+3*x2"]
            .iter()
            .map(|s| MultivariatePolynomial::parse(s, ["x1", "x2"]).unwrap())
            .collect();
        assert_eq!(
            basis_digest(&basis, 32003),
            "58f41dc0cc2e9a8f7be29d3926990116044001f97e05066d0ed0065842eaf754"
        );
    }
}
