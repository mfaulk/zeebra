// `m33-basis-v1` (plan §11.3): the digest `tools/external/basis_digest.py` computes from any solver's
// text, taken here from the basis itself so the timed region renders nothing. Elements must be monic,
// as a reduced basis is; the Python side normalizes and would expose one that is not.

use std::io::Write;
use zeebra::{util::sha256_hex, FiniteField, MultivariatePolynomial};

pub fn basis_digest<const N: usize, F: FiniteField>(
    basis: &[MultivariatePolynomial<N, F>],
    modulus: u128,
) -> String {
    let mut elements: Vec<Vec<u8>> = basis
        .iter()
        .filter(|p| !p.is_zero())
        .map(|p| {
            let mut terms: Vec<_> = p.terms().iter().collect();
            terms.sort_unstable_by(|a, b| a.0.exponents().cmp(b.0.exponents()));
            let mut bytes = Vec::with_capacity(terms.len() * (4 * N + 12));
            for (monomial, coefficient) in terms {
                for e in monomial.exponents() {
                    bytes.extend_from_slice(&e.to_le_bytes());
                }
                write!(bytes, "{coefficient};").unwrap();
            }
            bytes
        })
        .collect();
    elements.sort_unstable();
    let mut data = format!("m33-basis-v1 {modulus} {N}\n").into_bytes();
    for element in &elements {
        data.extend_from_slice(&(element.len() as u32).to_le_bytes());
        data.extend_from_slice(element);
    }
    sha256_hex(&data)
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
            "732b64fcd26daed997c49a9b032cd303f0c8d3e76264275156efa161c9028e7c"
        );
    }
}
