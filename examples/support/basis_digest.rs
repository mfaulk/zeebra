// `m33-basis-v1` (plan §11.3): the digest `tools/external/basis_digest.py` computes from any solver's
// text, taken here from the basis itself so the timed region renders nothing. Elements must be monic,
// as a reduced basis is; the Python side normalizes and would expose one that is not.

use zeebra::{util::sha256_hex, FiniteField, MultivariatePolynomial};

pub fn basis_digest<const N: usize, F: FiniteField>(
    basis: &[MultivariatePolynomial<N, F>],
    modulus: u128,
) -> String {
    let mut elements: Vec<Vec<(&[u32], u128)>> = basis
        .iter()
        .filter(|p| !p.is_zero())
        .map(|p| {
            let mut terms: Vec<_> = p
                .terms()
                .iter()
                .map(|(m, c)| {
                    (
                        m.exponents(),
                        c.to_string().parse().expect("canonical residue"),
                    )
                })
                .collect();
            terms.sort_unstable();
            terms
        })
        .collect();
    elements.sort_unstable();
    let mut text = format!("m33-basis-v1 {modulus} {N}");
    for element in &elements {
        text.push('\n');
        for (i, (exponents, coefficient)) in element.iter().enumerate() {
            if i > 0 {
                text.push(' ');
            }
            for (j, e) in exponents.iter().enumerate() {
                if j > 0 {
                    text.push(',');
                }
                text.push_str(&e.to_string());
            }
            text.push(':');
            text.push_str(&coefficient.to_string());
        }
    }
    sha256_hex(text.as_bytes())
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
