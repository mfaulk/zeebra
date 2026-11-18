//! Berlekamp–Massey is the extended Euclidean algorithm on `(x^{2n}, S)` halted at degree `n`
//! (Dornstetter 1987), so above a measured crossover it runs as [`partial_bezout`]'s half-GCD
//! route. `docs/research/certified-wiedemann.md` § Reconstruction has the measurement.

use super::gcd::{partial_bezout_half_with_base_case, HALF_GCD_BASE_CASE};
use crate::{FiniteField, Polynomial, UnivariatePolynomial};

/// Smallest `n` (half the sequence length) from which [`berlekamp_massey`] takes half-GCD, for a
/// field element of at most 4 bytes.
const EUCLID_CROSSOVER_32_BIT: usize = 6144;
/// As [`EUCLID_CROSSOVER_32_BIT`], for 5 to 8 bytes.
const EUCLID_CROSSOVER_64_BIT: usize = 3072;
/// As [`EUCLID_CROSSOVER_32_BIT`], for wider elements.
const EUCLID_CROSSOVER_WIDE: usize = 1536;

/// The `n` from which [`berlekamp_massey`] takes half-GCD for `F`.
pub(crate) fn berlekamp_massey_crossover<F: FiniteField>() -> usize {
    match std::mem::size_of::<F>() {
        0..=4 => EUCLID_CROSSOVER_32_BIT,
        5..=8 => EUCLID_CROSSOVER_64_BIT,
        _ => EUCLID_CROSSOVER_WIDE,
    }
}

/// The monic minimal recurrence polynomial of `sequence`, in ascending powers, including its
/// nilpotent factors: the `p` of least degree `L` with `sum_i p[i] s[k + i] = 0` for every
/// `k + L < len`.
///
/// Classical Berlekamp–Massey, or half-GCD once an even-length sequence's half reaches
/// `berlekamp_massey_crossover`. Both return the same polynomial.
pub fn berlekamp_massey<F: FiniteField>(sequence: &[F]) -> Vec<F> {
    if sequence.len().is_multiple_of(2) && sequence.len() / 2 >= berlekamp_massey_crossover::<F>() {
        if let Some(p) = berlekamp_massey_euclid_unstable(sequence) {
            return p;
        }
    }
    berlekamp_massey_classical_unstable(sequence)
}

/// [`berlekamp_massey`] by the classical recurrence at every size.
pub fn berlekamp_massey_classical_unstable<F: FiniteField>(sequence: &[F]) -> Vec<F> {
    let mut c = vec![F::one()];
    let mut b = c.clone();
    let mut degree = 0;
    let mut shift = 1;
    let mut previous = F::one();
    for (n, value) in sequence.iter().enumerate() {
        let discrepancy = *value
            + (1..=degree)
                .map(|i| c.get(i).copied().unwrap_or(F::zero()) * sequence[n - i])
                .fold(F::zero(), |a, b| a + b);
        if discrepancy.is_zero() {
            shift += 1;
            continue;
        }
        let saved = c.clone();
        let factor = discrepancy / previous;
        c.resize(c.len().max(b.len() + shift), F::zero());
        for (i, coefficient) in b.iter().enumerate() {
            c[i + shift] -= factor * *coefficient;
        }
        if 2 * degree <= n {
            degree = n + 1 - degree;
            b = saved;
            previous = discrepancy;
            shift = 1;
        } else {
            shift += 1;
        }
    }
    c.resize(degree + 1, F::zero());
    c.reverse();
    c
}

/// [`berlekamp_massey`] by half-GCD at every size, on an even-length sequence; `None` when the
/// sequence's linear complexity exceeds half its length, where the minimal recurrence is not
/// unique and the classical route's choice is the one [`berlekamp_massey`] reports.
///
/// # Panics
/// Panics if `sequence` has odd length.
pub fn berlekamp_massey_euclid_unstable<F: FiniteField>(sequence: &[F]) -> Option<Vec<F>> {
    berlekamp_massey_euclid_with_base_case(sequence, HALF_GCD_BASE_CASE)
}

pub(crate) fn berlekamp_massey_euclid_with_base_case<F: FiniteField>(
    sequence: &[F],
    base_case: i64,
) -> Option<Vec<F>> {
    assert!(
        sequence.len().is_multiple_of(2),
        "the Euclidean route needs an even-length sequence"
    );
    let length = sequence.len();
    let half = length / 2;
    let mut power = vec![F::zero(); length + 1];
    power[length] = F::one();
    let s = UnivariatePolynomial::new(sequence);

    // v * S = r mod x^{2n} with deg v <= n and deg r < n. When v(0) is a unit, v / v(0) is the
    // connection polynomial C, and the complexity is max(deg C, deg r + 1): a nilpotent factor x^k
    // of the recurrence shows up as deg C falling short of L by k, with r carrying the difference.
    // A zero v(0) happens exactly when the complexity exceeds n.
    let (v, r) = partial_bezout_half_with_base_case(
        &UnivariatePolynomial::new(&power),
        &s,
        half as u32,
        base_case,
    );
    let lowest = v.coefficients().first().copied().unwrap_or(F::zero());
    if lowest.is_zero() {
        return None;
    }
    let scale = lowest.inverse();
    let degree_of = |p: &UnivariatePolynomial<F>| {
        if p.is_zero() {
            None
        } else {
            Some(p.degree() as usize)
        }
    };
    let complexity = degree_of(&v)
        .unwrap_or(0)
        .max(degree_of(&r).map_or(0, |d| d + 1));

    // Ascending p is C reversed at length L + 1: p[i] = C[L - i].
    let mut p = vec![F::zero(); complexity + 1];
    for (j, coefficient) in v.coefficients().iter().enumerate() {
        p[complexity - j] = *coefficient * scale;
    }
    Some(p)
}

#[cfg(test)]
mod tests {
    use super::{
        berlekamp_massey, berlekamp_massey_classical_unstable, berlekamp_massey_crossover,
        berlekamp_massey_euclid_unstable, berlekamp_massey_euclid_with_base_case,
    };
    use crate::{
        fields::{Bn254Fr, KoalaBear, PrimeFieldElement64, Zp13, Zp18446744069414584321},
        FiniteField, One, Polynomial, UnivariatePolynomial, Zero,
    };
    use rand::{prelude::StdRng, SeedableRng};

    type Gf2 = PrimeFieldElement64<2>;
    type Gf3 = PrimeFieldElement64<3>;

    /// The Euclidean route reports the classical polynomial whenever its complexity is at most
    /// half the length, and `None` exactly when it is not.
    fn assert_routes_agree<F: FiniteField>(sequence: &[F], base_case: i64) {
        let classical = berlekamp_massey_classical_unstable(sequence);
        let euclid = berlekamp_massey_euclid_with_base_case(sequence, base_case);
        if 2 * (classical.len() - 1) <= sequence.len() {
            assert_eq!(
                euclid.as_ref(),
                Some(&classical),
                "routes disagree on {sequence:?}"
            );
        } else {
            assert_eq!(euclid, None, "complexity above n/2 on {sequence:?}");
        }
        assert_eq!(berlekamp_massey(sequence), classical);
    }

    /// `2n` terms of the recurrence `p` (ascending, monic) from random initial values.
    fn sequence_of<F: FiniteField>(p: &[F], length: usize, rng: &mut StdRng) -> Vec<F> {
        let order = p.len() - 1;
        let mut values: Vec<F> = (0..order.min(length)).map(|_| F::random(rng)).collect();
        while values.len() < length {
            let k = values.len() - order;
            values.push(
                -(0..order)
                    .map(|i| p[i] * values[k + i])
                    .fold(F::zero(), |a, b| a + b),
            );
        }
        values
    }

    // A finite impulse retains its nilpotent factor instead of collapsing to a squarefree
    // relation, and an all-zero sequence has the constant recurrence.
    #[test]
    fn recurrence_preserves_nilpotents_and_zero_sequences() {
        type F = Zp13;
        let sequence = [F::zero(), F::one(), F::zero(), F::zero()];
        let expected = vec![F::zero(), F::zero(), F::one()];
        assert_eq!(berlekamp_massey_classical_unstable(&sequence), expected);
        assert_eq!(berlekamp_massey_euclid_unstable(&sequence), Some(expected));
        assert_eq!(
            berlekamp_massey_classical_unstable(&[F::zero(); 6]),
            vec![F::one()]
        );
        assert_eq!(
            berlekamp_massey_euclid_unstable(&[F::zero(); 6]),
            Some(vec![F::one()])
        );
        assert_eq!(
            berlekamp_massey_euclid_unstable::<F>(&[]),
            Some(vec![F::one()])
        );
    }

    // Every term of a known order-three recurrence agrees with the recovered ascending polynomial,
    // on both routes.
    #[test]
    fn recurrence_matches_a_known_polynomial() {
        type F = Zp13;
        let p = [F::new(2), F::new(3), F::new(4), F::one()];
        let mut values = vec![F::new(5), F::new(7), F::new(11)];
        for k in 3..12 {
            values.push(
                -(0..3)
                    .map(|i| p[i] * values[k - 3 + i])
                    .fold(F::zero(), |a, b| a + b),
            );
        }
        assert_eq!(berlekamp_massey_classical_unstable(&values), p);
        assert_eq!(berlekamp_massey_euclid_unstable(&values), Some(p.to_vec()));
    }

    // Every even-length GF(2) sequence up to length 12, and every GF(3) one up to length 6, gets
    // the classical answer from the Euclidean route at base cases that recurse and that do not.
    #[test]
    fn test_routes_agree_exhaustively_over_small_fields() {
        for length in (0..=12).step_by(2) {
            for bits in 0..1u64 << length {
                let sequence: Vec<Gf2> = (0..length).map(|i| Gf2::new((bits >> i) & 1)).collect();
                for base_case in [1, 2, 3, 64] {
                    assert_routes_agree(&sequence, base_case);
                }
            }
        }
        for length in (0..=6).step_by(2) {
            for mut index in 0..3u64.pow(length as u32) {
                let sequence: Vec<Gf3> = (0..length)
                    .map(|_| {
                        let digit = index % 3;
                        index /= 3;
                        Gf3::new(digit)
                    })
                    .collect();
                for base_case in [1, 2, 64] {
                    assert_routes_agree(&sequence, base_case);
                }
            }
        }
    }

    // Sequences from planted recurrences, some with a nilpotent factor x^k and some of full
    // complexity n, agree across three element widths at sizes where half-GCD recurses.
    #[test]
    fn test_routes_agree_on_planted_recurrences() {
        check_planted::<KoalaBear>();
        check_planted::<Zp18446744069414584321>();
        check_planted::<Bn254Fr>();
    }

    fn check_planted<F: FiniteField>() {
        let mut rng = StdRng::seed_from_u64(0x0008_15b3);
        for (n, order, nilpotent) in [
            (70, 70, 0),
            (150, 149, 0),
            (150, 90, 7),
            (260, 260, 0),
            (260, 200, 1),
            (300, 3, 0),
        ] {
            let tail = UnivariatePolynomial::<F>::rand((order - nilpotent) as u64, &mut rng);
            let lead = tail.coefficients().last().copied().unwrap();
            let mut p = vec![F::zero(); nilpotent];
            p.extend(tail.scale(&lead.inverse()).coefficients());
            let sequence = sequence_of(&p, 2 * n, &mut rng);
            assert_routes_agree(&sequence, 64);
            assert_eq!(berlekamp_massey_classical_unstable(&sequence), p, "n = {n}");
            // And a random sequence, whose complexity is n or close to it.
            let random: Vec<F> = (0..2 * n).map(|_| F::random(&mut rng)).collect();
            assert_routes_agree(&random, 64);
        }
    }

    // The public entry point agrees with the classical recurrence either side of its dispatch.
    #[test]
    fn test_berlekamp_massey_agrees_across_its_dispatch() {
        type F = Bn254Fr;
        let crossover = berlekamp_massey_crossover::<F>();
        let mut rng = StdRng::seed_from_u64(0x815_d15);
        for n in [crossover - 1, crossover] {
            let random: Vec<F> = (0..2 * n).map(|_| F::random(&mut rng)).collect();
            assert_eq!(
                berlekamp_massey(&random),
                berlekamp_massey_classical_unstable(&random)
            );
        }
    }
}
