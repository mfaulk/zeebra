//! Karatsuba multiplication of dense univariate coefficient slices.
//!
//! The call contract, written for the multiplication dispatcher of #124 rather than for a direct
//! user: [`multiply_karatsuba`] takes both operands' coefficients in ascending degree order and
//! returns exactly `a.len() + b.len() - 1` of them, or an empty `Vec` when either input is empty.
//! It does **not** trim high-order zeros — it cannot know the caller's canonical form — so a
//! dispatcher reproduces the schoolbook `Mul`'s degree by handing the `Vec` to
//! `DensePolynomial::new`, which trims. Nothing in the recursion constructs a `DensePolynomial`,
//! and the whole recursion runs on two allocations: the output and one scratch arena carved by
//! slicing.
//!
//! The recursion stops at a schoolbook base case of [`karatsuba_base_case`] coefficients, which is
//! measured per field element width and not derived, and which is **not one number**: 48
//! coefficients at 4 bytes an element, 16 at 8, and 4 above that. A 4-byte multiply is cheap and
//! its schoolbook inner loop vectorizes, so Karatsuba's extra additions have to be amortized over
//! a much larger leaf than they do over a 254-bit field. Below the base case the output is
//! bit-identical to the schoolbook `Mul`'s because it *is* schoolbook. See
//! `docs/research/fast-univariate.md` §4.1 and `examples/karatsuba_crossover.rs`.

use crate::FiniteField;

/// Operand length below which the recursion multiplies schoolbook, for an element of at most 4
/// bytes. Measured, not derived; see the module comment.
pub(crate) const KARATSUBA_BASE_CASE_32_BIT: usize = 48;

/// The same, for an element of 5 to 8 bytes.
pub(crate) const KARATSUBA_BASE_CASE_64_BIT: usize = 16;

/// The same, for an element wider than 8 bytes. Measured over BN254 `Fr`, where an element is 32
/// bytes; the 16-byte `PrimeFieldElement128` is not separately measured and takes this figure.
pub(crate) const KARATSUBA_BASE_CASE_WIDE: usize = 4;

/// The measured schoolbook base case for `F`, the single source of truth for a dispatcher.
///
/// Three tiers rather than two, because the measurement found three: the base case falls by 12x
/// across the widths this crate uses, in the direction the cost of one field multiplication
/// predicts.
pub(crate) fn karatsuba_base_case<F: FiniteField>() -> usize {
    match std::mem::size_of::<F>() {
        0..=4 => KARATSUBA_BASE_CASE_32_BIT,
        5..=8 => KARATSUBA_BASE_CASE_64_BIT,
        _ => KARATSUBA_BASE_CASE_WIDE,
    }
}

/// The product of two coefficient slices, in ascending degree order. See the module comment for
/// the contract.
///
/// `allow(dead_code)`: this is the entry point #124's multiplication dispatcher consumes, and
/// nothing in the crate calls it until that lands. It is exercised by this module's tests and,
/// through `karatsuba_unstable`, by `examples/karatsuba_crossover.rs`.
#[allow(dead_code)]
pub(crate) fn multiply_karatsuba<F: FiniteField>(a: &[F], b: &[F]) -> Vec<F> {
    multiply_with_base_case(a, b, karatsuba_base_case::<F>())
}

/// [`multiply_karatsuba`] with the base case chosen by the caller, so that the crossover can be
/// swept. `usize::MAX` is plain schoolbook, which is what the A/B measures against.
#[doc(hidden)]
pub fn karatsuba_unstable<F: FiniteField>(a: &[F], b: &[F], base_case: usize) -> Vec<F> {
    multiply_with_base_case(a, b, base_case)
}

/// [`karatsuba_base_case`], reachable from an example binary.
#[doc(hidden)]
pub fn karatsuba_base_case_unstable<F: FiniteField>() -> usize {
    karatsuba_base_case::<F>()
}

/// The smallest base case the recursion can terminate on: splitting a two-coefficient operand is
/// what guarantees the max length strictly decreases, so one coefficient must be schoolbook.
fn effective_base_case(base_case: usize) -> usize {
    base_case.max(2)
}

fn multiply_with_base_case<F: FiniteField>(a: &[F], b: &[F], base_case: usize) -> Vec<F> {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    let mut product = vec![F::zero(); a.len() + b.len() - 1];
    let (long, short) = if a.len() >= b.len() { (a, b) } else { (b, a) };

    if short.len() < effective_base_case(base_case) {
        schoolbook_into(long, short, &mut product);
        return product;
    }

    // One arena for the whole recursion, sized from a closed form and then carved by slicing.
    // Balanced, the deepest operand is the long one; chunked below, it is the short one.
    let balanced = long.len() <= 2 * short.len();
    let longest = if balanced { long.len() } else { short.len() };
    let mut scratch = vec![F::zero(); scratch_len(longest, base_case)];

    if balanced {
        karatsuba_into(long, short, &mut product, &mut scratch, base_case);
        return product;
    }

    // Unbalanced operands: cut the long one into blocks the short one's length, so every
    // recursive product is balanced. Letting the split-at-the-half recursion handle a 1:k ratio
    // instead computes two half-length products where one would do, at every level, for no gain.
    let mut block = vec![F::zero(); 2 * short.len() - 1];
    for (index, chunk) in long.chunks(short.len()).enumerate() {
        let partial = &mut block[..chunk.len() + short.len() - 1];
        karatsuba_into(chunk, short, partial, &mut scratch, base_case);
        let offset = index * short.len();
        for (slot, value) in product[offset..].iter_mut().zip(partial.iter()) {
            *slot += *value;
        }
    }
    product
}

/// An upper bound on the scratch the recursion carves for an operand of `m` coefficients.
///
/// Each level holds `a0 + a1`, `b0 + b1` and their product; the halves are `ceil(m/2)` long, so a
/// level costs `4 ceil(m/2) - 1` and the series sums to roughly `4 m`.
fn scratch_len(m: usize, base_case: usize) -> usize {
    let base = effective_base_case(base_case);
    let mut total = 0;
    let mut m = m;
    while m >= base {
        let half = m - m / 2;
        total += 4 * half - 1;
        m = half;
    }
    total
}

/// `a * b` written into `out`, which must be exactly `a.len() + b.len() - 1` long. Overwrites;
/// does not accumulate.
fn karatsuba_into<F: FiniteField>(
    a: &[F],
    b: &[F],
    out: &mut [F],
    scratch: &mut [F],
    base_case: usize,
) {
    debug_assert!(!a.is_empty() && !b.is_empty());
    debug_assert_eq!(out.len(), a.len() + b.len() - 1);

    if a.len().min(b.len()) < effective_base_case(base_case) {
        out.fill(F::zero());
        schoolbook_into(a, b, out);
        return;
    }

    // Split at the floor of the half of the *longer* operand. Rounding down rather than up is
    // what keeps the `x^k` and `x^{2k}` blocks inside `out` when the lengths differ.
    let split = a.len().max(b.len()) / 2;
    let (a0, a1) = a.split_at(split.min(a.len()));
    let (b0, b1) = b.split_at(split.min(b.len()));

    let z0_len = a0.len() + b0.len() - 1;
    let z2_len = if a1.is_empty() || b1.is_empty() {
        0
    } else {
        a1.len() + b1.len() - 1
    };
    let sum_a_len = a0.len().max(a1.len());
    let sum_b_len = b0.len().max(b1.len());
    let middle_len = sum_a_len + sum_b_len - 1;
    debug_assert!(split + middle_len <= out.len());

    let (sum_a, rest) = scratch.split_at_mut(sum_a_len);
    let (sum_b, rest) = rest.split_at_mut(sum_b_len);
    let (middle, child) = rest.split_at_mut(middle_len);

    // z0 at x^0 and z2 at x^{2 split}, with the gap between and above them zeroed.
    karatsuba_into(a0, b0, &mut out[..z0_len], child, base_case);
    out[z0_len..].fill(F::zero());
    if z2_len > 0 {
        karatsuba_into(
            a1,
            b1,
            &mut out[2 * split..2 * split + z2_len],
            child,
            base_case,
        );
    }

    // z1 = (a0+a1)(b0+b1) - z0 - z2, with z0 and z2 read back out of `out` before the += below
    // writes over them: the x^{split} block overlaps both.
    add_into(a0, a1, sum_a);
    add_into(b0, b1, sum_b);
    karatsuba_into(sum_a, sum_b, middle, child, base_case);
    for (slot, value) in middle.iter_mut().zip(out[..z0_len].iter()) {
        *slot -= *value;
    }
    for (slot, value) in middle
        .iter_mut()
        .zip(out[2 * split..2 * split + z2_len].iter())
    {
        *slot -= *value;
    }
    for (slot, value) in out[split..].iter_mut().zip(middle.iter()) {
        *slot += *value;
    }
}

/// `out += a * b`, coefficient by coefficient. The same two loops the schoolbook `Mul` runs,
/// sliced so the inner one carries no bounds check.
fn schoolbook_into<F: FiniteField>(a: &[F], b: &[F], out: &mut [F]) {
    for (i, x) in a.iter().enumerate() {
        let x = *x;
        for (slot, y) in out[i..].iter_mut().zip(b.iter()) {
            *slot += x * *y;
        }
    }
}

/// `out = x + y`, padding the shorter with zeros. `out` must be `max(x.len(), y.len())` long.
fn add_into<F: FiniteField>(x: &[F], y: &[F], out: &mut [F]) {
    debug_assert_eq!(out.len(), x.len().max(y.len()));
    let (longer, shorter) = if x.len() >= y.len() { (x, y) } else { (y, x) };
    out.copy_from_slice(longer);
    for (slot, value) in out.iter_mut().zip(shorter.iter()) {
        *slot += *value;
    }
}

#[cfg(test)]
mod tests {
    use super::{
        karatsuba_base_case, karatsuba_unstable, multiply_karatsuba, KARATSUBA_BASE_CASE_32_BIT,
        KARATSUBA_BASE_CASE_64_BIT, KARATSUBA_BASE_CASE_WIDE,
    };
    use crate::{
        fields::{Bn254Fr, KoalaBear, Mersenne31, Zp18446744069414584321},
        identities::Zero,
        FiniteField, Polynomial, UnivariatePolynomial,
    };
    use proptest::prelude::*;
    use rand::{prelude::StdRng, SeedableRng};

    /// Goldilocks, the 64-bit width in the field-coverage set.
    type Goldilocks = Zp18446744069414584321;

    /// The definition, used as the oracle: no trimming, no shortcuts.
    fn naive<F: FiniteField>(a: &[F], b: &[F]) -> Vec<F> {
        if a.is_empty() || b.is_empty() {
            return Vec::new();
        }
        let mut product = vec![F::zero(); a.len() + b.len() - 1];
        for (i, x) in a.iter().enumerate() {
            for (j, y) in b.iter().enumerate() {
                product[i + j] += *x * *y;
            }
        }
        product
    }

    fn random_coefficients<F: FiniteField>(len: usize, seed: u64) -> Vec<F> {
        let mut rng = StdRng::seed_from_u64(seed);
        (0..len).map(|_| F::random(&mut rng)).collect()
    }

    /// An empty operand on either side yields an empty product rather than a `[0]`.
    #[test]
    fn test_an_empty_operand_gives_an_empty_product() {
        type F = KoalaBear;
        let a: Vec<F> = random_coefficients(5, 1);
        assert!(multiply_karatsuba::<F>(&a, &[]).is_empty());
        assert!(multiply_karatsuba::<F>(&[], &a).is_empty());
        assert!(multiply_karatsuba::<F>(&[], &[]).is_empty());
    }

    /// Two degree-zero operands give a single coefficient, their field product.
    #[test]
    fn test_degree_zero_operands_give_one_coefficient() {
        type F = KoalaBear;
        let a = [F::new(7)];
        let b = [F::new(11)];
        assert_eq!(multiply_karatsuba(&a, &b), vec![F::new(77)]);
    }

    /// High-order zeros in the inputs are carried, not trimmed: the output is always
    /// `a.len() + b.len() - 1` long and agrees with the definition coefficient for coefficient.
    #[test]
    fn test_high_order_zeros_are_carried_rather_than_trimmed() {
        type F = KoalaBear;
        let mut a: Vec<F> = random_coefficients(40, 2);
        let mut b: Vec<F> = random_coefficients(40, 3);
        for slot in a.iter_mut().skip(25) {
            *slot = F::zero();
        }
        for slot in b.iter_mut().skip(30) {
            *slot = F::zero();
        }
        let product = multiply_karatsuba(&a, &b);
        assert_eq!(product.len(), a.len() + b.len() - 1);
        assert_eq!(product, naive(&a, &b));
    }

    /// A product of two all-zero operands is all zeros, at the full untrimmed length.
    #[test]
    fn test_a_zero_operand_gives_a_zero_product() {
        type F = Bn254Fr;
        let a = vec![F::zero(); 70];
        let b: Vec<F> = random_coefficients(50, 4);
        let product = multiply_karatsuba(&a, &b);
        assert_eq!(product.len(), 119);
        assert!(product.iter().all(|c| *c == F::zero()));
    }

    /// Asymmetric operand lengths agree with the definition in both orders, across the ratios and
    /// parities where a split-at-the-half recursion mishandles the high half.
    #[test]
    fn test_asymmetric_lengths_agree_with_the_definition() {
        type F = KoalaBear;
        let lengths = [
            (1, 1),
            (1, 200),
            (200, 1),
            (2, 97),
            (97, 2),
            (31, 32),
            (32, 31),
            (33, 64),
            (64, 33),
            (35, 36),
            (36, 35),
            (37, 1000),
            (1000, 37),
            (63, 65),
            (65, 63),
            (127, 128),
            (128, 127),
            (129, 511),
            (511, 129),
            (513, 1025),
            (1025, 513),
        ];
        for (la, lb) in lengths {
            let a: Vec<F> = random_coefficients(la, la as u64 * 31 + 5);
            let b: Vec<F> = random_coefficients(lb, lb as u64 * 37 + 7);
            assert_eq!(multiply_karatsuba(&a, &b), naive(&a, &b), "{} x {}", la, lb);
            assert_eq!(multiply_karatsuba(&b, &a), naive(&b, &a), "{} x {}", lb, la);
        }
    }

    /// Every operand length from 0 to a little past twice the largest base case agrees with the
    /// definition, which pins the base case's boundary and the first two recursion levels.
    #[test]
    fn test_every_short_length_agrees_with_the_definition() {
        type F = KoalaBear;
        for la in 0..=(2 * KARATSUBA_BASE_CASE_32_BIT + 3) {
            for lb in 0..=(2 * KARATSUBA_BASE_CASE_32_BIT + 3) {
                let a: Vec<F> = random_coefficients(la, la as u64 + 1);
                let b: Vec<F> = random_coefficients(lb, lb as u64 + 1_000);
                assert_eq!(multiply_karatsuba(&a, &b), naive(&a, &b), "{} x {}", la, lb);
            }
        }
    }

    /// The product is independent of the base case: every base case from 2 to 70, and
    /// `usize::MAX` for plain schoolbook, give the same coefficients at sizes straddling the
    /// measured constants.
    #[test]
    fn test_the_base_case_changes_nothing_but_the_work() {
        type F = Goldilocks;
        for len in [
            KARATSUBA_BASE_CASE_WIDE - 1,
            KARATSUBA_BASE_CASE_WIDE,
            KARATSUBA_BASE_CASE_WIDE + 1,
            KARATSUBA_BASE_CASE_64_BIT - 1,
            KARATSUBA_BASE_CASE_64_BIT,
            KARATSUBA_BASE_CASE_64_BIT + 1,
            KARATSUBA_BASE_CASE_32_BIT - 1,
            KARATSUBA_BASE_CASE_32_BIT,
            KARATSUBA_BASE_CASE_32_BIT + 1,
            2 * KARATSUBA_BASE_CASE_32_BIT + 1,
            257,
        ] {
            let a: Vec<F> = random_coefficients(len, len as u64 + 11);
            let b: Vec<F> = random_coefficients(len + 3, len as u64 + 13);
            let expected = naive(&a, &b);
            for base_case in (2..=70).chain([usize::MAX]) {
                assert_eq!(
                    karatsuba_unstable(&a, &b, base_case),
                    expected,
                    "len {} base case {}",
                    len,
                    base_case
                );
            }
        }
    }

    /// `karatsuba_base_case` returns the measured figure for each of the three element widths: 4
    /// bytes, 8 bytes, and wider.
    #[test]
    fn test_the_base_case_is_chosen_by_element_width() {
        assert_eq!(std::mem::size_of::<KoalaBear>(), 4);
        assert_eq!(std::mem::size_of::<Goldilocks>(), 8);
        assert_eq!(
            karatsuba_base_case::<KoalaBear>(),
            KARATSUBA_BASE_CASE_32_BIT
        );
        assert_eq!(
            karatsuba_base_case::<Goldilocks>(),
            KARATSUBA_BASE_CASE_64_BIT
        );
        assert_eq!(karatsuba_base_case::<Bn254Fr>(), KARATSUBA_BASE_CASE_WIDE);
    }

    /// Routed through `DensePolynomial::new`, the Karatsuba product equals the schoolbook `Mul`'s
    /// — same coefficients and same degree — over a narrow, a 64-bit and a wide field.
    #[test]
    fn test_it_agrees_with_the_mul_operator_over_every_field_width() {
        fn check<F: FiniteField>(degree: u64, seed: u64) {
            let mut rng = StdRng::seed_from_u64(seed);
            let f = UnivariatePolynomial::<F>::rand(degree, &mut rng);
            let g = UnivariatePolynomial::<F>::rand(degree + 7, &mut rng);
            let karatsuba = UnivariatePolynomial::<F>::new(&multiply_karatsuba(
                f.coefficients(),
                g.coefficients(),
            ));
            let schoolbook = &f * &g;
            assert_eq!(karatsuba, schoolbook);
            assert_eq!(karatsuba.degree(), schoolbook.degree());
        }
        for degree in [1, 17, 63, 64, 100, 255, 256] {
            check::<Mersenne31>(degree, degree);
            check::<KoalaBear>(degree, degree + 1);
            check::<Goldilocks>(degree, degree + 2);
            check::<Bn254Fr>(degree, degree + 3);
        }
    }

    /// `f * 1 == f`, `f * 0` is the zero polynomial, and `deg(f*g) == deg f + deg g` for nonzero
    /// operands.
    #[test]
    fn test_the_multiplicative_identities_and_the_degree_rule() {
        fn check<F: FiniteField>(seed: u64) {
            let mut rng = StdRng::seed_from_u64(seed);
            let f = UnivariatePolynomial::<F>::rand(50, &mut rng);
            let g = UnivariatePolynomial::<F>::rand(70, &mut rng);
            let one = UnivariatePolynomial::<F>::one();
            let zero = UnivariatePolynomial::<F>::zero();

            let times_one = UnivariatePolynomial::<F>::new(&multiply_karatsuba(
                f.coefficients(),
                one.coefficients(),
            ));
            assert_eq!(times_one, f);

            let times_zero = UnivariatePolynomial::<F>::new(&multiply_karatsuba(
                f.coefficients(),
                zero.coefficients(),
            ));
            assert!(times_zero.is_zero());

            let product = UnivariatePolynomial::<F>::new(&multiply_karatsuba(
                f.coefficients(),
                g.coefficients(),
            ));
            assert_eq!(product.degree(), f.degree() + g.degree());
        }
        check::<KoalaBear>(21);
        check::<Goldilocks>(22);
        check::<Bn254Fr>(23);
    }

    /// The product commutes, and distributes over addition: `f*(g+h) == f*g + f*h`.
    #[test]
    fn test_it_commutes_and_distributes_over_addition() {
        fn check<F: FiniteField>(seed: u64) {
            let mut rng = StdRng::seed_from_u64(seed);
            let f = UnivariatePolynomial::<F>::rand(80, &mut rng);
            let g = UnivariatePolynomial::<F>::rand(45, &mut rng);
            let h = UnivariatePolynomial::<F>::rand(91, &mut rng);
            let poly = |coefficients: Vec<F>| UnivariatePolynomial::<F>::new(&coefficients);

            let fg = poly(multiply_karatsuba(f.coefficients(), g.coefficients()));
            let gf = poly(multiply_karatsuba(g.coefficients(), f.coefficients()));
            assert_eq!(fg, gf);

            let sum = &g + &h;
            let left = poly(multiply_karatsuba(f.coefficients(), sum.coefficients()));
            let right = &fg + &poly(multiply_karatsuba(f.coefficients(), h.coefficients()));
            assert_eq!(left, right);
        }
        check::<Mersenne31>(31);
        check::<Goldilocks>(32);
        check::<Bn254Fr>(33);
    }

    proptest! {
        /// Differential against the schoolbook `Mul` on randomized narrow-field operands of
        /// independently chosen degrees.
        #[test]
        fn proptest_matches_schoolbook_over_a_narrow_field(
            seed: u64,
            degree_a in 0u64..300,
            degree_b in 0u64..300,
        ) {
            type F = Mersenne31;
            let mut rng = StdRng::seed_from_u64(seed);
            let f = UnivariatePolynomial::<F>::rand(degree_a, &mut rng);
            let g = UnivariatePolynomial::<F>::rand(degree_b, &mut rng);
            let karatsuba = UnivariatePolynomial::<F>::new(
                &multiply_karatsuba(f.coefficients(), g.coefficients()),
            );
            prop_assert_eq!(karatsuba, &f * &g);
        }

        /// The same differential over a 254-bit field, where the element is 32 bytes and the base
        /// case differs.
        #[test]
        fn proptest_matches_schoolbook_over_a_wide_field(
            seed: u64,
            degree_a in 0u64..200,
            degree_b in 0u64..200,
        ) {
            type F = Bn254Fr;
            let mut rng = StdRng::seed_from_u64(seed);
            let f = UnivariatePolynomial::<F>::rand(degree_a, &mut rng);
            let g = UnivariatePolynomial::<F>::rand(degree_b, &mut rng);
            let karatsuba = UnivariatePolynomial::<F>::new(
                &multiply_karatsuba(f.coefficients(), g.coefficients()),
            );
            prop_assert_eq!(karatsuba, &f * &g);
        }

        /// Untrimmed slices of arbitrary, independently chosen lengths — including zero — agree
        /// with the definition coefficient for coefficient over a 64-bit field.
        #[test]
        fn proptest_untrimmed_slices_match_the_definition(
            seed: u64,
            len_a in 0usize..260,
            len_b in 0usize..260,
        ) {
            type F = Goldilocks;
            let a: Vec<F> = random_coefficients(len_a, seed);
            let b: Vec<F> = random_coefficients(len_b, seed ^ 0xa5a5);
            prop_assert_eq!(multiply_karatsuba(&a, &b), naive(&a, &b));
        }
    }
}
