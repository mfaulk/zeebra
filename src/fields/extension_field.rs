//! Fields GF(p^n) of prime-power order.
//!
//! For prime p, the field GF(q) with q = p^n is represented as polynomials over GF(p) of degree
//! strictly less than n. Addition and subtraction are the coefficientwise operations of GF(p). The
//! product of a and b is the remainder of ab on Euclidean division by a monic irreducible
//! polynomial of degree n, supplied by the [`IrreduciblePolynomial`] parameter. That reduction is
//! what keeps multiplication closed and makes every nonzero element invertible.

use std::{
    fmt::{Debug, Display, Formatter},
    hash::{Hash, Hasher},
    marker::PhantomData,
    ops,
};

use proptest::{
    prelude::Arbitrary,
    strategy::{BoxedStrategy, Strategy},
};
use rand::{CryptoRng, RngCore};
use serde::{
    ser::{Serialize, Serializer},
    Deserialize, Deserializer,
};

use crate::{impl_add_variants, impl_div_variants, impl_mul_variants, impl_sub_variants};

use crate::{
    identities::{One, Zero},
    FiniteField, Ring,
};

/// The monic irreducible polynomial of degree N over GF(P) that defines GF(P^N).
///
/// The polynomial must genuinely be irreducible over GF(P). A reducible modulus yields a ring with
/// zero divisors, in which some nonzero elements have no multiplicative inverse and `inverse` —
/// which relies on Fermat's little theorem — returns a silently wrong value.
pub trait IrreduciblePolynomial<const P: u64, const N: usize>: 'static {
    /// Coefficients c_0, ..., c_{N-1} of `x^N + c_{N-1} x^{N-1} + ... + c_1 x + c_0`, low-order
    /// first. The leading coefficient is implicitly 1.
    const COEFFICIENTS: [u64; N];
}

/// Element of the field GF(P^N), with multiplication reduced by the irreducible polynomial M.
pub struct ExtensionFieldElement<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> {
    /// Coefficients c_0, ..., c_{N-1} of the polynomial `sum c_i x^i`, low-order first. Every
    /// coefficient is a reduced residue mod P, which `new` establishes and the arithmetic
    /// operations preserve. `PartialEq` and `Hash` both key on this array, so that canonical form
    /// is what keeps them consistent.
    coefficients: [u64; N],
    modulus: PhantomData<M>,
}

// The trait impls below are written out rather than derived: a derive would bound the modulus
// marker type M by each trait, even though M appears only in `PhantomData`.

impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> Clone
    for ExtensionFieldElement<P, N, M>
{
    fn clone(&self) -> Self {
        *self
    }
}

impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> Copy
    for ExtensionFieldElement<P, N, M>
{
}

impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> PartialEq
    for ExtensionFieldElement<P, N, M>
{
    fn eq(&self, other: &Self) -> bool {
        self.coefficients == other.coefficients
    }
}

impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> Eq
    for ExtensionFieldElement<P, N, M>
{
}

impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> Hash
    for ExtensionFieldElement<P, N, M>
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.coefficients.hash(state);
    }
}

impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> Debug
    for ExtensionFieldElement<P, N, M>
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.coefficients)
    }
}

impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> Default
    for ExtensionFieldElement<P, N, M>
{
    fn default() -> Self {
        Self::ZERO
    }
}

impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> ExtensionFieldElement<P, N, M> {
    /// An element of GF(P^N).
    ///
    /// # Arguments
    /// * `coefficients` - coefficients[i] is c_i in the polynomial `sum c_i x^i`. Each is reduced
    ///   mod P so that equal elements share one representation.
    pub fn new(coefficients: [u64; N]) -> Self {
        let mut reduced = coefficients;
        for c in reduced.iter_mut() {
            *c %= P;
        }
        Self {
            coefficients: reduced,
            modulus: PhantomData,
        }
    }

    /// The polynomial's coefficients, low-order first, each reduced mod P.
    pub fn coefficients(&self) -> &[u64; N] {
        &self.coefficients
    }
}

// impl Serialize
impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> Serialize
    for ExtensionFieldElement<P, N, M>
{
    fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        todo!()
    }
}

// impl Deserialize
impl<'de, const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> Deserialize<'de>
    for ExtensionFieldElement<P, N, M>
{
    fn deserialize<D>(_deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        todo!()
    }
}

// impl Zero
impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> Zero
    for ExtensionFieldElement<P, N, M>
{
    const ZERO: Self = ExtensionFieldElement {
        coefficients: [0u64; N],
        modulus: PhantomData,
    };
}

// impl One
impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> One
    for ExtensionFieldElement<P, N, M>
{
    const ONE: Self = {
        // The constant polynomial 1.
        let mut coefficients = [0u64; N];
        coefficients[0] = 1;
        ExtensionFieldElement {
            coefficients,
            modulus: PhantomData,
        }
    };
}

// impl Ring
impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> Ring
    for ExtensionFieldElement<P, N, M>
{
}

// impl FiniteField
impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> FiniteField
    for ExtensionFieldElement<P, N, M>
{
    fn new(val: u64) -> Self {
        // The constant polynomial `val`.
        let mut coefficients = [0u64; N];
        coefficients[0] = val % P;
        Self {
            coefficients,
            modulus: PhantomData,
        }
    }

    fn from_str(_value: &str) -> Result<Self, ()> {
        todo!()
    }

    fn random<R: RngCore + CryptoRng>(rng: &mut R) -> Self {
        let mut coefficients = [0u64; N];
        for c in coefficients.iter_mut() {
            *c = rng.next_u64() % P;
        }
        Self {
            coefficients,
            modulus: PhantomData,
        }
    }

    fn primitive_element<R: RngCore + CryptoRng>(_rng: &mut R) -> Self {
        todo!()
    }

    fn root_of_unity<R: RngCore + CryptoRng>(_n: u64, _rng: &mut R) -> Self {
        todo!()
    }

    fn order() -> u128 {
        // TODO: p^n can be larger than u128
        (P as u128).pow(N as u32)
    }

    fn characteristic() -> u128 {
        P as u128
    }
}

// impl Display
impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> Display
    for ExtensionFieldElement<P, N, M>
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.coefficients)
    }
}

// Borrowed + Borrowed
impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>>
    ops::Add<&ExtensionFieldElement<P, N, M>> for &ExtensionFieldElement<P, N, M>
{
    type Output = ExtensionFieldElement<P, N, M>;

    fn add(self, rhs: &ExtensionFieldElement<P, N, M>) -> Self::Output {
        let mut coefficients = [0u64; N];
        for i in 0..N {
            let sum = self.coefficients[i] as u128 + rhs.coefficients[i] as u128;
            coefficients[i] = (sum % P as u128) as u64;
        }
        ExtensionFieldElement::new(coefficients)
    }
}

impl_add_variants!([const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>], ExtensionFieldElement<P, N, M>);

// Borrowed - Borrowed
impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>>
    ops::Sub<&ExtensionFieldElement<P, N, M>> for &ExtensionFieldElement<P, N, M>
{
    type Output = ExtensionFieldElement<P, N, M>;

    fn sub(self, rhs: &ExtensionFieldElement<P, N, M>) -> Self::Output {
        let mut coefficients = [0u64; N];
        for i in 0..N {
            let difference = self.coefficients[i] as i128 - rhs.coefficients[i] as i128;
            coefficients[i] = difference.rem_euclid(P as i128) as u64;
        }
        ExtensionFieldElement::new(coefficients)
    }
}

impl_sub_variants!([const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>], ExtensionFieldElement<P, N, M>);

impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> ops::Neg
    for ExtensionFieldElement<P, N, M>
{
    type Output = ExtensionFieldElement<P, N, M>;

    fn neg(self) -> Self::Output {
        ExtensionFieldElement::zero() - self
    }
}

impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> ops::Neg
    for &ExtensionFieldElement<P, N, M>
{
    type Output = ExtensionFieldElement<P, N, M>;

    fn neg(self) -> Self::Output {
        ExtensionFieldElement::zero() - self
    }
}

// Borrowed * Borrowed
impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> ops::Mul<Self>
    for &ExtensionFieldElement<P, N, M>
{
    type Output = ExtensionFieldElement<P, N, M>;

    fn mul(self, rhs: Self) -> Self::Output {
        let p = P as u128;

        // The schoolbook product of two polynomials of degree < N has degree < 2N - 1. A heap
        // buffer is used because `[u64; 2 * N - 1]` would need const-expression arithmetic.
        let mut product = vec![0u128; 2 * N - 1];
        for i in 0..N {
            let a = self.coefficients[i] as u128;
            if a == 0 {
                continue;
            }
            for j in 0..N {
                product[i + j] = (product[i + j] + a * rhs.coefficients[j] as u128) % p;
            }
        }

        // Reduce to degree < N. The modulus gives x^N = -(c_{N-1} x^{N-1} + ... + c_0), so each
        // term of degree i >= N folds down into the N coefficients below it. Working downwards
        // means a folded term is itself reduced before it is reached.
        let modulus = M::COEFFICIENTS;
        for i in (N..product.len()).rev() {
            let leading = product[i];
            if leading == 0 {
                continue;
            }
            product[i] = 0;
            for j in 0..N {
                let term = (leading * modulus[j] as u128) % p;
                product[i - N + j] = (product[i - N + j] + p - term) % p;
            }
        }

        let mut coefficients = [0u64; N];
        for (coefficient, reduced) in coefficients.iter_mut().zip(product.iter()) {
            *coefficient = *reduced as u64;
        }
        ExtensionFieldElement::new(coefficients)
    }
}

impl_mul_variants!([const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>], ExtensionFieldElement<P, N, M>);

// Borrowed / Borrowed
impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> ops::Div<Self>
    for &ExtensionFieldElement<P, N, M>
{
    type Output = ExtensionFieldElement<P, N, M>;

    fn div(self, rhs: Self) -> Self::Output {
        // Division is multiplication by the inverse.
        self * &rhs.inverse()
    }
}

impl_div_variants!([const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>], ExtensionFieldElement<P, N, M>);

// impl Arbitrary
impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> Arbitrary
    for ExtensionFieldElement<P, N, M>
{
    type Parameters = ();

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        // Each of the N coefficients is independently drawn from GF(p).
        proptest::collection::vec(0u64..P, N)
            .prop_map(|drawn| {
                let mut coefficients = [0u64; N];
                coefficients.copy_from_slice(&drawn);
                Self::new(coefficients)
            })
            .boxed()
    }

    type Strategy = BoxedStrategy<Self>;
}

#[cfg(test)]
mod tests {
    use proptest::{arbitrary::Arbitrary, prop_assert_eq, proptest};
    use rand::thread_rng;

    use crate::{
        fields::{
            binary_field::BinaryFieldElement,
            extension_field::{ExtensionFieldElement, IrreduciblePolynomial},
            irreducible_polynomials::{
                Modulus13Pow4, Modulus251Pow4, Modulus2Pow8, Modulus5Pow3, X8_X4_X3_X_1,
            },
        },
        identities::{One, Zero},
        FiniteField,
    };

    type F13x4 = ExtensionFieldElement<13, 4, Modulus13Pow4>;
    type F251x4 = ExtensionFieldElement<251, 4, Modulus251Pow4>;
    type F5x3 = ExtensionFieldElement<5, 3, Modulus5Pow3>;
    type F2x8 = ExtensionFieldElement<2, 8, Modulus2Pow8>;

    #[test]
    // random should not panic.
    fn test_random() {
        let mut rng = thread_rng();
        for _i in 0..1000 {
            let _element = F251x4::random(&mut rng);
        }
    }

    #[test]
    // ZERO is the additive identity.
    fn test_add_zero() {
        type F = F251x4;
        let mut rng = thread_rng();
        let element = F::random(&mut rng);
        let sum = element + F::zero();
        assert_eq!(element, sum);
    }

    #[test]
    fn test_add() {
        type Field = F13x4;
        let a = Field::new([1, 2, 3, 4]);
        let b = Field::new([11, 11, 11, 11]);
        let sum = a + b;
        assert_eq!(sum, Field::new([12, 0, 1, 2]));
    }

    #[test]
    fn test_sub() {
        type F = F13x4;
        let a = F::new([1, 2, 3, 4]);
        let b = F::new([11, 11, 11, 11]);
        let diff = a - b;
        assert_eq!(diff, F::new([3, 4, 5, 6]));
    }

    #[test]
    // ONE is the multiplicative identity.
    fn test_mul_one() {
        type F = F251x4;
        let mut rng = thread_rng();
        let element = F::random(&mut rng);
        let prod = element * F::one();
        assert_eq!(element, prod);
    }

    #[test]
    fn test_mul() {
        // (1 + 2X + 3X^2 + 4X^3)(11 + 11X + 11X^2 + 11X^3) mod X^4 + X^3 + 1 over GF(13).
        type F = F13x4;
        let a = F::new([1, 2, 3, 4]);
        let b = F::new([11, 11, 11, 11]);
        let prod = a * b;
        assert_eq!(prod, F::new([10, 0, 9, 5]));
    }

    /// Multiplication is polynomial multiplication: X * X is X^2, not a componentwise product.
    #[test]
    fn test_multiplication_is_polynomial_multiplication() {
        let x = F13x4::new([0, 1, 0, 0]); // X
        assert_eq!(x * x, F13x4::new([0, 0, 1, 0])); // X^2
    }

    /// ONE is the constant polynomial 1, not an all-ones coefficient vector.
    #[test]
    fn test_one_is_the_constant_polynomial_one() {
        assert_eq!(F13x4::one(), F13x4::new([1, 0, 0, 0]));
    }

    /// Every nonzero element is invertible, including those with a zero coefficient.
    #[test]
    fn test_inverse_of_element_with_a_zero_coefficient() {
        let a = F13x4::new([1, 0, 1, 1]);
        assert_eq!(a * a.inverse(), F13x4::one());
    }

    /// Reduction by X^N wraps a product back into degree less than N.
    #[test]
    fn test_multiplication_reduces_by_the_modulus() {
        // In GF(13^4) modulo X^4 + X^3 + 1, X^3 * X = X^4 = -(X^3 + 1) = 12*X^3 + 12.
        let x = F13x4::new([0, 1, 0, 0]);
        let x_cubed = F13x4::new([0, 0, 0, 1]);
        assert_eq!(x_cubed * x, F13x4::new([12, 0, 0, 12]));
    }

    #[test]
    // a * a_inv = 1
    fn test_inverse() {
        type F = F13x4;
        let a = F::new([1, 2, 3, 4]);
        assert_eq!(a * a.inverse(), F::one());
    }

    #[test]
    #[should_panic]
    // Zero does not have a multiplicative inverse.
    fn test_inverse_of_zero() {
        type F = F251x4;
        let mut rng = thread_rng();
        let element = F::random(&mut rng);
        let _result = element / F::zero();
    }

    #[test]
    fn test_divide_by_one() {
        type F = F251x4;
        let mut rng = thread_rng();
        let element = F::random(&mut rng);
        let result = element / F::one();
        assert_eq!(element, result);
    }

    #[test]
    fn test_divide() {
        // b^-1 = 9 + 8X + 4X^2 + 8X^3 mod X^4 + X^3 + 1 over GF(13), so a/b = a * b^-1.
        type F = F13x4;
        let a = F::new([1, 2, 3, 4]);
        let b = F::new([11, 11, 11, 11]);
        let result = a / b;
        assert_eq!(result, F::new([9, 5, 2, 11]));
    }

    // The field axioms, checked over arbitrary elements of GF(5^3), GF(13^4), and GF(251^4).

    fn addition_is_commutative<F: FiniteField>(a: F, b: F) {
        assert_eq!(a + b, b + a);
    }

    fn addition_is_associative<F: FiniteField>(a: F, b: F, c: F) {
        assert_eq!((a + b) + c, a + (b + c));
    }

    fn zero_is_the_additive_identity<F: FiniteField>(a: F) {
        assert_eq!(a + F::zero(), a);
    }

    // `a - a` is the point of the test, not a mistake.
    #[allow(clippy::eq_op)]
    fn subtracting_an_element_from_itself_gives_zero<F: FiniteField>(a: F) {
        assert_eq!(a - a, F::zero());
    }

    fn multiplication_is_commutative<F: FiniteField>(a: F, b: F) {
        assert_eq!(a * b, b * a);
    }

    fn multiplication_is_associative<F: FiniteField>(a: F, b: F, c: F) {
        assert_eq!((a * b) * c, a * (b * c));
    }

    fn one_is_the_multiplicative_identity<F: FiniteField>(a: F) {
        assert_eq!(a * F::one(), a);
    }

    fn multiplication_distributes_over_addition<F: FiniteField>(a: F, b: F, c: F) {
        assert_eq!(a * (b + c), (a * b) + (a * c));
    }

    fn element_times_its_inverse_is_one<F: FiniteField>(a: F) {
        if a.is_zero() {
            return; // Zero has no multiplicative inverse.
        }
        assert_eq!(a * a.inverse(), F::one());
    }

    fn division_undoes_multiplication<F: FiniteField>(a: F, b: F) {
        if b.is_zero() {
            return; // Division by zero is undefined.
        }
        assert_eq!((a * b) / b, a);
    }

    fn frobenius_fixes_every_element<F: FiniteField>(a: F) {
        // a^(p^n) = a for every a in GF(p^n).
        assert_eq!(a.pow(F::order()), a);
    }

    fn coefficients_stay_reduced<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>>(
        a: ExtensionFieldElement<P, N, M>,
        b: ExtensionFieldElement<P, N, M>,
    ) {
        // Every coefficient of a sum or product must be a reduced residue mod p.
        for c in (a + b)
            .coefficients
            .iter()
            .chain((a * b).coefficients.iter())
        {
            assert!(*c < P);
        }
    }

    proptest! {
        #[test]
        fn test_addition_is_commutative_13x4(a in F13x4::arbitrary(), b in F13x4::arbitrary()) {
            addition_is_commutative(a, b);
        }

        #[test]
        fn test_addition_is_commutative_61x8(a in F251x4::arbitrary(), b in F251x4::arbitrary()) {
            addition_is_commutative(a, b);
        }

        #[test]
        fn test_addition_is_associative_13x4(a in F13x4::arbitrary(), b in F13x4::arbitrary(), c in F13x4::arbitrary()) {
            addition_is_associative(a, b, c);
        }

        #[test]
        fn test_addition_is_associative_61x8(a in F251x4::arbitrary(), b in F251x4::arbitrary(), c in F251x4::arbitrary()) {
            addition_is_associative(a, b, c);
        }

        #[test]
        fn test_zero_is_the_additive_identity_13x4(a in F13x4::arbitrary()) {
            zero_is_the_additive_identity(a);
        }

        #[test]
        fn test_zero_is_the_additive_identity_61x8(a in F251x4::arbitrary()) {
            zero_is_the_additive_identity(a);
        }

        #[test]
        fn test_subtracting_an_element_from_itself_gives_zero_13x4(a in F13x4::arbitrary()) {
            subtracting_an_element_from_itself_gives_zero(a);
        }

        #[test]
        fn test_subtracting_an_element_from_itself_gives_zero_61x8(a in F251x4::arbitrary()) {
            subtracting_an_element_from_itself_gives_zero(a);
        }

        #[test]
        fn test_multiplication_is_commutative_13x4(a in F13x4::arbitrary(), b in F13x4::arbitrary()) {
            multiplication_is_commutative(a, b);
        }

        #[test]
        fn test_multiplication_is_commutative_61x8(a in F251x4::arbitrary(), b in F251x4::arbitrary()) {
            multiplication_is_commutative(a, b);
        }

        #[test]
        fn test_multiplication_is_associative_13x4(a in F13x4::arbitrary(), b in F13x4::arbitrary(), c in F13x4::arbitrary()) {
            multiplication_is_associative(a, b, c);
        }

        #[test]
        fn test_multiplication_is_associative_61x8(a in F251x4::arbitrary(), b in F251x4::arbitrary(), c in F251x4::arbitrary()) {
            multiplication_is_associative(a, b, c);
        }

        #[test]
        fn test_one_is_the_multiplicative_identity_13x4(a in F13x4::arbitrary()) {
            one_is_the_multiplicative_identity(a);
        }

        #[test]
        fn test_one_is_the_multiplicative_identity_61x8(a in F251x4::arbitrary()) {
            one_is_the_multiplicative_identity(a);
        }

        #[test]
        fn test_multiplication_distributes_over_addition_13x4(a in F13x4::arbitrary(), b in F13x4::arbitrary(), c in F13x4::arbitrary()) {
            multiplication_distributes_over_addition(a, b, c);
        }

        #[test]
        fn test_multiplication_distributes_over_addition_61x8(a in F251x4::arbitrary(), b in F251x4::arbitrary(), c in F251x4::arbitrary()) {
            multiplication_distributes_over_addition(a, b, c);
        }

        #[test]
        fn test_coefficients_stay_reduced_13x4(a in F13x4::arbitrary(), b in F13x4::arbitrary()) {
            coefficients_stay_reduced(a, b);
        }

        #[test]
        fn test_coefficients_stay_reduced_61x8(a in F251x4::arbitrary(), b in F251x4::arbitrary()) {
            coefficients_stay_reduced(a, b);
        }

        #[test]
        fn test_element_times_its_inverse_is_one_5x3(a in F5x3::arbitrary()) {
            element_times_its_inverse_is_one(a);
        }

        #[test]
        fn test_element_times_its_inverse_is_one_13x4(a in F13x4::arbitrary()) {
            element_times_its_inverse_is_one(a);
        }

        #[test]
        fn test_element_times_its_inverse_is_one_251x4(a in F251x4::arbitrary()) {
            element_times_its_inverse_is_one(a);
        }

        #[test]
        fn test_division_undoes_multiplication_13x4(a in F13x4::arbitrary(), b in F13x4::arbitrary()) {
            division_undoes_multiplication(a, b);
        }

        #[test]
        fn test_division_undoes_multiplication_251x4(a in F251x4::arbitrary(), b in F251x4::arbitrary()) {
            division_undoes_multiplication(a, b);
        }

        #[test]
        fn test_frobenius_fixes_every_element_5x3(a in F5x3::arbitrary()) {
            frobenius_fixes_every_element(a);
        }

        #[test]
        fn test_frobenius_fixes_every_element_13x4(a in F13x4::arbitrary()) {
            frobenius_fixes_every_element(a);
        }

        #[test]
        fn test_multiplication_is_associative_5x3(a in F5x3::arbitrary(), b in F5x3::arbitrary(), c in F5x3::arbitrary()) {
            multiplication_is_associative(a, b, c);
        }

        #[test]
        fn test_multiplication_distributes_over_addition_5x3(a in F5x3::arbitrary(), b in F5x3::arbitrary(), c in F5x3::arbitrary()) {
            multiplication_distributes_over_addition(a, b, c);
        }

        /// GF(2^8) built as an extension field agrees with the independent bit-pattern
        /// implementation in `binary_field`, given the same irreducible polynomial.
        #[test]
        fn test_gf256_agrees_with_binary_field(a in 0u64..256, b in 0u64..256) {
            let extension = |bits: u64| {
                let mut coefficients = [0u64; 8];
                for (i, c) in coefficients.iter_mut().enumerate() {
                    *c = (bits >> i) & 1;
                }
                F2x8::new(coefficients)
            };
            let bits = |element: F2x8| {
                element
                    .coefficients
                    .iter()
                    .enumerate()
                    .fold(0u64, |acc, (i, c)| acc | (c << i))
            };

            let binary_product = BinaryFieldElement::<X8_X4_X3_X_1>::new(a)
                * BinaryFieldElement::<X8_X4_X3_X_1>::new(b);
            prop_assert_eq!(bits(extension(a) * extension(b)), binary_product.coefficients());
        }
    }

    /// The strategy is usable, equal values hash equally, and coefficients stay reduced mod P.
    #[test]
    fn test_arbitrary_and_representation_are_sound() {
        use crate::test_support::{
            assert_hash_agrees_with_eq, assert_strategy_is_not_degenerate, draw,
        };
        let strategy = F13x4::arbitrary();
        assert_strategy_is_not_degenerate(&strategy, "ExtensionFieldElement");

        let mut values = draw(&strategy, 32);
        values.extend([F13x4::zero(), F13x4::one(), F13x4::default()]);
        assert_hash_agrees_with_eq(&values, "ExtensionFieldElement");

        for v in &values {
            for c in v.coefficients {
                assert!(c < 13, "{:?} has an unreduced coefficient", v);
            }
        }
    }
}
