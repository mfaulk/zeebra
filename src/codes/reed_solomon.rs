//! Reed-Solomon codes in evaluation form over a caller-supplied FFT domain.
//!
//! A `[n, k]` Reed-Solomon codeword is the evaluation of a polynomial of degree below `k` on a
//! domain of `n` points. Two message layouts are offered over the same code: [`ReedSolomon::encode`]
//! reads the message as the polynomial's coefficients, and [`ReedSolomon::encode_systematic`]
//! reads it as the polynomial's values on the first `k` domain points, so that the message appears
//! verbatim as the first `k` symbols of the codeword.
//!
//! # Why the syndromes are the top interpolated coefficients
//!
//! Interpolating a received word `y` over the domain gives `r(x)` with
//! `r_j = (1/n) * sum_i y_i w^{-ij}`. A codeword's `r_j` vanishes for `j >= k` by definition, so
//! the `n - k` top coefficients of `r` *are* the syndromes, and no separate syndrome transform is
//! needed. Writing an error `e` supported on `E`, the `j`th of them is
//!
//! ```text
//! S_j = r_{k+j} = sum_{i in E} Y_i X_i^j,   X_i = w^{-i},   Y_i = e_i w^{-ik} / n
//! ```
//!
//! which is the classical syndrome form, so the classical key equation
//! `Λ(x)S(x) ≡ Ω(x) mod x^{2t}` applies unchanged. That is what makes the FFT the only transform
//! this module needs.

use std::fmt::{Display, Formatter};

use crate::{
    codes::euclidean::partial_bezout, evaluate, interpolate, lagrange_interpolate, FFTDomain,
    FiniteField, Polynomial, UnivariatePolynomial,
};

/// Why an encode or decode could not produce an answer.
///
/// Every variant is a fact about the data rather than a broken invariant, which is why they are
/// returned rather than asserted: a caller cannot know in advance how many symbols of a received
/// word were corrupted.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CodeError {
    /// A message longer than the block length, which no polynomial of degree below `k` can carry.
    MessageTooLong {
        message_length: usize,
        block_length: usize,
    },

    /// A message or word of the wrong length for this code.
    WrongLength { expected: usize, actual: usize },

    /// An erasure index at or beyond the block length.
    ErasureOutOfRange {
        position: usize,
        block_length: usize,
    },

    /// More erasures than the `n - k` the code can fill in.
    TooManyErasures { erasures: usize, recoverable: usize },

    /// The received word is not within the decoder's radius of any codeword.
    ///
    /// Returned rather than a nearest-codeword guess. Beyond `t = (n - k) / 2` errors the nearest
    /// codeword need not be the transmitted one, so a decoder that answered anyway would be
    /// silently wrong; this module reports the failure instead.
    Uncorrectable,
}

impl Display for CodeError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MessageTooLong {
                message_length,
                block_length,
            } => write!(
                f,
                "a message length of {message_length} exceeds the block length {block_length}"
            ),
            Self::WrongLength { expected, actual } => {
                write!(f, "expected {expected} symbols, got {actual}")
            }
            Self::ErasureOutOfRange {
                position,
                block_length,
            } => write!(
                f,
                "erasure position {position} is outside a block of {block_length} symbols"
            ),
            Self::TooManyErasures {
                erasures,
                recoverable,
            } => write!(
                f,
                "{erasures} erasures exceed the {recoverable} this code can recover"
            ),
            Self::Uncorrectable => write!(
                f,
                "the received word is beyond the decoder's correction radius"
            ),
        }
    }
}

impl std::error::Error for CodeError {}

/// A decoded word: the corrected codeword, the message it carries, and what was repaired.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Correction<F: FiniteField> {
    /// The corrected codeword, of length `n`.
    pub codeword: Vec<F>,

    /// The coefficients of the message polynomial, of length `k`.
    ///
    /// This is the message [`ReedSolomon::encode`] takes. A word produced by
    /// [`ReedSolomon::encode_systematic`] carries its message in `codeword[..k]` instead.
    pub message: Vec<F>,

    /// The positions the decoder changed, or for erasure recovery the positions it was told to
    /// fill in, ascending.
    pub error_positions: Vec<usize>,
}

/// A Reed-Solomon code: a domain of `n` evaluation points and a message length `k`.
///
/// The domain is supplied by the caller rather than built here, following [`crate::evaluate`] and
/// [`crate::interpolate`] — only the caller knows which field it is working over and which sizes
/// that field can host.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReedSolomon<F: FiniteField> {
    domain: FFTDomain<F>,
    message_length: usize,
}

impl<F: FiniteField> ReedSolomon<F> {
    /// A code of block length `domain.size()` carrying `message_length` symbols.
    ///
    /// `message_length` may be zero, giving the code whose only word is all zeros, and may equal
    /// the block length, giving the rate-1 code that corrects nothing.
    pub fn new(domain: FFTDomain<F>, message_length: usize) -> Result<Self, CodeError> {
        if message_length > domain.size() {
            return Err(CodeError::MessageTooLong {
                message_length,
                block_length: domain.size(),
            });
        }
        Ok(Self {
            domain,
            message_length,
        })
    }

    /// The block length `n`: the number of symbols in a codeword.
    pub fn block_length(&self) -> usize {
        self.domain.size()
    }

    /// The message length `k`: the number of field elements a codeword carries.
    pub fn message_length(&self) -> usize {
        self.message_length
    }

    /// The minimum distance `n - k + 1`, which is the Singleton bound met with equality.
    pub fn distance(&self) -> usize {
        self.block_length() - self.message_length + 1
    }

    /// The number of symbol errors the decoder corrects: `t = (n - k) / 2`, rounded down.
    pub fn max_errors(&self) -> usize {
        (self.block_length() - self.message_length) / 2
    }

    /// The number of erasures [`Self::recover_erasures`] fills in: `n - k`, twice [`Self::max_errors`]
    /// because a known position needs no locator.
    pub fn max_erasures(&self) -> usize {
        self.block_length() - self.message_length
    }

    /// The evaluation domain.
    pub fn domain(&self) -> &FFTDomain<F> {
        &self.domain
    }

    /// Encode `message` as the coefficients of the codeword polynomial.
    ///
    /// The codeword is the polynomial's evaluations on the domain, in domain order. The message
    /// does not appear verbatim in it — see [`Self::encode_systematic`] for the layout where it
    /// does.
    pub fn encode(&self, message: &[F]) -> Result<Vec<F>, CodeError> {
        self.check_length(message, self.message_length)?;
        Ok(self.evaluate_message_polynomial(&UnivariatePolynomial::new(message)))
    }

    /// Encode `message` so that it appears as the first `k` symbols of the codeword.
    ///
    /// The message is read as the codeword polynomial's values on the first `k` domain points and
    /// interpolated, which is `O(k^2)`; the coefficient form above is `O(n log n)`. Systematic
    /// layout is worth that when the message must be readable without decoding.
    pub fn encode_systematic(&self, message: &[F]) -> Result<Vec<F>, CodeError> {
        self.check_length(message, self.message_length)?;
        if message.is_empty() {
            return Ok(vec![F::zero(); self.block_length()]);
        }
        let points = message
            .iter()
            .enumerate()
            .map(|(i, m_i)| (self.domain[i], *m_i))
            .collect();
        Ok(self.evaluate_message_polynomial(&lagrange_interpolate(points)))
    }

    /// The `n - k` syndromes of a received word, all zero exactly when it is a codeword.
    pub fn syndromes(&self, received: &[F]) -> Result<Vec<F>, CodeError> {
        self.check_length(received, self.block_length())?;
        let coefficients = self.interpolated_coefficients(received);
        Ok(coefficients[self.message_length..].to_vec())
    }

    /// Whether a word of length `n` is a codeword of this code.
    pub fn is_codeword(&self, word: &[F]) -> Result<bool, CodeError> {
        Ok(self.syndromes(word)?.iter().all(|s| s.is_zero()))
    }

    /// Correct up to [`Self::max_errors`] symbol errors at unknown positions.
    ///
    /// Syndromes from the interpolated word, the key equation by the extended Euclidean algorithm
    /// on `(x^{2t}, S(x))`, error positions by evaluating the locator on the domain, and
    /// magnitudes by Forney's formula. The candidate is re-checked against the code before it is
    /// returned, so a word beyond the correction radius yields [`CodeError::Uncorrectable`] rather
    /// than a wrong codeword — including for a code of odd redundancy, where the `n - k` syndromes
    /// detect one more error than the `2t` used for correction can locate.
    pub fn decode(&self, received: &[F]) -> Result<Correction<F>, CodeError> {
        self.check_length(received, self.block_length())?;
        let coefficients = self.interpolated_coefficients(received);
        let syndromes = &coefficients[self.message_length..];

        if syndromes.iter().all(|s| s.is_zero()) {
            return Ok(Correction {
                codeword: received.to_vec(),
                message: coefficients[..self.message_length].to_vec(),
                error_positions: Vec::new(),
            });
        }

        // Nonzero syndromes with no correction capability: detected, not correctable. This is the
        // whole of a rate-1 or single-parity code's decoder.
        let t = self.max_errors();
        if t == 0 {
            return Err(CodeError::Uncorrectable);
        }

        let (locator, evaluator) = self.solve_key_equation(&syndromes[..2 * t], t)?;
        let error_positions = self.locate(&locator);
        if error_positions.len() != locator.degree() as usize {
            // The locator has a repeated root, or a root outside the domain. Either way it is not
            // the locator of an error pattern this code can correct.
            return Err(CodeError::Uncorrectable);
        }

        let mut codeword = received.to_vec();
        let derivative = formal_derivative(&locator);
        let n = integer_multiple_of_one::<F>(self.block_length());
        for &position in &error_positions {
            // X_i = w^{-i} and its inverse w^i is the domain point the locator vanished at.
            let x_inverse = self.domain[position];
            let x = self.domain[(self.block_length() - position) % self.block_length()];
            let slope = derivative.eval(&x_inverse);
            if slope.is_zero() {
                return Err(CodeError::Uncorrectable);
            }
            // Forney: Y_i = -X_i * Ω(X_i^-1) / Λ'(X_i^-1), then e_i = n * Y_i * (w^i)^k undoes the
            // w^{-ik}/n folded into Y_i by the interpolation.
            let y = (evaluator.eval(&x_inverse) * x).neg() / slope;
            codeword[position] -= y * n * x_inverse.pow(self.message_length as u128);
        }

        // The correction is only a candidate until it is a codeword: beyond t errors the Euclidean
        // step still returns *some* locator, and this is what separates "corrected" from "the
        // syndromes were consistent with a pattern that is not the one that happened".
        let corrected = self.interpolated_coefficients(&codeword);
        if corrected[self.message_length..]
            .iter()
            .any(|c| !c.is_zero())
        {
            return Err(CodeError::Uncorrectable);
        }

        Ok(Correction {
            codeword,
            message: corrected[..self.message_length].to_vec(),
            error_positions,
        })
    }

    /// Fill in up to [`Self::max_erasures`] symbols whose positions are known.
    ///
    /// The easy half of decoding: with the positions given, the locator is known and only the
    /// magnitudes remain, so `k` surviving symbols determine the codeword polynomial outright. Any
    /// surviving symbol beyond those `k` is spent checking the result, so an unerased symbol that
    /// is also wrong is reported as [`CodeError::Uncorrectable`] rather than silently interpolated
    /// into a different codeword.
    ///
    /// Values at the erased positions of `received` are ignored, so any placeholder will do.
    pub fn recover_erasures(
        &self,
        received: &[F],
        erasures: &[usize],
    ) -> Result<Correction<F>, CodeError> {
        self.check_length(received, self.block_length())?;

        let mut erased = erasures.to_vec();
        erased.sort_unstable();
        erased.dedup();
        if let Some(&position) = erased.iter().find(|&&p| p >= self.block_length()) {
            return Err(CodeError::ErasureOutOfRange {
                position,
                block_length: self.block_length(),
            });
        }
        if erased.len() > self.max_erasures() {
            return Err(CodeError::TooManyErasures {
                erasures: erased.len(),
                recoverable: self.max_erasures(),
            });
        }

        let survivors: Vec<usize> = (0..self.block_length())
            .filter(|i| !erased.contains(i))
            .collect();
        let (interpolated, checks) = survivors.split_at(self.message_length);

        let message_polynomial = if interpolated.is_empty() {
            UnivariatePolynomial::zero()
        } else {
            lagrange_interpolate(
                interpolated
                    .iter()
                    .map(|&i| (self.domain[i], received[i]))
                    .collect(),
            )
        };

        if checks
            .iter()
            .any(|&i| message_polynomial.eval(&self.domain[i]) != received[i])
        {
            return Err(CodeError::Uncorrectable);
        }

        let mut message = message_polynomial.coefficients().to_vec();
        message.resize(self.message_length, F::zero());
        Ok(Correction {
            codeword: self.evaluate_message_polynomial(&message_polynomial),
            message,
            error_positions: erased,
        })
    }

    /// Solve `Λ(x)S(x) ≡ Ω(x) mod x^{2t}` for the locator and the error evaluator.
    ///
    /// The Euclidean sequence on `(x^{2t}, S(x))` halted at the first remainder of degree below
    /// `t` gives both at once; the pair is normalized so that `Λ(0) = 1`, which is the locator's
    /// defining constant term.
    fn solve_key_equation(
        &self,
        syndromes: &[F],
        t: usize,
    ) -> Result<(UnivariatePolynomial<F>, UnivariatePolynomial<F>), CodeError> {
        let mut x_to_the_2t = vec![F::zero(); 2 * t + 1];
        x_to_the_2t[2 * t] = F::one();
        let (locator, evaluator) = partial_bezout(
            &UnivariatePolynomial::new(&x_to_the_2t),
            &UnivariatePolynomial::new(syndromes),
            t as u32,
        );

        // Λ(0) = 0 would mean a root at infinity, i.e. no error pattern of weight at most t
        // explains these syndromes.
        let constant_term = locator.coefficients()[0];
        if constant_term.is_zero() {
            return Err(CodeError::Uncorrectable);
        }
        let scale = constant_term.inverse();
        let locator = locator.scale(&scale);
        if locator.is_zero() || locator.degree() == 0 || locator.degree() as usize > t {
            return Err(CodeError::Uncorrectable);
        }
        Ok((locator, evaluator.scale(&scale)))
    }

    /// The positions whose domain point is a root of the locator, ascending.
    ///
    /// `Λ(x) = prod (1 - w^{-i} x)` vanishes at `x = w^i`, so one evaluation per domain point
    /// names the error positions directly. `O(n * deg Λ)`, and unlike general root finding it
    /// cannot return a root that is not a position.
    fn locate(&self, locator: &UnivariatePolynomial<F>) -> Vec<usize> {
        (0..self.block_length())
            .filter(|&i| locator.eval(&self.domain[i]).is_zero())
            .collect()
    }

    /// The codeword polynomial's evaluations on the whole domain.
    fn evaluate_message_polynomial(&self, p: &UnivariatePolynomial<F>) -> Vec<F> {
        evaluate(p, &self.domain)
    }

    /// The interpolation of a word, as exactly `n` coefficients.
    ///
    /// `UnivariatePolynomial` trims its high-order zeros, and the syndromes are read off the top
    /// of this vector by index, so the padding is what makes the indices meaningful.
    fn interpolated_coefficients(&self, word: &[F]) -> Vec<F> {
        let mut coefficients = interpolate(word, &self.domain).coefficients().to_vec();
        coefficients.resize(self.block_length(), F::zero());
        coefficients
    }

    fn check_length(&self, symbols: &[F], expected: usize) -> Result<(), CodeError> {
        if symbols.len() == expected {
            Ok(())
        } else {
            Err(CodeError::WrongLength {
                expected,
                actual: symbols.len(),
            })
        }
    }
}

/// `i` copies of the field's one, summed.
///
/// Not `F::new(i)`: that reads `i` as the field's own representation of a value, which for a prime
/// field happens to coincide with `i * 1` and for an extension or binary field does not. The
/// decoder needs the sum, which is `i mod p` times one — zero whenever the characteristic divides
/// `i`.
fn integer_multiple_of_one<F: FiniteField>(i: usize) -> F {
    let mut result = F::zero();
    let mut addend = F::one();
    let mut remaining = i;
    while remaining > 0 {
        if remaining & 1 == 1 {
            result += addend;
        }
        addend += addend;
        remaining >>= 1;
    }
    result
}

/// `d/dx` of a polynomial, term by term.
///
/// Forney's formula needs it and nothing else in the crate does. In characteristic `p` the
/// derivative of `x^p` vanishes, which is correct here: the locator has degree at most `t`, and a
/// vanishing slope at an error position is caught as [`CodeError::Uncorrectable`].
fn formal_derivative<F: FiniteField>(p: &UnivariatePolynomial<F>) -> UnivariatePolynomial<F> {
    // The multiplier walks 1, 2, 3, ... by repeated addition rather than `F::new(i)`, for the
    // reason given on `integer_multiple_of_one`.
    let mut multiplier = F::zero();
    let coefficients: Vec<F> = p
        .coefficients()
        .iter()
        .skip(1)
        .map(|c| {
            multiplier += F::one();
            *c * multiplier
        })
        .collect();
    UnivariatePolynomial::new(&coefficients)
}

#[cfg(test)]
pub(crate) mod tests {
    use super::{formal_derivative, CodeError, ReedSolomon};
    use crate::{FFTDomain, FiniteField, KnownOrder, One, Polynomial, UnivariatePolynomial, Zero};
    use rand::{prelude::StdRng, Rng, SeedableRng};

    /// A polynomial from small integer coefficients, lowest degree first.
    pub(crate) fn poly<F: FiniteField>(coefficients: &[u64]) -> UnivariatePolynomial<F> {
        let elements: Vec<F> = coefficients.iter().map(|c| F::new(*c)).collect();
        UnivariatePolynomial::new(&elements)
    }

    /// The largest FFT domain of at most 16 points that this field can host, or `None` where the
    /// crate cannot yet run an inverse transform over the field at all.
    ///
    /// No single size works over every field in [`for_each_field!`]: `Gf256`'s multiplicative group
    /// has order 255 and `Zp65537`'s has order 2^16, so the only common domain size is one. Each
    /// field therefore gets the largest small domain it admits — a power of two through the
    /// two-adic root, which is the only route a 254-bit field has, otherwise any divisor of
    /// `q - 1`.
    ///
    /// Characteristic 2 is `None` rather than a size: `interpolate` scales by `F::new(n)`, and
    /// `FiniteField::new` is `todo!()` for `BinaryFieldElement`, so every decode over `Gf256`
    /// panics inside the inverse transform. That is #396, in `src/fields/`, and removing this
    /// guard is its acceptance check.
    fn largest_small_domain<F: KnownOrder>(rng: &mut StdRng) -> Option<FFTDomain<F>> {
        if F::characteristic_u128() == Some(2) {
            return None;
        }
        for size in (3..=16usize).rev() {
            let generator = if size.is_power_of_two() {
                F::try_two_adic_root_of_unity(size.trailing_zeros(), rng).ok()
            } else {
                F::try_root_of_unity(size as u64, rng).ok()
            };
            if let Some(generator) = generator {
                if let Ok(domain) = FFTDomain::try_from_generator(generator, size) {
                    return Some(domain);
                }
            }
        }
        panic!("no FFT domain of 3 to 16 points exists over this field");
    }

    /// A random message of the code's length.
    fn random_message<F: FiniteField>(code: &ReedSolomon<F>, rng: &mut StdRng) -> Vec<F> {
        (0..code.message_length()).map(|_| F::random(rng)).collect()
    }

    /// Corrupt `count` distinct positions, each by a nonzero amount.
    fn corrupt<F: FiniteField>(word: &mut [F], count: usize, rng: &mut StdRng) -> Vec<usize> {
        let mut positions: Vec<usize> = (0..word.len()).collect();
        for i in 0..count {
            positions.swap(i, rng.gen_range(i..word.len()));
        }
        let mut chosen = positions[..count].to_vec();
        chosen.sort_unstable();
        for &position in &chosen {
            let mut error = F::random(rng);
            while error.is_zero() {
                error = F::random(rng);
            }
            word[position] += error;
        }
        chosen
    }

    // Encoding then decoding an uncorrupted word returns the message and reports no errors.
    for_each_field!(
        fn an_error_free_round_trip_recovers_the_message<F>() {
            let mut rng = StdRng::seed_from_u64(20261107);
            let Some(domain) = largest_small_domain::<F>(&mut rng) else {
                return;
            };
            let n = domain.size();
            let code = ReedSolomon::new(domain, n - 2).unwrap();
            let message = random_message(&code, &mut rng);
            let codeword = code.encode(&message).unwrap();
            assert_eq!(codeword.len(), n);
            assert!(code.is_codeword(&codeword).unwrap());
            let decoded = code.decode(&codeword).unwrap();
            assert_eq!(decoded.message, message);
            assert_eq!(decoded.codeword, codeword);
            assert!(decoded.error_positions.is_empty());
        }
    );

    // Systematic encoding puts the message verbatim in the first k symbols, and the result is a
    // codeword of the same code.
    for_each_field!(
        fn systematic_encoding_leaves_the_message_in_place<F>() {
            let mut rng = StdRng::seed_from_u64(20261108);
            let Some(domain) = largest_small_domain::<F>(&mut rng) else {
                return;
            };
            let n = domain.size();
            let code = ReedSolomon::new(domain, n - 2).unwrap();
            let message = random_message(&code, &mut rng);
            let codeword = code.encode_systematic(&message).unwrap();
            assert_eq!(&codeword[..code.message_length()], &message[..]);
            assert!(code.is_codeword(&codeword).unwrap());
        }
    );

    // A systematic codeword survives decoding at the full error radius with its message still
    // readable from the first k symbols.
    for_each_field!(
        fn systematic_layout_survives_correction<F>() {
            let mut rng = StdRng::seed_from_u64(20261109);
            let Some(domain) = largest_small_domain::<F>(&mut rng) else {
                return;
            };
            let n = domain.size();
            let code = ReedSolomon::new(domain, n - 4).unwrap();
            let message = random_message(&code, &mut rng);
            let codeword = code.encode_systematic(&message).unwrap();
            let mut received = codeword.clone();
            corrupt(&mut received, code.max_errors(), &mut rng);
            let decoded = code.decode(&received).unwrap();
            assert_eq!(decoded.codeword, codeword);
            assert_eq!(&decoded.codeword[..code.message_length()], &message[..]);
        }
    );

    // Exactly t errors are located and corrected, for every weight up to t.
    for_each_field!(
        fn errors_up_to_the_distance_bound_are_corrected<F>() {
            let mut rng = StdRng::seed_from_u64(20261110);
            let Some(domain) = largest_small_domain::<F>(&mut rng) else {
                return;
            };
            let n = domain.size();
            let code = ReedSolomon::new(domain, n - 4).unwrap();
            assert_eq!(code.max_errors(), 2);
            let message = random_message(&code, &mut rng);
            let codeword = code.encode(&message).unwrap();

            for weight in 0..=code.max_errors() {
                let mut received = codeword.clone();
                let positions = corrupt(&mut received, weight, &mut rng);
                let decoded = code.decode(&received).unwrap();
                assert_eq!(decoded.message, message, "weight {weight}");
                assert_eq!(decoded.codeword, codeword, "weight {weight}");
                assert_eq!(decoded.error_positions, positions, "weight {weight}");
            }
        }
    );

    // t + 1 errors are detected as uncorrectable rather than decoded to some other codeword.
    for_each_field!(
        fn one_error_beyond_the_bound_is_detected_not_mis_corrected<F>() {
            let mut rng = StdRng::seed_from_u64(20261111);
            let Some(domain) = largest_small_domain::<F>(&mut rng) else {
                return;
            };
            let n = domain.size();
            let code = ReedSolomon::new(domain, n - 4).unwrap();
            let message = random_message(&code, &mut rng);
            let codeword = code.encode(&message).unwrap();

            let mut detected = 0;
            for _ in 0..20 {
                let mut received = codeword.clone();
                corrupt(&mut received, code.max_errors() + 1, &mut rng);
                match code.decode(&received) {
                    Err(CodeError::Uncorrectable) => detected += 1,
                    // A decode that succeeds must at least have landed on a genuine codeword, and
                    // never on the transmitted one, since the received word is further from it
                    // than from the answer.
                    Ok(decoded) => {
                        assert!(code.is_codeword(&decoded.codeword).unwrap());
                        assert_ne!(decoded.codeword, codeword);
                    }
                    Err(e) => panic!("unexpected error {e}"),
                }
            }
            assert!(detected > 0, "no beyond-bound pattern was detected at all");
        }
    );

    // Exactly n - k erasures are filled in, and one more is refused.
    for_each_field!(
        fn erasures_are_recovered_up_to_the_redundancy_and_no_further<F>() {
            let mut rng = StdRng::seed_from_u64(20261112);
            let Some(domain) = largest_small_domain::<F>(&mut rng) else {
                return;
            };
            let n = domain.size();
            let code = ReedSolomon::new(domain, n - 3).unwrap();
            assert_eq!(code.max_erasures(), 3);
            let message = random_message(&code, &mut rng);
            let codeword = code.encode(&message).unwrap();

            let erasures: Vec<usize> = (0..code.max_erasures()).collect();
            let mut received = codeword.clone();
            for &position in &erasures {
                received[position] = F::zero();
            }
            let recovered = code.recover_erasures(&received, &erasures).unwrap();
            assert_eq!(recovered.codeword, codeword);
            assert_eq!(recovered.message, message);
            assert_eq!(recovered.error_positions, erasures);

            let too_many: Vec<usize> = (0..code.max_erasures() + 1).collect();
            assert_eq!(
                code.recover_erasures(&received, &too_many),
                Err(CodeError::TooManyErasures {
                    erasures: code.max_erasures() + 1,
                    recoverable: code.max_erasures(),
                })
            );
        }
    );

    // An error at an unerased position is detected by the surviving parity rather than
    // interpolated into a different codeword.
    for_each_field!(
        fn an_error_outside_the_erasures_is_detected<F>() {
            let mut rng = StdRng::seed_from_u64(20261113);
            let Some(domain) = largest_small_domain::<F>(&mut rng) else {
                return;
            };
            let n = domain.size();
            let code = ReedSolomon::new(domain, n - 3).unwrap();
            let message = random_message(&code, &mut rng);
            let codeword = code.encode(&message).unwrap();

            // One erasure leaves two spare parity symbols to check against.
            let mut received = codeword.clone();
            received[0] = F::zero();
            let mut error = F::random(&mut rng);
            while error.is_zero() {
                error = F::random(&mut rng);
            }
            received[n - 1] += error;
            assert_eq!(
                code.recover_erasures(&received, &[0]),
                Err(CodeError::Uncorrectable)
            );
        }
    );

    // Erasing every symbol a rate-1 code has is refused: it has no redundancy to recover from.
    for_each_field!(
        fn the_rate_one_code_corrects_nothing<F>() {
            let mut rng = StdRng::seed_from_u64(20261114);
            let Some(domain) = largest_small_domain::<F>(&mut rng) else {
                return;
            };
            let n = domain.size();
            let code = ReedSolomon::new(domain, n).unwrap();
            assert_eq!(code.max_errors(), 0);
            assert_eq!(code.max_erasures(), 0);
            assert_eq!(code.distance(), 1);

            let message = random_message(&code, &mut rng);
            let codeword = code.encode(&message).unwrap();
            // Every word of length n is a codeword, so decoding is pure interpolation.
            assert!(code.is_codeword(&codeword).unwrap());
            assert_eq!(code.decode(&codeword).unwrap().message, message);
            assert_eq!(
                code.recover_erasures(&codeword, &[0]),
                Err(CodeError::TooManyErasures {
                    erasures: 1,
                    recoverable: 0,
                })
            );
        }
    );

    // A single parity symbol detects one error without being able to correct it, and recovers one
    // erasure.
    for_each_field!(
        fn a_single_parity_symbol_detects_but_cannot_correct<F>() {
            let mut rng = StdRng::seed_from_u64(20261115);
            let Some(domain) = largest_small_domain::<F>(&mut rng) else {
                return;
            };
            let n = domain.size();
            let code = ReedSolomon::new(domain, n - 1).unwrap();
            assert_eq!(code.max_errors(), 0);
            assert_eq!(code.max_erasures(), 1);

            let message = random_message(&code, &mut rng);
            let codeword = code.encode(&message).unwrap();

            // One error at an unknown position moves the word off the code and is reported, but
            // the single syndrome does not say where it is.
            let mut received = codeword.clone();
            corrupt(&mut received, 1, &mut rng);
            assert!(!code.is_codeword(&received).unwrap());
            assert_eq!(code.decode(&received), Err(CodeError::Uncorrectable));

            // The same symbol lost rather than corrupted is recovered, because the position is
            // then known. The one parity symbol is spent on that, so nothing is left to check
            // the answer with.
            let mut erased = codeword.clone();
            erased[0] = F::zero();
            let recovered = code.recover_erasures(&erased, &[0]).unwrap();
            assert_eq!(recovered.codeword, codeword);
            assert_eq!(recovered.message, message);
        }
    );

    // The k = 0 code has the all-zero word as its only codeword, and says so.
    for_each_field!(
        fn the_empty_message_code_has_one_codeword<F>() {
            let mut rng = StdRng::seed_from_u64(20261116);
            let Some(domain) = largest_small_domain::<F>(&mut rng) else {
                return;
            };
            let n = domain.size();
            let code = ReedSolomon::new(domain, 0).unwrap();
            assert_eq!(code.encode(&[]).unwrap(), vec![F::zero(); n]);
            assert_eq!(code.encode_systematic(&[]).unwrap(), vec![F::zero(); n]);

            let zeros = vec![F::zero(); n];
            assert!(code.is_codeword(&zeros).unwrap());
            assert!(code.decode(&zeros).unwrap().message.is_empty());

            let mut received = zeros.clone();
            received[1] = F::one();
            assert!(!code.is_codeword(&received).unwrap());
            assert_eq!(code.decode(&received).unwrap().codeword, zeros);
        }
    );

    // A code whose redundancy is odd detects d - 1 errors while correcting only (d-1)/2.
    for_each_field!(
        fn odd_redundancy_detects_further_than_it_corrects<F>() {
            let mut rng = StdRng::seed_from_u64(20261117);
            let Some(domain) = largest_small_domain::<F>(&mut rng) else {
                return;
            };
            let n = domain.size();
            let code = ReedSolomon::new(domain, n - 3).unwrap();
            assert_eq!(code.max_errors(), 1);
            let message = random_message(&code, &mut rng);
            let codeword = code.encode(&message).unwrap();

            // Up to n - k = 3 errors still move the word off the code, so they are all detected.
            for weight in 1..=3 {
                let mut received = codeword.clone();
                corrupt(&mut received, weight, &mut rng);
                assert!(!code.is_codeword(&received).unwrap(), "weight {weight}");
            }
        }
    );

    // A message of the wrong length is refused rather than padded or truncated.
    #[test]
    fn test_a_message_of_the_wrong_length_is_refused() {
        type F = crate::fields::Zp65537;
        let domain = FFTDomain::<F>::from_generator(
            F::two_adic_root_of_unity(3, &mut StdRng::seed_from_u64(1)),
            8,
        );
        let code = ReedSolomon::new(domain, 5).unwrap();
        assert_eq!(
            code.encode(&[F::one(); 4]),
            Err(CodeError::WrongLength {
                expected: 5,
                actual: 4
            })
        );
        assert_eq!(
            code.decode(&[F::one(); 7]),
            Err(CodeError::WrongLength {
                expected: 8,
                actual: 7
            })
        );
    }

    // A message longer than the block length is not a code at all.
    #[test]
    fn test_a_message_longer_than_the_block_is_not_a_code() {
        type F = crate::fields::Zp65537;
        let domain = FFTDomain::<F>::from_generator(
            F::two_adic_root_of_unity(2, &mut StdRng::seed_from_u64(1)),
            4,
        );
        assert_eq!(
            ReedSolomon::new(domain, 5).err(),
            Some(CodeError::MessageTooLong {
                message_length: 5,
                block_length: 4
            })
        );
    }

    // An erasure index outside the block is reported rather than ignored.
    #[test]
    fn test_an_erasure_outside_the_block_is_reported() {
        type F = crate::fields::Zp65537;
        let domain = FFTDomain::<F>::from_generator(
            F::two_adic_root_of_unity(3, &mut StdRng::seed_from_u64(1)),
            8,
        );
        let code = ReedSolomon::new(domain, 6).unwrap();
        assert_eq!(
            code.recover_erasures(&[F::zero(); 8], &[8]),
            Err(CodeError::ErasureOutOfRange {
                position: 8,
                block_length: 8
            })
        );
    }

    // Repeated erasure positions count once, so a duplicated hole does not exhaust the budget.
    #[test]
    fn test_duplicate_erasure_positions_count_once() {
        type F = crate::fields::Zp65537;
        let mut rng = StdRng::seed_from_u64(7);
        let domain = FFTDomain::<F>::from_generator(F::two_adic_root_of_unity(3, &mut rng), 8);
        let code = ReedSolomon::new(domain, 7).unwrap();
        let message: Vec<F> = (0..7).map(|_| F::random(&mut rng)).collect();
        let codeword = code.encode(&message).unwrap();
        let mut received = codeword.clone();
        received[2] = F::zero();
        let recovered = code.recover_erasures(&received, &[2, 2, 2]).unwrap();
        assert_eq!(recovered.codeword, codeword);
        assert_eq!(recovered.error_positions, vec![2]);
    }

    // The formal derivative differentiates term by term, and kills a constant.
    #[test]
    fn test_the_formal_derivative_differentiates_term_by_term() {
        type F = crate::fields::Zp65537;
        // d/dx (5 + 3x + 4x^2 + x^3) = 3 + 8x + 3x^2.
        assert_eq!(
            formal_derivative(&poly::<F>(&[5, 3, 4, 1])),
            poly::<F>(&[3, 8, 3])
        );
        assert!(formal_derivative(&poly::<F>(&[7])).is_zero());
    }
}
