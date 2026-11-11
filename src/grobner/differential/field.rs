//! Which field a differential case is stated over, and the two sides' syntax for its elements.
//!
//! A characteristic does not name a field: GF(2) and GF(2^8) are both characteristic two, so a
//! case carrying only `2` cannot be dispatched to the right monomorphization and cannot record
//! which irreducible polynomial it was computed modulo. [`Gf256`](crate::fields::Gf256) is
//! `x^8+x^4+x^3+x+1` and [`Gf256Mq`](crate::fields::Gf256Mq) is `x^8+x^4+x^3+x^2+1`, and the same
//! pair of bytes has two different products in them — so a case that did not record its modulus
//! would be checked against whichever one the dispatch happened to pick.
//!
//! # The modulus is pinned behaviourally
//! [`CaseField::matches`] does not ask a field type what its modulus is; it multiplies. In
//! `GF(2)[x]/(P)` with `P = x^m + r`, the relation `x^m = r` holds and determines `P`, so raising
//! the element whose bit pattern is `2` to the `m`-th power and comparing it with the element
//! whose bit pattern is `r` accepts exactly one modulus. That is what makes modulus agreement an
//! assertion rather than a convention.
//!
//! # Two syntaxes for one element
//! Over a binary extension Zeebra writes an element as the decimal of its coefficient bit pattern
//! — `10` is `x^3 + x`, settled by #377 — and Singular, over `ring R = (2,a),...` with a declared
//! `minpoly`, writes `(a^3+a)`. Neither side can read the other, so [`CaseField::to_singular`] and
//! [`CaseField::from_singular`] rewrite the coefficients of a polynomial's text while leaving its
//! monomials, exponents and term structure alone. Over a prime field both are the identity: the
//! two syntaxes already coincide there, which is why the prime half of the harness never needed
//! this.

use std::fmt::{Display, Formatter};

use crate::KnownOrder;

/// The field a generated system, an oracle query and a recorded case are all stated over.
///
/// `Copy` so that a committed fixture stays a table of literals.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CaseField {
    /// GF(p) for a prime `p`, where a residue is its own representation.
    Prime {
        /// The prime.
        characteristic: u64,
    },

    /// GF(2^m) = GF(2)\[x\] / (modulus), with `modulus` the bit pattern of the irreducible
    /// polynomial — so `283` is `x^8+x^4+x^3+x+1` and `m` is read off its degree.
    Binary {
        /// The irreducible polynomial, as a bit pattern. Monic of degree `m`, so at least 4.
        modulus: u64,
    },
}

/// Why a piece of field text could not be read.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FieldTextError {
    /// The text is not a polynomial in the shared syntax.
    Malformed {
        /// What was being read.
        text: String,
        /// Where it stopped making sense.
        detail: String,
    },

    /// A coefficient is not an element of this field.
    OutOfRange {
        /// The coefficient as written.
        coefficient: String,
        /// The field it was read against.
        field: CaseField,
    },
}

impl Display for FieldTextError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Malformed { text, detail } => write!(f, "cannot read {:?}: {}", text, detail),
            Self::OutOfRange { coefficient, field } => {
                write!(f, "{} is not an element of GF({})", coefficient, field)
            }
        }
    }
}

impl std::error::Error for FieldTextError {}

/// The parameter Singular's algebraic extensions are declared with, and the one variable name the
/// coefficient syntax reserves.
pub const EXTENSION_PARAMETER: &str = "a";

impl CaseField {
    /// GF(`characteristic`).
    pub const fn prime(characteristic: u64) -> Self {
        Self::Prime { characteristic }
    }

    /// GF(2^m) modulo the bit pattern `modulus`.
    pub const fn binary(modulus: u64) -> Self {
        Self::Binary { modulus }
    }

    /// The characteristic.
    pub const fn characteristic(&self) -> u64 {
        match self {
            Self::Prime { characteristic } => *characteristic,
            Self::Binary { .. } => 2,
        }
    }

    /// The extension degree: one over a prime field, and the modulus' degree over an extension.
    pub const fn degree(&self) -> u32 {
        match self {
            Self::Prime { .. } => 1,
            Self::Binary { modulus } => 63 - modulus.leading_zeros(),
        }
    }

    /// The number of elements.
    pub const fn order(&self) -> u128 {
        match self {
            Self::Prime { characteristic } => *characteristic as u128,
            Self::Binary { .. } => 1u128 << self.degree(),
        }
    }

    /// Whether `F` is this field, modulus included.
    ///
    /// Characteristic alone is not enough — GF(2) and GF(2^8) share it — and neither is order with
    /// characteristic, since two irreducible polynomials of the same degree give two
    /// non-interchangeable fields of the same order. Over a binary extension the modulus is pinned
    /// by the arithmetic: `x^m = r` for `P = x^m + r`, which only the intended `P` satisfies.
    pub fn matches<F: KnownOrder>(&self) -> bool {
        match *self {
            Self::Prime { characteristic } => {
                let p = u128::from(characteristic);
                F::characteristic_u128() == Some(p) && F::order_u128() == Some(p)
            }
            Self::Binary { modulus } => {
                let m = self.degree();
                if F::characteristic_u128() != Some(2) || F::order_u128() != Some(self.order()) {
                    return false;
                }
                // `element_at` over a binary field is the bit pattern, so `2` is x and
                // `modulus - 2^m` is the modulus' tail. See the module header.
                let Some(x) = F::element_at(2) else {
                    return false;
                };
                let Some(tail) = F::element_at(u128::from(modulus) - self.order()) else {
                    return false;
                };
                x.pow(u128::from(m)) == tail
            }
        }
    }

    /// A name for this field that is safe in an identifier, a file name and a fixture name.
    ///
    /// [`Display`] writes `2^8/283`, which reads well in a report and badly in a path. This is the
    /// same text with the separator replaced, and [`CaseField::from_str`](std::str::FromStr::from_str) accepts both.
    pub fn slug(&self) -> String {
        self.to_string().replace('/', "_")
    }

    /// This field as the Rust expression a generated fixture table holds.
    ///
    /// A `const fn` constructor rather than a struct literal, so a table stays readable and the
    /// emitter does not have to know the variants' field names.
    pub fn rust_literal(&self) -> String {
        match self {
            Self::Prime { characteristic } => format!("CaseField::prime({})", characteristic),
            Self::Binary { modulus } => format!("CaseField::binary({})", modulus),
        }
    }

    /// The coefficient-field part of a Singular `ring` declaration.
    pub fn singular_coefficients(&self) -> String {
        match self {
            Self::Prime { characteristic } => characteristic.to_string(),
            Self::Binary { .. } => format!("(2,{})", EXTENSION_PARAMETER),
        }
    }

    /// The `minpoly` Singular must be given, or `None` where the field needs none.
    ///
    /// Singular's own `(2^8, a)` Galois fields carry a modulus from an internal table that cannot
    /// be chosen, so the harness declares an algebraic extension of GF(2) instead and sets its
    /// minimal polynomial explicitly. That is the only form in which the two sides can be made to
    /// agree on which polynomial they reduce by.
    pub fn singular_minpoly(&self) -> Option<String> {
        match self {
            Self::Prime { .. } => None,
            Self::Binary { modulus } => Some(render_binary(*modulus, false)),
        }
    }

    /// `a + b` on the integer representations, which is what a text generator needs.
    ///
    /// Residue addition over a prime field and XOR over a binary extension. **Not cosmetic**: the
    /// generator merges two terms on one monomial before rendering, and merging them modulo 2
    /// rather than by XOR would produce a polynomial neither side was sent.
    pub const fn add(&self, a: u64, b: u64) -> u64 {
        match self {
            Self::Prime { characteristic } => (a + b) % *characteristic,
            Self::Binary { .. } => a ^ b,
        }
    }

    /// The nonzero element `1 + draw mod (q - 1)`, so a draw never yields an absent term.
    pub const fn nonzero(&self, draw: u64) -> u64 {
        1 + draw % (self.order() as u64 - 1)
    }

    /// `text`, written in Zeebra's syntax, rewritten in Singular's for this field.
    ///
    /// The identity over a prime field. Over a binary extension every coefficient — a decimal that
    /// is not an exponent — becomes a polynomial in the extension parameter.
    ///
    /// # Errors
    /// [`FieldTextError`] if `text` is not a polynomial in the shared syntax, or holds a
    /// coefficient outside this field.
    pub fn to_singular(&self, text: &str) -> Result<String, FieldTextError> {
        match self {
            Self::Prime { .. } => Ok(text.to_string()),
            Self::Binary { .. } => self.rewrite(text, Direction::ToSingular),
        }
    }

    /// `text`, as Singular printed it, rewritten in Zeebra's syntax for this field.
    ///
    /// # Errors
    /// As [`Self::to_singular`].
    pub fn from_singular(&self, text: &str) -> Result<String, FieldTextError> {
        match self {
            Self::Prime { .. } => Ok(text.to_string()),
            Self::Binary { .. } => self.rewrite(text, Direction::FromSingular),
        }
    }

    /// A bare polynomial in the extension parameter as a bit pattern, with no degree bound.
    ///
    /// For reading Singular's `minpoly` back, which has degree `m` exactly and so is *not* an
    /// element of the field — it is the modulus. Comparing what comes back with the modulus asked
    /// for is what turns "both sides use the same polynomial" into an assertion.
    ///
    /// # Errors
    /// [`FieldTextError::Malformed`] if `text` is not a sum of powers of the parameter.
    pub fn read_binary_polynomial(text: &str) -> Result<u64, FieldTextError> {
        let trimmed = text.trim();
        let inner = match trimmed.strip_prefix('(') {
            Some(rest) => rest
                .strip_suffix(')')
                .ok_or_else(|| FieldTextError::Malformed {
                    text: text.to_string(),
                    detail: "an opening parenthesis with no closing one".to_string(),
                })?,
            None => trimmed,
        };
        read_binary(inner).ok_or_else(|| FieldTextError::Malformed {
            text: text.to_string(),
            detail: format!("not a sum of powers of {}", EXTENSION_PARAMETER),
        })
    }

    /// Rewrite the coefficients of a polynomial's text, leaving everything else alone.
    fn rewrite(&self, text: &str, direction: Direction) -> Result<String, FieldTextError> {
        let malformed = |detail: String| FieldTextError::Malformed {
            text: text.to_string(),
            detail,
        };

        let bytes = text.as_bytes();
        let mut out = String::with_capacity(text.len());
        let mut index = 0usize;
        // A decimal run is an exponent when it follows a caret, and a coefficient otherwise. That
        // is the whole of the disambiguation: `x1^2` has a digit in the name and a digit in the
        // exponent, and neither is a coefficient.
        let mut after_caret = false;

        while index < bytes.len() {
            let byte = bytes[index];
            match byte {
                b'^' => {
                    after_caret = true;
                    out.push('^');
                    index += 1;
                }
                b'0'..=b'9' => {
                    let start = index;
                    while index < bytes.len() && bytes[index].is_ascii_digit() {
                        index += 1;
                    }
                    let digits = &text[start..index];
                    if after_caret {
                        out.push_str(digits);
                    } else {
                        let value: u64 = digits.parse().map_err(|_| {
                            malformed(format!("{} does not fit a coefficient", digits))
                        })?;
                        out.push_str(&self.render_coefficient(value, direction)?);
                    }
                    after_caret = false;
                }
                b'(' if direction == Direction::FromSingular => {
                    let close = text[index..].find(')').ok_or_else(|| {
                        malformed("a coefficient opens a parenthesis it never closes".to_string())
                    })? + index;
                    let inner = &text[index + 1..close];
                    let value = read_binary(inner).ok_or_else(|| FieldTextError::OutOfRange {
                        coefficient: inner.to_string(),
                        field: *self,
                    })?;
                    if u128::from(value) >= self.order() {
                        return Err(FieldTextError::OutOfRange {
                            coefficient: inner.to_string(),
                            field: *self,
                        });
                    }
                    out.push_str(&value.to_string());
                    index = close + 1;
                    after_caret = false;
                }
                b'a'..=b'z' | b'A'..=b'Z' | b'_' => {
                    let start = index;
                    while index < bytes.len()
                        && (bytes[index].is_ascii_alphanumeric() || bytes[index] == b'_')
                    {
                        index += 1;
                    }
                    let name = &text[start..index];
                    // A bare parameter, which Singular prints unparenthesized for `minpoly` and
                    // which a hand-written case may use. A variable called `a` would be
                    // indistinguishable, which is why the harness reserves the name.
                    if direction == Direction::FromSingular && name == EXTENSION_PARAMETER {
                        let exponent = read_exponent(text, &mut index);
                        let shift = exponent.ok_or_else(|| {
                            malformed(format!("{} has an unreadable exponent", name))
                        })?;
                        if shift >= self.degree() {
                            return Err(FieldTextError::OutOfRange {
                                coefficient: format!("{}^{}", name, shift),
                                field: *self,
                            });
                        }
                        out.push_str(&(1u64 << shift).to_string());
                    } else {
                        out.push_str(name);
                    }
                    after_caret = false;
                }
                _ => {
                    out.push(byte as char);
                    index += 1;
                    after_caret = false;
                }
            }
        }
        Ok(out)
    }

    /// One coefficient, rewritten for the side `direction` points at.
    fn render_coefficient(
        &self,
        value: u64,
        direction: Direction,
    ) -> Result<String, FieldTextError> {
        if u128::from(value) >= self.order() {
            return Err(FieldTextError::OutOfRange {
                coefficient: value.to_string(),
                field: *self,
            });
        }
        Ok(match direction {
            // A bare decimal in Singular's dialect is in GF(2), so only 0 and 1 may stay bare.
            Direction::ToSingular => render_binary(value, true),
            Direction::FromSingular => value.to_string(),
        })
    }
}

/// Which way a rewrite goes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Direction {
    ToSingular,
    FromSingular,
}

/// A bit pattern as a polynomial in the extension parameter.
///
/// `parenthesize` wraps anything with more than one term, and anything that is a power of the
/// parameter, which is the form Singular both prints and accepts as a coefficient factor.
fn render_binary(pattern: u64, parenthesize: bool) -> String {
    if pattern == 0 {
        return "0".to_string();
    }
    if pattern == 1 {
        return "1".to_string();
    }
    let mut terms: Vec<String> = Vec::new();
    for bit in (0..64).rev() {
        if pattern & (1u64 << bit) == 0 {
            continue;
        }
        terms.push(match bit {
            0 => "1".to_string(),
            1 => EXTENSION_PARAMETER.to_string(),
            _ => format!("{}^{}", EXTENSION_PARAMETER, bit),
        });
    }
    let joined = terms.join("+");
    if parenthesize {
        format!("({})", joined)
    } else {
        joined
    }
}

/// A sum of powers of the extension parameter as a bit pattern, or `None` if it is not one.
///
/// Signs are accepted and treated as addition: the coefficients are in GF(2), where `-1 = 1`.
/// Repeated powers XOR, which is addition in the same place.
fn read_binary(text: &str) -> Option<u64> {
    let mut pattern = 0u64;
    let mut any = false;
    for term in text.split('+').flat_map(|t| t.split('-')) {
        let term = term.trim();
        if term.is_empty() {
            continue;
        }
        any = true;
        let bit = if let Some(rest) = term.strip_prefix(EXTENSION_PARAMETER) {
            match rest.trim() {
                "" => 1u32,
                rest => {
                    let exponent = rest.strip_prefix('^').unwrap_or(rest);
                    exponent.trim().parse::<u32>().ok()?
                }
            }
        } else {
            // A GF(2) constant. `1` is the only nonzero one, and `0` contributes nothing.
            match term.parse::<u64>().ok()? {
                0 => continue,
                1 => 0u32,
                _ => return None,
            }
        };
        if bit >= 64 {
            return None;
        }
        pattern ^= 1u64 << bit;
    }
    any.then_some(pattern)
}

/// The exponent of a parameter occurrence at `index`, advancing past it. One where there is none.
fn read_exponent(text: &str, index: &mut usize) -> Option<u32> {
    let bytes = text.as_bytes();
    if bytes.get(*index) != Some(&b'^') {
        return Some(1);
    }
    let start = *index + 1;
    let mut end = start;
    while end < bytes.len() && bytes[end].is_ascii_digit() {
        end += 1;
    }
    if end == start {
        return None;
    }
    *index = end;
    text[start..end].parse().ok()
}

impl Display for CaseField {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Prime { characteristic } => write!(f, "{}", characteristic),
            Self::Binary { modulus } => write!(f, "2^{}/{}", self.degree(), modulus),
        }
    }
}

impl std::str::FromStr for CaseField {
    type Err = String;

    /// `13`, or `2^8/283` — and `2^8_283`, which is what [`CaseField::slug`] writes.
    fn from_str(value: &str) -> Result<Self, Self::Err> {
        let value = value.trim();
        if let Ok(characteristic) = value.parse::<u64>() {
            if characteristic < 2 {
                return Err(format!("{} is not a prime", characteristic));
            }
            return Ok(Self::prime(characteristic));
        }

        let (base, modulus) = value
            .split_once('/')
            .or_else(|| value.split_once('_'))
            .ok_or_else(|| format!("{:?} is neither a prime nor `2^m/modulus`", value))?;
        let degree: u32 = base
            .strip_prefix("2^")
            .ok_or_else(|| format!("{:?} is not an extension of GF(2)", value))?
            .parse()
            .map_err(|_| format!("{:?} has an unreadable degree", value))?;
        let modulus: u64 = modulus
            .parse()
            .map_err(|_| format!("{:?} has an unreadable modulus", value))?;

        let spec = Self::binary(modulus);
        if spec.degree() != degree {
            return Err(format!(
                "{:?} declares degree {} and the modulus {} has degree {}",
                value,
                degree,
                modulus,
                spec.degree()
            ));
        }
        Ok(spec)
    }
}

#[cfg(test)]
mod tests {
    use super::{CaseField, FieldTextError};
    use crate::fields::{Gf256, Gf256Mq, Gf32, Zp13, Zp2};
    use std::str::FromStr;

    /// The AES modulus, which is `Gf256`'s.
    const GF256: CaseField = CaseField::binary(0x11B);

    /// The Fukuoka MQ Challenge modulus, which is `Gf256Mq`'s. Same order, different field.
    const GF256_MQ: CaseField = CaseField::binary(0x11D);

    /// A binary extension reports characteristic two, its order and its degree from the modulus.
    #[test]
    fn test_a_binary_extension_reports_its_degree_and_order() {
        assert_eq!(GF256.characteristic(), 2);
        assert_eq!(GF256.degree(), 8);
        assert_eq!(GF256.order(), 256);
        assert_eq!(CaseField::binary(0x25).degree(), 5);
        assert_eq!(CaseField::binary(0x25).order(), 32);
    }

    /// A prime field reports its characteristic as both characteristic and order.
    #[test]
    fn test_a_prime_field_has_degree_one() {
        let field = CaseField::prime(13);
        assert_eq!(field.characteristic(), 13);
        assert_eq!(field.degree(), 1);
        assert_eq!(field.order(), 13);
    }

    /// `matches` distinguishes GF(2) from GF(2^8), which a characteristic cannot.
    #[test]
    fn test_gf2_and_gf256_are_not_the_same_field() {
        assert!(CaseField::prime(2).matches::<Zp2>());
        assert!(!CaseField::prime(2).matches::<Gf256>());
        assert!(GF256.matches::<Gf256>());
        assert!(!GF256.matches::<Zp2>());
    }

    /// `matches` rejects a field of the right order and the wrong modulus.
    ///
    /// The acceptance criterion of #378: `Gf256` and `Gf256Mq` are both GF(2^8) and the same byte
    /// decodes to a different product in each, so a case recorded modulo one must not be checked
    /// against the other.
    #[test]
    fn test_the_modulus_is_part_of_the_field() {
        assert!(GF256.matches::<Gf256>());
        assert!(!GF256.matches::<Gf256Mq>());
        assert!(GF256_MQ.matches::<Gf256Mq>());
        assert!(!GF256_MQ.matches::<Gf256>());
    }

    /// `matches` rejects a binary extension of the wrong degree.
    #[test]
    fn test_a_binary_extension_of_the_wrong_degree_is_rejected() {
        assert!(!GF256.matches::<Gf32>());
        assert!(CaseField::binary(0x25).matches::<Gf32>());
    }

    /// `matches` rejects an unrelated prime field.
    #[test]
    fn test_an_unrelated_prime_field_is_rejected() {
        assert!(CaseField::prime(13).matches::<Zp13>());
        assert!(!CaseField::prime(13).matches::<Zp2>());
        assert!(!GF256.matches::<Zp13>());
    }

    /// Every field spelling round-trips through `Display` and `FromStr`.
    #[test]
    fn test_a_field_round_trips_through_its_text() {
        for field in [
            CaseField::prime(2),
            CaseField::prime(2147483647),
            GF256,
            GF256_MQ,
            CaseField::binary(0x25),
        ] {
            let text = field.to_string();
            assert_eq!(
                CaseField::from_str(&text),
                Ok(field),
                "{} did not round-trip",
                text
            );
            assert_eq!(
                CaseField::from_str(&field.slug()),
                Ok(field),
                "{} did not round-trip",
                field.slug()
            );
        }
    }

    /// A field's text is what a report and a fixture name want: no separator a path would reject.
    #[test]
    fn test_the_text_forms_are_the_documented_ones() {
        assert_eq!(GF256.to_string(), "2^8/283");
        assert_eq!(GF256.slug(), "2^8_283");
        assert_eq!(CaseField::prime(7).to_string(), "7");
        assert_eq!(CaseField::prime(7).slug(), "7");
    }

    /// A declared degree that disagrees with the modulus' own degree is refused.
    #[test]
    fn test_a_degree_that_contradicts_the_modulus_is_refused() {
        assert!(CaseField::from_str("2^4/283").is_err());
        assert!(CaseField::from_str("3^2/11").is_err());
        assert!(CaseField::from_str("nonsense").is_err());
    }

    /// Singular is given an algebraic extension of GF(2) and the modulus it must reduce by.
    #[test]
    fn test_the_singular_ring_declares_the_minimal_polynomial() {
        assert_eq!(GF256.singular_coefficients(), "(2,a)");
        assert_eq!(GF256.singular_minpoly().as_deref(), Some("a^8+a^4+a^3+a+1"));
        assert_eq!(
            GF256_MQ.singular_minpoly().as_deref(),
            Some("a^8+a^4+a^3+a^2+1")
        );
        assert_eq!(CaseField::prime(13).singular_coefficients(), "13");
        assert_eq!(CaseField::prime(13).singular_minpoly(), None);
    }

    /// Addition of representations is residue addition over a prime and XOR over an extension.
    #[test]
    fn test_addition_follows_the_field() {
        assert_eq!(CaseField::prime(13).add(7, 9), 3);
        assert_eq!(GF256.add(0b1010, 0b0110), 0b1100);
        assert_eq!(GF256.add(5, 5), 0);
    }

    /// A draw becomes a nonzero element, over the whole field and not only its prime subfield.
    #[test]
    fn test_a_draw_becomes_a_nonzero_element() {
        for draw in 0..1024u64 {
            let value = GF256.nonzero(draw);
            assert!((1..256).contains(&value), "{} is not a nonzero byte", value);
        }
        assert_eq!(
            (0..255u64)
                .map(|draw| GF256.nonzero(draw))
                .collect::<std::collections::HashSet<u64>>()
                .len(),
            255,
            "the draw does not reach every nonzero element"
        );
        assert_eq!(CaseField::prime(2).nonzero(17), 1);
    }

    /// A coefficient crosses to Singular as a polynomial in the parameter and back as a decimal.
    #[test]
    fn test_a_coefficient_round_trips_through_singulars_syntax() {
        let zeebra = "10*x1^2+x2+255";
        let singular = GF256.to_singular(zeebra).expect("rewrites");
        assert_eq!(singular, "(a^3+a)*x1^2+x2+(a^7+a^6+a^5+a^4+a^3+a^2+a+1)");
        assert_eq!(GF256.from_singular(&singular).as_deref(), Ok(zeebra));
    }

    /// An exponent is never mistaken for a coefficient, and a variable's digits are left alone.
    #[test]
    fn test_an_exponent_is_not_a_coefficient() {
        assert_eq!(GF256.to_singular("x1^8*x2^10").as_deref(), Ok("x1^8*x2^10"));
        assert_eq!(
            GF256.from_singular("x1^8*x2^10").as_deref(),
            Ok("x1^8*x2^10")
        );
    }

    /// Zero and one stay bare in both syntaxes, since they are the same in GF(2) and GF(2^8).
    #[test]
    fn test_zero_and_one_are_written_the_same_way_on_both_sides() {
        assert_eq!(GF256.to_singular("0").as_deref(), Ok("0"));
        assert_eq!(GF256.to_singular("1+x1").as_deref(), Ok("1+x1"));
        assert_eq!(GF256.from_singular("0").as_deref(), Ok("0"));
        assert_eq!(GF256.from_singular("1+x1").as_deref(), Ok("1+x1"));
    }

    /// Singular's bare parameter, which it prints for `minpoly` and for a degree-one coefficient.
    #[test]
    fn test_a_bare_parameter_reads_as_its_bit_pattern() {
        assert_eq!(GF256.from_singular("(a)*x1").as_deref(), Ok("2*x1"));
        assert_eq!(GF256.from_singular("(a^7)*x1").as_deref(), Ok("128*x1"));
    }

    /// Over a prime field both rewrites are the identity, so the recorded prime corpus is untouched.
    #[test]
    fn test_a_prime_field_rewrites_nothing() {
        for text in ["x2^2-2*x1-2*x2-3", "0", "1259705035+x1"] {
            assert_eq!(CaseField::prime(13).to_singular(text).as_deref(), Ok(text));
            assert_eq!(
                CaseField::prime(13).from_singular(text).as_deref(),
                Ok(text)
            );
        }
    }

    /// A coefficient outside the field is refused rather than reduced into it.
    #[test]
    fn test_a_coefficient_outside_the_field_is_refused() {
        assert!(matches!(
            GF256.to_singular("256*x1"),
            Err(FieldTextError::OutOfRange { .. })
        ));
        assert!(matches!(
            GF256.from_singular("(a^8)*x1"),
            Err(FieldTextError::OutOfRange { .. })
        ));
    }

    /// Singular's echoed `minpoly` reads back as the bit pattern that was declared.
    ///
    /// The modulus-agreement check on the oracle's side: the degree-`m` polynomial it reports is
    /// not an element of the field, so it is read with no degree bound and compared with what the
    /// script asked for.
    #[test]
    fn test_the_echoed_minpoly_reads_back_as_the_modulus() {
        assert_eq!(
            CaseField::read_binary_polynomial("(a^8+a^4+a^3+a+1)"),
            Ok(0x11B)
        );
        assert_eq!(
            CaseField::read_binary_polynomial("a^8+a^4+a^3+a^2+1"),
            Ok(0x11D)
        );
        assert!(CaseField::read_binary_polynomial("(a^8+").is_err());
        assert!(CaseField::read_binary_polynomial("x1+1").is_err());
    }
}
