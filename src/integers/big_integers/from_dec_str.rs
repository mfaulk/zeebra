use crate::integers::{multi_word_add, multi_word_mul};
use core::fmt;

/// Conversion from decimal string error
#[derive(Debug, PartialEq)]
pub enum FromDecStrErr {
    /// Char not from range 0-9.
    InvalidCharacter(u8),
    /// Value does not fit into type.
    InvalidLength,
}

impl fmt::Display for FromDecStrErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                FromDecStrErr::InvalidCharacter(_c) => "A character is not in the range 0-9.",
                FromDecStrErr::InvalidLength => "The number is too large for the type.",
            }
        )
    }
}

impl std::error::Error for FromDecStrErr {}

/// Convert from a decimal string.
pub fn from_dec_str(value: &str) -> Result<Vec<u64>, FromDecStrErr> {
    let mut result = vec![0u64; 1];
    for b in value.bytes().map(|b| b.wrapping_sub(b'0')) {
        if b > 9 {
            return Err(FromDecStrErr::InvalidCharacter(b));
        }

        result = multi_word_mul(&result, &[10u64]);
        result = multi_word_add(&result, &[b as u64]);
    }
    Ok(result)
}

// TODO: to_dec_str

#[cfg(test)]
mod tests {
    use crate::integers::big_integers::from_dec_str::from_dec_str;

    #[test]
    fn test_from_dec_str() {
        assert_eq!(from_dec_str("").unwrap(), vec![0]);
        assert_eq!(from_dec_str("0").unwrap(), vec![0]);
        assert_eq!(from_dec_str("111").unwrap(), vec![111]);

        // 2^128 -1 = 340282366920938463463374607431768211455 = u128::MAX
        assert_eq!(
            from_dec_str("340282366920938463463374607431768211455").unwrap(),
            vec![u64::MAX, u64::MAX]
        );

        // 2^250 = 1809251394333065553493296640760748560207343510400633813116524750123642650624
        assert_eq!(
            from_dec_str(
                "1809251394333065553493296640760748560207343510400633813116524750123642650624"
            )
            .unwrap(),
            vec![0, 0, 0, 1 << 58]
        );
    }
}
