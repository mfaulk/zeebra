//! Integer-related utility functions.

/// Split u128 into low and high u64s.
pub const fn split_u128(value: u128) -> (u64, u64) {
    let low = (value & 0xffff_ffff_ffff_ffff) as u64;
    let high = (value >> 64) as u64;
    (low, high)
}

pub const fn u128_from_parts(low: u64, hi: u64) -> u128 {
    (hi as u128) << 64 | low as u128
}

#[cfg(test)]
mod tests {
    use crate::integers::utils::{split_u128, u128_from_parts};
    use proptest::prelude::*;

    fn split_and_recover(x: u128) {
        let (low, hi) = split_u128(x);
        let y = u128_from_parts(low, hi);
        assert_eq!(x, y);
    }

    proptest! {
        #[test]
        fn test_foo(x in any::<u128>()) {
            split_and_recover(x);
        }
    }
}
