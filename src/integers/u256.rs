//! 256-bit unsigned integer.
//!
//! This type is designed to be "const friendly": its constructors are const functions, allowing
//! them to be used to initialize constants. This is particularly useful for defining numerical
//! types with const generic parameters.

use crate::integers::ux64::Ux64;

pub type U256 = Ux64<4>;

#[cfg(test)]
mod tests {
    use crate::integers::u256::U256;
    use rand::thread_rng;

    #[test]
    fn test_from_u64() {
        let x: u64 = 1287235;
        let instance = U256::from(x);
        assert_eq!(instance.words[0], x);
        assert_eq!(instance.words[1], 0);
        assert_eq!(instance.words[2], 0);
        assert_eq!(instance.words[3], 0);
    }

    // #[test]
    // fn test_from_u128() {
    //     let x: u128 = u128::MAX;
    //     let instance = U256::from(x);
    //     assert_eq!(instance.words[0], u64::MAX);
    //     assert_eq!(instance.words[1], u64::MAX);
    //     assert_eq!(instance.words[2], 0);
    //     assert_eq!(instance.words[3], 0);
    // }

    #[test]
    fn test_zero() {
        // let zero = 0;
        let instance = U256::from(0);
        assert_eq!(U256::zero(), instance)
    }

    #[test]
    fn test_one() {
        // let one = 1u128;
        let instance = U256::from(1);
        assert_eq!(U256::one(), instance)
    }

    #[test]
    fn test_gcd() {
        // gcd(a,0) = a, gcd(0,b) = b
        assert_eq!(U256::from(5), U256::gcd(U256::from(5), U256::from(0)));
        assert_eq!(U256::from(6), U256::gcd(U256::from(0), U256::from(6)));

        assert_eq!(U256::from(1), U256::gcd(U256::from(5), U256::from(6)));
        assert_eq!(U256::from(8), U256::gcd(U256::from(16), U256::from(24)));
        assert_eq!(U256::from(2), U256::gcd(U256::from(18), U256::from(88)));

        // TODO: larger values.

        // gcd(a,b) = gcd(b,a)
        let mut rng = thread_rng();
        for _i in 0..1000 {
            let a = U256::random(&mut rng);
            let b = U256::random(&mut rng);
            assert_eq!(U256::gcd(a, b), U256::gcd(b, a));
        }
    }

    #[test]
    // Should return carry=true if the sum overflows.
    fn test_carrying_add() {
        // No carry-in, No overflow.
        {
            let a = U256::new([u64::MAX, u64::MAX, 0, 0]);
            let (sum, carry) = a.carrying_add(U256::one(), false);
            assert_eq!(sum, U256::new([0u64, 0, 1, 0]));
            // assert_eq!(sum, U256::from_128_bit_words(0, 1u128));
            assert!(!carry);
        }

        // Carry-in, No overflow.
        {
            let a = U256::new([u64::MAX, u64::MAX, 0, 0]);
            // let a = U256::from(u128::MAX);
            let (sum, carry) = a.carrying_add(U256::one(), true);
            assert_eq!(sum, U256::new([1u64, 0, 1, 0]));
            assert!(!carry);
        }

        // No carry-in, With overflow.
        {
            let a = U256::new([u64::MAX; 4]);
            let (sum, carry) = a.carrying_add(U256::one(), false);
            assert_eq!(sum, U256::zero());
            assert!(carry);
        }

        // Carry-in, With overflow
        {
            let a = U256::new([u64::MAX; 4]);
            let (sum, carry) = a.carrying_add(U256::one(), true);
            assert_eq!(sum, U256::one());
            assert!(carry);
        }
    }

    #[test]
    // (Carrying) Addition is commutative.
    fn test_carrying_add_is_commutative() {
        let mut rng = thread_rng();
        for _i in 0..1000 {
            let a = U256::random(&mut rng);
            let b = U256::random(&mut rng);
            assert_eq!(a.carrying_add(b, false), b.carrying_add(a, false));
        }
    }

    #[test]
    fn test_add() {
        // 123 + 456*2^128
        let a = U256::new([123u64, 0, 456, 0]);
        // 535 + 23*2^128
        let b = U256::new([535u64, 0, 23, 0]);
        assert_eq!(a + b, U256::new([658u64, 0, 479, 0]));
    }

    #[test]
    #[should_panic]
    fn test_add_overflowing() {
        let a = U256::new([123u64, 0, u64::MAX, u64::MAX]);
        let _sum = a + a;
    }

    #[test]
    fn test_borrowing_sub_one() {
        let a = U256::from(1u64 << 63);
        let b = U256::from(1u64);
        let (diff, borrow) = a.borrowing_sub(b, false);
        assert_eq!(diff, U256::from(9223372036854775807u64)); // (1<<63) - 1
        assert!(!borrow);
    }

    #[test]
    // 'borrow' should be true when b>a.
    fn test_borrowing_sub_with_borrow() {
        let a = U256::from(0u64);
        let b = U256::from(1u64);
        let (diff, borrow) = a.borrowing_sub(b, false);
        assert_eq!(diff, U256::max()); // 0-1 wraps around to U256::max()
        assert!(borrow);
    }

    #[ignore]
    #[test]
    fn test_sub() {
        unimplemented!()
    }

    #[test]
    #[should_panic]
    fn test_sub_wrapping() {
        let a = U256::from(0u64);
        let b = U256::from(1u64);
        let _diff = a - b;
    }

    #[test]
    // Multiply some small values.
    fn test_carrying_mul_one() {
        let a = U256::from(17);
        let b = U256::from(19);
        let (low, high) = a.carrying_mul(b, U256::from(0));
        assert_eq!(low, U256::from(323));
        assert_eq!(high, U256::from(0));
    }

    #[test]
    // Multiply values whose product fits in 256 bits.
    fn test_carrying_mul_two() {
        let a = U256::from_dec_str("9872349872349873498372498234792").unwrap();
        let b = U256::from_dec_str("98127301297120012301231213210").unwrap();
        let (low, high) = a.carrying_mul(b, U256::from(0));
        assert_eq!(
            low,
            U256::from_dec_str("968747050434660329601373955723862939888152461268977592002320")
                .unwrap()
        );
        assert_eq!(high, U256::zero());
    }

    #[test]
    // Multiply values whose product does not fit in 256 bits.
    fn test_carrying_mul_three() {
        // 2^240 = 1766847064778384329583297500742918515827483896875618958121606201292619776
        let a = U256::from_dec_str(
            "1766847064778384329583297500742918515827483896875618958121606201292619776",
        )
        .unwrap();

        // 2^198 = 401734511064747568885490523085290650630550748445698208825344
        let b = U256::from_dec_str("401734511064747568885490523085290650630550748445698208825344")
            .unwrap();

        // 2^438 = 709803441694928604052074031140629428079727891296209043243642772637343054798240159498233447962659731992932150006119314388217384402944
        let (low, high) = a.carrying_mul(b, U256::zero());
        assert_eq!(low, U256::zero());
        // 2^182 = 6129982163463555433433388108601236734474956488734408704
        assert_eq!(
            high,
            U256::from_dec_str("6129982163463555433433388108601236734474956488734408704").unwrap()
        );
    }

    #[test]
    // a * b == b * a
    fn test_carrying_mul_is_commutative() {
        let mut rng = thread_rng();
        for _i in 0..1000 {
            let a = U256::random(&mut rng);
            let b = U256::random(&mut rng);
            println!("a: {:#?}", a);
            println!("b: {:#?}", b);
            assert_eq!(
                a.carrying_mul(b, U256::zero()),
                b.carrying_mul(a, U256::zero())
            );
        }
    }

    #[test]
    fn test_mul() {
        let a = U256::from_dec_str("9872349872349873498372498234792").unwrap();
        let b = U256::from_dec_str("98127301297120012301231213210").unwrap();
        let prod = a * b;
        assert_eq!(
            prod,
            U256::from_dec_str("968747050434660329601373955723862939888152461268977592002320")
                .unwrap()
        );
    }

    #[test]
    #[should_panic]
    fn test_mul_overflowing() {
        let a = U256::max();
        let _prod = a * a;
    }

    #[test]
    // u = qv + r
    fn test_div_with_remainder() {
        let mut rng = thread_rng();
        for _i in 0..1000 {
            let u = U256::random(&mut rng);
            let v = U256::random(&mut rng);
            let (q, r) = u.div_with_remainder(v);
            assert_eq!(u, q * v + r);
        }
    }

    #[ignore]
    #[test]
    fn test_to_string() {
        unimplemented!()
    }

    #[test]
    fn test_from_dec_str() {
        let a = U256::from_dec_str("111").unwrap();
        assert_eq!(a, U256::from(111u64));

        // // 2^128 -1 = 340282366920938463463374607431768211455
        // let b = U256::from_dec_str("340282366920938463463374607431768211455").unwrap();
        // assert_eq!(b, U256::from(340282366920938463463374607431768211455u128));

        // 2^250 = 1809251394333065553493296640760748560207343510400633813116524750123642650624
        let c = U256::from_dec_str(
            "1809251394333065553493296640760748560207343510400633813116524750123642650624",
        )
        .unwrap();
        assert_eq!(c, U256::new([0u64, 0, 0, 1 << 58]));
    }

    #[test]
    // An empty string parses to 0.
    fn test_from_dec_str_empty_str() {
        let a = U256::from_dec_str("").unwrap();
        assert_eq!(a, U256::zero());
    }

    #[test]
    #[should_panic]
    fn test_from_dec_str_too_big() {
        // 2^256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936
        let _a = U256::from_dec_str(
            "115792089237316195423570985008687907853269984665640564039457584007913129639936",
        )
        .unwrap();
    }

    #[test]
    #[should_panic]
    fn test_from_dec_str_invalid_character() {
        let _a = U256::from_dec_str("111meow222").unwrap();
    }

    #[test]
    fn test_ord() {
        assert!(U256::one() > U256::zero());
        assert!(U256::new([12, 13, 14, 15]) > U256::new([13, 13, 13, 13]));
        assert!(U256::from(1u64 << 58) > U256::from(1u64 << 27));
        // TODO: better test coverage.
    }
}
