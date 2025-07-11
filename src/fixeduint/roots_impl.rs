use crate::fixeduint::FixedUInt;
use crate::machineword::MachineWord;
use num_integer::Roots;
use num_traits::{FromPrimitive, One, PrimInt, Zero};

impl<T: MachineWord, const N: usize> Roots for FixedUInt<T, N> {
    fn nth_root(&self, n: u32) -> Self {
        if n == 0 {
            panic!("nth_root: n must be non-zero");
        }

        if self.is_zero() {
            return Self::zero();
        }

        if self.is_one() || n == 1 {
            return *self;
        }

        let bit_len = self.bit_length();
        if n > bit_len && !self.is_zero() && !self.is_one() {
            return Self::one();
        }

        // Initial guess: use ceiling(bit_len / n) for overestimate
        let initial_exp = bit_len.div_ceil(n).max(1);
        let mut x = Self::one() << (initial_exp as usize);

        // Constants using FromPrimitive
        let n_val = Self::from_u32(n).expect("n too large for FixedUInt");
        let n_minus_1 = if n > 1 {
            Self::from_u32(n - 1).expect("n too large for FixedUInt")
        } else {
            Self::zero()
        };

        // Newton's method iteration
        loop {
            let x_pow_n_minus_1 = x.pow(n - 1);

            if x_pow_n_minus_1.is_zero() {
                break;
            }

            let quotient = *self / x_pow_n_minus_1;

            let numerator = x * n_minus_1 + quotient;
            let x_new = numerator / n_val;

            if x_new >= x {
                break;
            }

            x = x_new;
        }

        // Final adjustment to ensure r^n <= self < (r+1)^n
        while x.pow(n) > *self {
            x -= Self::one();
        }

        let mut x_plus_one = x + Self::one();
        while x_plus_one.pow(n) <= *self {
            x += Self::one();
            x_plus_one = x + Self::one();
        }

        x
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_integer::Roots;
    use num_traits::{One, PrimInt};

    #[test]
    fn test_sqrt_basic() {
        type TestInt = FixedUInt<u32, 2>;

        assert_eq!(TestInt::from(0u8).sqrt(), TestInt::from(0u8));
        assert_eq!(TestInt::from(1u8).sqrt(), TestInt::from(1u8));
        assert_eq!(TestInt::from(4u8).sqrt(), TestInt::from(2u8));
        assert_eq!(TestInt::from(9u8).sqrt(), TestInt::from(3u8));
        assert_eq!(TestInt::from(16u8).sqrt(), TestInt::from(4u8));
        assert_eq!(TestInt::from(25u8).sqrt(), TestInt::from(5u8));

        // Test non-perfect squares
        assert_eq!(TestInt::from(2u8).sqrt(), TestInt::from(1u8));
        assert_eq!(TestInt::from(3u8).sqrt(), TestInt::from(1u8));
        assert_eq!(TestInt::from(8u8).sqrt(), TestInt::from(2u8));
        assert_eq!(TestInt::from(15u8).sqrt(), TestInt::from(3u8));
        assert_eq!(TestInt::from(24u8).sqrt(), TestInt::from(4u8));
    }

    #[test]
    fn test_cbrt_basic() {
        type TestInt = FixedUInt<u32, 2>;

        assert_eq!(TestInt::from(0u8).cbrt(), TestInt::from(0u8));
        assert_eq!(TestInt::from(1u8).cbrt(), TestInt::from(1u8));
        assert_eq!(TestInt::from(8u8).cbrt(), TestInt::from(2u8));
        assert_eq!(TestInt::from(27u8).cbrt(), TestInt::from(3u8));
        assert_eq!(TestInt::from(64u8).cbrt(), TestInt::from(4u8));
        assert_eq!(TestInt::from(125u8).cbrt(), TestInt::from(5u8));

        // Test non-perfect cubes
        assert_eq!(TestInt::from(2u8).cbrt(), TestInt::from(1u8));
        assert_eq!(TestInt::from(7u8).cbrt(), TestInt::from(1u8));
        assert_eq!(TestInt::from(26u8).cbrt(), TestInt::from(2u8));
        assert_eq!(TestInt::from(63u8).cbrt(), TestInt::from(3u8));
    }

    #[test]
    fn test_nth_root_basic() {
        type TestInt = FixedUInt<u32, 2>;

        // Test 4th roots
        assert_eq!(TestInt::from(16u8).nth_root(4), TestInt::from(2u8));
        assert_eq!(TestInt::from(81u8).nth_root(4), TestInt::from(3u8));
        assert_eq!(TestInt::from(15u8).nth_root(4), TestInt::from(1u8));
        assert_eq!(TestInt::from(80u8).nth_root(4), TestInt::from(2u8));

        // Test 5th roots
        assert_eq!(TestInt::from(32u8).nth_root(5), TestInt::from(2u8));
        assert_eq!(TestInt::from(243u8).nth_root(5), TestInt::from(3u8));
        assert_eq!(TestInt::from(31u8).nth_root(5), TestInt::from(1u8));

        // Test n=1 (should return self)
        assert_eq!(TestInt::from(42u8).nth_root(1), TestInt::from(42u8));
        assert_eq!(TestInt::from(123u8).nth_root(1), TestInt::from(123u8));
    }

    #[test]
    fn test_nth_root_edge_cases() {
        type TestInt = FixedUInt<u32, 2>;

        // Test with 0 and 1
        assert_eq!(TestInt::from(0u8).nth_root(2), TestInt::from(0u8));
        assert_eq!(TestInt::from(1u8).nth_root(2), TestInt::from(1u8));
        assert_eq!(TestInt::from(0u8).nth_root(10), TestInt::from(0u8));
        assert_eq!(TestInt::from(1u8).nth_root(10), TestInt::from(1u8));

        // Test with large n (should return 1 for numbers > 1)
        assert_eq!(TestInt::from(2u8).nth_root(100), TestInt::from(1u8));
        assert_eq!(TestInt::from(1000u16).nth_root(50), TestInt::from(1u8));
    }

    #[test]
    #[should_panic(expected = "nth_root: n must be non-zero")]
    fn test_nth_root_zero_n() {
        let x = FixedUInt::<u32, 2>::from(16u8);
        x.nth_root(0);
    }

    #[test]
    fn test_root_correctness() {
        type TestInt = FixedUInt<u32, 2>;

        // Test that r^n <= x < (r+1)^n for various cases
        for x in 1..=100u16 {
            let x_int = TestInt::from(x);

            // Test square root
            let sqrt_x = x_int.sqrt();
            assert!(sqrt_x.pow(2) <= x_int);
            assert!((sqrt_x + TestInt::one()).pow(2) > x_int);

            // Test cube root
            let cbrt_x = x_int.cbrt();
            assert!(cbrt_x.pow(3) <= x_int);
            assert!((cbrt_x + TestInt::one()).pow(3) > x_int);

            // Test 4th root
            let root4_x = x_int.nth_root(4);
            assert!(root4_x.pow(4) <= x_int);
            assert!((root4_x + TestInt::one()).pow(4) > x_int);
        }
    }
}
