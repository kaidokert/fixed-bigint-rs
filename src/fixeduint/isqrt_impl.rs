// Copyright 2021 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Integer square root for FixedUInt.

use super::{FixedUInt, MachineWord};
use crate::const_numtrait::{ConstIsqrt, ConstPrimInt, ConstZero};
use crate::machineword::ConstMachineWord;

c0nst::c0nst! {
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstIsqrt for FixedUInt<T, N> {
        fn isqrt(self) -> Self {
            // For unsigned types, isqrt always succeeds
            match ConstIsqrt::checked_isqrt(self) {
                Some(v) => v,
                None => unreachable!(),
            }
        }

        fn checked_isqrt(self) -> Option<Self> {
            // Bit-by-bit algorithm for integer square root
            // Returns the largest r such that r * r <= self
            if self.is_zero() {
                return Some(Self::zero());
            }

            // Start with the highest bit position that could be set in the result
            // For sqrt, the result has at most half the bits of the input
            let mut result = Self::zero();

            // Find starting bit position: half of the bit length of self
            let bit_len = Self::BIT_SIZE - ConstPrimInt::leading_zeros(self) as usize;
            let start_bit = bit_len.div_ceil(2);

            let mut bit_pos = start_bit;
            while bit_pos > 0 {
                bit_pos -= 1;

                // Try setting this bit in the result
                let mut candidate = result;
                candidate.array[bit_pos / Self::WORD_BITS] |=
                    T::one().shl(bit_pos % Self::WORD_BITS);

                // Check if candidate * candidate <= self
                // To avoid overflow, we check if candidate <= self / candidate
                // But division is expensive, so we compute candidate * candidate directly
                // and compare. Since candidate has at most half the bits of self,
                // candidate * candidate won't overflow.
                let square = candidate * candidate;
                if square <= self {
                    result = candidate;
                }
            }

            Some(result)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_isqrt() {
        type U16 = FixedUInt<u8, 2>;

        // Perfect squares
        assert_eq!(ConstIsqrt::isqrt(U16::from(0u8)), U16::from(0u8));
        assert_eq!(ConstIsqrt::isqrt(U16::from(1u8)), U16::from(1u8));
        assert_eq!(ConstIsqrt::isqrt(U16::from(4u8)), U16::from(2u8));
        assert_eq!(ConstIsqrt::isqrt(U16::from(9u8)), U16::from(3u8));
        assert_eq!(ConstIsqrt::isqrt(U16::from(16u8)), U16::from(4u8));
        assert_eq!(ConstIsqrt::isqrt(U16::from(25u8)), U16::from(5u8));
        assert_eq!(ConstIsqrt::isqrt(U16::from(100u8)), U16::from(10u8));
        assert_eq!(ConstIsqrt::isqrt(U16::from(144u8)), U16::from(12u8));

        // Non-perfect squares (floor)
        assert_eq!(ConstIsqrt::isqrt(U16::from(2u8)), U16::from(1u8));
        assert_eq!(ConstIsqrt::isqrt(U16::from(3u8)), U16::from(1u8));
        assert_eq!(ConstIsqrt::isqrt(U16::from(5u8)), U16::from(2u8));
        assert_eq!(ConstIsqrt::isqrt(U16::from(8u8)), U16::from(2u8));
        assert_eq!(ConstIsqrt::isqrt(U16::from(10u8)), U16::from(3u8));
        assert_eq!(ConstIsqrt::isqrt(U16::from(15u8)), U16::from(3u8));
        assert_eq!(ConstIsqrt::isqrt(U16::from(24u8)), U16::from(4u8));
    }

    #[test]
    fn test_isqrt_larger_values() {
        type U16 = FixedUInt<u8, 2>;

        // Larger values
        assert_eq!(ConstIsqrt::isqrt(U16::from(10000u16)), U16::from(100u8));
        assert_eq!(ConstIsqrt::isqrt(U16::from(65535u16)), U16::from(255u8)); // sqrt(65535) = 255.998...
        assert_eq!(ConstIsqrt::isqrt(U16::from(65025u16)), U16::from(255u8)); // 255^2 = 65025
    }

    #[test]
    fn test_checked_isqrt() {
        type U16 = FixedUInt<u8, 2>;

        // For unsigned, checked_isqrt always returns Some
        assert_eq!(
            ConstIsqrt::checked_isqrt(U16::from(0u8)),
            Some(U16::from(0u8))
        );
        assert_eq!(
            ConstIsqrt::checked_isqrt(U16::from(16u8)),
            Some(U16::from(4u8))
        );
        assert_eq!(
            ConstIsqrt::checked_isqrt(U16::from(17u8)),
            Some(U16::from(4u8))
        );
    }

    #[test]
    fn test_isqrt_correctness() {
        type U16 = FixedUInt<u8, 2>;

        // Verify r^2 <= n < (r+1)^2 for various values
        for n in 0..=1000u16 {
            let n_int = U16::from(n);
            let r = ConstIsqrt::isqrt(n_int);

            // r^2 <= n
            assert!(r * r <= n_int, "Failed: {}^2 > {}", r, n);

            // (r+1)^2 > n (unless r+1 would overflow, but won't happen for small n)
            let r_plus_1 = r + U16::from(1u8);
            assert!(
                r_plus_1 * r_plus_1 > n_int,
                "Failed: {}^2 <= {}",
                r_plus_1,
                n
            );
        }
    }

    c0nst::c0nst! {
        pub c0nst fn const_isqrt<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            v: FixedUInt<T, N>,
        ) -> FixedUInt<T, N> {
            ConstIsqrt::isqrt(v)
        }
    }

    #[test]
    fn test_const_isqrt() {
        type U16 = FixedUInt<u8, 2>;

        assert_eq!(const_isqrt(U16::from(16u8)), U16::from(4u8));
        assert_eq!(const_isqrt(U16::from(100u8)), U16::from(10u8));

        #[cfg(feature = "nightly")]
        {
            const SIXTEEN: U16 = FixedUInt { array: [16, 0] };
            const RESULT: U16 = const_isqrt(SIXTEEN);
            assert_eq!(RESULT, FixedUInt { array: [4, 0] });
        }
    }
}
