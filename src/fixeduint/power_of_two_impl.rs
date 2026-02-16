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

//! Power-of-two operations for FixedUInt.

use super::{FixedUInt, MachineWord};
use crate::const_numtrait::{ConstOne, ConstPowerOfTwo, ConstPrimInt, ConstZero};
use crate::machineword::ConstMachineWord;

c0nst::c0nst! {
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstPowerOfTwo for FixedUInt<T, N> {
        fn is_power_of_two(&self) -> bool {
            // Standard bitwise trick: n is power of two iff n != 0 && (n & (n-1)) == 0
            // This works because a power of two has exactly one bit set,
            // and subtracting 1 flips all lower bits, so AND gives zero.
            !self.is_zero() && (*self & (*self - Self::one())).is_zero()
        }

        fn next_power_of_two(self) -> Self {
            match self.checked_next_power_of_two() {
                Some(v) => v,
                None => panic!("next_power_of_two overflow"),
            }
        }

        fn checked_next_power_of_two(self) -> Option<Self> {
            if self.is_zero() {
                return Some(Self::one());
            }
            // Bit manipulation trick: (n-1).leading_zeros() gives the bit position
            // needed for the next power of two, handling both power-of-two and
            // non-power-of-two inputs correctly.
            let m_one = self - Self::one();
            let leading = ConstPrimInt::leading_zeros(m_one);
            let bits = Self::BIT_SIZE as u32 - leading;

            // Check for overflow
            if bits >= Self::BIT_SIZE as u32 {
                return None;
            }
            Some(Self::one() << (bits as usize))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_power_of_two() {
        type U16 = FixedUInt<u8, 2>;

        assert!(!ConstPowerOfTwo::is_power_of_two(&U16::from(0u8)));
        assert!(ConstPowerOfTwo::is_power_of_two(&U16::from(1u8)));
        assert!(ConstPowerOfTwo::is_power_of_two(&U16::from(2u8)));
        assert!(!ConstPowerOfTwo::is_power_of_two(&U16::from(3u8)));
        assert!(ConstPowerOfTwo::is_power_of_two(&U16::from(4u8)));
        assert!(!ConstPowerOfTwo::is_power_of_two(&U16::from(5u8)));
        assert!(ConstPowerOfTwo::is_power_of_two(&U16::from(8u8)));
        assert!(ConstPowerOfTwo::is_power_of_two(&U16::from(16u8)));
        assert!(ConstPowerOfTwo::is_power_of_two(&U16::from(128u8)));
        assert!(ConstPowerOfTwo::is_power_of_two(&U16::from(256u16)));
        assert!(!ConstPowerOfTwo::is_power_of_two(&U16::from(255u8)));
    }

    #[test]
    fn test_next_power_of_two() {
        type U16 = FixedUInt<u8, 2>;

        assert_eq!(
            ConstPowerOfTwo::next_power_of_two(U16::from(0u8)),
            U16::from(1u8)
        );
        assert_eq!(
            ConstPowerOfTwo::next_power_of_two(U16::from(1u8)),
            U16::from(1u8)
        );
        assert_eq!(
            ConstPowerOfTwo::next_power_of_two(U16::from(2u8)),
            U16::from(2u8)
        );
        assert_eq!(
            ConstPowerOfTwo::next_power_of_two(U16::from(3u8)),
            U16::from(4u8)
        );
        assert_eq!(
            ConstPowerOfTwo::next_power_of_two(U16::from(4u8)),
            U16::from(4u8)
        );
        assert_eq!(
            ConstPowerOfTwo::next_power_of_two(U16::from(5u8)),
            U16::from(8u8)
        );
        assert_eq!(
            ConstPowerOfTwo::next_power_of_two(U16::from(7u8)),
            U16::from(8u8)
        );
        assert_eq!(
            ConstPowerOfTwo::next_power_of_two(U16::from(8u8)),
            U16::from(8u8)
        );
        assert_eq!(
            ConstPowerOfTwo::next_power_of_two(U16::from(9u8)),
            U16::from(16u8)
        );
        assert_eq!(
            ConstPowerOfTwo::next_power_of_two(U16::from(100u8)),
            U16::from(128u8)
        );
        assert_eq!(
            ConstPowerOfTwo::next_power_of_two(U16::from(128u8)),
            U16::from(128u8)
        );
        assert_eq!(
            ConstPowerOfTwo::next_power_of_two(U16::from(129u8)),
            U16::from(256u16)
        );
    }

    #[test]
    fn test_checked_next_power_of_two() {
        type U16 = FixedUInt<u8, 2>;

        assert_eq!(
            ConstPowerOfTwo::checked_next_power_of_two(U16::from(0u8)),
            Some(U16::from(1u8))
        );
        assert_eq!(
            ConstPowerOfTwo::checked_next_power_of_two(U16::from(1u8)),
            Some(U16::from(1u8))
        );
        assert_eq!(
            ConstPowerOfTwo::checked_next_power_of_two(U16::from(100u8)),
            Some(U16::from(128u8))
        );

        // Test overflow case - 32769 needs next power of 2 = 65536 which overflows u16
        let large = U16::from(32769u16);
        assert_eq!(ConstPowerOfTwo::checked_next_power_of_two(large), None);

        // But 32768 is already a power of two
        let pow2 = U16::from(32768u16);
        assert_eq!(ConstPowerOfTwo::checked_next_power_of_two(pow2), Some(pow2));
    }

    c0nst::c0nst! {
        pub c0nst fn const_is_power_of_two<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            v: &FixedUInt<T, N>,
        ) -> bool {
            ConstPowerOfTwo::is_power_of_two(v)
        }

        pub c0nst fn const_next_power_of_two<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            v: FixedUInt<T, N>,
        ) -> FixedUInt<T, N> {
            ConstPowerOfTwo::next_power_of_two(v)
        }
    }

    #[test]
    fn test_const_power_of_two() {
        type U16 = FixedUInt<u8, 2>;

        assert!(const_is_power_of_two(&U16::from(4u8)));
        assert!(!const_is_power_of_two(&U16::from(5u8)));
        assert_eq!(const_next_power_of_two(U16::from(5u8)), U16::from(8u8));

        #[cfg(feature = "nightly")]
        {
            const FOUR: U16 = FixedUInt { array: [4, 0] };
            const FIVE: U16 = FixedUInt { array: [5, 0] };
            const IS_POW2_TRUE: bool = const_is_power_of_two(&FOUR);
            const IS_POW2_FALSE: bool = const_is_power_of_two(&FIVE);
            const NEXT_POW2: U16 = const_next_power_of_two(FIVE);

            assert!(IS_POW2_TRUE);
            assert!(!IS_POW2_FALSE);
            assert_eq!(NEXT_POW2, FixedUInt { array: [8, 0] });
        }
    }
}
