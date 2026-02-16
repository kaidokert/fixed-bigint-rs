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
            // A number is a power of two if it has exactly one bit set
            // and is not zero
            if self.is_zero() {
                return false;
            }
            ConstPrimInt::count_ones(*self) == 1u32
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
            if self.is_power_of_two() {
                return Some(self);
            }
            // Find the position of the highest set bit using leading_zeros
            // bit_length = total_bits - leading_zeros
            let total_bits = (N * core::mem::size_of::<T>() * 8) as u32;
            let leading = ConstPrimInt::leading_zeros(self);
            let bits = total_bits - leading;
            // Check if we can shift 1 left by that many bits
            if bits >= total_bits {
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
