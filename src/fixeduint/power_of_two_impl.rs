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
use crate::const_numtraits::{
    ConstBitPrimInt, ConstBounded, ConstOne, ConstPowerOfTwo, ConstWrappingSub, ConstZero,
};
use crate::machineword::ConstMachineWord;
use crate::personality::{Personality, PersonalityTag};

c0nst::c0nst! {
    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> ConstPowerOfTwo for FixedUInt<T, N, P> {
        fn is_power_of_two(&self) -> bool {
            match P::TAG {
                PersonalityTag::Nct => {
                    !self.is_zero() && (*self & (*self - Self::one())).is_zero()
                }
                PersonalityTag::Ct => {
                    let a = !self.is_zero();
                    let b = (*self & self.wrapping_sub(&Self::one())).is_zero();
                    a & b
                }
            }
        }

        fn next_power_of_two(self) -> Self {
            match P::TAG {
                PersonalityTag::Nct => {
                    match self.checked_next_power_of_two() {
                        Some(v) => v,
                        None => panic!("FixedUInt::next_power_of_two overflow: result exceeds type capacity"),
                    }
                }
                PersonalityTag::Ct => {
                    // CT path: saturate to MAX on overflow (same convention
                    // as SaturatingAdd/Sub/Mul). The Nct path's panic is
                    // value-dependent and so unavailable here; silently
                    // returning a wrong power of two would be worse than
                    // a defined saturation sentinel.
                    let m_one = <Self as ConstWrappingSub>::wrapping_sub(&self, &Self::one());
                    let leading = ConstBitPrimInt::leading_zeros(m_one);
                    let bits = Self::BIT_SIZE as u32 - leading;
                    let shifted = Self::one() << (bits as usize);
                    let is_zero = <Self as ConstZero>::is_zero(&self) as u8;
                    // Overflow when bits >= BIT_SIZE (and self != 0).
                    let overflow = ((bits >= Self::BIT_SIZE as u32) as u8) & (1u8 ^ is_zero);
                    let saturated = crate::fixeduint::const_ct_select(
                        shifted,
                        <Self as ConstBounded>::max_value(),
                        overflow,
                    );
                    crate::fixeduint::const_ct_select(saturated, Self::one(), is_zero)
                }
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
            let leading = ConstBitPrimInt::leading_zeros(m_one);
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
        pub c0nst fn const_is_power_of_two<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(
            v: &FixedUInt<T, N, P>,
        ) -> bool {
            ConstPowerOfTwo::is_power_of_two(v)
        }

        pub c0nst fn const_next_power_of_two<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(
            v: FixedUInt<T, N, P>,
        ) -> FixedUInt<T, N, P> {
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
            const FOUR: U16 = FixedUInt::from_array([4, 0]);
            const FIVE: U16 = FixedUInt::from_array([5, 0]);
            const IS_POW2_TRUE: bool = const_is_power_of_two(&FOUR);
            const IS_POW2_FALSE: bool = const_is_power_of_two(&FIVE);
            const NEXT_POW2: U16 = const_next_power_of_two(FIVE);

            assert!(IS_POW2_TRUE);
            assert!(!IS_POW2_FALSE);
            assert_eq!(NEXT_POW2, FixedUInt::from_array([8, 0]));
        }
    }
}
