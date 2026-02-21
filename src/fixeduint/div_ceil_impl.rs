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

//! Ceiling division for FixedUInt.

use super::{const_div, const_is_zero, FixedUInt, MachineWord};
use crate::const_numtraits::{ConstCheckedAdd, ConstDivCeil, ConstOne};
use crate::machineword::ConstMachineWord;

c0nst::c0nst! {
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstDivCeil for FixedUInt<T, N> {
        fn div_ceil(self, rhs: Self) -> Self {
            match self.checked_div_ceil(rhs) {
                Some(v) => v,
                None => panic!("div_ceil: division by zero or overflow"),
            }
        }

        fn checked_div_ceil(self, rhs: Self) -> Option<Self> {
            if const_is_zero(&rhs.array) {
                return None;
            }
            // Use const_div which computes both quotient and remainder in one pass
            let mut quotient = self.array;
            let remainder = const_div(&mut quotient, &rhs.array);
            if const_is_zero(&remainder) {
                Some(Self { array: quotient })
            } else {
                // Use checked_add to return None on overflow
                ConstCheckedAdd::checked_add(&Self { array: quotient }, &Self::one())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_div_ceil() {
        type U16 = FixedUInt<u8, 2>;

        // Exact division
        assert_eq!(
            ConstDivCeil::div_ceil(U16::from(10u8), U16::from(5u8)),
            U16::from(2u8)
        );
        assert_eq!(
            ConstDivCeil::div_ceil(U16::from(10u8), U16::from(2u8)),
            U16::from(5u8)
        );

        // Rounds up
        assert_eq!(
            ConstDivCeil::div_ceil(U16::from(10u8), U16::from(3u8)),
            U16::from(4u8)
        ); // 10/3 = 3.33... -> 4
        assert_eq!(
            ConstDivCeil::div_ceil(U16::from(11u8), U16::from(3u8)),
            U16::from(4u8)
        ); // 11/3 = 3.66... -> 4
        assert_eq!(
            ConstDivCeil::div_ceil(U16::from(12u8), U16::from(3u8)),
            U16::from(4u8)
        ); // 12/3 = 4 exact

        // Edge cases
        assert_eq!(
            ConstDivCeil::div_ceil(U16::from(0u8), U16::from(5u8)),
            U16::from(0u8)
        );
        assert_eq!(
            ConstDivCeil::div_ceil(U16::from(1u8), U16::from(5u8)),
            U16::from(1u8)
        ); // 1/5 = 0.2 -> 1
        assert_eq!(
            ConstDivCeil::div_ceil(U16::from(1u8), U16::from(1u8)),
            U16::from(1u8)
        );
    }

    #[test]
    fn test_checked_div_ceil() {
        type U16 = FixedUInt<u8, 2>;

        assert_eq!(
            ConstDivCeil::checked_div_ceil(U16::from(10u8), U16::from(3u8)),
            Some(U16::from(4u8))
        );

        // Division by zero
        assert_eq!(
            ConstDivCeil::checked_div_ceil(U16::from(10u8), U16::from(0u8)),
            None
        );

        // Edge case: MAX / 2 = 32767 remainder 1, ceil = 32768
        assert_eq!(
            ConstDivCeil::checked_div_ceil(U16::from(65535u16), U16::from(2u16)),
            Some(U16::from(32768u16))
        );

        // Edge case: MAX / 1 = MAX exactly (no remainder, no +1 needed)
        assert_eq!(
            ConstDivCeil::checked_div_ceil(U16::from(65535u16), U16::from(1u16)),
            Some(U16::from(65535u16))
        );
    }

    c0nst::c0nst! {
        pub c0nst fn const_div_ceil<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            a: FixedUInt<T, N>,
            b: FixedUInt<T, N>,
        ) -> FixedUInt<T, N> {
            ConstDivCeil::div_ceil(a, b)
        }
    }

    #[test]
    fn test_const_div_ceil() {
        type U16 = FixedUInt<u8, 2>;

        assert_eq!(
            const_div_ceil(U16::from(10u8), U16::from(3u8)),
            U16::from(4u8)
        );

        #[cfg(feature = "nightly")]
        {
            const TEN: U16 = FixedUInt { array: [10, 0] };
            const THREE: U16 = FixedUInt { array: [3, 0] };
            const RESULT: U16 = const_div_ceil(TEN, THREE);
            assert_eq!(RESULT, FixedUInt { array: [4, 0] });
        }
    }
}
