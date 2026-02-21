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

//! Midpoint (average) implementation for FixedUInt.

use super::{FixedUInt, MachineWord};
use crate::const_numtrait::ConstMidpoint;
use crate::machineword::ConstMachineWord;

c0nst::c0nst! {
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstMidpoint for FixedUInt<T, N> {
        fn midpoint(self, rhs: Self) -> Self {
            // (a & b) + ((a ^ b) >> 1) avoids overflow
            (self & rhs) + ((self ^ rhs) >> 1usize)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_midpoint() {
        type U16 = FixedUInt<u8, 2>;

        // Simple midpoint
        assert_eq!(
            ConstMidpoint::midpoint(U16::from(0u8), U16::from(10u8)),
            U16::from(5u8)
        );

        // Order doesn't matter
        assert_eq!(
            ConstMidpoint::midpoint(U16::from(10u8), U16::from(0u8)),
            U16::from(5u8)
        );

        // Midpoint rounds down
        assert_eq!(
            ConstMidpoint::midpoint(U16::from(0u8), U16::from(9u8)),
            U16::from(4u8)
        );

        // Same values
        assert_eq!(
            ConstMidpoint::midpoint(U16::from(42u8), U16::from(42u8)),
            U16::from(42u8)
        );

        // Max values (no overflow)
        let max = U16::from(0xFFFFu16);
        assert_eq!(ConstMidpoint::midpoint(max, max), max);

        // 0 and max
        assert_eq!(
            ConstMidpoint::midpoint(U16::from(0u8), max),
            U16::from(0x7FFFu16)
        );
    }

    c0nst::c0nst! {
        pub c0nst fn const_midpoint<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            a: FixedUInt<T, N>,
            b: FixedUInt<T, N>,
        ) -> FixedUInt<T, N> {
            ConstMidpoint::midpoint(a, b)
        }
    }

    #[test]
    fn test_const_midpoint() {
        type U16 = FixedUInt<u8, 2>;

        assert_eq!(
            const_midpoint(U16::from(0u8), U16::from(10u8)),
            U16::from(5u8)
        );

        #[cfg(feature = "nightly")]
        {
            const A: U16 = FixedUInt { array: [0, 0] };
            const B: U16 = FixedUInt { array: [10, 0] };
            const MID: U16 = const_midpoint(A, B);
            assert_eq!(MID, FixedUInt { array: [5, 0] });

            // Test with max values
            const MAX: U16 = FixedUInt {
                array: [0xFF, 0xFF],
            };
            const MID_MAX: U16 = const_midpoint(MAX, MAX);
            assert_eq!(MID_MAX, MAX);
        }
    }

    /// Polymorphic test: verify midpoint produces identical results across
    /// different word layouts for the same values.
    #[test]
    fn test_midpoint_polymorphic() {
        fn test_mid<T>(a: T, b: T, expected: T)
        where
            T: ConstMidpoint + Eq + core::fmt::Debug + Copy,
        {
            assert_eq!(ConstMidpoint::midpoint(a, b), expected);
            assert_eq!(ConstMidpoint::midpoint(b, a), expected); // order doesn't matter
        }

        // Test with different layouts
        type U8x2 = FixedUInt<u8, 2>;
        type U8x4 = FixedUInt<u8, 4>;
        type U16x2 = FixedUInt<u16, 2>;

        // 0 and 100
        test_mid(U8x2::from(0u8), U8x2::from(100u8), U8x2::from(50u8));
        test_mid(U8x4::from(0u8), U8x4::from(100u8), U8x4::from(50u8));
        test_mid(U16x2::from(0u8), U16x2::from(100u8), U16x2::from(50u8));

        // Same with primitives
        test_mid(0u8, 100u8, 50u8);
        test_mid(0u16, 100u16, 50u16);
        test_mid(0u32, 100u32, 50u32);

        // Rounding down: (0 + 99) / 2 = 49.5 -> 49
        test_mid(U8x2::from(0u8), U8x2::from(99u8), U8x2::from(49u8));
        test_mid(0u8, 99u8, 49u8);

        // Large values that would overflow with naive (a+b)/2
        let max_u16 = U8x2::from(0xFFFFu16);
        test_mid(max_u16, max_u16, max_u16);
        test_mid(u16::MAX, u16::MAX, u16::MAX);
    }
}
