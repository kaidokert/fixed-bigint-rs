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

//! Integer logarithm implementations for FixedUInt.

use super::{FixedUInt, MachineWord};
use crate::const_numtraits::{ConstIlog, ConstPrimInt, ConstZero};
use crate::machineword::ConstMachineWord;

c0nst::c0nst! {
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstIlog for FixedUInt<T, N> {
        fn ilog2(self) -> u32 {
            match self.checked_ilog2() {
                Some(v) => v,
                None => panic!("ilog2: argument is zero"),
            }
        }

        fn ilog10(self) -> u32 {
            match self.checked_ilog10() {
                Some(v) => v,
                None => panic!("ilog10: argument is zero"),
            }
        }

        fn ilog(self, base: Self) -> u32 {
            match self.checked_ilog(base) {
                Some(v) => v,
                None => panic!("ilog: argument is zero or base is less than 2"),
            }
        }

        fn checked_ilog2(self) -> Option<u32> {
            if self.is_zero() {
                return None;
            }
            // ilog2 = position of highest set bit = BIT_SIZE - 1 - leading_zeros
            let leading = ConstPrimInt::leading_zeros(self);
            Some(Self::BIT_SIZE as u32 - 1 - leading)
        }

        fn checked_ilog10(self) -> Option<u32> {
            if self.is_zero() {
                return None;
            }
            // Count how many times we can divide by 10
            let ten: Self = core::convert::From::from(10u8);
            let mut n = self;
            let mut count = 0u32;
            while n >= ten {
                n /= ten;
                count += 1;
            }
            Some(count)
        }

        fn checked_ilog(self, base: Self) -> Option<u32> {
            if self.is_zero() {
                return None;
            }
            let two: Self = core::convert::From::from(2u8);
            if base < two {
                return None;
            }
            // Count how many times we can divide by base
            let mut n = self;
            let mut count = 0u32;
            while n >= base {
                n /= base;
                count += 1;
            }
            Some(count)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ilog2() {
        type U16 = FixedUInt<u8, 2>;

        assert_eq!(ConstIlog::ilog2(U16::from(1u8)), 0);
        assert_eq!(ConstIlog::ilog2(U16::from(2u8)), 1);
        assert_eq!(ConstIlog::ilog2(U16::from(3u8)), 1);
        assert_eq!(ConstIlog::ilog2(U16::from(4u8)), 2);
        assert_eq!(ConstIlog::ilog2(U16::from(7u8)), 2);
        assert_eq!(ConstIlog::ilog2(U16::from(8u8)), 3);
        assert_eq!(ConstIlog::ilog2(U16::from(255u8)), 7);
        assert_eq!(ConstIlog::ilog2(U16::from(256u16)), 8);
        assert_eq!(ConstIlog::ilog2(U16::from(32768u16)), 15);
    }

    #[test]
    fn test_ilog10() {
        type U16 = FixedUInt<u8, 2>;

        assert_eq!(ConstIlog::ilog10(U16::from(1u8)), 0);
        assert_eq!(ConstIlog::ilog10(U16::from(9u8)), 0);
        assert_eq!(ConstIlog::ilog10(U16::from(10u8)), 1);
        assert_eq!(ConstIlog::ilog10(U16::from(99u8)), 1);
        assert_eq!(ConstIlog::ilog10(U16::from(100u8)), 2);
        assert_eq!(ConstIlog::ilog10(U16::from(999u16)), 2);
        assert_eq!(ConstIlog::ilog10(U16::from(1000u16)), 3);
        assert_eq!(ConstIlog::ilog10(U16::from(9999u16)), 3);
        assert_eq!(ConstIlog::ilog10(U16::from(10000u16)), 4);
    }

    #[test]
    fn test_ilog() {
        type U16 = FixedUInt<u8, 2>;

        // Base 2
        assert_eq!(ConstIlog::ilog(U16::from(8u8), U16::from(2u8)), 3);
        assert_eq!(ConstIlog::ilog(U16::from(9u8), U16::from(2u8)), 3);

        // Base 3
        assert_eq!(ConstIlog::ilog(U16::from(1u8), U16::from(3u8)), 0);
        assert_eq!(ConstIlog::ilog(U16::from(3u8), U16::from(3u8)), 1);
        assert_eq!(ConstIlog::ilog(U16::from(8u8), U16::from(3u8)), 1);
        assert_eq!(ConstIlog::ilog(U16::from(9u8), U16::from(3u8)), 2);
        assert_eq!(ConstIlog::ilog(U16::from(27u8), U16::from(3u8)), 3);

        // Base 16
        assert_eq!(ConstIlog::ilog(U16::from(255u8), U16::from(16u8)), 1);
        assert_eq!(ConstIlog::ilog(U16::from(256u16), U16::from(16u8)), 2);
    }

    #[test]
    fn test_checked_ilog2() {
        type U16 = FixedUInt<u8, 2>;

        assert_eq!(ConstIlog::checked_ilog2(U16::from(0u8)), None);
        assert_eq!(ConstIlog::checked_ilog2(U16::from(1u8)), Some(0));
        assert_eq!(ConstIlog::checked_ilog2(U16::from(8u8)), Some(3));
    }

    #[test]
    fn test_checked_ilog10() {
        type U16 = FixedUInt<u8, 2>;

        assert_eq!(ConstIlog::checked_ilog10(U16::from(0u8)), None);
        assert_eq!(ConstIlog::checked_ilog10(U16::from(1u8)), Some(0));
        assert_eq!(ConstIlog::checked_ilog10(U16::from(100u8)), Some(2));
    }

    #[test]
    fn test_checked_ilog() {
        type U16 = FixedUInt<u8, 2>;

        // Zero argument
        assert_eq!(
            ConstIlog::checked_ilog(U16::from(0u8), U16::from(2u8)),
            None
        );
        // Invalid base
        assert_eq!(
            ConstIlog::checked_ilog(U16::from(10u8), U16::from(0u8)),
            None
        );
        assert_eq!(
            ConstIlog::checked_ilog(U16::from(10u8), U16::from(1u8)),
            None
        );
        // Valid
        assert_eq!(
            ConstIlog::checked_ilog(U16::from(8u8), U16::from(2u8)),
            Some(3)
        );
    }

    c0nst::c0nst! {
        pub c0nst fn const_ilog2<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            v: FixedUInt<T, N>,
        ) -> u32 {
            ConstIlog::ilog2(v)
        }

        pub c0nst fn const_ilog10<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            v: FixedUInt<T, N>,
        ) -> u32 {
            ConstIlog::ilog10(v)
        }
    }

    #[test]
    fn test_const_ilog() {
        type U16 = FixedUInt<u8, 2>;

        assert_eq!(const_ilog2(U16::from(8u8)), 3);
        assert_eq!(const_ilog10(U16::from(100u8)), 2);

        #[cfg(feature = "nightly")]
        {
            const EIGHT: U16 = FixedUInt { array: [8, 0] };
            const HUNDRED: U16 = FixedUInt { array: [100, 0] };
            const LOG2_RESULT: u32 = const_ilog2(EIGHT);
            const LOG10_RESULT: u32 = const_ilog10(HUNDRED);
            assert_eq!(LOG2_RESULT, 3);
            assert_eq!(LOG10_RESULT, 2);
        }
    }
}
