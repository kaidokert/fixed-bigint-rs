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

//! Multiple-of operations for FixedUInt.

use super::{FixedUInt, MachineWord};
use crate::const_numtraits::{CheckedAdd, ConstZero, MultipleOf, NextMultipleOf, One, Zero};
use crate::machineword::ConstMachineWord;
use crate::personality::Nct;

c0nst::c0nst! {
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst MultipleOf for FixedUInt<T, N, Nct> {
        fn is_multiple_of(self, rhs: Self) -> bool {
            if <Self as Zero>::is_zero(&rhs) {
                false
            } else {
                <Self as Zero>::is_zero(&(self % rhs))
            }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst NextMultipleOf for FixedUInt<T, N, Nct> {
        fn next_multiple_of(self, rhs: Self) -> Self {
            match self.checked_next_multiple_of(rhs) {
                Some(v) => v,
                None => panic!("next_multiple_of: rhs is zero or result overflows"),
            }
        }

        fn checked_next_multiple_of(self, rhs: Self) -> Option<Self> {
            if rhs.is_zero() {
                return None;
            }
            let rem = self % rhs;
            if rem.is_zero() {
                Some(self)
            } else {
                // self + (rhs - rem)
                let add = rhs - rem;
                CheckedAdd::checked_add(self, add)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_multiple_of() {
        type U16 = FixedUInt<u8, 2>;

        assert!(MultipleOf::is_multiple_of(U16::from(0u8), U16::from(5u8)));
        assert!(MultipleOf::is_multiple_of(
            U16::from(10u8),
            U16::from(5u8)
        ));
        assert!(MultipleOf::is_multiple_of(
            U16::from(15u8),
            U16::from(5u8)
        ));
        assert!(!MultipleOf::is_multiple_of(
            U16::from(11u8),
            U16::from(5u8)
        ));
        assert!(MultipleOf::is_multiple_of(
            U16::from(100u8),
            U16::from(10u8)
        ));
        assert!(!MultipleOf::is_multiple_of(
            U16::from(101u8),
            U16::from(10u8)
        ));

        // rhs == 0 returns false
        assert!(!MultipleOf::is_multiple_of(
            U16::from(10u8),
            U16::from(0u8)
        ));
    }

    #[test]
    fn test_next_multiple_of() {
        type U16 = FixedUInt<u8, 2>;

        // Already a multiple
        assert_eq!(
            NextMultipleOf::next_multiple_of(U16::from(10u8), U16::from(5u8)),
            U16::from(10u8)
        );
        assert_eq!(
            NextMultipleOf::next_multiple_of(U16::from(0u8), U16::from(5u8)),
            U16::from(0u8)
        );

        // Not a multiple
        assert_eq!(
            NextMultipleOf::next_multiple_of(U16::from(11u8), U16::from(5u8)),
            U16::from(15u8)
        );
        assert_eq!(
            NextMultipleOf::next_multiple_of(U16::from(12u8), U16::from(5u8)),
            U16::from(15u8)
        );
        assert_eq!(
            NextMultipleOf::next_multiple_of(U16::from(14u8), U16::from(5u8)),
            U16::from(15u8)
        );

        // Larger values
        assert_eq!(
            NextMultipleOf::next_multiple_of(U16::from(101u8), U16::from(10u8)),
            U16::from(110u8)
        );
    }

    #[test]
    fn test_checked_next_multiple_of() {
        type U16 = FixedUInt<u8, 2>;

        // Normal cases
        assert_eq!(
            NextMultipleOf::checked_next_multiple_of(U16::from(11u8), U16::from(5u8)),
            Some(U16::from(15u8))
        );

        // rhs == 0
        assert_eq!(
            NextMultipleOf::checked_next_multiple_of(U16::from(10u8), U16::from(0u8)),
            None
        );

        // Already a multiple (no overflow)
        let large = U16::from(65530u16);
        assert_eq!(
            NextMultipleOf::checked_next_multiple_of(large, U16::from(10u8)),
            Some(large)
        ); // 65530 % 10 = 0, so returns itself

        // Overflow case
        let large2 = U16::from(65531u16);
        assert_eq!(
            NextMultipleOf::checked_next_multiple_of(large2, U16::from(10u8)),
            None
        ); // 65531 + 9 = 65540 > 65535, overflow
    }

    c0nst::c0nst! {
        pub c0nst fn const_is_multiple_of<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            a: &FixedUInt<T, N, Nct>,
            b: &FixedUInt<T, N, Nct>,
        ) -> bool {
            MultipleOf::is_multiple_of(*a, *b)
        }

        pub c0nst fn const_next_multiple_of<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            a: FixedUInt<T, N, Nct>,
            b: FixedUInt<T, N, Nct>,
        ) -> FixedUInt<T, N, Nct> {
            NextMultipleOf::next_multiple_of(a, b)
        }
    }

    #[test]
    fn test_const_multiple() {
        type U16 = FixedUInt<u8, 2>;

        assert!(const_is_multiple_of(&U16::from(10u8), &U16::from(5u8)));
        assert_eq!(
            const_next_multiple_of(U16::from(11u8), U16::from(5u8)),
            U16::from(15u8)
        );

        #[cfg(feature = "nightly")]
        {
            const TEN: U16 = FixedUInt::from_array([10, 0]);
            const FIVE: U16 = FixedUInt::from_array([5, 0]);
            const IS_MULT: bool = const_is_multiple_of(&TEN, &FIVE);
            assert!(IS_MULT);

            const ELEVEN: U16 = FixedUInt::from_array([11, 0]);
            const NEXT: U16 = const_next_multiple_of(ELEVEN, FIVE);
            assert_eq!(NEXT, FixedUInt::from_array([15, 0]));
        }
    }
}
