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

//! Absolute difference implementation for FixedUInt.

use super::{const_ct_select, FixedUInt, MachineWord};
use crate::const_numtraits::{ConstAbsDiff, ConstOverflowingSub, ConstWrappingSub, ConstZero};
use crate::machineword::ConstMachineWord;
use crate::personality::{Personality, PersonalityTag};

c0nst::c0nst! {
    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> ConstAbsDiff for FixedUInt<T, N, P> {
        fn abs_diff(self, other: Self) -> Self {
            match P::TAG {
                PersonalityTag::Nct => {
                    if self >= other {
                        self - other
                    } else {
                        other - self
                    }
                }
                PersonalityTag::Ct => {
                    let (diff, borrow) =
                        <Self as ConstOverflowingSub>::overflowing_sub(&self, &other);
                    let neg_diff =
                        <Self as ConstWrappingSub>::wrapping_sub(&<Self as ConstZero>::zero(), &diff);
                    const_ct_select(diff, neg_diff, borrow as u8)
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_abs_diff() {
        type U16 = FixedUInt<u8, 2>;

        assert_eq!(
            ConstAbsDiff::abs_diff(U16::from(10u8), U16::from(3u8)),
            U16::from(7u8)
        );
        assert_eq!(
            ConstAbsDiff::abs_diff(U16::from(3u8), U16::from(10u8)),
            U16::from(7u8)
        );
        assert_eq!(
            ConstAbsDiff::abs_diff(U16::from(5u8), U16::from(5u8)),
            U16::from(0u8)
        );
        assert_eq!(
            ConstAbsDiff::abs_diff(U16::from(0u8), U16::from(100u8)),
            U16::from(100u8)
        );
        assert_eq!(
            ConstAbsDiff::abs_diff(U16::from(255u8), U16::from(0u8)),
            U16::from(255u8)
        );
    }

    c0nst::c0nst! {
        pub c0nst fn const_abs_diff<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(
            a: FixedUInt<T, N, P>,
            b: FixedUInt<T, N, P>,
        ) -> FixedUInt<T, N, P> {
            ConstAbsDiff::abs_diff(a, b)
        }
    }

    #[test]
    fn test_const_abs_diff() {
        type U16 = FixedUInt<u8, 2>;

        assert_eq!(
            const_abs_diff(U16::from(10u8), U16::from(3u8)),
            U16::from(7u8)
        );

        #[cfg(feature = "nightly")]
        {
            const A: U16 = FixedUInt::from_array([10, 0]);
            const B: U16 = FixedUInt::from_array([3, 0]);
            const DIFF: U16 = const_abs_diff(A, B);
            assert_eq!(DIFF, FixedUInt::from_array([7, 0]));
        }
    }
}
