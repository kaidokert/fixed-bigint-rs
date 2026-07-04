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

use super::{FixedUInt, MachineWord, const_div, const_is_zero};
use crate::const_numtraits::{CheckedAdd, DivCeil, One};
use crate::machineword::ConstMachineWord;
use const_num_traits::Nct;

c0nst::c0nst! {
    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> DivCeil for FixedUInt<T, N, Nct> {
        fn div_ceil(self, rhs: Self) -> Self {
            match checked_div_ceil_impl(self, rhs) {
                Some(v) => v,
                None => panic!("div_ceil: division by zero or overflow"),
            }
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> DivCeil for &FixedUInt<T, N, Nct> {
        fn div_ceil(self, rhs: Self) -> FixedUInt<T, N, Nct> {
            <FixedUInt<T, N, Nct> as DivCeil>::div_ceil(*self, *rhs)
        }
    }
}

c0nst::c0nst! {
    /// Standalone const fn body for div_ceil's checked variant, used both
    /// by the inherent `checked_div_ceil` shim and (transitively) by the
    /// `DivCeil::div_ceil` trait impl above. Kept free-floating rather
    /// than as an inherent method because the c0nst macro doesn't
    /// translate `[c0nst]` bounds on inherent `impl` blocks (only on
    /// `c0nst fn` items directly).
    pub(crate) c0nst fn checked_div_ceil_impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
        a: FixedUInt<T, N, Nct>, rhs: FixedUInt<T, N, Nct>,
    ) -> Option<FixedUInt<T, N, Nct>> {
        if const_is_zero(&rhs.array) {
            return None;
        }
        let mut quotient = a.array;
        let remainder = const_div(&mut quotient, &rhs.array);
        if const_is_zero(&remainder) {
            Some(FixedUInt::from_array(quotient))
        } else {
            <FixedUInt<T, N, Nct> as CheckedAdd>::checked_add(
                FixedUInt::from_array(quotient),
                <FixedUInt<T, N, Nct> as One>::one(),
            )
        }
    }
}

impl<T: ConstMachineWord + MachineWord, const N: usize> FixedUInt<T, N, Nct> {
    /// Backwards-compatible inherent `checked_div_ceil`. External
    /// `DivCeil` doesn't surface a checked variant; we keep this so
    /// downstream callers can still get `None` on division-by-zero or
    /// overflow rather than a panic.
    ///
    /// Note on const-callability: this inherent shim is **not** itself
    /// `const fn`, because the `c0nst` macro does not translate
    /// `[c0nst]` trait bounds on inherent `impl` blocks (Rust syntax
    /// only allows `[const]` bounds in trait-impl headers and standalone
    /// `const fn` items). Nightly callers who need the const path can
    /// call `checked_div_ceil_impl(a, b)` directly — it's a free
    /// `pub(crate) c0nst fn` defined above, exercised in const context
    /// by the existing `test_const_div_ceil` test.
    pub fn checked_div_ceil(self, rhs: Self) -> Option<Self> {
        checked_div_ceil_impl(self, rhs)
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
            DivCeil::div_ceil(U16::from(10u8), U16::from(5u8)),
            U16::from(2u8)
        );
        assert_eq!(
            DivCeil::div_ceil(U16::from(10u8), U16::from(2u8)),
            U16::from(5u8)
        );

        // Rounds up
        assert_eq!(
            DivCeil::div_ceil(U16::from(10u8), U16::from(3u8)),
            U16::from(4u8)
        ); // 10/3 = 3.33... -> 4
        assert_eq!(
            DivCeil::div_ceil(U16::from(11u8), U16::from(3u8)),
            U16::from(4u8)
        ); // 11/3 = 3.66... -> 4
        assert_eq!(
            DivCeil::div_ceil(U16::from(12u8), U16::from(3u8)),
            U16::from(4u8)
        ); // 12/3 = 4 exact

        // Edge cases
        assert_eq!(
            DivCeil::div_ceil(U16::from(0u8), U16::from(5u8)),
            U16::from(0u8)
        );
        assert_eq!(
            DivCeil::div_ceil(U16::from(1u8), U16::from(5u8)),
            U16::from(1u8)
        ); // 1/5 = 0.2 -> 1
        assert_eq!(
            DivCeil::div_ceil(U16::from(1u8), U16::from(1u8)),
            U16::from(1u8)
        );
    }

    #[test]
    fn test_checked_div_ceil() {
        type U16 = FixedUInt<u8, 2>;

        assert_eq!(
            FixedUInt::checked_div_ceil(U16::from(10u8), U16::from(3u8)),
            Some(U16::from(4u8))
        );

        // Division by zero
        assert_eq!(
            FixedUInt::checked_div_ceil(U16::from(10u8), U16::from(0u8)),
            None
        );

        // Edge case: MAX / 2 = 32767 remainder 1, ceil = 32768
        assert_eq!(
            FixedUInt::checked_div_ceil(U16::from(65535u16), U16::from(2u16)),
            Some(U16::from(32768u16))
        );

        // Edge case: MAX / 1 = MAX exactly (no remainder, no +1 needed)
        assert_eq!(
            FixedUInt::checked_div_ceil(U16::from(65535u16), U16::from(1u16)),
            Some(U16::from(65535u16))
        );
    }

    c0nst::c0nst! {
        pub c0nst fn const_div_ceil<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            a: FixedUInt<T, N, Nct>,
            b: FixedUInt<T, N, Nct>,
        ) -> FixedUInt<T, N, Nct> {
            DivCeil::div_ceil(a, b)
        }
        /// Const-callable parallel to `FixedUInt::checked_div_ceil`
        /// (which can't itself be `const fn` on an inherent impl). Just
        /// re-exposes the existing `checked_div_ceil_impl` helper above
        /// under a `const_*` test-shim name for the empirical-proof
        /// pattern other files use.
        pub c0nst fn const_checked_div_ceil<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            a: FixedUInt<T, N, Nct>,
            b: FixedUInt<T, N, Nct>,
        ) -> Option<FixedUInt<T, N, Nct>> {
            super::checked_div_ceil_impl(a, b)
        }
    }

    #[test]
    fn test_const_div_ceil() {
        type U16 = FixedUInt<u8, 2>;

        assert_eq!(
            const_div_ceil(U16::from(10u8), U16::from(3u8)),
            U16::from(4u8)
        );
        assert_eq!(
            const_checked_div_ceil(U16::from(10u8), U16::from(3u8)),
            Some(U16::from(4u8))
        );
        assert_eq!(
            const_checked_div_ceil(U16::from(10u8), U16::from(0u8)),
            None
        );

        #[cfg(feature = "nightly")]
        {
            const TEN: U16 = FixedUInt::from_array([10, 0]);
            const THREE: U16 = FixedUInt::from_array([3, 0]);
            const ZERO: U16 = FixedUInt::from_array([0, 0]);
            const RESULT: U16 = const_div_ceil(TEN, THREE);
            const CHECKED_OK: Option<U16> = const_checked_div_ceil(TEN, THREE);
            const CHECKED_ZERO: Option<U16> = const_checked_div_ceil(TEN, ZERO);
            assert_eq!(RESULT, FixedUInt::from_array([4, 0]));
            assert!(CHECKED_OK.is_some());
            assert!(CHECKED_ZERO.is_none());
        }
    }
}
