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

//! `PowerOfTwoOps` for `FixedUInt`, plus the round-trip helper
//! [`FixedUInt::from_power_of_two`].
//!
//! `next_multiple_of_pow2` inherits the `+` semantic: panic under Nct,
//! wrap under Ct on overflow. Untrusted inputs should route through
//! `checked_next_multiple_of_pow2`.

use super::{FixedUInt, MachineWord};
use crate::machineword::ConstMachineWord;
use const_num_traits::{CheckedAdd, ConstOne, One, Zero};
use const_num_traits::{Personality, PowerOfTwo, PowerOfTwoOps};

impl<T: ConstMachineWord + MachineWord, const N: usize, P: Personality> FixedUInt<T, N, P> {
    /// Reconstructs the value `1 << p.exp()` proven by `p`. Symmetric
    /// with the safe upstream constructor `PowerOfTwo::new_checked`.
    #[inline]
    pub fn from_power_of_two(p: PowerOfTwo<FixedUInt<T, N, P>>) -> Self {
        <Self as One>::one() << (p.exp() as usize)
    }
}

c0nst::c0nst! {
    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> PowerOfTwoOps for FixedUInt<T, N, P> {
        type Output = Self;

        #[inline]
        fn div_pow2(self, p: PowerOfTwo<Self>) -> Self {
            self >> (p.exp() as usize)
        }

        #[inline]
        fn rem_pow2(self, p: PowerOfTwo<Self>) -> Self {
            let one = <Self as ConstOne>::ONE;
            let mask = (one << (p.exp() as usize)) - one;
            self & mask
        }

        #[inline]
        fn is_multiple_of_pow2(self, p: PowerOfTwo<Self>) -> bool {
            let one = <Self as ConstOne>::ONE;
            let mask = (one << (p.exp() as usize)) - one;
            <Self as Zero>::is_zero(&(self & mask))
        }

        #[inline]
        fn next_multiple_of_pow2(self, p: PowerOfTwo<Self>) -> Self {
            let one = <Self as ConstOne>::ONE;
            let mask = (one << (p.exp() as usize)) - one;
            (self + mask) & !mask
        }

        #[inline]
        fn checked_next_multiple_of_pow2(self, p: PowerOfTwo<Self>) -> Option<Self> {
            let one = <Self as ConstOne>::ONE;
            let mask = (one << (p.exp() as usize)) - one;
            match <Self as CheckedAdd>::checked_add(self, mask) {
                Some(s) => Some(s & !mask),
                None => None,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type U16 = FixedUInt<u8, 2>;

    /// Construction goes through the upstream `new_checked` — this is
    /// the same shape as the cross-crate tripwire in const-num-traits'
    /// `tests/typestate_generic_carrier.rs`. If upstream ever narrows
    /// `PowerOfTwo::new_checked` back to a per-primitive macro impl,
    /// this fails to compile because `FixedUInt` isn't a primitive.
    fn pow2_from_value(v: U16) -> Option<PowerOfTwo<U16>> {
        PowerOfTwo::<U16>::new_checked(v)
    }

    #[test]
    fn upstream_constructor_filters_non_powers() {
        assert!(pow2_from_value(U16::from(0u8)).is_none());
        assert!(pow2_from_value(U16::from(3u8)).is_none());
        assert!(pow2_from_value(U16::from(255u8)).is_none());
    }

    #[test]
    fn upstream_constructor_records_exponent_and_round_trips() {
        let cases = [
            (1u16, 0u32),
            (2, 1),
            (4, 2),
            (8, 3),
            (16, 4),
            (128, 7),
            (256, 8),
            (32768, 15),
        ];
        for (value, expected_exp) in cases {
            let v = U16::from(value);
            let p = pow2_from_value(v).expect("power of two");
            assert_eq!(p.exp(), expected_exp, "exp mismatch for value {value}");
            assert_eq!(
                U16::from_power_of_two(p),
                v,
                "round-trip mismatch for value {value}"
            );
        }
    }

    #[test]
    fn div_pow2_matches_division() {
        let p4 = pow2_from_value(U16::from(16u8)).unwrap(); // 2^4
        assert_eq!(
            PowerOfTwoOps::div_pow2(U16::from(100u8), p4),
            U16::from(6u8)
        );
        assert_eq!(
            PowerOfTwoOps::div_pow2(U16::from(1000u16), p4),
            U16::from(62u8)
        );
        let p0 = pow2_from_value(U16::from(1u8)).unwrap();
        assert_eq!(
            PowerOfTwoOps::div_pow2(U16::from(12345u16), p0),
            U16::from(12345u16)
        );
    }

    #[test]
    fn rem_pow2_matches_remainder() {
        let p4 = pow2_from_value(U16::from(16u8)).unwrap();
        assert_eq!(
            PowerOfTwoOps::rem_pow2(U16::from(100u8), p4),
            U16::from(4u8)
        );
        assert_eq!(
            PowerOfTwoOps::rem_pow2(U16::from(1000u16), p4),
            U16::from(8u8)
        );
        let p0 = pow2_from_value(U16::from(1u8)).unwrap();
        assert_eq!(
            PowerOfTwoOps::rem_pow2(U16::from(12345u16), p0),
            U16::from(0u8)
        );
    }

    #[test]
    fn is_multiple_of_pow2_works() {
        let p4 = pow2_from_value(U16::from(16u8)).unwrap();
        assert!(PowerOfTwoOps::is_multiple_of_pow2(U16::from(0u8), p4));
        assert!(PowerOfTwoOps::is_multiple_of_pow2(U16::from(16u8), p4));
        assert!(PowerOfTwoOps::is_multiple_of_pow2(U16::from(256u16), p4));
        assert!(!PowerOfTwoOps::is_multiple_of_pow2(U16::from(15u8), p4));
        assert!(!PowerOfTwoOps::is_multiple_of_pow2(U16::from(17u8), p4));
    }

    #[test]
    fn next_multiple_of_pow2_aligns_up() {
        let p4 = pow2_from_value(U16::from(16u8)).unwrap();
        assert_eq!(
            PowerOfTwoOps::next_multiple_of_pow2(U16::from(0u8), p4),
            U16::from(0u8)
        );
        assert_eq!(
            PowerOfTwoOps::next_multiple_of_pow2(U16::from(1u8), p4),
            U16::from(16u8)
        );
        assert_eq!(
            PowerOfTwoOps::next_multiple_of_pow2(U16::from(15u8), p4),
            U16::from(16u8)
        );
        assert_eq!(
            PowerOfTwoOps::next_multiple_of_pow2(U16::from(16u8), p4),
            U16::from(16u8)
        );
        assert_eq!(
            PowerOfTwoOps::next_multiple_of_pow2(U16::from(17u8), p4),
            U16::from(32u8)
        );
        assert_eq!(
            PowerOfTwoOps::next_multiple_of_pow2(U16::from(100u8), p4),
            U16::from(112u8)
        );
    }

    #[test]
    fn checked_next_multiple_of_pow2_is_the_no_panic_sibling() {
        let p4 = pow2_from_value(U16::from(16u8)).unwrap();
        assert_eq!(
            PowerOfTwoOps::checked_next_multiple_of_pow2(U16::from(65520u16), p4),
            Some(U16::from(65520u16))
        );
        // 65521 + mask (15) = 65536, overflows U16::MAX. Under Nct that
        // would panic; the checked variant returns None.
        assert_eq!(
            PowerOfTwoOps::checked_next_multiple_of_pow2(U16::from(65521u16), p4),
            None
        );
        let p15 = pow2_from_value(U16::from(32768u16)).unwrap();
        assert_eq!(
            PowerOfTwoOps::checked_next_multiple_of_pow2(U16::from(40000u16), p15),
            None
        );
    }

    #[test]
    fn wider_carrier_spans_limb_boundaries() {
        // Confirms the shifts/masks span limb boundaries correctly on a
        // u32-backed carrier (the FixedUInt-shape that motivates having
        // this trait at all — the perf win versus long division).
        type U128 = FixedUInt<u32, 4>;
        let p64 = PowerOfTwo::<U128>::new_checked(U128::from_array([0, 0, 1, 0])).unwrap();
        assert_eq!(p64.exp(), 64);
        // (2^65 + 7) / 2^64 = 2
        let v = U128::from_array([7, 0, 2, 0]);
        assert_eq!(
            PowerOfTwoOps::div_pow2(v, p64),
            U128::from_array([2, 0, 0, 0])
        );
        // (2^65 + 7) % 2^64 = 7
        assert_eq!(
            PowerOfTwoOps::rem_pow2(v, p64),
            U128::from_array([7, 0, 0, 0])
        );
    }

    c0nst::c0nst! {
        pub c0nst fn const_div_pow2<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(
            v: FixedUInt<T, N, P>,
            p: PowerOfTwo<FixedUInt<T, N, P>>,
        ) -> FixedUInt<T, N, P> {
            PowerOfTwoOps::div_pow2(v, p)
        }

        pub c0nst fn const_rem_pow2<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(
            v: FixedUInt<T, N, P>,
            p: PowerOfTwo<FixedUInt<T, N, P>>,
        ) -> FixedUInt<T, N, P> {
            PowerOfTwoOps::rem_pow2(v, p)
        }
    }

    #[test]
    fn const_eval_path() {
        let p = pow2_from_value(U16::from(16u8)).unwrap();
        assert_eq!(const_div_pow2(U16::from(100u8), p), U16::from(6u8));
        assert_eq!(const_rem_pow2(U16::from(100u8), p), U16::from(4u8));

        // Full construct-and-consume chain in const context: upstream
        // `new_checked` is `c0nst fn` and our `IsPowerOfTwo` + `PrimBits`
        // impls carry `[c0nst]` bounds.
        #[cfg(feature = "nightly")]
        {
            const HUNDRED: U16 = FixedUInt::from_array([100, 0]);
            const SIXTEEN: U16 = FixedUInt::from_array([16, 0]);
            const P4: PowerOfTwo<U16> = match PowerOfTwo::<U16>::new_checked(SIXTEEN) {
                Some(p) => p,
                None => panic!("16 is a power of two"),
            };
            const Q: U16 = const_div_pow2(HUNDRED, P4);
            const R: U16 = const_rem_pow2(HUNDRED, P4);
            assert_eq!(Q, FixedUInt::from_array([6, 0]));
            assert_eq!(R, FixedUInt::from_array([4, 0]));
        }
    }
}
