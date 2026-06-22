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

//! `PowerOfTwo<FixedUInt>` constructor + `PowerOfTwoOps` impls.
//!
//! Lifts the `const-num-traits` typestate that lets callers replace
//! `div`/`rem`/`is_multiple`/`next_multiple` with shifts and masks when the
//! divisor is a proven power of two. The proof stores only the exponent as a
//! `u32`, so the wrapper is `Copy` independent of `N`.
//!
//! Construction is exposed as an inherent method on `FixedUInt`
//! ([`FixedUInt::as_power_of_two`]) — the orphan rule blocks an inherent
//! `impl PowerOfTwo<FixedUInt<...>>` block in this crate. Callers
//! reconstruct the value via [`PowerOfTwo::exp`] (free) and a shift, or via
//! [`FixedUInt::from_power_of_two`] for symmetry.
//!
//! The consuming ops are uniform across both personalities: every body is a
//! shift, a mask, or an addition — none of which branch on operand values —
//! so there is no `match P::TAG` dispatch and no CT/NCT divergence.
//!
//! There is no `impl PowerOfTwoOps for &FixedUInt<...>`: the trait fixes
//! `p: PowerOfTwo<Self>`, which for `Self = &FixedUInt<...>` would be a
//! distinct type from `PowerOfTwo<FixedUInt<...>>` (same `u32` exponent
//! inside, but the `PhantomData` differs). Forcing callers to manufacture a
//! second proof for the borrowed shape adds noise without saving anything,
//! since `FixedUInt: Copy` makes the deref free. Use `(*v).div_pow2(p)` or
//! call `PowerOfTwoOps::div_pow2(*v, p)` directly.

use super::{FixedUInt, MachineWord};
use crate::const_numtraits::{CheckedAdd, ConstOne, IsPowerOfTwo, One, PrimBits, Zero};
use crate::machineword::ConstMachineWord;
use const_num_traits::{Personality, PowerOfTwo, PowerOfTwoOps};

impl<T: ConstMachineWord + MachineWord, const N: usize, P: Personality> FixedUInt<T, N, P> {
    /// If `self` is a power of two, returns a typestate proof
    /// ([`PowerOfTwo`]) that records the exponent; otherwise `None`.
    ///
    /// The proof is `Copy` and carries only a `u32` — the original value is
    /// not retained. Use it to feed [`PowerOfTwoOps`] consumers, which turn
    /// `div`/`rem`/`is_multiple`/`next_multiple` into shifts and masks.
    ///
    /// ```
    /// use fixed_bigint::FixedUInt;
    /// use const_num_traits::{PowerOfTwo, PowerOfTwoOps};
    ///
    /// type U16 = FixedUInt<u8, 2>;
    /// let p = U16::from(16u8).as_power_of_two().unwrap();
    /// assert_eq!(p.exp(), 4);
    /// assert_eq!(U16::from(100u8).div_pow2(p), U16::from(6u8));
    /// ```
    #[inline]
    pub fn as_power_of_two(self) -> Option<PowerOfTwo<FixedUInt<T, N, P>>> {
        if !<Self as IsPowerOfTwo>::is_power_of_two(self) {
            return None;
        }
        // `is_power_of_two` ⇒ exactly one bit set ⇒ its index is
        //   BIT_SIZE - 1 - leading_zeros(self)
        // which is `< BIT_SIZE`, the typestate invariant.
        let exp = (Self::BIT_SIZE as u32) - 1 - <Self as PrimBits>::leading_zeros(self);
        // SAFETY: established above.
        Some(unsafe { PowerOfTwo::from_exp_unchecked(exp) })
    }

    /// Reconstructs the value `1 << p.exp()` proven by `p`. Symmetric with
    /// [`as_power_of_two`](Self::as_power_of_two).
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
            // (self + mask) & !mask: align self up to the next multiple
            // of (1 << exp). The `+` follows the personality's `Add`
            // convention — panics on overflow under `Nct`, wraps under
            // `Ct` — so consumers handling untrusted inputs should call
            // `checked_next_multiple_of_pow2` instead.
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

    #[test]
    fn as_power_of_two_filters_non_powers() {
        assert!(U16::from(0u8).as_power_of_two().is_none());
        assert!(U16::from(3u8).as_power_of_two().is_none());
        assert!(U16::from(5u8).as_power_of_two().is_none());
        assert!(U16::from(7u8).as_power_of_two().is_none());
        assert!(U16::from(255u8).as_power_of_two().is_none());
    }

    #[test]
    fn as_power_of_two_records_exponent_and_round_trips() {
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
            let p = v.as_power_of_two().expect("power of two");
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
        let p4 = U16::from(16u8).as_power_of_two().unwrap(); // 2^4
        assert_eq!(
            PowerOfTwoOps::div_pow2(U16::from(100u8), p4),
            U16::from(6u8)
        );
        assert_eq!(
            PowerOfTwoOps::div_pow2(U16::from(1000u16), p4),
            U16::from(62u8)
        );
        // exp == 0 (divisor == 1) is identity.
        let p0 = U16::from(1u8).as_power_of_two().unwrap();
        assert_eq!(
            PowerOfTwoOps::div_pow2(U16::from(12345u16), p0),
            U16::from(12345u16)
        );
    }

    #[test]
    fn rem_pow2_matches_remainder() {
        let p4 = U16::from(16u8).as_power_of_two().unwrap();
        assert_eq!(
            PowerOfTwoOps::rem_pow2(U16::from(100u8), p4),
            U16::from(4u8)
        );
        assert_eq!(
            PowerOfTwoOps::rem_pow2(U16::from(1000u16), p4),
            U16::from(8u8)
        );
        // exp == 0 (divisor == 1) ⇒ remainder always 0.
        let p0 = U16::from(1u8).as_power_of_two().unwrap();
        assert_eq!(
            PowerOfTwoOps::rem_pow2(U16::from(12345u16), p0),
            U16::from(0u8)
        );
    }

    #[test]
    fn is_multiple_of_pow2_works() {
        let p4 = U16::from(16u8).as_power_of_two().unwrap();
        assert!(PowerOfTwoOps::is_multiple_of_pow2(U16::from(0u8), p4));
        assert!(PowerOfTwoOps::is_multiple_of_pow2(U16::from(16u8), p4));
        assert!(PowerOfTwoOps::is_multiple_of_pow2(U16::from(256u16), p4));
        assert!(!PowerOfTwoOps::is_multiple_of_pow2(U16::from(15u8), p4));
        assert!(!PowerOfTwoOps::is_multiple_of_pow2(U16::from(17u8), p4));
    }

    #[test]
    fn next_multiple_of_pow2_aligns_up() {
        let p4 = U16::from(16u8).as_power_of_two().unwrap();
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
    fn checked_next_multiple_of_pow2_detects_overflow() {
        let p4 = U16::from(16u8).as_power_of_two().unwrap();
        // Comfortably inside: 65520 is already aligned.
        assert_eq!(
            PowerOfTwoOps::checked_next_multiple_of_pow2(U16::from(65520u16), p4),
            Some(U16::from(65520u16))
        );
        // 65521 → next multiple of 16 = 65536 = 2^16, doesn't fit U16.
        // mask = 15, 65521 + 15 = 65536 overflows U16's MAX (65535).
        assert_eq!(
            PowerOfTwoOps::checked_next_multiple_of_pow2(U16::from(65521u16), p4),
            None
        );
        // High exponent (2^15 = 32768): self > 32768 always overflows.
        let p15 = U16::from(32768u16).as_power_of_two().unwrap();
        assert_eq!(
            PowerOfTwoOps::checked_next_multiple_of_pow2(U16::from(40000u16), p15),
            None
        );
    }

    #[test]
    fn wider_carrier_spans_limb_boundaries() {
        // Spot-check a u32-backed type to confirm the shifts/masks span
        // limb boundaries correctly.
        type U128 = FixedUInt<u32, 4>;
        let p64 = U128::from_array([0, 0, 1, 0]).as_power_of_two().unwrap();
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
        let p = U16::from(16u8).as_power_of_two().unwrap();
        assert_eq!(const_div_pow2(U16::from(100u8), p), U16::from(6u8));
        assert_eq!(const_rem_pow2(U16::from(100u8), p), U16::from(4u8));

        // Empirical const-eval proof on nightly: `from_exp_unchecked` is
        // const since 1.66, so we can build the proof at const time and
        // run the consuming ops in a const context.
        #[cfg(feature = "nightly")]
        {
            const P4: PowerOfTwo<U16> = unsafe { PowerOfTwo::from_exp_unchecked(4) };
            const HUNDRED: U16 = FixedUInt::from_array([100, 0]);
            const Q: U16 = const_div_pow2(HUNDRED, P4);
            const R: U16 = const_rem_pow2(HUNDRED, P4);
            assert_eq!(Q, FixedUInt::from_array([6, 0]));
            assert_eq!(R, FixedUInt::from_array([4, 0]));
        }
    }
}
