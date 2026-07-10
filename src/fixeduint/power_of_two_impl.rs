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
use crate::machineword::ConstMachineWord;
use const_num_traits::{
    Bounded, ConstOne, ConstZero, IsPowerOfTwo, NextPowerOfTwo, One, PrimBits, WrappingSub, Zero,
};
use const_num_traits::{Personality, PersonalityTag};

c0nst::c0nst! {
    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> IsPowerOfTwo for FixedUInt<T, N, P> {
        fn is_power_of_two(self) -> bool {
            match P::TAG {
                PersonalityTag::Nct => {
                    !<Self as Zero>::is_zero(&self) && <Self as Zero>::is_zero(&(self & (self - <Self as One>::one())))
                }
                PersonalityTag::Ct => {
                    // Opacify `a` so LLVM can't rewrite `a & b` back into
                    // a short-circuit `if a { b } else { false }` — same
                    // defence as `const_ct_select` at `fixeduint.rs`.
                    let a = core::hint::black_box(!<Self as Zero>::is_zero(&self));
                    let b = <Self as Zero>::is_zero(&(self & <Self as WrappingSub>::wrapping_sub(self, <Self as One>::one())));
                    a & b
                }
            }
        }

    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> NextPowerOfTwo for FixedUInt<T, N, P> {
        type Output = Self;

        fn wrapping_next_power_of_two(self) -> Self {
            // Overflow wraps to ZERO under both personalities, matching
            // std's primitive `wrapping_next_power_of_two`. The Ct arm
            // is the same branchless body as `next_power_of_two` below,
            // but selects ZERO on overflow instead of MAX.
            match P::TAG {
                PersonalityTag::Nct => match self.checked_next_power_of_two() {
                    Some(v) => v,
                    None => <Self as ConstZero>::ZERO,
                },
                PersonalityTag::Ct => {
                    let m_one = <Self as WrappingSub>::wrapping_sub(self, Self::one());
                    let leading = PrimBits::leading_zeros(m_one);
                    let bits = Self::BIT_SIZE as u32 - leading;
                    let shifted = Self::one() << (bits as usize);
                    let is_zero = <Self as Zero>::is_zero(&self) as u8;
                    let overflow = ((bits >= Self::BIT_SIZE as u32) as u8) & (1u8 ^ is_zero);
                    let wrapped = crate::fixeduint::const_ct_select(
                        shifted,
                        <Self as ConstZero>::ZERO,
                        overflow,
                    );
                    crate::fixeduint::const_ct_select(wrapped, Self::one(), is_zero)
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
                    let m_one = <Self as WrappingSub>::wrapping_sub(self, Self::one());
                    let leading = PrimBits::leading_zeros(m_one);
                    let bits = Self::BIT_SIZE as u32 - leading;
                    let shifted = Self::one() << (bits as usize);
                    let is_zero = <Self as Zero>::is_zero(&self) as u8;
                    // Overflow when bits >= BIT_SIZE (and self != 0).
                    let overflow = ((bits >= Self::BIT_SIZE as u32) as u8) & (1u8 ^ is_zero);
                    let saturated = crate::fixeduint::const_ct_select(
                        shifted,
                        <Self as Bounded>::max_value(),
                        overflow,
                    );
                    crate::fixeduint::const_ct_select(saturated, Self::one(), is_zero)
                }
            }
        }

        // NOTE: This impl is NOT constant-time on a `FixedUInt<_, _, Ct>`
        // carrier — the `Option` shape leaks whether the input was zero
        // and whether `next_power_of_two` overflowed, both of which are
        // range predicates on the secret. Ct callers should use the
        // inherent `FixedUInt::<_, _, Ct>::ct_checked_next_power_of_two`
        // instead, which returns `CtOption` with a value-masked flag.
        fn checked_next_power_of_two(self) -> Option<Self> {
            if self.is_zero() {
                return Some(Self::one());
            }
            // Bit manipulation trick: (n-1).leading_zeros() gives the bit position
            // needed for the next power of two, handling both power-of-two and
            // non-power-of-two inputs correctly.
            let m_one = self - Self::one();
            let leading = PrimBits::leading_zeros(m_one);
            let bits = Self::BIT_SIZE as u32 - leading;

            // Check for overflow
            if bits >= Self::BIT_SIZE as u32 {
                return None;
            }
            Some(Self::one() << (bits as usize))
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> IsPowerOfTwo for &FixedUInt<T, N, P> {
        fn is_power_of_two(self) -> bool {
            <FixedUInt<T, N, P> as IsPowerOfTwo>::is_power_of_two(FixedUInt::from_array(self.array))
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> NextPowerOfTwo for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn next_power_of_two(self) -> FixedUInt<T, N, P> {
            <FixedUInt<T, N, P> as NextPowerOfTwo>::next_power_of_two(FixedUInt::from_array(self.array))
        }
        fn checked_next_power_of_two(self) -> Option<FixedUInt<T, N, P>> {
            <FixedUInt<T, N, P> as NextPowerOfTwo>::checked_next_power_of_two(FixedUInt::from_array(self.array))
        }
        fn wrapping_next_power_of_two(self) -> FixedUInt<T, N, P> {
            <FixedUInt<T, N, P> as NextPowerOfTwo>::wrapping_next_power_of_two(FixedUInt::from_array(self.array))
        }
    }
}

// ── CtIsPowerOfTwo (masked-return is_power_of_two) ───────────────────
//
// `nonzero & is_zero(self & (self - 1))` — same predicate as the bool
// form, just composed of Choice values via `subtle::ConstantTimeEq`
// (transitively through `CtIsZero`). Uniform across both personalities.
impl<T, const N: usize, P: Personality> const_num_traits::ops::ct::CtIsPowerOfTwo
    for FixedUInt<T, N, P>
where
    T: MachineWord + subtle::ConstantTimeEq,
{
    fn ct_is_power_of_two(&self) -> subtle::Choice {
        use const_num_traits::ops::ct::CtIsZero;
        let nonzero = !self.ct_is_zero();
        let one = <Self as ConstOne>::ONE;
        // Route through the by-ref `WrappingSub` so `self` isn't
        // deref-copied onto the stack — matters on Ct paths where
        // `self` may point into a `Zeroizing<T>` nonce.
        let masked = self & <&Self as WrappingSub>::wrapping_sub(self, &one);
        let pow2 = masked.ct_is_zero();
        nonzero & pow2
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_power_of_two() {
        type U16 = FixedUInt<u8, 2>;

        assert!(!IsPowerOfTwo::is_power_of_two(U16::from(0u8)));
        assert!(IsPowerOfTwo::is_power_of_two(U16::from(1u8)));
        assert!(IsPowerOfTwo::is_power_of_two(U16::from(2u8)));
        assert!(!IsPowerOfTwo::is_power_of_two(U16::from(3u8)));
        assert!(IsPowerOfTwo::is_power_of_two(U16::from(4u8)));
        assert!(!IsPowerOfTwo::is_power_of_two(U16::from(5u8)));
        assert!(IsPowerOfTwo::is_power_of_two(U16::from(8u8)));
        assert!(IsPowerOfTwo::is_power_of_two(U16::from(16u8)));
        assert!(IsPowerOfTwo::is_power_of_two(U16::from(128u8)));
        assert!(IsPowerOfTwo::is_power_of_two(U16::from(256u16)));
        assert!(!IsPowerOfTwo::is_power_of_two(U16::from(255u8)));
    }

    #[test]
    fn test_next_power_of_two() {
        type U16 = FixedUInt<u8, 2>;

        assert_eq!(
            NextPowerOfTwo::next_power_of_two(U16::from(0u8)),
            U16::from(1u8)
        );
        assert_eq!(
            NextPowerOfTwo::next_power_of_two(U16::from(1u8)),
            U16::from(1u8)
        );
        assert_eq!(
            NextPowerOfTwo::next_power_of_two(U16::from(2u8)),
            U16::from(2u8)
        );
        assert_eq!(
            NextPowerOfTwo::next_power_of_two(U16::from(3u8)),
            U16::from(4u8)
        );
        assert_eq!(
            NextPowerOfTwo::next_power_of_two(U16::from(4u8)),
            U16::from(4u8)
        );
        assert_eq!(
            NextPowerOfTwo::next_power_of_two(U16::from(5u8)),
            U16::from(8u8)
        );
        assert_eq!(
            NextPowerOfTwo::next_power_of_two(U16::from(7u8)),
            U16::from(8u8)
        );
        assert_eq!(
            NextPowerOfTwo::next_power_of_two(U16::from(8u8)),
            U16::from(8u8)
        );
        assert_eq!(
            NextPowerOfTwo::next_power_of_two(U16::from(9u8)),
            U16::from(16u8)
        );
        assert_eq!(
            NextPowerOfTwo::next_power_of_two(U16::from(100u8)),
            U16::from(128u8)
        );
        assert_eq!(
            NextPowerOfTwo::next_power_of_two(U16::from(128u8)),
            U16::from(128u8)
        );
        assert_eq!(
            NextPowerOfTwo::next_power_of_two(U16::from(129u8)),
            U16::from(256u16)
        );
    }

    #[test]
    fn test_checked_next_power_of_two() {
        type U16 = FixedUInt<u8, 2>;

        assert_eq!(
            NextPowerOfTwo::checked_next_power_of_two(U16::from(0u8)),
            Some(U16::from(1u8))
        );
        assert_eq!(
            NextPowerOfTwo::checked_next_power_of_two(U16::from(1u8)),
            Some(U16::from(1u8))
        );
        assert_eq!(
            NextPowerOfTwo::checked_next_power_of_two(U16::from(100u8)),
            Some(U16::from(128u8))
        );

        // Test overflow case - 32769 needs next power of 2 = 65536 which overflows u16
        let large = U16::from(32769u16);
        assert_eq!(NextPowerOfTwo::checked_next_power_of_two(large), None);

        // But 32768 is already a power of two
        let pow2 = U16::from(32768u16);
        assert_eq!(NextPowerOfTwo::checked_next_power_of_two(pow2), Some(pow2));
    }

    c0nst::c0nst! {
        pub c0nst fn const_is_power_of_two<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(
            v: &FixedUInt<T, N, P>,
        ) -> bool {
            IsPowerOfTwo::is_power_of_two(FixedUInt::<T, N, P>::from_array(v.array))
        }

        pub c0nst fn const_next_power_of_two<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(
            v: FixedUInt<T, N, P>,
        ) -> FixedUInt<T, N, P> {
            NextPowerOfTwo::next_power_of_two(v)
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

    #[test]
    fn wrapping_next_power_of_two_wraps_to_zero_under_both_personalities() {
        use const_num_traits::{Ct, Nct};
        type U16Nct = FixedUInt<u8, 2, Nct>;
        type U16Ct = FixedUInt<u8, 2, Ct>;
        // 32769 > 2^15; next power of two is 2^16 = 0x1_0000, doesn't fit u16.
        // std's `u16::wrapping_next_power_of_two(32769) == 0`.
        assert_eq!(
            U16Nct::from(32769u16).wrapping_next_power_of_two(),
            U16Nct::from_array([0, 0])
        );
        assert_eq!(
            U16Ct::from(32769u16).wrapping_next_power_of_two(),
            U16Ct::from_array([0, 0])
        );
        // MAX-input overflow behaves the same way.
        assert_eq!(
            U16Nct::from(0xFFFFu16).wrapping_next_power_of_two(),
            U16Nct::from_array([0, 0])
        );
        assert_eq!(
            U16Ct::from(0xFFFFu16).wrapping_next_power_of_two(),
            U16Ct::from_array([0, 0])
        );
        // Non-overflow: both personalities agree on the same real result.
        assert_eq!(
            U16Nct::from(100u8).wrapping_next_power_of_two(),
            U16Nct::from(128u8)
        );
        assert_eq!(
            U16Ct::from(100u8).wrapping_next_power_of_two(),
            U16Ct::from(128u8)
        );
    }

    #[test]
    fn ct_is_power_of_two_matches_is_power_of_two() {
        use const_num_traits::ops::ct::CtIsPowerOfTwo;
        type U16 = FixedUInt<u8, 2>;
        // Zero is NOT a power of two
        assert!(!bool::from(CtIsPowerOfTwo::ct_is_power_of_two(&U16::from(
            0u8
        ))));
        // Powers of two
        for v in [1u16, 2, 4, 8, 16, 128, 256, 32768] {
            assert!(
                bool::from(CtIsPowerOfTwo::ct_is_power_of_two(&U16::from(v))),
                "ct_is_power_of_two({v}) should mask Some"
            );
        }
        // Non-powers of two
        for v in [3u16, 5, 6, 7, 9, 100, 255] {
            assert!(
                !bool::from(CtIsPowerOfTwo::ct_is_power_of_two(&U16::from(v))),
                "ct_is_power_of_two({v}) should mask None"
            );
        }
    }
}
