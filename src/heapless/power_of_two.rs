//! `const_num_traits::IsPowerOfTwo` / `NextPowerOfTwo` for `HeaplessBigInt`.
//!
//! `is_power_of_two` is personality-generic (the Ct arm is `black_box`-guarded,
//! no branch). `NextPowerOfTwo` is implemented for both personalities: the
//! `Nct` arm branches on overflow (panic / wrap-to-zero); the `Ct` arm is
//! constant-time — the `1 << bits` shift by a secret `bits` goes through the
//! [`ct_shl`](super::shift::ct_shl) barrel shifter (a plain `<<` would leak the
//! magnitude), and the overflow/zero selects use [`ct_select`]. Both arms share
//! the value-based `checked_next_pow2` helper; `checked_next_power_of_two`
//! itself stays branchful (its `Option` reveals the overflow bit) — not CT,
//! same caveat as FixedUInt — so Ct callers use `next`/`wrapping`.
//!
//! Result width is the operand width: `one` is widened before the shift so the
//! power of two lands at `len`, not the minimal identity width.

use super::cmp::ct_select;
use super::shift::ct_shl;
use super::{HeaplessBigInt, arith::max_at_len};
use crate::MachineWord;
use const_num_traits::{
    Ct, IsPowerOfTwo, Nct, NextPowerOfTwo, One, Personality, PersonalityTag, PrimBits, WrappingSub,
    Zero,
};

impl<T, const CAP: usize, P: Personality> IsPowerOfTwo for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord,
{
    fn is_power_of_two(self) -> bool {
        // A power of two has exactly one bit set: `x != 0 && x & (x - 1) == 0`.
        match P::TAG {
            PersonalityTag::Nct => {
                !<Self as Zero>::is_zero(&self)
                    && <Self as Zero>::is_zero(&(self & (self - <Self as One>::one())))
            }
            PersonalityTag::Ct => {
                // `black_box` stops LLVM rewriting `a & b` back into a
                // short-circuit; `wrapping_sub` avoids the Nct underflow panic.
                let a = core::hint::black_box(!<Self as Zero>::is_zero(&self));
                let b = <Self as Zero>::is_zero(
                    &(self & <Self as WrappingSub>::wrapping_sub(self, Self::one())),
                );
                a & b
            }
        }
    }
}

// Shared value-based checked next-power-of-two, P-generic. Branchful (the
// `Option` reveals the overflow bit), so on `Ct` it is NOT constant-time — Ct
// callers use `next`/`wrapping`, which are constant-time. `wrapping_sub` keeps
// it usable on `Ct` without the Nct underflow panic; `self` is non-zero there.
impl<T, const CAP: usize, P: Personality> HeaplessBigInt<T, CAP, P>
where
    T: MachineWord,
{
    fn checked_next_pow2(self) -> Option<Self> {
        let width = self.len();
        let word_bits = core::mem::size_of::<T>() as u32 * 8;
        let width_bits = width as u32 * word_bits;
        if <Self as Zero>::is_zero(&self) {
            return Some(<Self as One>::one().widened(core::cmp::max(1, width)));
        }
        // `(n - 1).leading_zeros()` gives the position of the next power of two.
        let m_one = <Self as WrappingSub>::wrapping_sub(self, <Self as One>::one());
        let bits = width_bits - PrimBits::leading_zeros(m_one);
        if bits >= width_bits {
            return None; // 2^width_bits doesn't fit the value width
        }
        Some(<Self as One>::one().widened(core::cmp::max(1, width)) << (bits as usize))
    }
}

impl<T, const CAP: usize> NextPowerOfTwo for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
{
    type Output = Self;

    fn wrapping_next_power_of_two(self) -> Self {
        let width = self.len();
        self.checked_next_pow2()
            .unwrap_or_else(|| Self::new_zero_with_len(width))
    }

    fn next_power_of_two(self) -> Self {
        self.checked_next_pow2().unwrap_or_else(|| {
            panic!("HeaplessBigInt::next_power_of_two overflow: exceeds the value width")
        })
    }

    fn checked_next_power_of_two(self) -> Option<Self> {
        self.checked_next_pow2()
    }
}

// Constant-time Ct core, shared by `next`/`wrapping` (differ only in the
// `overflow_sentinel`: width-max for `next`, zero for `wrapping`). Mirrors
// FixedUInt's Ct `next_power_of_two` but the secret-amount `1 << bits` shift
// goes through `ct_shl` (a barrel shifter) rather than the leaky `<<`, and the
// overflow flag is combined with `&` (not short-circuiting `&&`) so nothing
// branches on the secret.
#[inline]
fn ct_next_pow2<T, const CAP: usize>(
    x: HeaplessBigInt<T, CAP, Ct>,
    overflow_sentinel: HeaplessBigInt<T, CAP, Ct>,
) -> HeaplessBigInt<T, CAP, Ct>
where
    T: MachineWord + subtle::ConditionallySelectable,
{
    type H<T, const CAP: usize> = HeaplessBigInt<T, CAP, Ct>;
    let width = x.len();
    let word_bits = core::mem::size_of::<T>() as u32 * 8;
    let width_bits = width as u32 * word_bits;
    let one_w = <H<T, CAP> as One>::one().widened(core::cmp::max(1, width));
    let m_one = <H<T, CAP> as WrappingSub>::wrapping_sub(x, one_w);
    let bits = width_bits - PrimBits::leading_zeros(m_one);
    let shifted = ct_shl(one_w, bits); // CT shift by the secret `bits`
    let is_zero = <H<T, CAP> as Zero>::is_zero(&x);
    let overflow = (bits >= width_bits) & !is_zero;
    let saturated = ct_select(&shifted, &overflow_sentinel, overflow);
    ct_select(&saturated, &one_w, is_zero)
}

impl<T, const CAP: usize> NextPowerOfTwo for HeaplessBigInt<T, CAP, Ct>
where
    T: MachineWord + subtle::ConditionallySelectable,
{
    type Output = Self;

    fn next_power_of_two(self) -> Self {
        // Saturate to the width-max on overflow (the Nct panic is value-
        // dependent, so unavailable here — a defined sentinel beats a wrong one).
        ct_next_pow2(self, max_at_len(self.len()))
    }

    fn wrapping_next_power_of_two(self) -> Self {
        ct_next_pow2(self, Self::new_zero_with_len(self.len()))
    }

    fn checked_next_power_of_two(self) -> Option<Self> {
        // Branchful (see `checked_next_pow2`): NOT constant-time on Ct.
        self.checked_next_pow2()
    }
}

// `&Self` mirrors so `(&h).next_power_of_two()` resolves without an explicit copy.
impl<T, const CAP: usize, P: Personality> IsPowerOfTwo for &HeaplessBigInt<T, CAP, P>
where
    T: MachineWord,
{
    fn is_power_of_two(self) -> bool {
        <HeaplessBigInt<T, CAP, P> as IsPowerOfTwo>::is_power_of_two(*self)
    }
}

impl<T, const CAP: usize> NextPowerOfTwo for &HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
{
    type Output = HeaplessBigInt<T, CAP, Nct>;

    fn wrapping_next_power_of_two(self) -> Self::Output {
        <HeaplessBigInt<T, CAP, Nct> as NextPowerOfTwo>::wrapping_next_power_of_two(*self)
    }

    fn next_power_of_two(self) -> Self::Output {
        <HeaplessBigInt<T, CAP, Nct> as NextPowerOfTwo>::next_power_of_two(*self)
    }

    fn checked_next_power_of_two(self) -> Option<Self::Output> {
        <HeaplessBigInt<T, CAP, Nct> as NextPowerOfTwo>::checked_next_power_of_two(*self)
    }
}

impl<T, const CAP: usize> NextPowerOfTwo for &HeaplessBigInt<T, CAP, Ct>
where
    T: MachineWord + subtle::ConditionallySelectable,
{
    type Output = HeaplessBigInt<T, CAP, Ct>;

    fn next_power_of_two(self) -> Self::Output {
        <HeaplessBigInt<T, CAP, Ct> as NextPowerOfTwo>::next_power_of_two(*self)
    }

    fn wrapping_next_power_of_two(self) -> Self::Output {
        <HeaplessBigInt<T, CAP, Ct> as NextPowerOfTwo>::wrapping_next_power_of_two(*self)
    }

    fn checked_next_power_of_two(self) -> Option<Self::Output> {
        <HeaplessBigInt<T, CAP, Ct> as NextPowerOfTwo>::checked_next_power_of_two(*self)
    }
}

// `CtIsPowerOfTwo` — masked-return `is_power_of_two`, the same subtle-predicate
// style as `CtIsZero`/`CtParity` (`nonzero & is_zero(x & (x - 1))` composed of
// `Choice`s). No `const_ct_select` needed, so it's personality-generic.
impl<T, const CAP: usize, P: Personality> const_num_traits::ops::ct::CtIsPowerOfTwo
    for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord + subtle::ConstantTimeEq,
{
    fn ct_is_power_of_two(&self) -> subtle::Choice {
        use const_num_traits::ops::ct::CtIsZero;
        let nonzero = !self.ct_is_zero();
        let one = <Self as const_num_traits::ConstOne>::ONE;
        let masked = *self & <Self as WrappingSub>::wrapping_sub(*self, one);
        nonzero & masked.ct_is_zero()
    }
}

#[cfg(test)]
mod tests {
    use super::HeaplessBigInt;
    use const_num_traits::NextPowerOfTwo;
    use const_num_traits::ops::ct::CtIsPowerOfTwo;

    type H = HeaplessBigInt<u8, 8>;

    // The result carries the operand width, not the minimal identity width:
    // `one` is widened before `<< bits`. A value-only `==` can't see this —
    // only the `.len` assertions catch a narrowing regression.
    #[test]
    fn next_power_of_two_preserves_width() {
        let five = H::from(5u8).widened(8);
        let np = NextPowerOfTwo::next_power_of_two(five);
        assert_eq!(np, H::from(8u8));
        assert_eq!(np.len(), 8);

        // Zero widens the identity to the operand width too.
        let zero = H::new_zero_with_len(8);
        let np0 = NextPowerOfTwo::next_power_of_two(zero);
        assert_eq!(np0, H::from(1u8));
        assert_eq!(np0.len(), 8);

        let already = H::from(128u8).widened(8);
        let np2 = NextPowerOfTwo::next_power_of_two(already);
        assert_eq!(np2.len(), 8);
    }

    #[test]
    fn checked_overflow_at_value_width() {
        // A one-word carrier: 0x81 rounds up to 0x100, past the 8-bit width.
        let x = HeaplessBigInt::<u8, 8>::from(0x81u8);
        assert_eq!(x.len(), 1);
        assert_eq!(NextPowerOfTwo::checked_next_power_of_two(x), None);
        // wrapping wraps to zero, still at the operand width.
        let w = NextPowerOfTwo::wrapping_next_power_of_two(x);
        assert_eq!(w, HeaplessBigInt::<u8, 8>::from(0u8));
        assert_eq!(w.len(), 1);
    }

    #[test]
    fn ct_is_power_of_two_matches_bool() {
        for v in [0u32, 1, 2, 3, 4, 100, 255, 256, 0x8000_0000] {
            let h = H::from(v);
            let ct = bool::from(h.ct_is_power_of_two());
            assert_eq!(ct, v != 0 && v & (v - 1) == 0, "ct_is_power_of_two({v})");
        }
    }

    #[test]
    fn ct_next_power_of_two_matches_and_saturates() {
        use const_num_traits::Ct;
        type HC = HeaplessBigInt<u8, 4, Ct>;

        // Non-overflow values agree with std (via the CT barrel-shift path).
        for v in [1u32, 5, 128, 0x4000_0000] {
            assert_eq!(
                NextPowerOfTwo::next_power_of_two(HC::from(v)),
                HC::from(v.next_power_of_two()),
                "ct next_power_of_two({v})"
            );
        }
        // 0 -> 1 at the operand width.
        assert_eq!(
            NextPowerOfTwo::next_power_of_two(HC::from(0u8).widened(4)),
            HC::from(1u8)
        );
        // 2^31+1 rounds to 2^32, past the 32-bit width: `next` saturates to the
        // width-max, `wrapping` wraps to zero, `checked` is None.
        let big = HC::from(0x8000_0001u32);
        assert_eq!(
            NextPowerOfTwo::next_power_of_two(big),
            HC::from(0xFFFF_FFFFu32)
        );
        assert_eq!(
            NextPowerOfTwo::wrapping_next_power_of_two(big),
            HC::from(0u8)
        );
        assert_eq!(NextPowerOfTwo::checked_next_power_of_two(big), None);
    }

    #[test]
    fn byref_matches_value() {
        use const_num_traits::{Ct, IsPowerOfTwo};
        let a = H::from(5u8);
        let r = &a; // dispatch through the `&Self` mirror
        assert_eq!(
            IsPowerOfTwo::is_power_of_two(r),
            IsPowerOfTwo::is_power_of_two(a)
        );
        assert_eq!(
            NextPowerOfTwo::next_power_of_two(r),
            NextPowerOfTwo::next_power_of_two(a)
        );
        assert_eq!(
            NextPowerOfTwo::wrapping_next_power_of_two(r),
            NextPowerOfTwo::wrapping_next_power_of_two(a)
        );
        assert_eq!(
            NextPowerOfTwo::checked_next_power_of_two(r),
            NextPowerOfTwo::checked_next_power_of_two(a)
        );

        type HC = HeaplessBigInt<u8, 4, Ct>;
        let c = HC::from(5u8);
        assert_eq!(
            NextPowerOfTwo::next_power_of_two(&c),
            NextPowerOfTwo::next_power_of_two(c)
        );
    }
}
