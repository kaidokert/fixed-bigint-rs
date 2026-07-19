//! The shift-family traits for `HeaplessBigInt`: overflowing / wrapping /
//! checked / unbounded / exact / funnel shifts, plus the `num_traits`
//! wrapping/checked wrappers.
//!
//! All build on the inherent `<<` / `>>`, so they inherit those width
//! contracts: the left-shift family is width-preserving (`out_len =
//! self.len`, bits past the width discarded), the right-shift family follows
//! `Shr`'s whole-word narrowing (`out_len = self.len - bits/word_bits`). The
//! shift amount is a public `u32`, so every arm is personality-generic.
//!
//! The "overflow" flag / `None` / wrap is purely about the *amount* (`bits >=
//! value_width`), exactly like the primitive `overflowing_shl` — it is not a
//! value predicate, so it stays uniform across `Nct`/`Ct`.

use super::HeaplessBigInt;
use crate::MachineWord;
use const_num_traits::{
    CheckedShl, CheckedShr, FunnelShl, FunnelShr, OverflowingShl, OverflowingShr, Personality,
    PrimBits, ShlExact, ShrExact, UnboundedShl, UnboundedShr, WrappingShl, WrappingShr,
};

impl<T: MachineWord, const CAP: usize, P: Personality> HeaplessBigInt<T, CAP, P> {
    /// Operating width in bits (`len · word_bits`). Fits `u32` for any
    /// representable `len` (≤ `u16::MAX`) and word size (≤ 64).
    #[inline]
    fn value_bits(&self) -> u32 {
        self.len as u32 * (core::mem::size_of::<T>() as u32 * 8)
    }
}

/// `(normalized_shift, overflowed)` — mirrors the primitive masking. A
/// zero-width value (`len == 0`) always overflows.
#[inline]
fn normalize_shift(bits: u32, value_bits: u32) -> (usize, bool) {
    if value_bits == 0 {
        (0, true)
    } else if bits >= value_bits {
        ((bits % value_bits) as usize, true)
    } else {
        (bits as usize, false)
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> OverflowingShl
    for HeaplessBigInt<T, CAP, P>
{
    type Output = Self;
    fn overflowing_shl(self, bits: u32) -> (Self, bool) {
        let (shift, overflow) = normalize_shift(bits, self.value_bits());
        (self << shift, overflow)
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> OverflowingShr
    for HeaplessBigInt<T, CAP, P>
{
    type Output = Self;
    fn overflowing_shr(self, bits: u32) -> (Self, bool) {
        let (shift, overflow) = normalize_shift(bits, self.value_bits());
        (self >> shift, overflow)
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> WrappingShl for HeaplessBigInt<T, CAP, P> {
    type Output = Self;
    fn wrapping_shl(self, bits: u32) -> Self {
        OverflowingShl::overflowing_shl(self, bits).0
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> WrappingShr for HeaplessBigInt<T, CAP, P> {
    type Output = Self;
    fn wrapping_shr(self, bits: u32) -> Self {
        OverflowingShr::overflowing_shr(self, bits).0
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> CheckedShl for HeaplessBigInt<T, CAP, P> {
    type Output = Self;
    fn checked_shl(self, bits: u32) -> Option<Self> {
        let (res, overflow) = OverflowingShl::overflowing_shl(self, bits);
        if overflow { None } else { Some(res) }
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> CheckedShr for HeaplessBigInt<T, CAP, P> {
    type Output = Self;
    fn checked_shr(self, bits: u32) -> Option<Self> {
        let (res, overflow) = OverflowingShr::overflowing_shr(self, bits);
        if overflow { None } else { Some(res) }
    }
}

// Unbounded: shift by any amount, saturating to zero past the width. The
// inherent `<<` / `>>` already collapse to zero once the whole-word shift
// clears every limb, so an over-width amount is handled directly.
impl<T: MachineWord, const CAP: usize, P: Personality> UnboundedShl for HeaplessBigInt<T, CAP, P> {
    type Output = Self;
    fn unbounded_shl(self, rhs: u32) -> Self {
        if rhs >= self.value_bits() {
            Self::new_zero_with_len(self.len())
        } else {
            self << (rhs as usize)
        }
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> UnboundedShr for HeaplessBigInt<T, CAP, P> {
    type Output = Self;
    fn unbounded_shr(self, rhs: u32) -> Self {
        if rhs >= self.value_bits() {
            Self::new_zero_with_len(self.len())
        } else {
            self >> (rhs as usize)
        }
    }
}

// Exact (lossless) shifts: `None` if any one-bit would be shifted out or the
// amount reaches the value width.
impl<T: MachineWord, const CAP: usize, P: Personality> ShlExact for HeaplessBigInt<T, CAP, P> {
    type Output = Self;
    fn shl_exact(self, rhs: u32) -> Option<Self> {
        if rhs < self.value_bits() && rhs <= PrimBits::leading_zeros(self) {
            Some(self << (rhs as usize))
        } else {
            None
        }
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> ShrExact for HeaplessBigInt<T, CAP, P> {
    type Output = Self;
    fn shr_exact(self, rhs: u32) -> Option<Self> {
        if rhs < self.value_bits() && rhs <= PrimBits::trailing_zeros(self) {
            // A whole-limb `>>` narrows `len`; an *exact* (reversible) shift
            // must keep the operand width so `<<` by the same amount recovers
            // the input. No bits are lost (the trailing-zero check passed), so
            // widening back is value-preserving.
            let width = self.len();
            Some((self >> (rhs as usize)).widened(width))
        } else {
            None
        }
    }
}

// Funnel shifts: the double-width `(self, rhs)` shifted by `n`, one half
// returned. Both halves are taken at `self`'s width — `rhs` must share it, or
// its high limbs (outside the funnel word) would leak into the result — so a
// width mismatch is a caller error, asserted for `n > 0`. `n == 0` is a no-op
// checked first, so it never trips the width/range asserts (a `len == 0`
// operand has `value_bits() == 0`, against which `n < bits` would fail).
impl<T: MachineWord, const CAP: usize, P: Personality> FunnelShl for HeaplessBigInt<T, CAP, P> {
    type Output = Self;
    fn funnel_shl(self, rhs: Self, n: u32) -> Self {
        if n == 0 {
            return self;
        }
        assert!(
            self.len() == rhs.len(),
            "HeaplessBigInt::funnel_shl: operands must share a width"
        );
        let bits = self.value_bits();
        assert!(n < bits, "HeaplessBigInt::funnel_shl: n out of range");
        let lo_shift = bits - n;
        (self << (n as usize)) | (rhs >> (lo_shift as usize))
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> FunnelShr for HeaplessBigInt<T, CAP, P> {
    type Output = Self;
    fn funnel_shr(self, rhs: Self, n: u32) -> Self {
        if n == 0 {
            return rhs;
        }
        assert!(
            self.len() == rhs.len(),
            "HeaplessBigInt::funnel_shr: operands must share a width"
        );
        let bits = self.value_bits();
        assert!(n < bits, "HeaplessBigInt::funnel_shr: n out of range");
        let hi_shift = bits - n;
        (rhs >> (n as usize)) | (self << (hi_shift as usize))
    }
}

// num_traits wrappers — delegate to the const-num-traits impls above.
#[cfg(feature = "num-traits")]
impl<T: MachineWord, const CAP: usize, P: Personality> num_traits::WrappingShl
    for HeaplessBigInt<T, CAP, P>
{
    fn wrapping_shl(&self, bits: u32) -> Self {
        <Self as WrappingShl>::wrapping_shl(*self, bits)
    }
}

#[cfg(feature = "num-traits")]
impl<T: MachineWord, const CAP: usize, P: Personality> num_traits::WrappingShr
    for HeaplessBigInt<T, CAP, P>
{
    fn wrapping_shr(&self, bits: u32) -> Self {
        <Self as WrappingShr>::wrapping_shr(*self, bits)
    }
}

#[cfg(feature = "num-traits")]
impl<T: MachineWord, const CAP: usize, P: Personality> num_traits::CheckedShl
    for HeaplessBigInt<T, CAP, P>
{
    fn checked_shl(&self, bits: u32) -> Option<Self> {
        <Self as CheckedShl>::checked_shl(*self, bits)
    }
}

#[cfg(feature = "num-traits")]
impl<T: MachineWord, const CAP: usize, P: Personality> num_traits::CheckedShr
    for HeaplessBigInt<T, CAP, P>
{
    fn checked_shr(&self, bits: u32) -> Option<Self> {
        <Self as CheckedShr>::checked_shr(*self, bits)
    }
}

#[cfg(test)]
mod tests {
    use super::HeaplessBigInt;
    use const_num_traits::{
        CheckedShl, CheckedShr, FunnelShl, FunnelShr, OverflowingShl, ShlExact, ShrExact,
        UnboundedShl, UnboundedShr, WrappingShl,
    };

    type H = HeaplessBigInt<u8, 4>; // 32-bit width at len 4

    #[test]
    fn overflowing_wrapping_checked() {
        let v = H::from(1u8).widened(4);
        // In-range shift, no overflow.
        assert_eq!(
            OverflowingShl::overflowing_shl(v, 4),
            (H::from(16u8), false)
        );
        // Amount == width overflows; masked to 0 → shift by 0.
        assert_eq!(OverflowingShl::overflowing_shl(v, 32), (v, true));
        assert_eq!(WrappingShl::wrapping_shl(v, 32), v);
        assert_eq!(CheckedShl::checked_shl(v, 32), None);
        assert_eq!(CheckedShl::checked_shl(v, 5), Some(H::from(32u8)));
        assert_eq!(CheckedShr::checked_shr(v, 32), None);
    }

    #[test]
    fn unbounded_saturates_to_zero() {
        let v = H::from(0xFFu8).widened(4);
        assert_eq!(UnboundedShl::unbounded_shl(v, 100), H::from(0u8));
        assert_eq!(UnboundedShr::unbounded_shr(v, 100), H::from(0u8));
        // Over-width shift keeps the operand width.
        assert_eq!(UnboundedShl::unbounded_shl(v, 100).len(), 4);
    }

    #[test]
    fn exact_shifts() {
        let v = H::from(0b100u8).widened(4);
        // 0b100 has 2 trailing zeros: shr by 2 is exact, by 3 loses the bit.
        assert_eq!(ShrExact::shr_exact(v, 2), Some(H::from(1u8)));
        assert_eq!(ShrExact::shr_exact(v, 3), None);
        // shl by more than leading_zeros drops the top bit.
        assert!(ShlExact::shl_exact(H::from(1u8).widened(4), 31).is_some());
        assert_eq!(ShlExact::shl_exact(H::from(1u8).widened(4), 32), None);
    }

    // A whole-limb exact shr must keep the operand width so it's reversible.
    #[test]
    fn shr_exact_preserves_width() {
        let v = H::from(256u16).widened(4); // [0, 1, 0, 0], len 4
        let r = ShrExact::shr_exact(v, 8).unwrap();
        assert_eq!(r, H::from(1u8));
        assert_eq!(r.len(), 4, "exact shr must not narrow away the width");
        // Reversible: shifting back left recovers the input.
        assert_eq!(r << 8usize, H::from(256u16));
    }

    // Over-width `Shl<u32>` / `Shr<u32>` zero out without truncating the count
    // (the 16-bit-usize hazard); Shl keeps the width, Shr empties.
    #[test]
    fn u32_operator_shifts_handle_over_width() {
        let v = H::from(0xFFu8).widened(4);
        let sl = core::ops::Shl::<u32>::shl(v, 100);
        assert!(<H as const_num_traits::Zero>::is_zero(&sl));
        assert_eq!(sl.len(), 4);
        let sr = core::ops::Shr::<u32>::shr(v, 100);
        assert!(<H as const_num_traits::Zero>::is_zero(&sr));
    }

    // funnel with n == 0 is a no-op even on a len-0 operand (value_bits() == 0
    // would otherwise trip the `n < bits` assert).
    #[test]
    fn funnel_zero_shift_on_empty_operand() {
        let z0 = H::new_zero_with_len(0);
        assert_eq!(FunnelShl::funnel_shl(z0, z0, 0).len(), 0);
        assert_eq!(FunnelShr::funnel_shr(z0, z0, 0).len(), 0);
    }

    #[test]
    #[should_panic(expected = "must share a width")]
    fn funnel_rejects_width_mismatch() {
        let narrow = H::from(1u8); // len 1
        let wide = H::from(1u8).widened(4); // len 4
        FunnelShl::funnel_shl(narrow, wide, 1);
    }

    #[test]
    fn funnel() {
        // (hi=0x1234, lo=0x5678) as a 32-bit pair, funnel_shl by 8 →
        // top 32 bits of (0x1234_5678 << 8) = 0x3456_78__ >> ... check value.
        let hi = H::from(0x1234_5678u32);
        let lo = H::from(0x9ABC_DEF0u32);
        // funnel_shl by 8: (hi << 8) | (lo >> 24) = 0x3456_7800 | 0x9A = 0x3456_789A
        assert_eq!(FunnelShl::funnel_shl(hi, lo, 8), H::from(0x3456_789Au32));
        // funnel_shr by 8: (lo >> 8) | (hi << 24) = 0x009A_BCDE | 0x7800_0000 = 0x789A_BCDE
        assert_eq!(FunnelShr::funnel_shr(hi, lo, 8), H::from(0x789A_BCDEu32));
        assert_eq!(FunnelShl::funnel_shl(hi, lo, 0), hi);
        assert_eq!(FunnelShr::funnel_shr(hi, lo, 0), lo);
    }
}
