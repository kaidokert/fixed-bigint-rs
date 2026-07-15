//! `bit_length` and `leading_zeros` for `HeaplessBigInt`.
//!
//! Both are NCT-implicit: they scan limb content to find the highest
//! non-zero position. Ct callers that need a masked-return counterpart
//! wire it through a separate primitive.
//!
//! `bit_length` is the position of the highest set bit plus one, so
//! `bit_length(0) == 0` and `bit_length(1) == 1`. `leading_zeros` is
//! taken against the value's **width** (`len * word_bits`), not capacity
//! — so `bit_length + leading_zeros == bits_precision()` and `CAP` never
//! enters. A caller that wants zeros relative to a wider window sizes it
//! from that window's own `bits_precision`, not this value's capacity.

use super::HeaplessBigInt;
use crate::MachineWord;
use const_num_traits::Personality;

impl<T: MachineWord, const CAP: usize, P: Personality> HeaplessBigInt<T, CAP, P> {
    /// Number of bits needed to represent the value: `0` for zero,
    /// otherwise the position of the highest set bit plus one.
    pub fn bit_length(&self) -> usize {
        let word_bits = core::mem::size_of::<T>() * 8;
        // Walk MSB-to-LSB. First non-zero limb determines the answer;
        // limbs beyond that are zero by the invariant so we don't need
        // to inspect them.
        let mut i = self.len as usize;
        while i > 0 {
            i -= 1;
            let limb = self.limbs[i];
            if !super::is_zero(&limb) {
                let leading = limb.leading_zeros() as usize;
                return i * word_bits + (word_bits - leading);
            }
        }
        0
    }

    /// Leading zeros against the value's width (`len * word_bits`), so
    /// `leading_zeros + bit_length == bits_precision()`. A `len = 0`
    /// value has width 0, hence `leading_zeros() == 0`.
    pub fn leading_zeros(&self) -> usize {
        let width = self.len as usize * core::mem::size_of::<T>() * 8;
        width - self.bit_length()
    }
}

// ── const_num_traits::BitWidth (bit-length) / BitsPrecision (width) ──
//
// Two distinct quantities (bit-vocabulary canon): `bit_width` is the
// significant-bit count (per-value magnitude); `bits_precision` is the
// operating width, which for this variable-width carrier is the
// constructed `len·word_bits` — NOT `CAP` (capacity stays out of any
// trait answer). `bit_length <= bits_precision` always. Value receiver
// per the traits; `&Self` mirrors (no reference blanket upstream).

impl<T: MachineWord, const CAP: usize, P: Personality> const_num_traits::BitWidth
    for HeaplessBigInt<T, CAP, P>
{
    fn bit_width(self) -> u32 {
        self.bit_length() as u32
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> const_num_traits::BitWidth
    for &HeaplessBigInt<T, CAP, P>
{
    fn bit_width(self) -> u32 {
        self.bit_length() as u32
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> const_num_traits::BitsPrecision
    for HeaplessBigInt<T, CAP, P>
{
    fn bits_precision(&self) -> u32 {
        self.len as u32 * (core::mem::size_of::<T>() as u32 * 8)
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> const_num_traits::BitsPrecision
    for &HeaplessBigInt<T, CAP, P>
{
    fn bits_precision(&self) -> u32 {
        self.len as u32 * (core::mem::size_of::<T>() as u32 * 8)
    }
}

// Establish a width from a witness. Grow-only, value-preserving: widen `self`
// to the whole-word length covering `bits_precision` bits, never shrinking.
// The zero/one/witness constructors (`zero_with_precision_of(&modulus)` etc.)
// default over this, giving generic reducers a correctly-sized seed instead of
// the minimal-width `zero()` that silently truncates. `CAP` is the ceiling:
// `widened` panics if the requested width exceeds it.
impl<T: MachineWord, const CAP: usize, P: Personality> const_num_traits::WithPrecision
    for HeaplessBigInt<T, CAP, P>
{
    fn widen_to_precision(self, bits_precision: u32) -> Self {
        let word_bits = core::mem::size_of::<T>() as u32 * 8;
        let target_len = bits_precision.div_ceil(word_bits) as u16;
        self.widened(target_len.max(self.len()))
    }
}
