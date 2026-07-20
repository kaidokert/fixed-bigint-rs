//! `Shl<usize>` / `Shr<usize>` for `HeaplessBigInt`.
//!
//! Bit-count shifts by a public `usize` amount. Output `len` is derived
//! from operand `len` + shift amount, both public shape parameters. The
//! shape math:
//!
//! - `Shl`: width-preserving — `out_len = self.len`, bits shifted past the
//!   operand width are discarded (`x << bits mod 2^(len·word_bits)`), so a
//!   value at `len = k` shifts exactly like `FixedUInt<T, k>`. `CAP` never
//!   enters; the words beyond `len` do not exist. A caller wanting the
//!   shifted value to occupy more words constructs it at the wider width
//!   first (as `div_rem` does).
//! - `Shr`: `out_len = self.len.saturating_sub(bits / word_bits)`. The
//!   top limb may become zero — that's fine under the zero-tail invariant
//!   and downstream can trim explicitly if needed (NCT-only).
//!
//! Iteration count is derived from `self.len` + shift amount — both
//! public — so the Nct and Ct arms share the same body.

use super::cmp::ct_select;
use super::{HeaplessBigInt, zero};
use crate::MachineWord;
use const_num_traits::Personality;
use core::marker::PhantomData;
use core::ops::{Shl, ShlAssign, Shr, ShrAssign};

/// Constant-time left shift by a **secret** `amount`: a barrel shifter.
///
/// The inherent `Shl<usize>` branches and cache-indexes on the shift amount
/// (`word_shift`/`bit_shift`), so shifting by a secret leaks it. Here the
/// secret never drives control flow: each stage `k` shifts by the **public**
/// constant `2^k` and applies-or-not via a masked [`ct_select`] on bit `k` of
/// `amount`. Amounts `>= self.len·word_bits` yield zero (masked). The only
/// operations that touch `amount` are the arithmetic `>> k & 1` and the u32
/// `>=` — no branch or memory access depends on it.
///
/// Cost is `O(width · log(width_bits))`. Result width is `self.len`, as `<<`.
pub(crate) fn ct_shl<T, const CAP: usize, P: Personality>(
    value: HeaplessBigInt<T, CAP, P>,
    amount: u32,
) -> HeaplessBigInt<T, CAP, P>
where
    T: MachineWord + subtle::ConditionallySelectable,
{
    let width = value.len();
    let word_bits = core::mem::size_of::<T>() as u32 * 8;
    let width_bits = width as u32 * word_bits;
    let mut result = value;
    // Public loop bound: stages cover bit positions `0..ceil(log2(width_bits))`.
    let mut k = 0u32;
    while (1u32 << k) < width_bits {
        // Stage amount `2^k` stays in `u32` (< width_bits < 2^32) — `1usize << k`
        // would overflow on a 16-bit-usize target once k >= 16. The `Shl<u32>`
        // it routes through carries the same over-width cast guard as elsewhere.
        let shifted = result << (1u32 << k); // fixed, public shift by 2^k
        let bit_k = (amount >> k) & 1;
        result = ct_select(&result, &shifted, bit_k != 0);
        k += 1;
    }
    // Over-width amount shifts everything out.
    let zero_w = HeaplessBigInt::<T, CAP, P>::new_zero_with_len(width);
    ct_select(&result, &zero_w, amount >= width_bits)
}

// `Shl<u32>` / `Shr<u32>` delegate to the `usize` impls, matching `FixedUInt`.
// The `num_traits` shift traits (`WrappingShl`, `CheckedShl`, …) require these
// as supertraits.
//
// An over-width amount is guarded *before* the `as usize` cast: on a 16-bit
// `usize` target a bare cast of a `u32 >= 2^16` would truncate an over-width
// count into a small in-range one (e.g. `<< 65536` becoming `<< 0`), so we
// short-circuit to the over-width result the `usize` impls would produce
// (`Shl` zeroes at `self.len`, `Shr` empties to len 0). `value_bits()` is a
// `u32`, so the comparison itself never truncates.
impl<T: MachineWord, const CAP: usize, P: Personality> Shl<u32> for HeaplessBigInt<T, CAP, P> {
    type Output = Self;
    fn shl(self, bits: u32) -> Self::Output {
        let value_bits = self.len as u32 * (core::mem::size_of::<T>() as u32 * 8);
        if bits >= value_bits {
            Self::new_zero_with_len(self.len())
        } else {
            self << (bits as usize)
        }
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> Shr<u32> for HeaplessBigInt<T, CAP, P> {
    type Output = Self;
    fn shr(self, bits: u32) -> Self::Output {
        let value_bits = self.len as u32 * (core::mem::size_of::<T>() as u32 * 8);
        if bits >= value_bits {
            Self::new_zero_with_len(0)
        } else {
            self >> (bits as usize)
        }
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> Shl<usize> for HeaplessBigInt<T, CAP, P> {
    type Output = Self;

    fn shl(self, bits: usize) -> Self::Output {
        let word_bits = core::mem::size_of::<T>() * 8;
        let word_shift = bits / word_bits;
        let bit_shift = bits % word_bits;

        // Width-preserving: out_len = self.len (see module doc).
        let out_len = self.len as usize;
        let mut limbs = [zero::<T>(); CAP];

        let mut i = 0;
        while i < out_len {
            let dst_lo = i + word_shift;
            if dst_lo < out_len {
                let lo = self.limbs[i] << bit_shift;
                limbs[dst_lo] |= lo;
                if bit_shift > 0 {
                    let dst_hi = dst_lo + 1;
                    if dst_hi < out_len {
                        let hi = self.limbs[i] >> (word_bits - bit_shift);
                        limbs[dst_hi] |= hi;
                    }
                }
            }
            i += 1;
        }

        Self {
            limbs,
            len: out_len as u16,
            _p: PhantomData,
        }
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> ShlAssign<usize>
    for HeaplessBigInt<T, CAP, P>
{
    fn shl_assign(&mut self, bits: usize) {
        *self = *self << bits;
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> ShrAssign<usize>
    for HeaplessBigInt<T, CAP, P>
{
    fn shr_assign(&mut self, bits: usize) {
        *self = *self >> bits;
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> Shr<usize> for HeaplessBigInt<T, CAP, P> {
    type Output = Self;

    fn shr(self, bits: usize) -> Self::Output {
        let word_bits = core::mem::size_of::<T>() * 8;
        let word_shift = bits / word_bits;
        let bit_shift = bits % word_bits;

        let mut limbs = [zero::<T>(); CAP];
        if word_shift >= self.len as usize {
            return Self {
                limbs,
                len: 0,
                _p: PhantomData,
            };
        }

        let out_len = self.len as usize - word_shift;

        let mut i = 0;
        while i < out_len {
            let src_lo = i + word_shift;
            let lo = self.limbs[src_lo] >> bit_shift;
            let hi = if bit_shift > 0 && src_lo + 1 < self.len as usize {
                self.limbs[src_lo + 1] << (word_bits - bit_shift)
            } else {
                zero::<T>()
            };
            limbs[i] = lo | hi;
            i += 1;
        }

        Self {
            limbs,
            len: out_len as u16,
            _p: PhantomData,
        }
    }
}

#[cfg(test)]
mod ct_shl_tests {
    use super::{HeaplessBigInt, ct_shl};
    use const_num_traits::Ct;

    type HC = HeaplessBigInt<u8, 4, Ct>; // 32-bit width

    #[test]
    fn ct_shl_matches_plain_shift_all_amounts() {
        // The barrel shifter must produce the same value as the (leaky) `<<`
        // for every amount, including over-width (both yield 0 at the width).
        for &raw in &[1u32, 0x1234_5678, 0xFFFF_FFFF, 0x8000_0000] {
            let v = HC::from(raw);
            for amount in 0u32..=40 {
                assert_eq!(
                    ct_shl(v, amount),
                    v << (amount as usize),
                    "ct_shl({raw:#x}, {amount})"
                );
            }
        }
    }
}
