//! `Shl<usize>` / `Shr<usize>` for `HeaplessBigInt`.
//!
//! Bit-count shifts by a public `usize` amount. Output `len` is derived
//! from operand `len` + shift amount, both public shape parameters. The
//! shape math:
//!
//! - `Shl`: `out_len = min(ceil((self.len * word_bits + bits) / word_bits), CAP)`.
//!   Bits that would need `CAP + 1` limbs are discarded (wrapping).
//! - `Shr`: `out_len = self.len.saturating_sub(bits / word_bits)`. The
//!   top limb may become zero — that's fine under the zero-tail invariant
//!   and downstream can trim explicitly if needed (NCT-only).
//!
//! Iteration count is derived from `self.len` + shift amount — both
//! public — so the Nct and Ct arms share the same body.

use super::{HeaplessBigInt, zero};
use crate::MachineWord;
use const_num_traits::Personality;
use core::marker::PhantomData;
use core::ops::{Shl, Shr};

impl<T: MachineWord, const CAP: usize, P: Personality> Shl<usize> for HeaplessBigInt<T, CAP, P> {
    type Output = Self;

    fn shl(self, bits: usize) -> Self::Output {
        let word_bits = core::mem::size_of::<T>() * 8;
        let word_shift = bits / word_bits;
        let bit_shift = bits % word_bits;

        // out_len: enough to hold self.len limbs shifted by word_shift,
        // plus one extra if any bits carry across a word boundary.
        let extra = if bit_shift > 0 { 1 } else { 0 };
        let natural = self.len as usize + word_shift + extra;
        let out_len = core::cmp::min(natural, CAP);

        let mut limbs = [zero::<T>(); CAP];
        if word_shift >= CAP {
            return Self {
                limbs,
                len: 0,
                _p: PhantomData,
            };
        }

        let mut i = 0;
        while i < self.len as usize {
            let dst_lo = i + word_shift;
            if dst_lo < out_len {
                let lo = self.limbs[i] << bit_shift;
                limbs[dst_lo] = limbs[dst_lo] | lo;
                if bit_shift > 0 {
                    let dst_hi = dst_lo + 1;
                    if dst_hi < out_len {
                        let hi = self.limbs[i] >> (word_bits - bit_shift);
                        limbs[dst_hi] = limbs[dst_hi] | hi;
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
