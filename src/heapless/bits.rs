//! `bit_length` and `leading_zeros` for `HeaplessBigInt`.
//!
//! Both are NCT-implicit: they scan limb content to find the highest
//! non-zero position. Ct callers that need a masked-return counterpart
//! wire it through a separate primitive.
//!
//! `bit_length` is the position of the highest set bit plus one, so
//! `bit_length(0) == 0` and `bit_length(1) == 1`. `leading_zeros` is
//! taken against `CAP * word_bits` — the full container width, not the
//! runtime `len` — so it composes cleanly with other bit-width-sized
//! callers (Barrett reduction start, sliding-window scalar decomposition).

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

    /// Leading zeros against the full container width (`CAP * word_bits`).
    /// `leading_zeros(0) == CAP * word_bits`.
    pub fn leading_zeros(&self) -> usize {
        let total_bits = CAP * core::mem::size_of::<T>() * 8;
        total_bits - self.bit_length()
    }
}
