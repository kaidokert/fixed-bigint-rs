//! `const_num_traits::DepositBits` / `ExtractBits` (PDEP / PEXT) for
//! `HeaplessBigInt<_, Nct>`.
//!
//! Nct-only: the loop runs once per set bit of the mask, which is
//! value-dependent. (A constant-time version would iterate the full width
//! unconditionally — a separate Ct exercise, as on `FixedUInt`.)
//!
//! The result is seeded at `max(self.len, mask.len)` so it carries the
//! operand width rather than the minimal identity width.

use super::HeaplessBigInt;
use crate::MachineWord;
use const_num_traits::{
    DepositBits, ExtractBits, IsolateLowestOne, Nct, One, WrappingShl, WrappingSub, Zero,
};

impl<T, const CAP: usize> DepositBits for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
{
    type Output = Self;
    fn deposit_bits(self, mask: Self) -> Self {
        // Scatter the contiguous low bits of `self` into the one-bit
        // positions of `mask`, lowest to highest.
        let width = core::cmp::max(self.len(), mask.len());
        let mut result = Self::new_zero_with_len(width);
        // Nothing to scatter for an all-zero mask (which is the only way
        // `width == 0`); returning early also avoids `one().widened(0)`, which
        // rejects the grow. A non-zero mask has `len >= 1`, so `width >= 1`.
        if <Self as Zero>::is_zero(&mask) {
            return result;
        }
        let one = <Self as One>::one();
        let mut remaining = mask;
        let mut bb = one.widened(width);
        while !<Self as Zero>::is_zero(&remaining) {
            let lowest = IsolateLowestOne::isolate_lowest_one(remaining);
            if !<Self as Zero>::is_zero(&(self & bb)) {
                result |= lowest;
            }
            // Clear the lowest set bit of `remaining` (`x & (x - 1)`).
            remaining &= WrappingSub::wrapping_sub(remaining, one);
            bb = WrappingShl::wrapping_shl(bb, 1);
        }
        result
    }
}

impl<T, const CAP: usize> ExtractBits for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
{
    type Output = Self;
    fn extract_bits(self, mask: Self) -> Self {
        // Gather the `mask`-selected bits of `self` into the low end —
        // mirror of `deposit_bits`.
        let width = core::cmp::max(self.len(), mask.len());
        let mut result = Self::new_zero_with_len(width);
        // See `deposit_bits`: an all-zero mask (the only `width == 0` case)
        // gathers nothing and would otherwise trip `one().widened(0)`.
        if <Self as Zero>::is_zero(&mask) {
            return result;
        }
        let one = <Self as One>::one();
        let mut remaining = mask;
        let mut bb = one.widened(width);
        while !<Self as Zero>::is_zero(&remaining) {
            let lowest = IsolateLowestOne::isolate_lowest_one(remaining);
            if !<Self as Zero>::is_zero(&(self & lowest)) {
                result |= bb;
            }
            remaining &= WrappingSub::wrapping_sub(remaining, one);
            bb = WrappingShl::wrapping_shl(bb, 1);
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::HeaplessBigInt;
    use const_num_traits::{DepositBits, ExtractBits};

    type H = HeaplessBigInt<u8, 4>;

    #[test]
    fn deposit_extract_roundtrip() {
        // mask selects bits 0,2,4,6; deposit the low nibble of 0b1011 into them.
        let mask = H::from(0b0101_0101u8).widened(4);
        let src = H::from(0b1011u8).widened(4);
        let dep = DepositBits::deposit_bits(src, mask);
        // low four mask bits get 1,1,0,1 → positions 0,2,6 set = 0b0100_0101
        assert_eq!(dep, H::from(0b0100_0101u8));
        assert_eq!(dep.len(), 4);

        // extract is the inverse: pull those masked bits back to the low end.
        let ext = ExtractBits::extract_bits(dep, mask);
        assert_eq!(ext, H::from(0b1011u8));
        assert_eq!(ext.len(), 4);
    }

    #[test]
    fn deposit_full_mask_is_identity() {
        let mask = H::from(0xFFFF_FFFFu32);
        let v = H::from(0x1234_5678u32);
        assert_eq!(DepositBits::deposit_bits(v, mask), v);
        assert_eq!(ExtractBits::extract_bits(v, mask), v);
    }

    // An all-zero mask scatters/gathers nothing and returns zero — including
    // the len-0 shape, which would otherwise panic on one().widened(0).
    #[test]
    fn zero_mask_returns_zero_without_panic() {
        let src = H::from(0x1234_5678u32);
        let zero_mask = H::new_zero_with_len(4);
        assert_eq!(DepositBits::deposit_bits(src, zero_mask), H::from(0u8));
        assert_eq!(ExtractBits::extract_bits(src, zero_mask), H::from(0u8));

        // Both operands the minimal len-0 zero shape (width 0).
        let z0 = H::new_zero_with_len(0);
        assert_eq!(DepositBits::deposit_bits(z0, z0).len(), 0);
        assert_eq!(ExtractBits::extract_bits(z0, z0).len(), 0);
    }
}
