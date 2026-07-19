//! Bit-scan traits for `HeaplessBigInt`: `HighestOne` / `LowestOne` (bit
//! indices) and `IsolateHighestOne` / `IsolateLowestOne` (masks).
//!
//! `HighestOne` / `LowestOne` return a `u32` index (or `None` for zero), so
//! there is no result width to preserve. The `Isolate*` masks return a value
//! and are width-preserving: the single-bit result carries `self.len`
//! (`one` is widened before the shift; the low-bit trick resolves at
//! `max(len)`).
//!
//! `IsolateHighestOne` is P-generic in name only for parity with `FixedUInt`,
//! but note the highest-bit path is not constant-time (the zero test and the
//! shift amount both depend on the value). `IsolateLowestOne` uses the
//! branchless `self & (0 - self)` trick.

use super::HeaplessBigInt;
use crate::MachineWord;
use const_num_traits::{
    HighestOne, IsolateHighestOne, IsolateLowestOne, LowestOne, One, Personality, PrimBits,
    WrappingSub, Zero,
};

impl<T, const CAP: usize, P: Personality> HighestOne for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord,
{
    fn highest_one(self) -> Option<u32> {
        // Index of the highest set bit = bit_length - 1; zero has none.
        let bl = self.bit_length();
        if bl == 0 { None } else { Some(bl as u32 - 1) }
    }
}

impl<T, const CAP: usize, P: Personality> LowestOne for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord,
{
    fn lowest_one(self) -> Option<u32> {
        if <Self as Zero>::is_zero(&self) {
            None
        } else {
            Some(PrimBits::trailing_zeros(self))
        }
    }
}

impl<T, const CAP: usize, P: Personality> IsolateHighestOne for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord,
{
    type Output = Self;
    fn isolate_highest_one(self) -> Self {
        match self.highest_one() {
            // Zero has no set bit; return it unchanged (width-preserving).
            None => self,
            Some(pos) => {
                <Self as One>::one().widened(core::cmp::max(1, self.len())) << (pos as usize)
            }
        }
    }
}

impl<T, const CAP: usize, P: Personality> IsolateLowestOne for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord,
{
    type Output = Self;
    fn isolate_lowest_one(self) -> Self {
        // `self & (-self)`: for unsigned, `-x == wrapping_sub(0, x)`. Works at
        // `self.len` (the zero seed resolves up to it) and gives 0 for 0.
        let neg = <Self as WrappingSub>::wrapping_sub(<Self as Zero>::zero(), self);
        self & neg
    }
}

#[cfg(test)]
mod tests {
    use super::HeaplessBigInt;
    use const_num_traits::{HighestOne, IsolateHighestOne, IsolateLowestOne, LowestOne};

    type H = HeaplessBigInt<u8, 8>;

    #[test]
    fn indices() {
        assert_eq!(HighestOne::highest_one(H::from(0u8)), None);
        assert_eq!(HighestOne::highest_one(H::from(1u8)), Some(0));
        assert_eq!(HighestOne::highest_one(H::from(0xB4u8)), Some(7));
        assert_eq!(LowestOne::lowest_one(H::from(0u8)), None);
        assert_eq!(LowestOne::lowest_one(H::from(0xB0u8)), Some(4));
        assert_eq!(LowestOne::lowest_one(H::from(1u8)), Some(0));
    }

    #[test]
    fn isolate_masks_and_width() {
        // 0xB4 = 1011_0100: highest bit 7, lowest bit 2.
        let v = H::from(0xB4u8).widened(8);
        let hi = IsolateHighestOne::isolate_highest_one(v);
        assert_eq!(hi, H::from(0x80u8));
        assert_eq!(hi.len(), 8);
        let lo = IsolateLowestOne::isolate_lowest_one(v);
        assert_eq!(lo, H::from(0x04u8));
        assert_eq!(lo.len(), 8);

        // Zero isolates to zero, keeping its width.
        let z = H::new_zero_with_len(8);
        assert_eq!(IsolateHighestOne::isolate_highest_one(z).len(), 8);
        assert_eq!(IsolateLowestOne::isolate_lowest_one(z).len(), 8);

        // A len-0 operand stays len 0: `zero()` (the neg seed) is itself len 0,
        // so `wrapping_sub`/`&` resolve at max(0, 0) = 0.
        let z0 = H::new_zero_with_len(0);
        assert_eq!(IsolateHighestOne::isolate_highest_one(z0).len(), 0);
        assert_eq!(IsolateLowestOne::isolate_lowest_one(z0).len(), 0);
    }
}
