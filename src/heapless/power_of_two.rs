//! `const_num_traits::IsPowerOfTwo` / `NextPowerOfTwo` for `HeaplessBigInt`.
//!
//! `is_power_of_two` is personality-generic (the Ct arm is `black_box`-guarded,
//! no branch). `NextPowerOfTwo` is Nct-only: its Ct variant needs a branchless
//! whole-value select (FixedUInt's `const_ct_select`), which heapless doesn't
//! carry, and even FixedUInt notes `checked_next_power_of_two` isn't CT.
//!
//! Result width is the operand width: `one` is widened before the `<< bits`
//! so the power of two lands at `len`, not the minimal identity width.

use super::HeaplessBigInt;
use crate::MachineWord;
use const_num_traits::{
    IsPowerOfTwo, Nct, NextPowerOfTwo, One, Personality, PersonalityTag, PrimBits, WrappingSub,
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

impl<T, const CAP: usize> NextPowerOfTwo for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
{
    type Output = Self;

    fn wrapping_next_power_of_two(self) -> Self {
        let width = self.len();
        match self.checked_next_power_of_two() {
            Some(v) => v,
            None => Self::new_zero_with_len(width), // overflow wraps to zero
        }
    }

    fn next_power_of_two(self) -> Self {
        match self.checked_next_power_of_two() {
            Some(v) => v,
            None => panic!("HeaplessBigInt::next_power_of_two overflow: exceeds the value width"),
        }
    }

    fn checked_next_power_of_two(self) -> Option<Self> {
        let width = self.len();
        let word_bits = core::mem::size_of::<T>() as u32 * 8;
        let width_bits = width as u32 * word_bits;
        if <Self as Zero>::is_zero(&self) {
            return Some(<Self as One>::one().widened(core::cmp::max(1, width)));
        }
        // `(n - 1).leading_zeros()` gives the position of the next power of two.
        let m_one = self - <Self as One>::one();
        let bits = width_bits - PrimBits::leading_zeros(m_one);
        if bits >= width_bits {
            return None; // 2^width_bits doesn't fit the value width
        }
        Some(<Self as One>::one().widened(core::cmp::max(1, width)) << (bits as usize))
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
}
