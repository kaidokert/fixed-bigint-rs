//! MulAccOps implementation for FixedUInt.
//!
//! Provides row-level fused multiply-accumulate operations used by
//! Montgomery multiplication variants. All limb access is internal to
//! this module; the public trait surface never exposes raw arrays.

use super::{FixedUInt, MachineWord};
use crate::const_numtraits::{ConstCarryingAdd, ConstZero};
use crate::mul_acc_ops::MulAccOps;
use crate::patch_num_traits::CarryingMul;

impl<T, const N: usize> MulAccOps for FixedUInt<T, N>
where
    T: MachineWord + CarryingMul<Output = T> + ConstCarryingAdd,
{
    type Word = T;

    fn word_count() -> usize {
        N
    }

    fn get_word(&self, i: usize) -> Option<T> {
        self.array.get(i).copied()
    }

    fn mul_acc_row(scalar: T, multiplicand: &Self, acc: &mut Self, carry_in: T) -> T {
        let mut carry = carry_in;
        let mut j = 0;
        while j < N {
            let (lo, hi) =
                CarryingMul::carrying_mul_add(scalar, multiplicand.array[j], acc.array[j], carry);
            acc.array[j] = lo;
            carry = hi;
            j += 1;
        }
        carry
    }

    fn mul_acc_shift_row(scalar: T, multiplicand: &Self, acc: &mut Self, acc_hi: T) -> T {
        debug_assert!(N > 0, "MulAccOps requires at least one word");
        // First word: discarded (zero by construction)
        let (_, mut carry) = CarryingMul::carrying_mul_add(
            scalar,
            multiplicand.array[0],
            acc.array[0],
            <T as ConstZero>::zero(),
        );

        // Remaining words: shift down by one position
        let mut j = 1;
        while j < N {
            let (lo, hi) =
                CarryingMul::carrying_mul_add(scalar, multiplicand.array[j], acc.array[j], carry);
            acc.array[j - 1] = lo;
            carry = hi;
            j += 1;
        }

        // Fold acc_hi + carry into acc[N-1]
        let (sum, overflow) = <T as ConstCarryingAdd>::carrying_add(acc_hi, carry, false);
        acc.array[N - 1] = sum;

        // Branchless: convert overflow bool to word via carrying_add(0, 0, overflow)
        let (overflow_word, _) = <T as ConstCarryingAdd>::carrying_add(
            <T as ConstZero>::zero(),
            <T as ConstZero>::zero(),
            overflow,
        );
        overflow_word
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type U8x1 = FixedUInt<u8, 1>;
    type U16 = FixedUInt<u8, 2>;
    type U32 = FixedUInt<u8, 4>;
    type U64x4 = FixedUInt<u64, 4>;

    #[test]
    fn test_word_access() {
        let val = U16::from(0x1234u16);
        assert_eq!(U16::word_count(), 2);
        assert_eq!(val.get_word(0), Some(0x34u8));
        assert_eq!(val.get_word(1), Some(0x12u8));
        assert_eq!(val.get_word(2), None);
    }

    #[test]
    fn test_zero_init() {
        use crate::const_numtraits::ConstZero;
        let z = <U32 as ConstZero>::zero();
        assert_eq!(z, U32::from(0u8));
    }

    #[test]
    fn test_mul_acc_row() {
        // Compute acc += 3 * 5 with acc starting at 10
        // Expected: 10 + 15 = 25, carry = 0
        let multiplicand = U16::from(5u8);
        let mut acc = U16::from(10u8);
        let carry = U16::mul_acc_row(3u8, &multiplicand, &mut acc, 0u8);
        assert_eq!(acc, U16::from(25u8));
        assert_eq!(carry, 0u8);
    }

    #[test]
    fn test_mul_acc_row_with_overflow() {
        // Compute acc += 200 * 200 with acc starting at 0
        // 200 * 200 = 40000 = 0x9C40
        use crate::const_numtraits::ConstZero;
        let multiplicand = U16::from(200u16);
        let mut acc = <U16 as ConstZero>::zero();
        let carry = U16::mul_acc_row(200u8, &multiplicand, &mut acc, 0u8);
        assert_eq!(acc, U16::from(40000u16));
        assert_eq!(carry, 0u8);
    }

    #[test]
    fn test_word_count_u64x4() {
        assert_eq!(U64x4::word_count(), 4);
    }

    #[test]
    fn test_mul_acc_shift_row_no_overflow() {
        // scalar=2, multiplicand=0x0003, acc=0x0006, acc_hi=0
        // Word-by-word (u8 limbs, N=2):
        //   j=0: carrying_mul_add(2, 3, 6, 0) = 2*3+6+0 = 12 = (0x0C, 0x00)
        //        -> discard lo=0x0C, carry=0x00
        //   j=1: carrying_mul_add(2, 0, 0, 0) = 0 = (0x00, 0x00)
        //        -> acc[0] = 0x00, carry=0x00
        //   fold: acc_hi(0) + carry(0) = 0, no overflow -> acc[1] = 0x00
        // Result: acc = 0x0000, return 0
        let multiplicand = U16::from(3u8);
        let mut acc = U16::from(6u8);
        let overflow = U16::mul_acc_shift_row(2u8, &multiplicand, &mut acc, 0u8);
        assert_eq!(acc, U16::from(0u16));
        assert_eq!(overflow, 0u8);
    }

    #[test]
    fn test_mul_acc_shift_row_with_carry() {
        // scalar=0xFF, multiplicand=0x00FF, acc=0x00FF, acc_hi=0x10
        // Word-by-word (u8 limbs, N=2):
        //   j=0: carrying_mul_add(0xFF, 0xFF, 0xFF, 0) = 255*255+255+0 = 65280 = (0x00, 0xFF)
        //        -> discard lo=0x00, carry=0xFF
        //   j=1: carrying_mul_add(0xFF, 0x00, 0x00, 0xFF) = 0+0+0xFF = 255 = (0xFF, 0x00)
        //        -> acc[0] = 0xFF, carry=0x00
        //   fold: acc_hi(0x10) + carry(0x00) = 0x10, no overflow -> acc[1] = 0x10
        // Result: acc = 0x10FF, return 0
        let multiplicand = U16::from(0x00FFu16);
        let mut acc = U16::from(0x00FFu16);
        let overflow = U16::mul_acc_shift_row(0xFFu8, &multiplicand, &mut acc, 0x10u8);
        assert_eq!(acc, U16::from(0x10FFu16));
        assert_eq!(overflow, 0u8);
    }

    #[test]
    fn test_mul_acc_shift_row_fold_overflow() {
        // Force the fold step (acc_hi + carry) to overflow.
        // scalar=0xFF, multiplicand=0xFFFF, acc=0xFFFF, acc_hi=0xFF
        // Word-by-word (u8 limbs, N=2):
        //   j=0: carrying_mul_add(0xFF, 0xFF, 0xFF, 0) = 255*255+255 = 65280 = (0x00, 0xFF)
        //        -> discard lo, carry=0xFF
        //   j=1: carrying_mul_add(0xFF, 0xFF, 0xFF, 0xFF) = 255*255+255+255 = 65535 = (0xFF, 0xFF)
        //        -> acc[0] = 0xFF, carry=0xFF
        //   fold: acc_hi(0xFF) + carry(0xFF) = 0x1FE -> sum=0xFE, overflow=true
        //        -> acc[1] = 0xFE, return 1
        let multiplicand = U16::from(0xFFFFu16);
        let mut acc = U16::from(0xFFFFu16);
        let overflow = U16::mul_acc_shift_row(0xFFu8, &multiplicand, &mut acc, 0xFFu8);
        assert_eq!(acc, U16::from(0xFEFFu16));
        assert_eq!(overflow, 1u8);
    }

    #[test]
    fn test_mul_acc_shift_row_n1() {
        // N=1: single word. The shift discards the only word and folds acc_hi.
        // scalar=3, multiplicand=0x05, acc=0x07, acc_hi=0x02
        // j=0: carrying_mul_add(3, 5, 7, 0) = 15+7 = 22 = (0x16, 0x00)
        //      -> discard lo=0x16, carry=0x00
        // No j=1..N-1 loop iterations.
        // fold: acc_hi(2) + carry(0) = 2, no overflow -> acc[0] = 0x02
        // Result: acc = 0x02, return 0
        let multiplicand = U8x1::from(5u8);
        let mut acc = U8x1::from(7u8);
        let overflow = U8x1::mul_acc_shift_row(3u8, &multiplicand, &mut acc, 2u8);
        assert_eq!(acc, U8x1::from(2u8));
        assert_eq!(overflow, 0u8);
    }
}
