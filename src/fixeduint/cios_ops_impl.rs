//! CiosOps implementation for FixedUInt.
//!
//! Provides row-level fused multiply-accumulate operations used by
//! CIOS Montgomery multiplication. All limb access is internal to
//! this module; the public trait surface never exposes raw arrays.

use super::{FixedUInt, MachineWord};
use crate::cios_ops::CiosOps;
use crate::const_numtraits::{ConstBorrowingSub, ConstCarryingAdd, ConstZero};
use crate::patch_num_traits::CarryingMul;

impl<T, const N: usize> CiosOps for FixedUInt<T, N>
where
    T: MachineWord
        + CarryingMul<Output = T>
        + ConstCarryingAdd
        + ConstBorrowingSub
        + num_traits::Zero
        + num_traits::One
        + num_traits::WrappingMul
        + num_traits::ops::overflowing::OverflowingAdd
        + core::ops::Add<Output = T>,
{
    type Word = T;

    #[inline]
    fn word_count() -> usize {
        N
    }

    #[inline]
    fn word(&self, i: usize) -> T {
        self.array[i]
    }

    #[inline]
    fn lowest_word(&self) -> T {
        self.array[0]
    }

    #[inline]
    fn zero_value() -> Self {
        Self {
            array: [<T as ConstZero>::zero(); N],
        }
    }

    fn mul_acc_row(
        scalar: T,
        multiplicand: &Self,
        acc: &mut Self,
        carry_in: T,
    ) -> T {
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

    fn mul_acc_shift_row(
        scalar: T,
        multiplicand: &Self,
        acc: &mut Self,
        acc_hi: T,
    ) -> T {
        // First word: discarded (zero by CIOS construction)
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
        let (sum, overflow) =
            <T as ConstCarryingAdd>::carrying_add(acc_hi, carry, false);
        acc.array[N - 1] = sum;

        // Return overflow as word (0 or 1)
        if overflow {
            <T as num_traits::One>::one()
        } else {
            <T as ConstZero>::zero()
        }
    }

    fn conditional_sub(acc: &mut Self, modulus: &Self, overflow: T) {
        if overflow > <T as ConstZero>::zero() || *acc >= *modulus {
            let (result, _) =
                <Self as ConstBorrowingSub>::borrowing_sub(*acc, *modulus, false);
            *acc = result;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type U16 = FixedUInt<u8, 2>;
    type U32 = FixedUInt<u8, 4>;
    type U64x4 = FixedUInt<u64, 4>;

    #[test]
    fn test_word_access() {
        let val = U16::from(0x1234u16);
        assert_eq!(U16::word_count(), 2);
        assert_eq!(val.lowest_word(), 0x34u8);
        assert_eq!(val.word(0), 0x34u8);
        assert_eq!(val.word(1), 0x12u8);
    }

    #[test]
    fn test_zero_value() {
        let z = U32::zero_value();
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
        // 200 * 200 = 40000, which overflows U16 (max 65535 fits, but carry may propagate)
        let multiplicand = U16::from(200u16);
        let mut acc = U16::zero_value();
        let carry = U16::mul_acc_row(200u8, &multiplicand, &mut acc, 0u8);
        // 200 * 200 = 40000 = 0x9C40
        // The row operation is word-by-word, so:
        // j=0: 200 * (200 & 0xFF) + 0 + 0 = 200 * 200 = 40000 = (0x40, 0x9C) -> acc[0]=0x40, carry=0x9C
        // j=1: 200 * 0 + 0 + 0x9C = 0x9C -> acc[1]=0x9C, carry=0
        assert_eq!(acc, U16::from(40000u16));
        assert_eq!(carry, 0u8);
    }

    #[test]
    fn test_conditional_sub() {
        let modulus = U16::from(13u16);

        // acc < modulus: no change
        let mut acc = U16::from(5u16);
        U16::conditional_sub(&mut acc, &modulus, 0u8);
        assert_eq!(acc, U16::from(5u16));

        // acc == modulus: subtract
        let mut acc = U16::from(13u16);
        U16::conditional_sub(&mut acc, &modulus, 0u8);
        assert_eq!(acc, U16::from(0u16));

        // acc > modulus: subtract
        let mut acc = U16::from(15u16);
        U16::conditional_sub(&mut acc, &modulus, 0u8);
        assert_eq!(acc, U16::from(2u16));

        // overflow > 0: always subtract
        let mut acc = U16::from(5u16);
        U16::conditional_sub(&mut acc, &modulus, 1u8);
        // 0x10005 - 13 = 65528 (wrapping), but since we just subtract modulus from acc:
        // 5 - 13 wraps to 65528 (0xFFF8)
        assert_eq!(acc, U16::from(0xFFF8u16));
    }

    #[test]
    fn test_word_count_u64x4() {
        assert_eq!(U64x4::word_count(), 4);
    }
}
