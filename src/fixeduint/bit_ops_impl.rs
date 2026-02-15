use super::{const_shl_impl, const_shr_impl, FixedUInt, MachineWord};

use crate::const_numtrait::{
    ConstCheckedShl, ConstCheckedShr, ConstOverflowingShl, ConstOverflowingShr, ConstWrappingShl,
    ConstWrappingShr, ConstZero,
};
use crate::machineword::ConstMachineWord;
use crate::patch_num_traits::{OverflowingShl, OverflowingShr};

c0nst::c0nst! {
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Not for FixedUInt<T, N> {
        type Output = Self;
        fn not(self) -> Self::Output {
            let mut ret = <Self as ConstZero>::zero();
            let mut i = 0;
            while i < N {
                ret.array[i] = !self.array[i];
                i += 1;
            }
            ret
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::BitAnd<&FixedUInt<T, N>> for &FixedUInt<T, N> {
        type Output = FixedUInt<T, N>;
        fn bitand(self, other: &FixedUInt<T, N>) -> Self::Output {
            let mut ret = <FixedUInt<T, N> as ConstZero>::zero();
            let mut i = 0;
            while i < N {
                ret.array[i] = self.array[i] & other.array[i];
                i += 1;
            }
            ret
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::BitAnd for FixedUInt<T, N> {
        type Output = Self;
        fn bitand(self, other: Self) -> Self::Output {
            (&self).bitand(&other)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::BitAnd<&FixedUInt<T, N>> for FixedUInt<T, N> {
        type Output = Self;
        fn bitand(self, other: &FixedUInt<T, N>) -> Self::Output {
            (&self).bitand(other)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::BitAnd<FixedUInt<T, N>> for &FixedUInt<T, N> {
        type Output = FixedUInt<T, N>;
        fn bitand(self, other: FixedUInt<T, N>) -> Self::Output {
            self.bitand(&other)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::BitAndAssign for FixedUInt<T, N> {
        fn bitand_assign(&mut self, other: Self) {
            let mut i = 0;
            while i < N {
                self.array[i] &= other.array[i];
                i += 1;
            }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::BitOr<&FixedUInt<T, N>> for &FixedUInt<T, N> {
        type Output = FixedUInt<T, N>;
        fn bitor(self, other: &FixedUInt<T, N>) -> Self::Output {
            let mut ret = <FixedUInt<T, N> as ConstZero>::zero();
            let mut i = 0;
            while i < N {
                ret.array[i] = self.array[i] | other.array[i];
                i += 1;
            }
            ret
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::BitOr for FixedUInt<T, N> {
        type Output = Self;
        fn bitor(self, other: Self) -> Self::Output {
            (&self).bitor(&other)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::BitOr<&FixedUInt<T, N>> for FixedUInt<T, N> {
        type Output = Self;
        fn bitor(self, other: &FixedUInt<T, N>) -> Self::Output {
            (&self).bitor(other)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::BitOr<FixedUInt<T, N>> for &FixedUInt<T, N> {
        type Output = FixedUInt<T, N>;
        fn bitor(self, other: FixedUInt<T, N>) -> Self::Output {
            self.bitor(&other)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::BitOrAssign for FixedUInt<T, N> {
        fn bitor_assign(&mut self, other: Self) {
            let mut i = 0;
            while i < N {
                self.array[i] |= other.array[i];
                i += 1;
            }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::BitXor<&FixedUInt<T, N>> for &FixedUInt<T, N> {
        type Output = FixedUInt<T, N>;
        fn bitxor(self, other: &FixedUInt<T, N>) -> Self::Output {
            let mut ret = <FixedUInt<T, N> as ConstZero>::zero();
            let mut i = 0;
            while i < N {
                ret.array[i] = self.array[i] ^ other.array[i];
                i += 1;
            }
            ret
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::BitXor for FixedUInt<T, N> {
        type Output = Self;
        fn bitxor(self, other: Self) -> Self::Output {
            (&self).bitxor(&other)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::BitXor<&FixedUInt<T, N>> for FixedUInt<T, N> {
        type Output = Self;
        fn bitxor(self, other: &FixedUInt<T, N>) -> Self::Output {
            (&self).bitxor(other)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::BitXor<FixedUInt<T, N>> for &FixedUInt<T, N> {
        type Output = FixedUInt<T, N>;
        fn bitxor(self, other: FixedUInt<T, N>) -> Self::Output {
            self.bitxor(&other)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::BitXorAssign for FixedUInt<T, N> {
        fn bitxor_assign(&mut self, other: Self) {
            let mut i = 0;
            while i < N {
                self.array[i] ^= other.array[i];
                i += 1;
            }
        }
    }

    // Primary Shl/Shr implementations
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Shl<usize> for FixedUInt<T, N> {
        type Output = Self;
        fn shl(self, bits: usize) -> Self::Output {
            let mut result = self;
            const_shl_impl(&mut result, bits);
            result
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Shr<usize> for FixedUInt<T, N> {
        type Output = Self;
        fn shr(self, bits: usize) -> Self::Output {
            let mut result = self;
            const_shr_impl(&mut result, bits);
            result
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Shl<u32> for FixedUInt<T, N> {
        type Output = Self;
        fn shl(self, bits: u32) -> Self::Output {
            self.shl(bits as usize)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Shr<u32> for FixedUInt<T, N> {
        type Output = Self;
        fn shr(self, bits: u32) -> Self::Output {
            self.shr(bits as usize)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Shl<&usize> for FixedUInt<T, N> {
        type Output = Self;
        fn shl(self, bits: &usize) -> Self::Output {
            self.shl(*bits)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Shr<&usize> for FixedUInt<T, N> {
        type Output = Self;
        fn shr(self, bits: &usize) -> Self::Output {
            self.shr(*bits)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Shl<&u32> for FixedUInt<T, N> {
        type Output = Self;
        fn shl(self, bits: &u32) -> Self::Output {
            self.shl(*bits as usize)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Shr<&u32> for FixedUInt<T, N> {
        type Output = Self;
        fn shr(self, bits: &u32) -> Self::Output {
            self.shr(*bits as usize)
        }
    }

    // Shl/Shr for &FixedUInt
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Shl<usize> for &FixedUInt<T, N> {
        type Output = FixedUInt<T, N>;
        fn shl(self, bits: usize) -> Self::Output {
            (*self).shl(bits)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Shr<usize> for &FixedUInt<T, N> {
        type Output = FixedUInt<T, N>;
        fn shr(self, bits: usize) -> Self::Output {
            (*self).shr(bits)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Shl<u32> for &FixedUInt<T, N> {
        type Output = FixedUInt<T, N>;
        fn shl(self, bits: u32) -> Self::Output {
            (*self).shl(bits as usize)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Shr<u32> for &FixedUInt<T, N> {
        type Output = FixedUInt<T, N>;
        fn shr(self, bits: u32) -> Self::Output {
            (*self).shr(bits as usize)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Shl<&usize> for &FixedUInt<T, N> {
        type Output = FixedUInt<T, N>;
        fn shl(self, bits: &usize) -> Self::Output {
            (*self).shl(*bits)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Shr<&usize> for &FixedUInt<T, N> {
        type Output = FixedUInt<T, N>;
        fn shr(self, bits: &usize) -> Self::Output {
            (*self).shr(*bits)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Shl<&u32> for &FixedUInt<T, N> {
        type Output = FixedUInt<T, N>;
        fn shl(self, bits: &u32) -> Self::Output {
            (*self).shl(*bits as usize)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Shr<&u32> for &FixedUInt<T, N> {
        type Output = FixedUInt<T, N>;
        fn shr(self, bits: &u32) -> Self::Output {
            (*self).shr(*bits as usize)
        }
    }

    // ShlAssign/ShrAssign
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::ShlAssign<usize> for FixedUInt<T, N> {
        fn shl_assign(&mut self, bits: usize) {
            const_shl_impl(self, bits);
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::ShrAssign<usize> for FixedUInt<T, N> {
        fn shr_assign(&mut self, bits: usize) {
            const_shr_impl(self, bits);
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::ShlAssign<&usize> for FixedUInt<T, N> {
        fn shl_assign(&mut self, bits: &usize) {
            const_shl_impl(self, *bits);
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::ShrAssign<&usize> for FixedUInt<T, N> {
        fn shr_assign(&mut self, bits: &usize) {
            const_shr_impl(self, *bits);
        }
    }

    // Helper to normalize shift amount and detect overflow.
    // Handles both 16-bit (usize < u32) and 64-bit (bit_size > u32::MAX) platforms.
    c0nst fn normalize_shift_amount(bits: u32, bit_size: usize) -> (usize, bool) {
        let bit_size_u32 = bit_size as u32;
        if bit_size == 0 {
            // Zero-size type: always overflow
            (0, true)
        } else if bit_size_u32 == 0 {
            // bit_size is a non-zero multiple of 2^32 (huge type on 64-bit).
            // Since bits is u32, it's always smaller than bit_size. No overflow.
            (bits as usize, false)
        } else if bits >= bit_size_u32 {
            // Normal case: shift exceeds bit width
            ((bits % bit_size_u32) as usize, true)
        } else {
            (bits as usize, false)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstOverflowingShl for FixedUInt<T, N> {
        fn overflowing_shl(self, bits: u32) -> (Self, bool) {
            let (shift, overflow) = normalize_shift_amount(bits, Self::BIT_SIZE);
            let res = core::ops::Shl::<usize>::shl(self, shift);
            (res, overflow)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstOverflowingShr for FixedUInt<T, N> {
        fn overflowing_shr(self, bits: u32) -> (Self, bool) {
            let (shift, overflow) = normalize_shift_amount(bits, Self::BIT_SIZE);
            let res = core::ops::Shr::<usize>::shr(self, shift);
            (res, overflow)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstWrappingShl for FixedUInt<T, N> {
        fn wrapping_shl(self, bits: u32) -> Self {
            ConstOverflowingShl::overflowing_shl(self, bits).0
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstWrappingShr for FixedUInt<T, N> {
        fn wrapping_shr(self, bits: u32) -> Self {
            ConstOverflowingShr::overflowing_shr(self, bits).0
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstCheckedShl for FixedUInt<T, N> {
        fn checked_shl(self, bits: u32) -> Option<Self> {
            let (res, overflow) = ConstOverflowingShl::overflowing_shl(self, bits);
            if overflow { None } else { Some(res) }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstCheckedShr for FixedUInt<T, N> {
        fn checked_shr(self, bits: u32) -> Option<Self> {
            let (res, overflow) = ConstOverflowingShr::overflowing_shr(self, bits);
            if overflow { None } else { Some(res) }
        }
    }
}

// OverflowingShl/Shr from patch_num_traits - delegate to const impls
impl<T: MachineWord, const N: usize> OverflowingShl for FixedUInt<T, N> {
    fn overflowing_shl(self, bits: u32) -> (Self, bool) {
        ConstOverflowingShl::overflowing_shl(self, bits)
    }
}

impl<T: MachineWord, const N: usize> OverflowingShr for FixedUInt<T, N> {
    fn overflowing_shr(self, bits: u32) -> (Self, bool) {
        ConstOverflowingShr::overflowing_shr(self, bits)
    }
}

// num_traits wrappers - delegate to const impls
impl<T: MachineWord, const N: usize> num_traits::WrappingShl for FixedUInt<T, N> {
    fn wrapping_shl(&self, bits: u32) -> Self {
        ConstWrappingShl::wrapping_shl(*self, bits)
    }
}

impl<T: MachineWord, const N: usize> num_traits::WrappingShr for FixedUInt<T, N> {
    fn wrapping_shr(&self, bits: u32) -> Self {
        ConstWrappingShr::wrapping_shr(*self, bits)
    }
}

impl<T: MachineWord, const N: usize> num_traits::CheckedShl for FixedUInt<T, N> {
    fn checked_shl(&self, bits: u32) -> Option<Self> {
        ConstCheckedShl::checked_shl(*self, bits)
    }
}

impl<T: MachineWord, const N: usize> num_traits::CheckedShr for FixedUInt<T, N> {
    fn checked_shr(&self, bits: u32) -> Option<Self> {
        ConstCheckedShr::checked_shr(*self, bits)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bitand_combinations() {
        let a = FixedUInt::<u8, 2>::from(12u8); // 1100
        let b = FixedUInt::<u8, 2>::from(10u8); // 1010
        let expected = FixedUInt::<u8, 2>::from(8u8); // 1000

        // value & value
        assert_eq!(a & b, expected);
        // value & ref
        assert_eq!(a & &b, expected);
        // ref & value
        assert_eq!(&a & b, expected);
        // ref & ref
        assert_eq!(&a & &b, expected);
    }

    #[test]
    fn test_bitor_combinations() {
        let a = FixedUInt::<u8, 2>::from(12u8); // 1100
        let b = FixedUInt::<u8, 2>::from(10u8); // 1010
        let expected = FixedUInt::<u8, 2>::from(14u8); // 1110

        // value | value
        assert_eq!(a | b, expected);
        // value | ref
        assert_eq!(a | &b, expected);
        // ref | value
        assert_eq!(&a | b, expected);
        // ref | ref
        assert_eq!(&a | &b, expected);
    }

    #[test]
    fn test_bitxor_combinations() {
        let a = FixedUInt::<u8, 2>::from(12u8); // 1100
        let b = FixedUInt::<u8, 2>::from(10u8); // 1010
        let expected = FixedUInt::<u8, 2>::from(6u8); // 0110

        // value ^ value
        assert_eq!(a ^ b, expected);
        // value ^ ref
        assert_eq!(a ^ &b, expected);
        // ref ^ value
        assert_eq!(&a ^ b, expected);
        // ref ^ ref
        assert_eq!(&a ^ &b, expected);
    }

    #[test]
    fn test_shl_combinations() {
        let a = FixedUInt::<u8, 2>::from(2u8); // 0010
        let shift: usize = 2;
        let expected = FixedUInt::<u8, 2>::from(8u8); // 1000

        // value << value
        assert_eq!(a << shift, expected);
        // value << ref
        assert_eq!(a << &shift, expected);
        // ref << value
        assert_eq!(&a << shift, expected);
        // ref << ref
        assert_eq!(&a << &shift, expected);

        // Same with u32
        let shift32: u32 = 2;
        assert_eq!(a << shift32, expected);
        assert_eq!(a << &shift32, expected);
        assert_eq!(&a << shift32, expected);
        assert_eq!(&a << &shift32, expected);
    }

    #[test]
    fn test_shr_combinations() {
        let a = FixedUInt::<u8, 2>::from(8u8); // 1000
        let shift: usize = 2;
        let expected = FixedUInt::<u8, 2>::from(2u8); // 0010

        // value >> value
        assert_eq!(a >> shift, expected);
        // value >> ref
        assert_eq!(a >> &shift, expected);
        // ref >> value
        assert_eq!(&a >> shift, expected);
        // ref >> ref
        assert_eq!(&a >> &shift, expected);

        // Same with u32
        let shift32: u32 = 2;
        assert_eq!(a >> shift32, expected);
        assert_eq!(a >> &shift32, expected);
        assert_eq!(&a >> shift32, expected);
        assert_eq!(&a >> &shift32, expected);
    }

    #[test]
    fn test_const_bitops() {
        type TestInt = FixedUInt<u8, 2>;

        let a = TestInt::from(0b11001100u8);
        let b = TestInt::from(0b10101010u8);

        // Test not
        let not_a = !a;
        assert_eq!(not_a.array[0], 0b00110011);
        assert_eq!(not_a.array[1], 0xFF);

        // Test bitand
        assert_eq!(a & b, TestInt::from(0b10001000u8));

        // Test bitor
        assert_eq!(a | b, TestInt::from(0b11101110u8));

        // Test bitxor
        assert_eq!(a ^ b, TestInt::from(0b01100110u8));

        // Test shl
        assert_eq!(TestInt::from(1u8) << 4usize, TestInt::from(16u8));

        // Test shr
        assert_eq!(TestInt::from(16u8) >> 2usize, TestInt::from(4u8));

        #[cfg(feature = "nightly")]
        {
            const A: TestInt = FixedUInt {
                array: [0b11001100, 0],
            };
            const B: TestInt = FixedUInt {
                array: [0b10101010, 0],
            };

            const NOT_A: TestInt = !A;
            const AND_AB: TestInt = A & B;
            const OR_AB: TestInt = A | B;
            const XOR_AB: TestInt = A ^ B;
            const SHL_1: TestInt = FixedUInt { array: [1u8, 0] } << 4usize;
            const SHR_16: TestInt = FixedUInt { array: [16u8, 0] } >> 2usize;

            assert_eq!(NOT_A.array[0], 0b00110011);
            assert_eq!(AND_AB.array[0], 0b10001000);
            assert_eq!(OR_AB.array[0], 0b11101110);
            assert_eq!(XOR_AB.array[0], 0b01100110);
            assert_eq!(SHL_1.array[0], 16);
            assert_eq!(SHR_16.array[0], 4);
        }
    }
}
