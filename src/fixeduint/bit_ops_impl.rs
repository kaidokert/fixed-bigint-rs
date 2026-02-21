use super::{const_shl_impl, const_shr_impl, FixedUInt, MachineWord};

use crate::const_numtrait::{
    ConstCheckedShl, ConstCheckedShr, ConstOverflowingShl, ConstOverflowingShr,
    ConstUnboundedShift, ConstWrappingShl, ConstWrappingShr, ConstZero,
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
        fn overflowing_shl(&self, bits: u32) -> (Self, bool) {
            let (shift, overflow) = normalize_shift_amount(bits, Self::BIT_SIZE);
            let res = core::ops::Shl::<usize>::shl(*self, shift);
            (res, overflow)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstOverflowingShr for FixedUInt<T, N> {
        fn overflowing_shr(&self, bits: u32) -> (Self, bool) {
            let (shift, overflow) = normalize_shift_amount(bits, Self::BIT_SIZE);
            let res = core::ops::Shr::<usize>::shr(*self, shift);
            (res, overflow)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstWrappingShl for FixedUInt<T, N> {
        fn wrapping_shl(&self, bits: u32) -> Self {
            ConstOverflowingShl::overflowing_shl(self, bits).0
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstWrappingShr for FixedUInt<T, N> {
        fn wrapping_shr(&self, bits: u32) -> Self {
            ConstOverflowingShr::overflowing_shr(self, bits).0
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstCheckedShl for FixedUInt<T, N> {
        fn checked_shl(&self, bits: u32) -> Option<Self> {
            let (res, overflow) = ConstOverflowingShl::overflowing_shl(self, bits);
            if overflow { None } else { Some(res) }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstCheckedShr for FixedUInt<T, N> {
        fn checked_shr(&self, bits: u32) -> Option<Self> {
            let (res, overflow) = ConstOverflowingShr::overflowing_shr(self, bits);
            if overflow { None } else { Some(res) }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstUnboundedShift for FixedUInt<T, N> {
        fn unbounded_shl(self, rhs: u32) -> Self {
            let (shift, overflow) = normalize_shift_amount(rhs, Self::BIT_SIZE);
            if overflow {
                Self::zero()
            } else {
                self << shift
            }
        }

        fn unbounded_shr(self, rhs: u32) -> Self {
            let (shift, overflow) = normalize_shift_amount(rhs, Self::BIT_SIZE);
            if overflow {
                Self::zero()
            } else {
                self >> shift
            }
        }
    }
}

// OverflowingShl/Shr from patch_num_traits - delegate to const impls
impl<T: MachineWord, const N: usize> OverflowingShl for FixedUInt<T, N> {
    fn overflowing_shl(self, bits: u32) -> (Self, bool) {
        ConstOverflowingShl::overflowing_shl(&self, bits)
    }
}

impl<T: MachineWord, const N: usize> OverflowingShr for FixedUInt<T, N> {
    fn overflowing_shr(self, bits: u32) -> (Self, bool) {
        ConstOverflowingShr::overflowing_shr(&self, bits)
    }
}

// num_traits wrappers - delegate to const impls
impl<T: MachineWord, const N: usize> num_traits::WrappingShl for FixedUInt<T, N> {
    fn wrapping_shl(&self, bits: u32) -> Self {
        ConstWrappingShl::wrapping_shl(self, bits)
    }
}

impl<T: MachineWord, const N: usize> num_traits::WrappingShr for FixedUInt<T, N> {
    fn wrapping_shr(&self, bits: u32) -> Self {
        ConstWrappingShr::wrapping_shr(self, bits)
    }
}

impl<T: MachineWord, const N: usize> num_traits::CheckedShl for FixedUInt<T, N> {
    fn checked_shl(&self, bits: u32) -> Option<Self> {
        ConstCheckedShl::checked_shl(self, bits)
    }
}

impl<T: MachineWord, const N: usize> num_traits::CheckedShr for FixedUInt<T, N> {
    fn checked_shr(&self, bits: u32) -> Option<Self> {
        ConstCheckedShr::checked_shr(self, bits)
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

    #[test]
    fn test_const_shift_traits() {
        type TestInt = FixedUInt<u8, 2>; // 16-bit

        // Test overflowing_shl
        let a = TestInt::from(0x80u8); // 0x0080
        let (res, overflow) = ConstOverflowingShl::overflowing_shl(&a, 8);
        assert_eq!(res.array, [0, 0x80]); // 0x8000
        assert!(!overflow);

        let (res, overflow) = ConstOverflowingShl::overflowing_shl(&a, 16);
        assert_eq!(res.array, [0x80, 0]); // wraps around
        assert!(overflow);

        let (res, overflow) = ConstOverflowingShl::overflowing_shl(&a, 9);
        assert_eq!(res.array, [0, 0]); // high bits shifted out (but shift < bit_width)
        assert!(!overflow); // 9 < 16, so no overflow

        // Test overflowing_shr
        let b = TestInt::from(0x0100u16); // 0x0100
        let (res, overflow) = ConstOverflowingShr::overflowing_shr(&b, 8);
        assert_eq!(res.array, [1, 0]); // 0x0001
        assert!(!overflow);

        let (res, overflow) = ConstOverflowingShr::overflowing_shr(&b, 16);
        assert_eq!(res.array, [0, 1]); // wraps
        assert!(overflow);

        // Test wrapping_shl
        let c = TestInt::from(1u8);
        assert_eq!(ConstWrappingShl::wrapping_shl(&c, 4).array, [16, 0]);
        assert_eq!(ConstWrappingShl::wrapping_shl(&c, 16).array, [1, 0]); // wraps
        assert_eq!(ConstWrappingShl::wrapping_shl(&c, 17).array, [2, 0]); // wraps

        // Test wrapping_shr
        let d = TestInt::from(0x8000u16);
        assert_eq!(ConstWrappingShr::wrapping_shr(&d, 4).array, [0, 0x08]);
        assert_eq!(ConstWrappingShr::wrapping_shr(&d, 16).array, [0, 0x80]); // wraps
        assert_eq!(ConstWrappingShr::wrapping_shr(&d, 17).array, [0, 0x40]); // wraps

        // Test checked_shl
        let e = TestInt::from(1u8);
        assert_eq!(
            ConstCheckedShl::checked_shl(&e, 4),
            Some(TestInt::from(16u8))
        );
        assert_eq!(
            ConstCheckedShl::checked_shl(&e, 15),
            Some(TestInt::from(0x8000u16))
        );
        assert_eq!(ConstCheckedShl::checked_shl(&e, 16), None); // overflow

        // Test checked_shr
        let f = TestInt::from(0x8000u16);
        assert_eq!(
            ConstCheckedShr::checked_shr(&f, 15),
            Some(TestInt::from(1u8))
        );
        assert_eq!(ConstCheckedShr::checked_shr(&f, 16), None); // overflow

        // Test edge case: zero shift
        let g = TestInt::from(42u8);
        assert_eq!(ConstOverflowingShl::overflowing_shl(&g, 0), (g, false));
        assert_eq!(ConstOverflowingShr::overflowing_shr(&g, 0), (g, false));
        assert_eq!(ConstWrappingShl::wrapping_shl(&g, 0), g);
        assert_eq!(ConstWrappingShr::wrapping_shr(&g, 0), g);
        assert_eq!(ConstCheckedShl::checked_shl(&g, 0), Some(g));
        assert_eq!(ConstCheckedShr::checked_shr(&g, 0), Some(g));
    }

    #[test]
    fn test_const_shift_traits_n0() {
        // Test with N=0 (zero-sized type)
        type ZeroInt = FixedUInt<u8, 0>;
        let z = ZeroInt { array: [] };

        // All shifts on zero-sized type should overflow
        assert_eq!(ConstOverflowingShl::overflowing_shl(&z, 0), (z, true));
        assert_eq!(ConstOverflowingShr::overflowing_shr(&z, 0), (z, true));
        assert_eq!(ConstWrappingShl::wrapping_shl(&z, 0), z);
        assert_eq!(ConstWrappingShr::wrapping_shr(&z, 0), z);
        assert_eq!(ConstCheckedShl::checked_shl(&z, 0), None);
        assert_eq!(ConstCheckedShr::checked_shr(&z, 0), None);
    }

    #[test]
    fn test_num_traits_shift_wrappers() {
        use num_traits::{CheckedShl, CheckedShr, WrappingShl, WrappingShr};

        type TestInt = FixedUInt<u8, 2>;

        let a = TestInt::from(1u8);

        // num_traits::WrappingShl delegates to ConstWrappingShl
        assert_eq!(WrappingShl::wrapping_shl(&a, 4), TestInt::from(16u8));
        assert_eq!(WrappingShl::wrapping_shl(&a, 16), a); // wraps

        // num_traits::WrappingShr
        let b = TestInt::from(16u8);
        assert_eq!(WrappingShr::wrapping_shr(&b, 4), TestInt::from(1u8));

        // num_traits::CheckedShl
        assert_eq!(CheckedShl::checked_shl(&a, 4), Some(TestInt::from(16u8)));
        assert_eq!(CheckedShl::checked_shl(&a, 16), None);

        // num_traits::CheckedShr
        assert_eq!(CheckedShr::checked_shr(&b, 4), Some(TestInt::from(1u8)));
        assert_eq!(CheckedShr::checked_shr(&b, 16), None);
    }

    #[test]
    fn test_unbounded_shift() {
        type U16 = FixedUInt<u8, 2>;

        let one = U16::from(1u8);

        // Normal shifts (within bounds)
        assert_eq!(ConstUnboundedShift::unbounded_shl(one, 0), one);
        assert_eq!(ConstUnboundedShift::unbounded_shl(one, 4), U16::from(16u8));
        assert_eq!(
            ConstUnboundedShift::unbounded_shl(one, 15),
            U16::from(0x8000u16)
        );

        assert_eq!(
            ConstUnboundedShift::unbounded_shr(U16::from(0x8000u16), 15),
            one
        );
        assert_eq!(ConstUnboundedShift::unbounded_shr(U16::from(16u8), 4), one);

        // At boundary (shift by bit width) - returns 0
        assert_eq!(ConstUnboundedShift::unbounded_shl(one, 16), U16::from(0u8));
        assert_eq!(
            ConstUnboundedShift::unbounded_shr(U16::from(0xFFFFu16), 16),
            U16::from(0u8)
        );

        // Beyond boundary - returns 0
        assert_eq!(
            ConstUnboundedShift::unbounded_shl(U16::from(0xFFFFu16), 17),
            U16::from(0u8)
        );
        assert_eq!(
            ConstUnboundedShift::unbounded_shl(U16::from(0xFFFFu16), 100),
            U16::from(0u8)
        );
        assert_eq!(
            ConstUnboundedShift::unbounded_shr(U16::from(0xFFFFu16), 17),
            U16::from(0u8)
        );
        assert_eq!(
            ConstUnboundedShift::unbounded_shr(U16::from(0xFFFFu16), 100),
            U16::from(0u8)
        );

        // Test with different word sizes
        type U32 = FixedUInt<u8, 4>;
        let one32 = U32::from(1u8);
        assert_eq!(
            ConstUnboundedShift::unbounded_shl(one32, 31),
            U32::from(0x80000000u32)
        );
        assert_eq!(
            ConstUnboundedShift::unbounded_shl(one32, 32),
            U32::from(0u8)
        );
        assert_eq!(
            ConstUnboundedShift::unbounded_shr(U32::from(0x80000000u32), 31),
            one32
        );
        assert_eq!(
            ConstUnboundedShift::unbounded_shr(U32::from(0x80000000u32), 32),
            U32::from(0u8)
        );
    }

    #[test]
    fn test_unbounded_shift_polymorphic() {
        fn test_unbounded<T>(val: T, shift: u32, expected_shl: T, expected_shr: T)
        where
            T: ConstUnboundedShift + Eq + core::fmt::Debug + Copy,
        {
            assert_eq!(ConstUnboundedShift::unbounded_shl(val, shift), expected_shl);
            assert_eq!(ConstUnboundedShift::unbounded_shr(val, shift), expected_shr);
        }

        // Test with FixedUInt layouts
        type U8x2 = FixedUInt<u8, 2>;
        type U8x4 = FixedUInt<u8, 4>;
        type U16x2 = FixedUInt<u16, 2>;

        // Same logical shift, different layouts
        test_unbounded(U8x2::from(1u8), 4, U8x2::from(16u8), U8x2::from(0u8));
        test_unbounded(U8x4::from(1u8), 4, U8x4::from(16u8), U8x4::from(0u8));
        test_unbounded(U16x2::from(1u8), 4, U16x2::from(16u8), U16x2::from(0u8));

        // Test with primitives
        test_unbounded(1u8, 4, 16u8, 0u8);
        test_unbounded(1u16, 4, 16u16, 0u16);
        test_unbounded(1u32, 4, 16u32, 0u32);

        // Boundary tests
        test_unbounded(1u8, 8, 0u8, 0u8);
        test_unbounded(U8x2::from(1u8), 16, U8x2::from(0u8), U8x2::from(0u8));
    }
}
