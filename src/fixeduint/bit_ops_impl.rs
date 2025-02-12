use super::{FixedUInt, MachineWord};

use crate::patch_num_traits::{OverflowingShl, OverflowingShr};

use num_traits::Zero;

impl<T: MachineWord, const N: usize> core::ops::Not for FixedUInt<T, N> {
    type Output = Self;
    fn not(self) -> <Self as core::ops::Not>::Output {
        let mut ret = Self::zero();
        for i in 0..N {
            ret.array[i] = !self.array[i]
        }
        ret
    }
}

impl<T: MachineWord, const N: usize> core::ops::BitAnd<&FixedUInt<T, N>> for &FixedUInt<T, N> {
    type Output = FixedUInt<T, N>;
    fn bitand(self, other: &FixedUInt<T, N>) -> Self::Output {
        let mut ret = Self::Output::zero();
        for i in 0..N {
            ret.array[i] = self.array[i] & other.array[i]
        }
        ret
    }
}

impl<T: MachineWord, const N: usize> core::ops::BitAnd for FixedUInt<T, N> {
    type Output = Self;
    fn bitand(self, other: Self) -> Self::Output {
        (&self).bitand(&other)
    }
}

impl<T: MachineWord, const N: usize> core::ops::BitAnd<&FixedUInt<T, N>> for FixedUInt<T, N> {
    type Output = Self;
    fn bitand(self, other: &FixedUInt<T, N>) -> Self::Output {
        (&self).bitand(other)
    }
}

impl<T: MachineWord, const N: usize> core::ops::BitAnd<FixedUInt<T, N>> for &FixedUInt<T, N> {
    type Output = FixedUInt<T, N>;
    fn bitand(self, other: FixedUInt<T, N>) -> Self::Output {
        self.bitand(&other)
    }
}

impl<T: MachineWord, const N: usize> core::ops::BitAndAssign for FixedUInt<T, N> {
    fn bitand_assign(&mut self, other: Self) {
        for i in 0..N {
            self.array[i] &= other.array[i]
        }
    }
}

impl<T: MachineWord, const N: usize> core::ops::BitOr<&FixedUInt<T, N>> for &FixedUInt<T, N> {
    type Output = FixedUInt<T, N>;
    fn bitor(self, other: &FixedUInt<T, N>) -> Self::Output {
        let mut ret = Self::Output::zero();
        for i in 0..N {
            ret.array[i] = self.array[i] | other.array[i]
        }
        ret
    }
}

impl<T: MachineWord, const N: usize> core::ops::BitOr for FixedUInt<T, N> {
    type Output = Self;
    fn bitor(self, other: Self) -> Self::Output {
        (&self).bitor(&other)
    }
}

impl<T: MachineWord, const N: usize> core::ops::BitOr<&FixedUInt<T, N>> for FixedUInt<T, N> {
    type Output = Self;
    fn bitor(self, other: &FixedUInt<T, N>) -> Self::Output {
        (&self).bitor(other)
    }
}

impl<T: MachineWord, const N: usize> core::ops::BitOr<FixedUInt<T, N>> for &FixedUInt<T, N> {
    type Output = FixedUInt<T, N>;
    fn bitor(self, other: FixedUInt<T, N>) -> Self::Output {
        self.bitor(&other)
    }
}

impl<T: MachineWord, const N: usize> core::ops::BitOrAssign for FixedUInt<T, N> {
    fn bitor_assign(&mut self, other: Self) {
        for i in 0..N {
            self.array[i] |= other.array[i]
        }
    }
}

impl<T: MachineWord, const N: usize> core::ops::BitXor<&FixedUInt<T, N>> for &FixedUInt<T, N> {
    type Output = FixedUInt<T, N>;
    fn bitxor(self, other: &FixedUInt<T, N>) -> Self::Output {
        let mut ret = Self::Output::zero();
        for i in 0..N {
            ret.array[i] = self.array[i] ^ other.array[i]
        }
        ret
    }
}

impl<T: MachineWord, const N: usize> core::ops::BitXor for FixedUInt<T, N> {
    type Output = Self;
    fn bitxor(self, other: Self) -> Self::Output {
        (&self).bitxor(&other)
    }
}

impl<T: MachineWord, const N: usize> core::ops::BitXor<&FixedUInt<T, N>> for FixedUInt<T, N> {
    type Output = Self;
    fn bitxor(self, other: &FixedUInt<T, N>) -> Self::Output {
        (&self).bitxor(other)
    }
}

impl<T: MachineWord, const N: usize> core::ops::BitXor<FixedUInt<T, N>> for &FixedUInt<T, N> {
    type Output = FixedUInt<T, N>;
    fn bitxor(self, other: FixedUInt<T, N>) -> Self::Output {
        self.bitxor(&other)
    }
}

impl<T: MachineWord, const N: usize> core::ops::BitXorAssign for FixedUInt<T, N> {
    fn bitxor_assign(&mut self, other: Self) {
        for i in 0..N {
            self.array[i] ^= other.array[i]
        }
    }
}

impl<T: MachineWord, const N: usize> OverflowingShl for FixedUInt<T, N> {
    fn overflowing_shl(self, bits: u32) -> (Self, bool) {
        let bitsu = bits as usize;
        let (shift, overflow) = if bitsu >= Self::BIT_SIZE {
            (bitsu & (Self::BIT_SIZE - 1), true)
        } else {
            (bitsu, false)
        };
        let res = core::ops::Shl::<usize>::shl(self, shift);
        (res, overflow)
    }
}

impl<T: MachineWord, const N: usize> core::ops::Shl<u32> for FixedUInt<T, N> {
    type Output = Self;
    fn shl(self, bits: u32) -> <Self as core::ops::Shl<u32>>::Output {
        core::ops::Shl::<usize>::shl(self, bits as usize)
    }
}

impl<T: MachineWord, const N: usize> core::ops::Shl<usize> for FixedUInt<T, N> {
    type Output = Self;
    fn shl(self, bits: usize) -> <Self as core::ops::Shl<usize>>::Output {
        // This copy can be avoided
        let mut result = self;
        Self::shl_impl(&mut result, bits);
        result
    }
}

impl<T: MachineWord, const N: usize> core::ops::Shl<&'_ usize> for FixedUInt<T, N> {
    type Output = Self;
    fn shl(self, bits: &usize) -> <Self as core::ops::Shl<usize>>::Output {
        let mut result = self;
        Self::shl_impl(&mut result, *bits);
        result
    }
}

impl<T: MachineWord, const N: usize> num_traits::WrappingShl for FixedUInt<T, N> {
    fn wrapping_shl(&self, bits: u32) -> Self {
        self.overflowing_shl(bits).0
    }
}

impl<T: MachineWord, const N: usize> num_traits::CheckedShl for FixedUInt<T, N> {
    fn checked_shl(&self, bits: u32) -> Option<Self> {
        let res = self.overflowing_shl(bits);
        if res.1 {
            None
        } else {
            Some(res.0)
        }
    }
}

// SaturatingShl doesn't exist

impl<T: MachineWord, const N: usize> core::ops::ShlAssign<usize> for FixedUInt<T, N> {
    fn shl_assign(&mut self, bits: usize) {
        Self::shl_impl(self, bits);
    }
}

impl<T: MachineWord, const N: usize> core::ops::ShlAssign<&'_ usize> for FixedUInt<T, N> {
    fn shl_assign(&mut self, bits: &usize) {
        Self::shl_impl(self, *bits);
    }
}

impl<T: MachineWord, const N: usize> OverflowingShr for FixedUInt<T, N> {
    fn overflowing_shr(self, bits: u32) -> (Self, bool) {
        let bitsu = bits as usize;
        let (shift, overflow) = if bitsu >= Self::BIT_SIZE {
            (bitsu & (Self::BIT_SIZE - 1), true)
        } else {
            (bitsu, false)
        };
        let res = core::ops::Shr::<usize>::shr(self, shift);
        (res, overflow)
    }
}

impl<T: MachineWord, const N: usize> core::ops::Shr<u32> for FixedUInt<T, N> {
    type Output = Self;
    fn shr(self, bits: u32) -> <Self as core::ops::Shr<u32>>::Output {
        core::ops::Shr::<usize>::shr(self, bits as usize)
    }
}

impl<T: MachineWord, const N: usize> core::ops::Shr<usize> for FixedUInt<T, N> {
    type Output = Self;
    fn shr(self, bits: usize) -> <Self as core::ops::Shr<usize>>::Output {
        // Technically, this copy can be avoided
        let mut result = self;
        Self::shr_impl(&mut result, bits);
        result
    }
}

impl<T: MachineWord, const N: usize> core::ops::Shr<&'_ usize> for FixedUInt<T, N> {
    type Output = Self;
    fn shr(self, bits: &usize) -> <Self as core::ops::Shr<usize>>::Output {
        let mut result = self;
        Self::shr_impl(&mut result, *bits);
        result
    }
}

impl<T: MachineWord, const N: usize> num_traits::WrappingShr for FixedUInt<T, N> {
    fn wrapping_shr(&self, bits: u32) -> Self {
        self.overflowing_shr(bits).0
    }
}

impl<T: MachineWord, const N: usize> num_traits::CheckedShr for FixedUInt<T, N> {
    fn checked_shr(&self, bits: u32) -> Option<Self> {
        let res = self.overflowing_shr(bits);
        if res.1 {
            None
        } else {
            Some(res.0)
        }
    }
}

// SaturatingShr doesn't exist

impl<T: MachineWord, const N: usize> core::ops::ShrAssign<usize> for FixedUInt<T, N> {
    fn shr_assign(&mut self, bits: usize) {
        Self::shr_impl(self, bits);
    }
}

impl<T: MachineWord, const N: usize> core::ops::ShrAssign<&'_ usize> for FixedUInt<T, N> {
    fn shr_assign(&mut self, bits: &usize) {
        Self::shr_impl(self, *bits);
    }
}

impl<T: MachineWord, const N: usize> core::ops::Shl<&usize> for &FixedUInt<T, N> {
    type Output = FixedUInt<T, N>;
    fn shl(self, bits: &usize) -> Self::Output {
        let mut result = *self;
        Self::Output::shl_impl(&mut result, *bits);
        result
    }
}

impl<T: MachineWord, const N: usize> core::ops::Shl<&u32> for &FixedUInt<T, N> {
    type Output = FixedUInt<T, N>;
    fn shl(self, bits: &u32) -> Self::Output {
        self.shl(&(*bits as usize))
    }
}

impl<T: MachineWord, const N: usize> core::ops::Shr<&usize> for &FixedUInt<T, N> {
    type Output = FixedUInt<T, N>;
    fn shr(self, bits: &usize) -> Self::Output {
        let mut result = *self;
        Self::Output::shr_impl(&mut result, *bits);
        result
    }
}

impl<T: MachineWord, const N: usize> core::ops::Shr<&u32> for &FixedUInt<T, N> {
    type Output = FixedUInt<T, N>;
    fn shr(self, bits: &u32) -> Self::Output {
        self.shr(&(*bits as usize))
    }
}

// Additional Shl implementations
impl<T: MachineWord, const N: usize> core::ops::Shl<usize> for &FixedUInt<T, N> {
    type Output = FixedUInt<T, N>;
    fn shl(self, bits: usize) -> Self::Output {
        self.shl(&bits)
    }
}

impl<T: MachineWord, const N: usize> core::ops::Shl<u32> for &FixedUInt<T, N> {
    type Output = FixedUInt<T, N>;
    fn shl(self, bits: u32) -> Self::Output {
        self.shl(&(bits as usize))
    }
}

impl<T: MachineWord, const N: usize> core::ops::Shl<&u32> for FixedUInt<T, N> {
    type Output = Self;
    fn shl(self, bits: &u32) -> Self::Output {
        self.shl(*bits)
    }
}

// Additional Shr implementations
impl<T: MachineWord, const N: usize> core::ops::Shr<usize> for &FixedUInt<T, N> {
    type Output = FixedUInt<T, N>;
    fn shr(self, bits: usize) -> Self::Output {
        self.shr(&bits)
    }
}

impl<T: MachineWord, const N: usize> core::ops::Shr<u32> for &FixedUInt<T, N> {
    type Output = FixedUInt<T, N>;
    fn shr(self, bits: u32) -> Self::Output {
        self.shr(&(bits as usize))
    }
}

impl<T: MachineWord, const N: usize> core::ops::Shr<&u32> for FixedUInt<T, N> {
    type Output = Self;
    fn shr(self, bits: &u32) -> Self::Output {
        self.shr(*bits)
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
}
