use super::{const_leading_zeros, const_trailing_zeros, FixedUInt, MachineWord};
use crate::const_numtrait::ConstPrimInt;
use crate::machineword::ConstMachineWord;

use num_traits::One;

c0nst::c0nst! {
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstPrimInt for FixedUInt<T, N> {
        fn count_ones(self) -> u32 {
            let mut count = 0u32;
            let mut i = 0;
            while i < N {
                count += self.array[i].count_ones();
                i += 1;
            }
            count
        }
        fn count_zeros(self) -> u32 {
            let mut count = 0u32;
            let mut i = 0;
            while i < N {
                count += self.array[i].count_zeros();
                i += 1;
            }
            count
        }
        fn leading_zeros(self) -> u32 {
            const_leading_zeros(&self.array)
        }
        fn trailing_zeros(self) -> u32 {
            const_trailing_zeros(&self.array)
        }
        fn swap_bytes(self) -> Self {
            let mut ret = <Self as crate::const_numtrait::ConstZero>::zero();
            let mut i = 0;
            while i < N {
                ret.array[i] = self.array[N - 1 - i].swap_bytes();
                i += 1;
            }
            ret
        }
        fn rotate_left(self, n: u32) -> Self {
            let shift = n % (Self::BIT_SIZE as u32);
            let a = core::ops::Shl::<u32>::shl(self, shift);
            let b = core::ops::Shr::<u32>::shr(self, Self::BIT_SIZE as u32 - shift);
            core::ops::BitOr::bitor(a, b)
        }
        fn rotate_right(self, n: u32) -> Self {
            let shift = n % (Self::BIT_SIZE as u32);
            let a = core::ops::Shr::<u32>::shr(self, shift);
            let b = core::ops::Shl::<u32>::shl(self, Self::BIT_SIZE as u32 - shift);
            core::ops::BitOr::bitor(a, b)
        }
        fn unsigned_shl(self, n: u32) -> Self {
            core::ops::Shl::<u32>::shl(self, n)
        }
        fn unsigned_shr(self, n: u32) -> Self {
            core::ops::Shr::<u32>::shr(self, n)
        }
    }
}

impl<T: MachineWord, const N: usize> num_traits::PrimInt for FixedUInt<T, N> {
    fn count_ones(self) -> u32 {
        self.array.iter().map(|&val| val.count_ones()).sum()
    }
    fn count_zeros(self) -> u32 {
        self.array.iter().map(|&val| val.count_zeros()).sum()
    }
    fn leading_zeros(self) -> u32 {
        const_leading_zeros(&self.array)
    }
    fn trailing_zeros(self) -> u32 {
        const_trailing_zeros(&self.array)
    }
    fn rotate_left(self, bits: u32) -> Self {
        let shift = Self::normalize_shift(bits);
        let a = self << shift;
        let b = self >> (Self::BIT_SIZE as u32 - shift);
        a | b
    }
    fn rotate_right(self, bits: u32) -> Self {
        let shift = Self::normalize_shift(bits);
        let a = self >> shift;
        let b = self << (Self::BIT_SIZE as u32 - shift);
        a | b
    }
    fn signed_shl(self, bits: u32) -> Self {
        core::ops::Shl::<u32>::shl(self, bits)
    }
    fn signed_shr(self, bits: u32) -> Self {
        core::ops::Shr::<u32>::shr(self, bits)
    }
    fn unsigned_shl(self, bits: u32) -> Self {
        core::ops::Shl::<u32>::shl(self, bits)
    }
    fn unsigned_shr(self, bits: u32) -> Self {
        core::ops::Shr::<u32>::shr(self, bits)
    }
    fn swap_bytes(self) -> Self {
        let mut ret = Self::new();
        for index in 0..N {
            ret.array[index] = self.array[N - 1 - index].swap_bytes();
        }

        ret
    }
    fn from_be(source: Self) -> Self {
        let mut ret = Self::new();
        for index in 0..N {
            ret.array[index] = source.array[N - 1 - index].swap_bytes();
        }

        ret
    }
    fn from_le(source: Self) -> Self {
        let mut ret = Self::new();
        for index in 0..N {
            ret.array[index] = source.array[index];
        }

        ret
    }
    fn to_be(self) -> Self {
        let mut ret = Self::new();
        for index in 0..N {
            ret.array[index] = self.array[N - 1 - index].swap_bytes();
        }

        ret
    }
    fn to_le(self) -> Self {
        let mut ret = Self::new();
        for index in 0..N {
            ret.array[index] = self.array[index];
        }

        ret
    }
    fn pow(self, n: u32) -> Self {
        if n == 0 {
            Self::one()
        } else {
            let mut ret = self;
            for _ in 1..n {
                ret *= self;
            }
            ret
        }
    }
}
