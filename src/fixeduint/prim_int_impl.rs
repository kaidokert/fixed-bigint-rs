use super::{FixedUInt, MachineWord};

use num_traits::One;

impl<T: MachineWord, const N: usize> num_traits::PrimInt for FixedUInt<T, N> {
    fn count_ones(self) -> u32 {
        self.array.iter().map(|&val| val.count_ones()).sum()
    }
    fn count_zeros(self) -> u32 {
        self.array.iter().map(|&val| val.count_zeros()).sum()
    }
    fn leading_zeros(self) -> u32 {
        let mut ret = 0u32;
        for index in (0..N).rev() {
            let v = self.array[index];
            ret += v.leading_zeros();
            if !v.is_zero() {
                break;
            }
        }
        ret
    }
    fn trailing_zeros(self) -> u32 {
        let mut ret = 0u32;
        for index in 0..N {
            let v = self.array[index];
            ret += v.trailing_zeros();
            if !v.is_zero() {
                break;
            }
        }
        ret
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
        self.unsigned_shl(bits)
    }
    fn signed_shr(self, bits: u32) -> Self {
        self.unsigned_shr(bits)
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
