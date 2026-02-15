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
            let bit_size = Self::BIT_SIZE as u32;
            if bit_size == 0 {
                return self;
            }
            let shift = n % bit_size;
            let a = core::ops::Shl::<u32>::shl(self, shift);
            let b = core::ops::Shr::<u32>::shr(self, bit_size - shift);
            core::ops::BitOr::bitor(a, b)
        }
        fn rotate_right(self, n: u32) -> Self {
            let bit_size = Self::BIT_SIZE as u32;
            if bit_size == 0 {
                return self;
            }
            let shift = n % bit_size;
            let a = core::ops::Shr::<u32>::shr(self, shift);
            let b = core::ops::Shl::<u32>::shl(self, bit_size - shift);
            core::ops::BitOr::bitor(a, b)
        }
        fn unsigned_shl(self, n: u32) -> Self {
            core::ops::Shl::<u32>::shl(self, n)
        }
        fn unsigned_shr(self, n: u32) -> Self {
            core::ops::Shr::<u32>::shr(self, n)
        }
        fn reverse_bits(self) -> Self {
            let mut ret = <Self as crate::const_numtrait::ConstZero>::zero();
            let mut i = 0;
            while i < N {
                ret.array[N - 1 - i] = self.array[i].reverse_bits();
                i += 1;
            }
            ret
        }
        fn from_be(x: Self) -> Self {
            let mut ret = <Self as crate::const_numtrait::ConstZero>::zero();
            let mut i = 0;
            while i < N {
                ret.array[i] = x.array[N - 1 - i].swap_bytes();
                i += 1;
            }
            ret
        }
        fn from_le(x: Self) -> Self {
            x
        }
        fn to_be(self) -> Self {
            let mut ret = <Self as crate::const_numtrait::ConstZero>::zero();
            let mut i = 0;
            while i < N {
                ret.array[i] = self.array[N - 1 - i].swap_bytes();
                i += 1;
            }
            ret
        }
        fn to_le(self) -> Self {
            self
        }
        fn pow(self, exp: u32) -> Self {
            if exp == 0 {
                return <Self as crate::const_numtrait::ConstOne>::one();
            }
            let mut ret = self;
            let mut i = 1u32;
            while i < exp {
                ret = core::ops::Mul::mul(ret, self);
                i += 1;
            }
            ret
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
        let bit_size = Self::BIT_SIZE as u32;
        if bit_size == 0 {
            return self;
        }
        let shift = bits % bit_size;
        let a = self << shift;
        let b = self >> (bit_size - shift);
        a | b
    }
    fn rotate_right(self, bits: u32) -> Self {
        let bit_size = Self::BIT_SIZE as u32;
        if bit_size == 0 {
            return self;
        }
        let shift = bits % bit_size;
        let a = self >> shift;
        let b = self << (bit_size - shift);
        a | b
    }
    fn signed_shl(self, bits: u32) -> Self {
        <Self as num_traits::PrimInt>::unsigned_shl(self, bits)
    }
    fn signed_shr(self, bits: u32) -> Self {
        <Self as num_traits::PrimInt>::unsigned_shr(self, bits)
    }
    fn unsigned_shl(self, bits: u32) -> Self {
        self << bits
    }
    fn unsigned_shr(self, bits: u32) -> Self {
        self >> bits
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
