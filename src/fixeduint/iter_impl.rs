use super::{FixedUInt, MachineWord};
use num_traits::{One, Zero};

impl<T: MachineWord, const N: usize> core::iter::Sum for FixedUInt<T, N> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), |acc, x| acc + x)
    }
}

impl<'a, T: MachineWord, const N: usize> core::iter::Sum<&'a Self> for FixedUInt<T, N> {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), |acc, x| acc + *x)
    }
}

impl<T: MachineWord, const N: usize> core::iter::Product for FixedUInt<T, N> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::one(), |acc, x| acc * x)
    }
}

impl<'a, T: MachineWord, const N: usize> core::iter::Product<&'a Self> for FixedUInt<T, N> {
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::one(), |acc, x| acc * *x)
    }
}
