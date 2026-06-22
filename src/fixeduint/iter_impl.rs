use super::{FixedUInt, MachineWord};
use crate::const_numtraits::{One, Zero};
use const_num_traits::Personality;

impl<T: MachineWord, const N: usize, P: Personality> core::iter::Sum for FixedUInt<T, N, P> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), |acc, x| acc + x)
    }
}

impl<'a, T: MachineWord, const N: usize, P: Personality> core::iter::Sum<&'a Self>
    for FixedUInt<T, N, P>
{
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), |acc, x| acc + *x)
    }
}

impl<T: MachineWord, const N: usize, P: Personality> core::iter::Product for FixedUInt<T, N, P> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::one(), |acc, x| acc * x)
    }
}

impl<'a, T: MachineWord, const N: usize, P: Personality> core::iter::Product<&'a Self>
    for FixedUInt<T, N, P>
{
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::one(), |acc, x| acc * *x)
    }
}
