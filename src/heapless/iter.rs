//! `core::iter::Sum` / `Product` for `HeaplessBigInt`.
//!
//! Fold with `+` / `*` from the identity seed. The seed (`zero()` / `one()`)
//! is minimal-width, so an **empty** iterator yields a minimal-width result;
//! a non-empty one settles at `max(operand len)` because each `+`/`*` resolves
//! there. To fix the accumulator width regardless of the operands, pin the
//! seed with `WithPrecision` and fold manually rather than using these.

use super::HeaplessBigInt;
use crate::MachineWord;
use const_num_traits::{CarryingMul, One, Personality, Zero};

impl<T, const CAP: usize, P: Personality> core::iter::Sum for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord,
{
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(<Self as Zero>::zero(), |acc, x| acc + x)
    }
}

impl<'a, T, const CAP: usize, P: Personality> core::iter::Sum<&'a Self>
    for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord,
{
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(<Self as Zero>::zero(), |acc, x| acc + *x)
    }
}

impl<T, const CAP: usize, P: Personality> core::iter::Product for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(<Self as One>::one(), |acc, x| acc * x)
    }
}

impl<'a, T, const CAP: usize, P: Personality> core::iter::Product<&'a Self>
    for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(<Self as One>::one(), |acc, x| acc * *x)
    }
}

#[cfg(test)]
mod tests {
    use super::HeaplessBigInt;

    type H = HeaplessBigInt<u8, 8>;

    #[test]
    fn sum_product() {
        let vals = [H::from(1u8), H::from(2u8), H::from(3u8), H::from(4u8)];
        assert_eq!(vals.iter().copied().sum::<H>(), H::from(10u8));
        assert_eq!(vals.iter().sum::<H>(), H::from(10u8));
        assert_eq!(vals.iter().copied().product::<H>(), H::from(24u8));
        assert_eq!(vals.iter().product::<H>(), H::from(24u8));
    }

    #[test]
    fn empty_iter_is_identity() {
        let empty: [H; 0] = [];
        assert_eq!(empty.iter().copied().sum::<H>(), H::from(0u8));
        assert_eq!(empty.iter().copied().product::<H>(), H::from(1u8));
    }
}
