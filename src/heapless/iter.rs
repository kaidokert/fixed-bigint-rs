//! `core::iter::Sum` / `Product` for `HeaplessBigInt`.
//!
//! A non-empty iterator settles at `max(operand len)`; an **empty** one yields
//! the minimal-width identity. `Sum` folds from `zero()` (already len 0, so it
//! never widens the result). `Product` can't fold from `one()` — the
//! multiplicative identity is len 1, which would inject that width into a
//! product of narrower operands — so it seeds from the first element instead,
//! falling back to `one()` only when empty. To fix the accumulator width
//! regardless of the operands, pin the seed with `WithPrecision` and fold
//! manually rather than using these.

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
    fn product<I: Iterator<Item = Self>>(mut iter: I) -> Self {
        match iter.next() {
            None => <Self as One>::one(),
            Some(first) => iter.fold(first, |acc, x| acc * x),
        }
    }
}

impl<'a, T, const CAP: usize, P: Personality> core::iter::Product<&'a Self>
    for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    fn product<I: Iterator<Item = &'a Self>>(mut iter: I) -> Self {
        match iter.next() {
            None => <Self as One>::one(),
            Some(first) => iter.fold(*first, |acc, x| acc * *x),
        }
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

    // A non-empty product carries max(operand len), not the len-1 identity:
    // seeding from the first element avoids injecting one()'s width.
    #[test]
    fn product_preserves_operand_width_not_identity() {
        // Single len-0 (empty-shape zero) operand: result stays len 0.
        let zeros = [H::new_zero_with_len(0)];
        let p = zeros.iter().copied().product::<H>();
        assert!(<H as const_num_traits::Zero>::is_zero(&p));
        assert_eq!(p.len(), 0);

        // Non-empty product settles at the widest operand.
        let mixed = [H::from(2u8), H::from(3u8).widened(8)];
        assert_eq!(mixed.iter().copied().product::<H>().len(), 8);
    }
}
