//! `const_num_traits::AbsDiff` for `HeaplessBigInt`.
//!
//! `|a - b|` = the larger minus the smaller. The `Nct` arm branches on the
//! comparison; the `Ct` arm computes `a - b` (with its borrow) and `b - a`
//! and picks branchlessly with `ct_select`, mirroring `FixedUInt`'s Ct
//! `abs_diff`.

use super::HeaplessBigInt;
use super::cmp::ct_select;
use crate::MachineWord;
use const_num_traits::{AbsDiff, Ct, Nct, OverflowingSub, WrappingSub, Zero};

impl<T, const CAP: usize> AbsDiff for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
{
    type Output = Self;
    fn abs_diff(self, other: Self) -> Self {
        if self >= other {
            self - other
        } else {
            other - self
        }
    }
}

impl<T, const CAP: usize> AbsDiff for HeaplessBigInt<T, CAP, Ct>
where
    T: MachineWord + subtle::ConditionallySelectable,
{
    type Output = Self;
    fn abs_diff(self, other: Self) -> Self {
        // `a - b` wraps to `-(b - a)` when `a < b` (borrow set), so the branchless
        // result is `select(diff, -diff, borrow)`.
        let (diff, borrow) = OverflowingSub::overflowing_sub(self, other);
        let neg_diff = WrappingSub::wrapping_sub(Self::zero(), diff);
        ct_select(&diff, &neg_diff, borrow)
    }
}

// `&Self` mirrors so `(&h).abs_diff(&g)` resolves without an explicit copy.
impl<T, const CAP: usize> AbsDiff for &HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
{
    type Output = HeaplessBigInt<T, CAP, Nct>;
    fn abs_diff(self, other: Self) -> Self::Output {
        <HeaplessBigInt<T, CAP, Nct> as AbsDiff>::abs_diff(*self, *other)
    }
}

impl<T, const CAP: usize> AbsDiff for &HeaplessBigInt<T, CAP, Ct>
where
    T: MachineWord + subtle::ConditionallySelectable,
{
    type Output = HeaplessBigInt<T, CAP, Ct>;
    fn abs_diff(self, other: Self) -> Self::Output {
        <HeaplessBigInt<T, CAP, Ct> as AbsDiff>::abs_diff(*self, *other)
    }
}

#[cfg(test)]
mod tests {
    use super::HeaplessBigInt;
    use const_num_traits::{AbsDiff, Ct, Nct};

    type HN = HeaplessBigInt<u8, 4, Nct>;
    type HC = HeaplessBigInt<u8, 4, Ct>;

    #[test]
    fn ct_abs_diff_matches_nct_and_value() {
        for (a, b) in [(10u32, 3), (3, 10), (0, 0), (u32::MAX, 1), (1, u32::MAX)] {
            let expected = a.abs_diff(b);
            assert_eq!(
                AbsDiff::abs_diff(HC::from(a), HC::from(b)),
                HC::from(expected),
                "ct abs_diff({a}, {b})"
            );
            assert_eq!(
                AbsDiff::abs_diff(HN::from(a), HN::from(b)),
                HN::from(expected)
            );
        }
    }

    #[test]
    fn byref_matches_value() {
        let (an, bn) = (HN::from(10u8), HN::from(3u8));
        assert_eq!(AbsDiff::abs_diff(&an, &bn), AbsDiff::abs_diff(an, bn));
        let (ac, bc) = (HC::from(3u8), HC::from(10u8));
        assert_eq!(AbsDiff::abs_diff(&ac, &bc), AbsDiff::abs_diff(ac, bc));
    }
}
