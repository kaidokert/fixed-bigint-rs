//! `const_num_traits::AbsDiff` for `HeaplessBigInt`.
//!
//! `|a - b|` = the larger minus the smaller. The `Nct` arm branches on the
//! comparison; the `Ct` arm computes `a - b` (with its borrow) and `b - a`
//! and picks branchlessly with `ct_select`, mirroring `FixedUInt`'s Ct
//! `abs_diff`.

use super::HeaplessBigInt;
use super::cmp::ct_select;
use crate::MachineWord;
use const_num_traits::{AbsDiff, Ct, Nct, WrappingSub, Zero};

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
        let (diff, borrow) =
            <Self as const_num_traits::OverflowingSub>::overflowing_sub(self, other);
        let neg_diff = <Self as WrappingSub>::wrapping_sub(<Self as Zero>::zero(), diff);
        ct_select(&diff, &neg_diff, borrow)
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
}
