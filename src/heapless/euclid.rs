//! `const_num_traits::Euclid` / `CheckedEuclid` for `HeaplessBigInt<_, Nct>`.
//!
//! Unsigned: Euclidean div/rem are ordinary div/rem. Nct-only, like the
//! division they build on; `checked_*` return `None` on a zero divisor.

use super::HeaplessBigInt;
use crate::MachineWord;
use const_num_traits::{CarryingMul, CheckedEuclid, Euclid, Nct, Zero};

impl<T, const CAP: usize> Euclid for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type Output = Self;
    fn div_euclid(self, v: Self) -> Self {
        self / v
    }
    fn rem_euclid(self, v: Self) -> Self {
        self % v
    }
    fn div_rem_euclid(self, v: Self) -> (Self, Self) {
        self.div_rem(&v)
    }
}

impl<T, const CAP: usize> CheckedEuclid for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    fn checked_div_euclid(self, v: Self) -> Option<Self> {
        if <Self as Zero>::is_zero(&v) {
            None
        } else {
            Some(self / v)
        }
    }
    fn checked_rem_euclid(self, v: Self) -> Option<Self> {
        if <Self as Zero>::is_zero(&v) {
            None
        } else {
            Some(self % v)
        }
    }
    fn checked_div_rem_euclid(self, v: Self) -> Option<(Self, Self)> {
        if <Self as Zero>::is_zero(&v) {
            None
        } else {
            Some(self.div_rem(&v))
        }
    }
}
