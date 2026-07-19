//! `const_num_traits::MultipleOf` / `NextMultipleOf` for `HeaplessBigInt<_, Nct>`.
//!
//! Division-based, so Nct-only. `MultipleOf::is_multiple_of` returns `false`
//! for a zero divisor (the const-num-traits convention — distinct from
//! `num_integer::Integer::is_multiple_of`, which returns `self.is_zero()`).

use super::HeaplessBigInt;
use crate::MachineWord;
use const_num_traits::{CarryingMul, CheckedAdd, MultipleOf, Nct, NextMultipleOf, Zero};

impl<T, const CAP: usize> MultipleOf for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    fn is_multiple_of(self, rhs: Self) -> bool {
        if <Self as Zero>::is_zero(&rhs) {
            false
        } else {
            <Self as Zero>::is_zero(&(self % rhs))
        }
    }
}

impl<T, const CAP: usize> NextMultipleOf for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type Output = Self;

    fn next_multiple_of(self, rhs: Self) -> Self {
        match self.checked_next_multiple_of(rhs) {
            Some(v) => v,
            None => panic!("HeaplessBigInt::next_multiple_of: rhs is zero or the result overflows"),
        }
    }

    fn checked_next_multiple_of(self, rhs: Self) -> Option<Self> {
        if <Self as Zero>::is_zero(&rhs) {
            return None;
        }
        let rem = self % rhs;
        if <Self as Zero>::is_zero(&rem) {
            Some(self)
        } else {
            // self + (rhs - rem), None on overflow.
            CheckedAdd::checked_add(self, rhs - rem)
        }
    }
}
