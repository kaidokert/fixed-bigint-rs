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
            // Already a multiple, but the result width is max(self.len, rhs.len)
            // (the non-zero path resolves there via `%`/`+`); widen so this
            // early return doesn't narrow below the contract.
            Some(self.widened(core::cmp::max(self.len(), rhs.len())))
        } else {
            // self + (rhs - rem), None on overflow.
            CheckedAdd::checked_add(self, rhs - rem)
        }
    }
}

// `&Self` mirrors so `(&h).is_multiple_of(&g)` resolves without an explicit copy.
impl<T, const CAP: usize> MultipleOf for &HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    fn is_multiple_of(self, rhs: Self) -> bool {
        <HeaplessBigInt<T, CAP, Nct> as MultipleOf>::is_multiple_of(*self, *rhs)
    }
}

impl<T, const CAP: usize> NextMultipleOf for &HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type Output = HeaplessBigInt<T, CAP, Nct>;

    fn next_multiple_of(self, rhs: Self) -> Self::Output {
        <HeaplessBigInt<T, CAP, Nct> as NextMultipleOf>::next_multiple_of(*self, *rhs)
    }

    fn checked_next_multiple_of(self, rhs: Self) -> Option<Self::Output> {
        <HeaplessBigInt<T, CAP, Nct> as NextMultipleOf>::checked_next_multiple_of(*self, *rhs)
    }
}

#[cfg(test)]
mod tests {
    use super::HeaplessBigInt;
    use const_num_traits::NextMultipleOf;

    type H = HeaplessBigInt<u8, 8>;

    // The already-a-multiple early return must carry max(self.len, rhs.len),
    // not the narrow self width. The value-based shared harness can't see this
    // (its operands are all one width), so pin it here.
    #[test]
    fn already_multiple_preserves_wider_rhs_width() {
        let self_narrow = H::from(10u8); // len 1
        let rhs_wide = H::from(5u8).widened(8); // len 8
        assert_eq!(self_narrow.len(), 1);
        let out = NextMultipleOf::checked_next_multiple_of(self_narrow, rhs_wide).unwrap();
        assert_eq!(out, H::from(10u8));
        assert_eq!(out.len(), 8, "result must widen to max(self.len, rhs.len)");
    }

    #[test]
    fn rhs_larger_than_self_is_rhs() {
        // 3's next multiple of 10 is 10 itself (the `self + (rhs - rem)` path).
        let out = NextMultipleOf::next_multiple_of(H::from(3u8), H::from(10u8));
        assert_eq!(out, H::from(10u8));
    }

    #[test]
    fn byref_matches_value() {
        use const_num_traits::MultipleOf;
        let a = H::from(12u8);
        let b = H::from(5u8);
        assert_eq!(
            MultipleOf::is_multiple_of(&a, &b),
            MultipleOf::is_multiple_of(a, b)
        );
        assert_eq!(
            NextMultipleOf::next_multiple_of(&a, &b),
            NextMultipleOf::next_multiple_of(a, b)
        );
        assert_eq!(
            NextMultipleOf::checked_next_multiple_of(&a, &b),
            NextMultipleOf::checked_next_multiple_of(a, b)
        );
    }
}
