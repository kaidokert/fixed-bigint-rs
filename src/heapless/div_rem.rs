//! `core::ops::Div` / `Rem` for `HeaplessBigInt<T, CAP, Nct>`.
//!
//! Nct-only. Division is data-dependent (early-exits on shift, on
//! `rem >= shifted`) — the personality rule mirrors `FixedUInt`, where
//! `Div`/`Rem` are `Nct` only. Ct callers that need `x mod modulus` use
//! Montgomery reduction via the CIOS driver, not this path.
//!
//! Algorithm is shift-and-subtract long division: shift the divisor to
//! the highest bit position where it might fit into the remaining
//! dividend, subtract when it does, set the corresponding quotient bit.
//! Uses only ops HeaplessBigInt already exposes (`Shl<usize>`,
//! `wrapping_sub`, `wrapping_add`, `cmp`, `bit_length`) — no direct
//! limb access, no new bit-poke helpers.

use super::HeaplessBigInt;
use crate::MachineWord;
use const_num_traits::{CarryingMul, CheckedDiv, CheckedRem, Nct, One, Zero};

fn div_rem_impl<T, const CAP: usize>(
    dividend: &HeaplessBigInt<T, CAP, Nct>,
    divisor: &HeaplessBigInt<T, CAP, Nct>,
) -> (HeaplessBigInt<T, CAP, Nct>, HeaplessBigInt<T, CAP, Nct>)
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    use core::cmp::Ordering;
    assert!(
        !<HeaplessBigInt<T, CAP, Nct> as Zero>::is_zero(divisor),
        "HeaplessBigInt: divide by zero"
    );

    // Both outputs are carried at the operands' width `max(len)`, the same
    // as the general path below — the early returns must widen too, or
    // `x / x` would come back at `len == 1` and later width-preserving ops
    // would run narrower than the operands.
    let work_len = core::cmp::max(dividend.len(), divisor.len());

    match dividend.cmp(divisor) {
        Ordering::Less => {
            return (
                <HeaplessBigInt<T, CAP, Nct> as Zero>::zero().widened(work_len),
                dividend.widened(work_len),
            );
        }
        Ordering::Equal => {
            return (
                <HeaplessBigInt<T, CAP, Nct> as One>::one().widened(work_len),
                <HeaplessBigInt<T, CAP, Nct> as Zero>::zero().widened(work_len),
            );
        }
        Ordering::Greater => {}
    }

    let d_bits = dividend.bit_length();
    let dv_bits = divisor.bit_length();
    let mut shift = d_bits - dv_bits;

    // `Shl` is width-preserving, so the divisor and the quotient-bit unit
    // must be carried at `work_len` for the up-shifts to have room. `shift
    // <= d_bits - dv_bits`, so `divisor << shift <= dividend`, which fits
    // in `dividend`'s words — `work_len` never needs to exceed the operands.
    let mut rem = dividend.widened(work_len);
    let wide_divisor = divisor.widened(work_len);
    let one = <HeaplessBigInt<T, CAP, Nct> as One>::one().widened(work_len);
    let mut quotient = <HeaplessBigInt<T, CAP, Nct> as Zero>::zero().widened(work_len);

    // Compute the top shift once, then walk down one bit per iteration. A
    // fresh `wide_divisor << shift` each step would be an O(W·shift) shift;
    // `>> 1` is O(W). `divisor << shift <= dividend` fits in `work_len`, so
    // no significant bit is lost on the initial shift and `>> 1` faithfully
    // reconstructs `<< (shift-k)`.
    let mut shifted = wide_divisor << shift;
    let mut bit = one << shift;
    loop {
        if rem >= shifted {
            rem = rem.wrapping_sub(&shifted);
            quotient = quotient.wrapping_add(&bit);
        }
        if shift == 0 {
            break;
        }
        shifted >>= 1;
        bit >>= 1;
        shift -= 1;
    }

    (quotient, rem)
}

macro_rules! div_impls {
    ($lhs:ty, $rhs:ty, $out:ty) => {
        impl<T, const CAP: usize> core::ops::Div<$rhs> for $lhs
        where
            T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
        {
            type Output = $out;
            fn div(self, other: $rhs) -> Self::Output {
                div_rem_impl::<T, CAP>(&self, &other).0
            }
        }

        impl<T, const CAP: usize> core::ops::Rem<$rhs> for $lhs
        where
            T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
        {
            type Output = $out;
            fn rem(self, other: $rhs) -> Self::Output {
                div_rem_impl::<T, CAP>(&self, &other).1
            }
        }
    };
}

div_impls!(
    HeaplessBigInt<T, CAP, Nct>,
    HeaplessBigInt<T, CAP, Nct>,
    HeaplessBigInt<T, CAP, Nct>
);
div_impls!(
    HeaplessBigInt<T, CAP, Nct>,
    &HeaplessBigInt<T, CAP, Nct>,
    HeaplessBigInt<T, CAP, Nct>
);
div_impls!(
    &HeaplessBigInt<T, CAP, Nct>,
    HeaplessBigInt<T, CAP, Nct>,
    HeaplessBigInt<T, CAP, Nct>
);
div_impls!(
    &HeaplessBigInt<T, CAP, Nct>,
    &HeaplessBigInt<T, CAP, Nct>,
    HeaplessBigInt<T, CAP, Nct>
);

// ── Checked division / remainder ──
//
// Nct-only, like `Div`/`Rem`. Return `None` on divide-by-zero instead of the
// `div_rem_impl` assert; the quotient/remainder is the value-width result the
// same-width `FixedUInt` gives.

impl<T, const CAP: usize> HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    /// Checked division. `None` on divide-by-zero.
    pub fn checked_div(&self, other: &Self) -> Option<Self> {
        if <Self as Zero>::is_zero(other) {
            None
        } else {
            Some(div_rem_impl(self, other).0)
        }
    }

    /// Checked remainder. `None` on divide-by-zero.
    pub fn checked_rem(&self, other: &Self) -> Option<Self> {
        if <Self as Zero>::is_zero(other) {
            None
        } else {
            Some(div_rem_impl(self, other).1)
        }
    }
}

// Value-form trait bridges to the by-reference inherent methods (free,
// `HeaplessBigInt: Copy`). Nct-only, matching Div/Rem.

impl<T, const CAP: usize> CheckedDiv for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type Output = Self;
    fn checked_div(self, v: Self) -> Option<Self> {
        Self::checked_div(&self, &v)
    }
}

impl<T, const CAP: usize> CheckedRem for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type Output = Self;
    fn checked_rem(self, v: Self) -> Option<Self> {
        Self::checked_rem(&self, &v)
    }
}

#[cfg(feature = "num-traits")]
impl<T, const CAP: usize> num_traits::CheckedDiv for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    fn checked_div(&self, v: &Self) -> Option<Self> {
        Self::checked_div(self, v)
    }
}

#[cfg(feature = "num-traits")]
impl<T, const CAP: usize> num_traits::CheckedRem for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    fn checked_rem(&self, v: &Self) -> Option<Self> {
        Self::checked_rem(self, v)
    }
}

// ── DivAssign / RemAssign ──
//
// `RemAssign` is the used form; `DivAssign` is added for symmetry. Both
// delegate to the same long-division kernel.

impl<T, const CAP: usize> core::ops::DivAssign for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    fn div_assign(&mut self, other: Self) {
        *self = div_rem_impl::<T, CAP>(self, &other).0;
    }
}

impl<T, const CAP: usize> core::ops::DivAssign<&HeaplessBigInt<T, CAP, Nct>>
    for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    fn div_assign(&mut self, other: &Self) {
        *self = div_rem_impl::<T, CAP>(self, other).0;
    }
}

impl<T, const CAP: usize> core::ops::RemAssign for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    fn rem_assign(&mut self, other: Self) {
        *self = div_rem_impl::<T, CAP>(self, &other).1;
    }
}

impl<T, const CAP: usize> core::ops::RemAssign<&HeaplessBigInt<T, CAP, Nct>>
    for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    fn rem_assign(&mut self, other: &Self) {
        *self = div_rem_impl::<T, CAP>(self, other).1;
    }
}
