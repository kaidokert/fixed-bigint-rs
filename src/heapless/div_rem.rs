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
use const_num_traits::{CarryingMul, CheckedAdd, CheckedDiv, CheckedRem, DivCeil, Nct, One, Zero};

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
        shifted >>= 1usize;
        bit >>= 1usize;
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
    /// Quotient and remainder in one pass. Panics on divide-by-zero, like the
    /// `Div`/`Rem` operators; use `checked_div`/`checked_rem` to avoid the panic.
    pub fn div_rem(&self, other: &Self) -> (Self, Self) {
        div_rem_impl(self, other)
    }

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

    /// Ceiling division. `None` on divide-by-zero or when rounding up
    /// overflows the value width. Result width is `max(self.len, other.len)`.
    pub fn checked_div_ceil(&self, other: &Self) -> Option<Self> {
        if <Self as Zero>::is_zero(other) {
            return None;
        }
        let (q, r) = div_rem_impl(self, other);
        if <Self as Zero>::is_zero(&r) {
            Some(q)
        } else {
            CheckedAdd::checked_add(q, <Self as One>::one())
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

impl<T, const CAP: usize> DivCeil for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type Output = Self;
    fn div_ceil(self, rhs: Self) -> Self {
        match Self::checked_div_ceil(&self, &rhs) {
            Some(v) => v,
            None => panic!("HeaplessBigInt::div_ceil: division by zero or overflow"),
        }
    }
}

// Reference-receiver mirrors: `(&h).checked_div(&g)` binds the same generic
// trait bound as the value form. `HeaplessBigInt: Copy`, so the deref-and-
// forward is a no-op at runtime. Nct-only, matching the value forms.

impl<T, const CAP: usize> CheckedDiv for &HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type Output = HeaplessBigInt<T, CAP, Nct>;
    fn checked_div(self, v: Self) -> Option<Self::Output> {
        <HeaplessBigInt<T, CAP, Nct> as CheckedDiv>::checked_div(*self, *v)
    }
}

impl<T, const CAP: usize> CheckedRem for &HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type Output = HeaplessBigInt<T, CAP, Nct>;
    fn checked_rem(self, v: Self) -> Option<Self::Output> {
        <HeaplessBigInt<T, CAP, Nct> as CheckedRem>::checked_rem(*self, *v)
    }
}

impl<T, const CAP: usize> DivCeil for &HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type Output = HeaplessBigInt<T, CAP, Nct>;
    fn div_ceil(self, rhs: Self) -> Self::Output {
        <HeaplessBigInt<T, CAP, Nct> as DivCeil>::div_ceil(*self, *rhs)
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

#[cfg(test)]
mod div_ceil_tests {
    use super::HeaplessBigInt;
    use const_num_traits::{CheckedDiv, CheckedRem, DivCeil};

    type H = HeaplessBigInt<u8, 4>;

    #[test]
    fn div_ceil_rounds_up() {
        assert_eq!(DivCeil::div_ceil(H::from(10u8), H::from(5u8)), H::from(2u8));
        assert_eq!(DivCeil::div_ceil(H::from(11u8), H::from(3u8)), H::from(4u8));
        assert_eq!(DivCeil::div_ceil(H::from(1u8), H::from(5u8)), H::from(1u8));
        assert_eq!(DivCeil::div_ceil(H::from(0u8), H::from(5u8)), H::from(0u8));
    }

    #[test]
    fn checked_div_ceil_edges() {
        // Divide-by-zero and rounding overflow both yield None.
        assert_eq!(H::from(10u8).checked_div_ceil(&H::from(0u8)), None);
        // MAX / 2 rounds to 2^31, still fits the 32-bit width.
        assert_eq!(
            H::from(u32::MAX).checked_div_ceil(&H::from(2u8)),
            Some(H::from(0x8000_0000u32))
        );
    }

    // Reference-receiver trait forms resolve to the same value as the by-value
    // forms for the const_num_traits div/rem/ceil family.
    #[test]
    fn by_ref_matches_value() {
        let a = H::from(100u8);
        let b = H::from(7u8);
        assert_eq!(
            CheckedDiv::checked_div(&a, &b),
            CheckedDiv::checked_div(a, b)
        );
        assert_eq!(
            CheckedRem::checked_rem(&a, &b),
            CheckedRem::checked_rem(a, b)
        );
        assert_eq!(DivCeil::div_ceil(&a, &b), DivCeil::div_ceil(a, b));
    }
}
