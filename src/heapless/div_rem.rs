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
use const_num_traits::{CarryingMul, Nct, One, Zero};

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

    match dividend.cmp(divisor) {
        Ordering::Less => return (<HeaplessBigInt<T, CAP, Nct> as Zero>::zero(), *dividend),
        Ordering::Equal => {
            return (
                <HeaplessBigInt<T, CAP, Nct> as One>::one(),
                <HeaplessBigInt<T, CAP, Nct> as Zero>::zero(),
            );
        }
        Ordering::Greater => {}
    }

    let d_bits = dividend.bit_length();
    let dv_bits = divisor.bit_length();
    let mut shift = d_bits - dv_bits;

    // Work at a fixed width wide enough for every shifted value. `Shl` is
    // width-preserving, so the divisor and the quotient-bit unit must be
    // carried at this width for the up-shifts to have room. `shift <=
    // d_bits - dv_bits`, so `divisor << shift <= dividend`, which fits in
    // `dividend`'s words — `work_len` never needs to exceed the operands.
    let work_len = core::cmp::max(dividend.len(), divisor.len());
    let mut rem = dividend.widened(work_len);
    let wide_divisor = divisor.widened(work_len);
    let one = <HeaplessBigInt<T, CAP, Nct> as One>::one().widened(work_len);
    let mut quotient = <HeaplessBigInt<T, CAP, Nct> as Zero>::zero();

    loop {
        let shifted = wide_divisor << shift;
        if rem >= shifted {
            rem = rem.wrapping_sub(&shifted);
            let bit = one << shift;
            quotient = quotient.wrapping_add(&bit);
        }
        if shift == 0 {
            break;
        }
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

// ── DivAssign / RemAssign ──
//
// modmath's constrained flavor uses `%=`; `DivAssign` is added for
// symmetry. Both delegate to the same long-division kernel.

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
