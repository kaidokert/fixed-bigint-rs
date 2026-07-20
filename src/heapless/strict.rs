//! `Strict*` arithmetic for `HeaplessBigInt` (the family minus `StrictPow`,
//! which lives with the other pow parallels in [`pow`](super::pow)).
//!
//! The strict ops panic on overflow in every build — a value-dependent
//! semantic incompatible with constant time, so they are `Nct`-only, matching
//! `FixedUInt`. Bodies delegate to the existing `Overflowing*` paths (add/sub/
//! mul) or the panicking `Div`/`Rem`/shift operators, turning the overflow
//! flag into a `panic!`. Result width follows the delegate (`max(operand len)`
//! for arithmetic, `self.len` for shifts).

use super::HeaplessBigInt;
use crate::MachineWord;
use const_num_traits::{
    CarryingMul, Nct, OverflowingAdd, OverflowingMul, OverflowingSub, StrictAdd, StrictDiv,
    StrictMul, StrictRem, StrictShl, StrictShr, StrictSub,
};

impl<T, const CAP: usize> StrictAdd for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
{
    type Output = Self;
    fn strict_add(self, v: Self) -> Self {
        let (res, overflow) = OverflowingAdd::overflowing_add(self, v);
        assert!(!overflow, "HeaplessBigInt: strict_add overflowed");
        res
    }
}

impl<T, const CAP: usize> StrictSub for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
{
    type Output = Self;
    fn strict_sub(self, v: Self) -> Self {
        let (res, overflow) = OverflowingSub::overflowing_sub(self, v);
        assert!(!overflow, "HeaplessBigInt: strict_sub underflowed");
        res
    }
}

impl<T, const CAP: usize> StrictMul for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type Output = Self;
    fn strict_mul(self, v: Self) -> Self {
        let (res, overflow) = OverflowingMul::overflowing_mul(self, v);
        assert!(!overflow, "HeaplessBigInt: strict_mul overflowed");
        res
    }
}

impl<T, const CAP: usize> StrictDiv for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type Output = Self;
    fn strict_div(self, v: Self) -> Self {
        // Unsigned: the only overflow mode is `v == 0`, on which `/` panics.
        self / v
    }
}

impl<T, const CAP: usize> StrictRem for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type Output = Self;
    fn strict_rem(self, v: Self) -> Self {
        self % v
    }
}

impl<T, const CAP: usize> StrictShl for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
{
    type Output = Self;
    fn strict_shl(self, rhs: u32) -> Self {
        let value_bits = self.len() as u32 * (core::mem::size_of::<T>() as u32 * 8);
        assert!(
            rhs < value_bits,
            "HeaplessBigInt: strict_shl shift exceeds the value width"
        );
        self << (rhs as usize)
    }
}

impl<T, const CAP: usize> StrictShr for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
{
    type Output = Self;
    fn strict_shr(self, rhs: u32) -> Self {
        let value_bits = self.len() as u32 * (core::mem::size_of::<T>() as u32 * 8);
        assert!(
            rhs < value_bits,
            "HeaplessBigInt: strict_shr shift exceeds the value width"
        );
        self >> (rhs as usize)
    }
}

// `&Self` reference-receiver mirrors. `HeaplessBigInt` is `Copy`, so each
// mirror derefs its receiver/operands and forwards to the value impl above.

impl<T, const CAP: usize> StrictAdd for &HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
{
    type Output = HeaplessBigInt<T, CAP, Nct>;
    fn strict_add(self, v: Self) -> Self::Output {
        <HeaplessBigInt<T, CAP, Nct> as StrictAdd>::strict_add(*self, *v)
    }
}

impl<T, const CAP: usize> StrictSub for &HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
{
    type Output = HeaplessBigInt<T, CAP, Nct>;
    fn strict_sub(self, v: Self) -> Self::Output {
        <HeaplessBigInt<T, CAP, Nct> as StrictSub>::strict_sub(*self, *v)
    }
}

impl<T, const CAP: usize> StrictMul for &HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type Output = HeaplessBigInt<T, CAP, Nct>;
    fn strict_mul(self, v: Self) -> Self::Output {
        <HeaplessBigInt<T, CAP, Nct> as StrictMul>::strict_mul(*self, *v)
    }
}

impl<T, const CAP: usize> StrictDiv for &HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type Output = HeaplessBigInt<T, CAP, Nct>;
    fn strict_div(self, v: Self) -> Self::Output {
        <HeaplessBigInt<T, CAP, Nct> as StrictDiv>::strict_div(*self, *v)
    }
}

impl<T, const CAP: usize> StrictRem for &HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type Output = HeaplessBigInt<T, CAP, Nct>;
    fn strict_rem(self, v: Self) -> Self::Output {
        <HeaplessBigInt<T, CAP, Nct> as StrictRem>::strict_rem(*self, *v)
    }
}

impl<T, const CAP: usize> StrictShl for &HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
{
    type Output = HeaplessBigInt<T, CAP, Nct>;
    fn strict_shl(self, rhs: u32) -> Self::Output {
        <HeaplessBigInt<T, CAP, Nct> as StrictShl>::strict_shl(*self, rhs)
    }
}

impl<T, const CAP: usize> StrictShr for &HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
{
    type Output = HeaplessBigInt<T, CAP, Nct>;
    fn strict_shr(self, rhs: u32) -> Self::Output {
        <HeaplessBigInt<T, CAP, Nct> as StrictShr>::strict_shr(*self, rhs)
    }
}

#[cfg(test)]
mod tests {
    use super::HeaplessBigInt;
    use const_num_traits::{StrictAdd, StrictMul, StrictShl, StrictSub};

    type H = HeaplessBigInt<u8, 4>; // 32-bit width at len 4

    #[test]
    fn strict_ok_paths() {
        let a = H::from(10u8).widened(4);
        assert_eq!(StrictAdd::strict_add(a, H::from(20u8)), H::from(30u8));
        assert_eq!(StrictSub::strict_sub(a, H::from(3u8)), H::from(7u8));
        assert_eq!(StrictMul::strict_mul(a, H::from(3u8)), H::from(30u8));
        assert_eq!(
            StrictShl::strict_shl(H::from(1u8).widened(4), 8),
            H::from(256u16)
        );
    }

    #[test]
    #[should_panic(expected = "strict_add overflowed")]
    fn strict_add_overflow_panics() {
        StrictAdd::strict_add(H::from(u32::MAX), H::from(1u8));
    }

    #[test]
    #[should_panic(expected = "strict_shl shift exceeds")]
    fn strict_shl_over_width_panics() {
        StrictShl::strict_shl(H::from(1u8).widened(4), 32);
    }

    #[test]
    fn byref_matches_value() {
        let a = H::from(10u8).widened(4);
        let b = H::from(20u8);
        assert_eq!(StrictAdd::strict_add(&a, &b), StrictAdd::strict_add(a, b));
    }
}
