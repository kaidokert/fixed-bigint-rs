//! `BitAnd` / `BitOr` / `BitXor` for `HeaplessBigInt` (all four receiver
//! forms each), plus the compound-assign forms.
//!
//! Limb-wise, width-based, `CAP` never enters:
//! - `BitAnd` → `len = min(a.len, b.len)`: at or above that bound one
//!   operand is in its zero-tail, so the AND is zero — `min` is
//!   value-tight and satisfies the zero-tail invariant.
//! - `BitOr` / `BitXor` → `len = max(a.len, b.len)`: they leave a bit set
//!   wherever exactly one operand has it, so the result spans the wider
//!   operand; the shorter operand's zero-tail leaves the wider operand's
//!   limbs unchanged there.
//!
//! Both lens are public shape parameters, so the body is identical for
//! Nct and Ct. The compound-assign forms delegate to the binary op.

use super::{HeaplessBigInt, zero};
use crate::MachineWord;
use const_num_traits::Personality;
use core::marker::PhantomData;
use core::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign};

// The value/mixed receiver forms of each bitwise op are uniform pure
// delegation to the hand-written `&Self $op &Self` core.
macro_rules! forward_bitwise_receivers {
    ($imp:ident, $method:ident) => {
        impl<T: MachineWord, const CAP: usize, P: Personality> $imp for HeaplessBigInt<T, CAP, P> {
            type Output = Self;
            fn $method(self, other: Self) -> Self {
                (&self).$method(&other)
            }
        }
        impl<T: MachineWord, const CAP: usize, P: Personality> $imp<&HeaplessBigInt<T, CAP, P>>
            for HeaplessBigInt<T, CAP, P>
        {
            type Output = Self;
            fn $method(self, other: &Self) -> Self {
                (&self).$method(other)
            }
        }
        impl<T: MachineWord, const CAP: usize, P: Personality> $imp<HeaplessBigInt<T, CAP, P>>
            for &HeaplessBigInt<T, CAP, P>
        {
            type Output = HeaplessBigInt<T, CAP, P>;
            fn $method(self, other: HeaplessBigInt<T, CAP, P>) -> HeaplessBigInt<T, CAP, P> {
                self.$method(&other)
            }
        }
    };
}

// Core: `&Self & &Self`. The value + mixed receiver forms delegate here.
impl<T: MachineWord, const CAP: usize, P: Personality> BitAnd<&HeaplessBigInt<T, CAP, P>>
    for &HeaplessBigInt<T, CAP, P>
{
    type Output = HeaplessBigInt<T, CAP, P>;
    fn bitand(self, other: &HeaplessBigInt<T, CAP, P>) -> Self::Output {
        let out_len = core::cmp::min(self.len, other.len);
        let n = out_len as usize;
        let mut limbs = [zero::<T>(); CAP];
        for ((&ai, &bi), oi) in self.limbs[..n]
            .iter()
            .zip(&other.limbs[..n])
            .zip(&mut limbs[..n])
        {
            *oi = ai & bi;
        }
        HeaplessBigInt {
            limbs,
            len: out_len,
            _p: PhantomData,
        }
    }
}

forward_bitwise_receivers!(BitAnd, bitand);

// Core: `&Self | &Self`. The value + mixed receiver forms delegate here.
impl<T: MachineWord, const CAP: usize, P: Personality> BitOr<&HeaplessBigInt<T, CAP, P>>
    for &HeaplessBigInt<T, CAP, P>
{
    type Output = HeaplessBigInt<T, CAP, P>;
    fn bitor(self, other: &HeaplessBigInt<T, CAP, P>) -> Self::Output {
        let out_len = core::cmp::max(self.len, other.len);
        let n = out_len as usize;
        let mut limbs = [zero::<T>(); CAP];
        for ((&ai, &bi), oi) in self.limbs[..n]
            .iter()
            .zip(&other.limbs[..n])
            .zip(&mut limbs[..n])
        {
            *oi = ai | bi;
        }
        HeaplessBigInt {
            limbs,
            len: out_len,
            _p: PhantomData,
        }
    }
}

forward_bitwise_receivers!(BitOr, bitor);

// Core: `&Self ^ &Self`. The value + mixed receiver forms delegate here.
impl<T: MachineWord, const CAP: usize, P: Personality> BitXor<&HeaplessBigInt<T, CAP, P>>
    for &HeaplessBigInt<T, CAP, P>
{
    type Output = HeaplessBigInt<T, CAP, P>;
    fn bitxor(self, other: &HeaplessBigInt<T, CAP, P>) -> Self::Output {
        let out_len = core::cmp::max(self.len, other.len);
        let n = out_len as usize;
        let mut limbs = [zero::<T>(); CAP];
        for ((&ai, &bi), oi) in self.limbs[..n]
            .iter()
            .zip(&other.limbs[..n])
            .zip(&mut limbs[..n])
        {
            *oi = ai ^ bi;
        }
        HeaplessBigInt {
            limbs,
            len: out_len,
            _p: PhantomData,
        }
    }
}

forward_bitwise_receivers!(BitXor, bitxor);

// ── Compound-assign forms (in-place on `self.limbs`) ──

impl<T: MachineWord, const CAP: usize, P: Personality> BitAndAssign for HeaplessBigInt<T, CAP, P> {
    fn bitand_assign(&mut self, other: Self) {
        self.bitand_assign(&other);
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> BitAndAssign<&HeaplessBigInt<T, CAP, P>>
    for HeaplessBigInt<T, CAP, P>
{
    fn bitand_assign(&mut self, other: &Self) {
        // Result width is `min(len)`: AND the overlap, then clear `self`'s
        // limbs above `min` (they AND with `other`'s zero-tail = 0).
        let min_len = core::cmp::min(self.len, other.len) as usize;
        let self_len = self.len as usize;
        for (si, &oi) in self.limbs[..min_len]
            .iter_mut()
            .zip(&other.limbs[..min_len])
        {
            *si &= oi;
        }
        for si in &mut self.limbs[min_len..self_len] {
            *si = zero::<T>();
        }
        self.len = min_len as u16;
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> BitOrAssign for HeaplessBigInt<T, CAP, P> {
    fn bitor_assign(&mut self, other: Self) {
        self.bitor_assign(&other);
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> BitOrAssign<&HeaplessBigInt<T, CAP, P>>
    for HeaplessBigInt<T, CAP, P>
{
    fn bitor_assign(&mut self, other: &Self) {
        // Result width is `max(len)`: OR the overlap, then copy `other`'s
        // high limbs (they OR with `self`'s zero-tail = `other`). The copy
        // range is empty when `self` is the wider operand.
        let self_len = self.len as usize;
        let max_len = core::cmp::max(self_len, other.len as usize);
        for (si, &oi) in self.limbs[..self_len]
            .iter_mut()
            .zip(&other.limbs[..self_len])
        {
            *si |= oi;
        }
        for (si, &oi) in self.limbs[self_len..max_len]
            .iter_mut()
            .zip(&other.limbs[self_len..max_len])
        {
            *si = oi;
        }
        self.len = max_len as u16;
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> BitXorAssign for HeaplessBigInt<T, CAP, P> {
    fn bitxor_assign(&mut self, other: Self) {
        self.bitxor_assign(&other);
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> BitXorAssign<&HeaplessBigInt<T, CAP, P>>
    for HeaplessBigInt<T, CAP, P>
{
    fn bitxor_assign(&mut self, other: &Self) {
        // Result width is `max(len)`: XOR the overlap, then copy `other`'s
        // high limbs (they XOR with `self`'s zero-tail = `other`). The copy
        // range is empty when `self` is the wider operand.
        let self_len = self.len as usize;
        let max_len = core::cmp::max(self_len, other.len as usize);
        for (si, &oi) in self.limbs[..self_len]
            .iter_mut()
            .zip(&other.limbs[..self_len])
        {
            *si ^= oi;
        }
        for (si, &oi) in self.limbs[self_len..max_len]
            .iter_mut()
            .zip(&other.limbs[self_len..max_len])
        {
            *si = oi;
        }
        self.len = max_len as u16;
    }
}
