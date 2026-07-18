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

// Core: `&Self & &Self`. The value + mixed receiver forms delegate here.
impl<T: MachineWord, const CAP: usize, P: Personality> BitAnd<&HeaplessBigInt<T, CAP, P>>
    for &HeaplessBigInt<T, CAP, P>
{
    type Output = HeaplessBigInt<T, CAP, P>;
    fn bitand(self, other: &HeaplessBigInt<T, CAP, P>) -> Self::Output {
        let out_len = core::cmp::min(self.len, other.len);
        let mut limbs = [zero::<T>(); CAP];
        let mut i = 0;
        while i < out_len as usize {
            limbs[i] = self.limbs[i] & other.limbs[i];
            i += 1;
        }
        HeaplessBigInt {
            limbs,
            len: out_len,
            _p: PhantomData,
        }
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> BitAnd for HeaplessBigInt<T, CAP, P> {
    type Output = Self;
    fn bitand(self, other: Self) -> Self {
        (&self).bitand(&other)
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> BitAnd<&HeaplessBigInt<T, CAP, P>>
    for HeaplessBigInt<T, CAP, P>
{
    type Output = Self;
    fn bitand(self, other: &Self) -> Self {
        (&self).bitand(other)
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> BitAnd<HeaplessBigInt<T, CAP, P>>
    for &HeaplessBigInt<T, CAP, P>
{
    type Output = HeaplessBigInt<T, CAP, P>;
    fn bitand(self, other: HeaplessBigInt<T, CAP, P>) -> Self::Output {
        self.bitand(&other)
    }
}

// Core: `&Self | &Self`. The value + mixed receiver forms delegate here.
impl<T: MachineWord, const CAP: usize, P: Personality> BitOr<&HeaplessBigInt<T, CAP, P>>
    for &HeaplessBigInt<T, CAP, P>
{
    type Output = HeaplessBigInt<T, CAP, P>;
    fn bitor(self, other: &HeaplessBigInt<T, CAP, P>) -> Self::Output {
        let out_len = core::cmp::max(self.len, other.len);
        let mut limbs = [zero::<T>(); CAP];
        let mut i = 0;
        while i < out_len as usize {
            limbs[i] = self.limbs[i] | other.limbs[i];
            i += 1;
        }
        HeaplessBigInt {
            limbs,
            len: out_len,
            _p: PhantomData,
        }
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> BitOr for HeaplessBigInt<T, CAP, P> {
    type Output = Self;
    fn bitor(self, other: Self) -> Self {
        (&self).bitor(&other)
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> BitOr<&HeaplessBigInt<T, CAP, P>>
    for HeaplessBigInt<T, CAP, P>
{
    type Output = Self;
    fn bitor(self, other: &Self) -> Self {
        (&self).bitor(other)
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> BitOr<HeaplessBigInt<T, CAP, P>>
    for &HeaplessBigInt<T, CAP, P>
{
    type Output = HeaplessBigInt<T, CAP, P>;
    fn bitor(self, other: HeaplessBigInt<T, CAP, P>) -> Self::Output {
        self.bitor(&other)
    }
}

// Core: `&Self ^ &Self`. The value + mixed receiver forms delegate here.
impl<T: MachineWord, const CAP: usize, P: Personality> BitXor<&HeaplessBigInt<T, CAP, P>>
    for &HeaplessBigInt<T, CAP, P>
{
    type Output = HeaplessBigInt<T, CAP, P>;
    fn bitxor(self, other: &HeaplessBigInt<T, CAP, P>) -> Self::Output {
        let out_len = core::cmp::max(self.len, other.len);
        let mut limbs = [zero::<T>(); CAP];
        let mut i = 0;
        while i < out_len as usize {
            limbs[i] = self.limbs[i] ^ other.limbs[i];
            i += 1;
        }
        HeaplessBigInt {
            limbs,
            len: out_len,
            _p: PhantomData,
        }
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> BitXor for HeaplessBigInt<T, CAP, P> {
    type Output = Self;
    fn bitxor(self, other: Self) -> Self {
        (&self).bitxor(&other)
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> BitXor<&HeaplessBigInt<T, CAP, P>>
    for HeaplessBigInt<T, CAP, P>
{
    type Output = Self;
    fn bitxor(self, other: &Self) -> Self {
        (&self).bitxor(other)
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> BitXor<HeaplessBigInt<T, CAP, P>>
    for &HeaplessBigInt<T, CAP, P>
{
    type Output = HeaplessBigInt<T, CAP, P>;
    fn bitxor(self, other: HeaplessBigInt<T, CAP, P>) -> Self::Output {
        self.bitxor(&other)
    }
}

// ── Compound-assign forms (delegate to the binary op) ──

impl<T: MachineWord, const CAP: usize, P: Personality> BitAndAssign for HeaplessBigInt<T, CAP, P> {
    fn bitand_assign(&mut self, other: Self) {
        *self = (&*self).bitand(&other);
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> BitAndAssign<&HeaplessBigInt<T, CAP, P>>
    for HeaplessBigInt<T, CAP, P>
{
    fn bitand_assign(&mut self, other: &Self) {
        *self = (&*self).bitand(other);
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> BitOrAssign for HeaplessBigInt<T, CAP, P> {
    fn bitor_assign(&mut self, other: Self) {
        *self = (&*self).bitor(&other);
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> BitOrAssign<&HeaplessBigInt<T, CAP, P>>
    for HeaplessBigInt<T, CAP, P>
{
    fn bitor_assign(&mut self, other: &Self) {
        *self = (&*self).bitor(other);
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> BitXorAssign for HeaplessBigInt<T, CAP, P> {
    fn bitxor_assign(&mut self, other: Self) {
        *self = (&*self).bitxor(&other);
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> BitXorAssign<&HeaplessBigInt<T, CAP, P>>
    for HeaplessBigInt<T, CAP, P>
{
    fn bitxor_assign(&mut self, other: &Self) {
        *self = (&*self).bitxor(other);
    }
}
