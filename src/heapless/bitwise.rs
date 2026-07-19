//! `BitAnd` / `BitOr` / `BitXor` for `HeaplessBigInt` (all four receiver
//! forms each), plus the compound-assign forms.
//!
//! All three resolve at `len = max(a.len, b.len)` — the same operand-width
//! rule as the arithmetic ops, so every binary op hands back one consistent
//! width. `CAP` never enters. Above `min(len)` the shorter operand is in its
//! zero-tail, so `AND` yields zero there while `OR` / `XOR` leave the wider
//! operand's limbs unchanged; the result is value-correct at the wider width.
//! (`AND` could store the value in `min(len)` — its high limbs are zero — but
//! a narrower result than the sibling ops would desync widths for a following
//! width-sensitive op such as `Not` / `count_zeros`.)
//!
//! `len` is a public shape parameter, so the body is identical for Nct and
//! Ct. The compound-assign forms delegate to (or mirror) the binary op.

use super::{HeaplessBigInt, zero};
use crate::MachineWord;
use const_num_traits::Personality;
use core::marker::PhantomData;
use core::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not};

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
        // Operand width, like every other binary op. Above `min(len)` one
        // operand's zero-tail forces the AND to zero, so the extra high limbs
        // stay zero — value-correct at the wider width.
        let out_len = core::cmp::max(self.len, other.len);
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

// Complement over the value width (`len` limbs); the result stays at `len`,
// so `!x` matches the same-width `FixedUInt` bit-for-bit. `CAP` never enters
// — the words beyond `len` do not exist. Data-independent, hence uniform
// across personalities and inherently constant-time.
impl<T: MachineWord, const CAP: usize, P: Personality> Not for HeaplessBigInt<T, CAP, P> {
    type Output = Self;
    fn not(self) -> Self {
        let n = self.len as usize;
        let mut limbs = [zero::<T>(); CAP];
        for (o, &s) in limbs[..n].iter_mut().zip(&self.limbs[..n]) {
            *o = !s;
        }
        HeaplessBigInt {
            limbs,
            len: self.len,
            _p: PhantomData,
        }
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> Not for &HeaplessBigInt<T, CAP, P> {
    type Output = HeaplessBigInt<T, CAP, P>;
    fn not(self) -> Self::Output {
        !*self
    }
}

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
        // Result width is `max(len)` (operand width). AND the overlap; every
        // limb above `min` ANDs with a zero-tail (whichever operand is shorter),
        // so it becomes zero.
        let min_len = core::cmp::min(self.len, other.len) as usize;
        let max_len = core::cmp::max(self.len, other.len) as usize;
        for (si, &oi) in self.limbs[..min_len]
            .iter_mut()
            .zip(&other.limbs[..min_len])
        {
            *si &= oi;
        }
        for si in &mut self.limbs[min_len..max_len] {
            *si = zero::<T>();
        }
        self.len = max_len as u16;
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
