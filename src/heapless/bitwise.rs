//! `BitAnd` for `HeaplessBigInt` (all four receiver forms).
//!
//! Limb-wise AND. Output `len = min(a.len, b.len)`: for any index at or
//! above that bound, one operand is in its zero-tail, so the AND is
//! zero — `min` is both value-tight and satisfies the zero-tail
//! invariant. Both operand lens are public shape parameters, so `min`
//! is public; the body is identical for Nct and Ct.
//!
//! Used by Montgomery `from_montgomery`'s reduction mask. `BitOr` /
//! `BitXor` are not implemented — no current consumer needs them.

use super::{HeaplessBigInt, zero};
use crate::MachineWord;
use const_num_traits::Personality;
use core::marker::PhantomData;
use core::ops::BitAnd;

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
