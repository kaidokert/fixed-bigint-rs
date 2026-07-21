//! `num_traits::PrimInt` for `HeaplessBigInt<T, CAP, Nct>`.
//!
//! A thin bridge: the bit-operation methods delegate to the already-implemented
//! `const_num_traits::PrimBits`, and `pow` to the shared `pow_impl`. Nct-only
//! (PrimInt supertrait-bundles `Num`, which is Nct on this carrier);
//! `reverse_bits`/`leading_ones`/`trailing_ones` use the trait defaults, same
//! as `FixedUInt`.

use super::HeaplessBigInt;
use super::pow::pow_impl;
use crate::MachineWord;
use const_num_traits::{CarryingMul, Nct, PrimBits};

impl<T, const CAP: usize> num_traits::PrimInt for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    fn count_ones(self) -> u32 {
        PrimBits::count_ones(self)
    }
    fn count_zeros(self) -> u32 {
        PrimBits::count_zeros(self)
    }
    fn leading_zeros(self) -> u32 {
        PrimBits::leading_zeros(self)
    }
    fn trailing_zeros(self) -> u32 {
        PrimBits::trailing_zeros(self)
    }
    fn rotate_left(self, n: u32) -> Self {
        PrimBits::rotate_left(self, n)
    }
    fn rotate_right(self, n: u32) -> Self {
        PrimBits::rotate_right(self, n)
    }
    fn signed_shl(self, n: u32) -> Self {
        PrimBits::signed_shl(self, n)
    }
    fn signed_shr(self, n: u32) -> Self {
        PrimBits::signed_shr(self, n)
    }
    fn unsigned_shl(self, n: u32) -> Self {
        PrimBits::unsigned_shl(self, n)
    }
    fn unsigned_shr(self, n: u32) -> Self {
        PrimBits::unsigned_shr(self, n)
    }
    fn swap_bytes(self) -> Self {
        PrimBits::swap_bytes(self)
    }
    // Override the num_traits default: it reverses via shifts, and heapless's
    // `Shr` narrows `len`, so the default collapses to zero. PrimBits does it
    // limb-wise at the value width.
    fn reverse_bits(self) -> Self {
        PrimBits::reverse_bits(self)
    }
    fn from_be(x: Self) -> Self {
        PrimBits::from_be(x)
    }
    fn from_le(x: Self) -> Self {
        PrimBits::from_le(x)
    }
    fn to_be(self) -> Self {
        PrimBits::to_be(self)
    }
    fn to_le(self) -> Self {
        PrimBits::to_le(self)
    }
    fn pow(self, exp: u32) -> Self {
        pow_impl(self, exp)
    }
}
