//! `const_num_traits::Midpoint` for `HeaplessBigInt`.
//!
//! `(a & b) + ((a ^ b) >> 1)` averages without overflow, and is branchless, so
//! it is personality-generic and constant-time. The `>> 1` is a single-bit
//! shift (width-preserving), and `&`/`^`/`+` all resolve at `max(len)`, so the
//! result is at the operand width.

use super::HeaplessBigInt;
use crate::MachineWord;
use const_num_traits::{Midpoint, Personality};

impl<T, const CAP: usize, P: Personality> Midpoint for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord,
{
    type Output = Self;
    fn midpoint(self, rhs: Self) -> Self {
        (self & rhs) + ((self ^ rhs) >> 1usize)
    }
}
