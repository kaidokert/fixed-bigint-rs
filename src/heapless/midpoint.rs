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

// `&Self` mirror so `(&h).midpoint(&g)` resolves without an explicit copy.
impl<T, const CAP: usize, P: Personality> Midpoint for &HeaplessBigInt<T, CAP, P>
where
    T: MachineWord,
{
    type Output = HeaplessBigInt<T, CAP, P>;
    fn midpoint(self, rhs: Self) -> Self::Output {
        <HeaplessBigInt<T, CAP, P> as Midpoint>::midpoint(*self, *rhs)
    }
}

#[cfg(test)]
mod tests {
    use super::HeaplessBigInt;
    use const_num_traits::Midpoint;

    type H = HeaplessBigInt<u8, 4>;

    #[test]
    fn byref_matches_value() {
        let a = H::from(10u8);
        let b = H::from(21u8);
        assert_eq!(Midpoint::midpoint(&a, &b), Midpoint::midpoint(a, b));
    }
}
