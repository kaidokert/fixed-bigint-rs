//! `pow` for `HeaplessBigInt<T, CAP, Nct>`: the inherent method plus the
//! `const_num_traits::CheckedPow` / `StrictPow` parallels.
//!
//! All Nct-only, mirroring `FixedUInt`. Exponentiation is by squaring at the
//! value width (`max(a.len, b.len)` per multiply), so a value at `len = k`
//! raises exactly like `FixedUInt<T, k>`. `pow_impl` is the shared kernel; the
//! num_traits::PrimInt bridge reuses it too.

use super::HeaplessBigInt;
use crate::MachineWord;
use const_num_traits::{CarryingMul, CheckedMul, CheckedPow, Nct, One, StrictPow};

/// Square-and-multiply with the panicking Nct `Mul`, so it panics on overflow
/// at the value width — like `FixedUInt`'s `pow_impl` and std's `pow`.
pub(crate) fn pow_impl<T, const CAP: usize>(
    base: HeaplessBigInt<T, CAP, Nct>,
    exp: u32,
) -> HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    // x^0 is 1 at the operand's width (`base.len`), matching FixedUInt<k>;
    // widen the identity so the `exp == 0` early path doesn't return a narrow
    // (len-1) value. For `exp > 0` the first multiply would widen it anyway.
    let mut result =
        <HeaplessBigInt<T, CAP, Nct> as One>::one().widened(core::cmp::max(1, base.len));
    let mut b = base;
    let mut e = exp;
    while e > 0 {
        if e & 1 == 1 {
            result *= b;
        }
        e >>= 1;
        if e > 0 {
            b *= b;
        }
    }
    result
}

impl<T, const CAP: usize> HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    /// Raises `self` to `exp` by squaring. Panics on overflow at the value
    /// width (Nct), like std's `pow`; use `checked_pow` to get `None` instead.
    pub fn pow(self, exp: u32) -> Self {
        pow_impl(self, exp)
    }
}

impl<T, const CAP: usize> CheckedPow for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type Output = Self;
    fn checked_pow(self, exp: u32) -> Option<Self> {
        let mut result = <Self as One>::one().widened(core::cmp::max(1, self.len));
        let mut base = self;
        let mut e = exp;
        while e > 0 {
            if e & 1 == 1 {
                result = CheckedMul::checked_mul(result, base)?;
            }
            e >>= 1;
            if e > 0 {
                base = CheckedMul::checked_mul(base, base)?;
            }
        }
        Some(result)
    }
}

impl<T, const CAP: usize> StrictPow for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type Output = Self;
    fn strict_pow(self, exp: u32) -> Self {
        match <Self as CheckedPow>::checked_pow(self, exp) {
            Some(v) => v,
            None => panic!("HeaplessBigInt: strict_pow overflowed"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::FixedUInt;

    type H = HeaplessBigInt<u32, 8, Nct>; // 256-bit CAP

    #[test]
    fn pow_value_width_and_overflow() {
        let base = H::from_le_bytes(&2u32.to_le_bytes()); // len 1 (32-bit)
        // 2^10 = 1024, still at the operand width (len 1), not CAP.
        let r = base.pow(10);
        assert_eq!(r.len, 1);
        assert_eq!(r.limbs[0], 1024);
        // x^0 = 1 at the operand width, not a narrowed len-1 value.
        assert_eq!(base.pow(0).len, 1);
        let base2 = base.widened(2);
        assert_eq!(base2.pow(0).len, 2);
        assert_eq!(base2.pow(0).limbs[0], 1);
        // 2^32 overflows the 32-bit width → None, matching FixedUInt<u32, 1>.
        assert_eq!(CheckedPow::checked_pow(base, 32), None);
        assert_eq!(
            CheckedPow::checked_pow(FixedUInt::<u32, 1, Nct>::from(2u8), 32),
            None
        );
        assert_eq!(StrictPow::strict_pow(base, 10).limbs[0], 1024);
    }

    #[test]
    #[should_panic(expected = "strict_pow overflowed")]
    fn strict_pow_panics_on_overflow() {
        let base = H::from_le_bytes(&2u32.to_le_bytes());
        let _ = StrictPow::strict_pow(base, 32);
    }
}
