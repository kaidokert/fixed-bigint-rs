//! `num_integer::Integer` for `HeaplessBigInt<T, CAP, Nct>`.
//!
//! Nct-only, mirroring `FixedUInt`. `div_floor`/`mod_floor`/`div_rem` are the
//! unsigned div/rem (floor == truncating); `gcd` is Stein's binary algorithm;
//! `lcm` = `a / gcd(a, b) * b`. `is_even`/`is_odd` delegate to the O(1)
//! `Parity` LSB check. Everything resolves at the operand width `max(len)`.

use super::HeaplessBigInt;
use crate::MachineWord;
use const_num_traits::{CarryingMul, Nct, One, PrimBits, Zero};

impl<T, const CAP: usize> num_integer::Integer for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    fn div_floor(&self, other: &Self) -> Self {
        *self / *other
    }

    fn mod_floor(&self, other: &Self) -> Self {
        *self % *other
    }

    fn gcd(&self, other: &Self) -> Self {
        // Stein's (binary) GCD. Heapless `>>` narrows `len`, so the running
        // values shrink as they're stripped of factors of two — that's
        // value-correct (comparisons are value-based). The result is pinned to
        // the operand width `max(len)`: widen before the final `<< shift` so no
        // bit is lost and the width matches FixedUInt<k>.
        let width = core::cmp::max(self.len(), other.len());
        let mut m = *self;
        let mut n = *other;
        let zero = <Self as Zero>::zero();
        if m == zero || n == zero {
            return m | n; // already at max(len) via BitOr
        }

        // Common factors of two, then strip each value to odd.
        let shift = PrimBits::trailing_zeros(m | n);
        m = m >> (PrimBits::trailing_zeros(m) as usize);
        n = n >> (PrimBits::trailing_zeros(n) as usize);

        while m != n {
            if m > n {
                m -= n;
                m = m >> (PrimBits::trailing_zeros(m) as usize);
            } else {
                n -= m;
                n = n >> (PrimBits::trailing_zeros(n) as usize);
            }
        }
        m.widened(width) << (shift as usize)
    }

    fn lcm(&self, other: &Self) -> Self {
        if <Self as Zero>::is_zero(self) && <Self as Zero>::is_zero(other) {
            // Zero at the operand width, not the minimal-width `zero()`.
            return <Self as Zero>::zero().widened(core::cmp::max(self.len(), other.len()));
        }
        let gcd = self.gcd(other);
        *self * (*other / gcd)
    }

    fn is_multiple_of(&self, other: &Self) -> bool {
        // Guard the zero divisor (as num_integer's primitive impls do): 0 is a
        // multiple of 0, nothing else is — no `% 0` panic.
        if <Self as Zero>::is_zero(other) {
            return <Self as Zero>::is_zero(self);
        }
        *self % *other == <Self as Zero>::zero()
    }

    fn is_even(&self) -> bool {
        // O(1) LSB check, like FixedUInt. `len == 0` (zero) is even; otherwise
        // `len > 0` guarantees `limbs[0]` exists.
        self.len == 0 || self.limbs[0] & <T as One>::one() == <T as Zero>::zero()
    }

    fn is_odd(&self) -> bool {
        !self.is_even()
    }

    fn div_rem(&self, other: &Self) -> (Self, Self) {
        // Inherent div_rem (single pass); resolves over `&self`, so it's the
        // inherent method, not this trait one.
        self.div_rem(other)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_integer::Integer;

    type H = HeaplessBigInt<u32, 8, Nct>; // 256-bit CAP

    #[test]
    fn gcd_preserves_operand_width() {
        // Two len-2 (64-bit) values in a CAP-8 carrier. Stein's `>>` narrows
        // the running values, but the result is pinned to the operand width
        // (len 2), not the narrow gcd magnitude — matching FixedUInt<u32, 2>.
        let a = H::from_le_bytes(&12u64.to_le_bytes()); // len 2
        let b = H::from_le_bytes(&18u64.to_le_bytes()); // len 2
        let g = a.gcd(&b);
        assert_eq!(g.len(), 2, "gcd resolves at the operand width");
        assert_eq!(g.limbs[0], 6);
        assert_eq!(g.limbs[1], 0);
    }

    #[test]
    fn gcd_lcm_multi_limb() {
        // 64-bit powers of two spanning 2 u32 limbs.
        let a = H::from_le_bytes(&0x1_0000_0000u64.to_le_bytes()); // 2^32
        let b = H::from_le_bytes(&0x1_8000_0000u64.to_le_bytes()); // 3·2^31
        assert_eq!(a.gcd(&b), H::from_le_bytes(&0x8000_0000u64.to_le_bytes())); // 2^31
        // lcm(2^32, 3·2^31) = 3·2^32
        assert_eq!(a.lcm(&b), H::from_le_bytes(&0x3_0000_0000u64.to_le_bytes()));
    }

    #[test]
    fn is_multiple_of_zero_divisor_no_panic() {
        // num_integer contract: is_multiple_of(&0) is a predicate, not a panic.
        let zero = H::from_le_bytes(&0u32.to_le_bytes());
        let five = H::from_le_bytes(&5u32.to_le_bytes());
        assert!(zero.is_multiple_of(&zero)); // 0 is a multiple of 0
        assert!(!five.is_multiple_of(&zero)); // 5 is not
    }

    #[test]
    fn lcm_of_zeros_keeps_operand_width() {
        // lcm(0, 0) = 0 at the operand width, not the minimal len-0 zero.
        let z = H::from_le_bytes(&0u64.to_le_bytes()); // len 2 (8 zero bytes)
        assert_eq!(z.len(), 2);
        assert_eq!(z.lcm(&z).len(), 2);
    }
}
