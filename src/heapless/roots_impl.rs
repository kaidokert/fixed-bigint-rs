//! `num_integer::Roots` (nth_root, and the `sqrt`/`cbrt` defaults) for
//! `HeaplessBigInt<_, Nct>`.
//!
//! Newton's method, Nct-only (value-dependent convergence). The estimate
//! `x` and the constants `n`, `n-1` are all pinned to the operand width so
//! every `pow`/`*`/`/` resolves at the value width. Power evaluations go
//! through `checked_pow`: an over-width `x^k` would panic (Nct multiply) or
//! silently wrap, either of which breaks the clamp loops, so overflow is
//! treated as "arbitrarily large" (quotient 0 / probe fails) instead.

use super::HeaplessBigInt;
use crate::MachineWord;
use const_num_traits::{CarryingMul, CheckedPow, Nct};
use num_integer::Roots;
use num_traits::{FromPrimitive, One, Zero};

impl<T, const CAP: usize> Roots for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    fn nth_root(&self, n: u32) -> Self {
        if n == 0 {
            panic!("nth_root: n must be non-zero");
        }
        // Zero and one are their own roots and already carry the width.
        if Zero::is_zero(self) {
            return *self;
        }
        if One::is_one(self) || n == 1 {
            return *self;
        }

        let width = self.len();
        let bit_len = self.bit_length();
        // Root of a value with fewer than `n` bits is 1.
        if n as usize > bit_len {
            return <Self as One>::one().widened(width);
        }

        let one_w = <Self as One>::one().widened(width);
        let initial_exp = (bit_len as u32).div_ceil(n).max(1);
        let mut x = one_w << (initial_exp as usize);

        // `n` fits the operand width (n <= bit_len <= width·word_bits), so
        // build the constants value-based at that width — `From::<u32>` would
        // carry the 4-byte source width (wrong shape, and it panics when
        // CAP < 4/word).
        let n_val = width_const(n, width);
        let n_minus_1 = width_const(n - 1, width);

        loop {
            // x^(n-1) overflowing the width means it dwarfs `self`, so the
            // quotient `self / x^(n-1)` is 0.
            let quotient = match CheckedPow::checked_pow(x, n - 1) {
                Some(p) if Zero::is_zero(&p) => break,
                Some(p) => *self / p,
                None => Self::new_zero_with_len(width),
            };
            let numerator = x * n_minus_1 + quotient;
            let x_new = numerator / n_val;
            if x_new >= x {
                break;
            }
            x = x_new;
        }

        // Clamp to r^n <= self < (r+1)^n. An over-width x^n is > self (self
        // fits the width), so `None` reads as "greater".
        while CheckedPow::checked_pow(x, n).is_none_or(|p| p > *self) {
            x -= one_w;
        }
        let mut x_plus_one = x + one_w;
        while CheckedPow::checked_pow(x_plus_one, n).is_some_and(|p| p <= *self) {
            x += one_w;
            x_plus_one = x + one_w;
        }

        x
    }
}

/// Build a small `u32` value at exactly `width` limbs. Used for the Newton
/// constants, which must carry the operand width, not the `u32` source width.
/// The caller guarantees the value fits `width` limbs (`n <= width·word_bits`).
fn width_const<T, const CAP: usize>(value: u32, width: u16) -> HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
{
    // `from_u64` is value-based (natural width, never panics); widen to the
    // operand width. natural_len <= width because the value fits `width` limbs.
    <HeaplessBigInt<T, CAP, Nct> as FromPrimitive>::from_u64(value as u64)
        .expect("width_const: value fits the carrier")
        .widened(width)
}

#[cfg(test)]
mod tests {
    use super::HeaplessBigInt;
    use num_integer::Roots;

    type H = HeaplessBigInt<u8, 8>;

    #[test]
    fn sqrt_cbrt_nth() {
        assert_eq!(H::from(16u8).sqrt(), H::from(4u8));
        assert_eq!(H::from(15u8).sqrt(), H::from(3u8));
        assert_eq!(H::from(27u8).cbrt(), H::from(3u8));
        assert_eq!(H::from(63u8).cbrt(), H::from(3u8));
        assert_eq!(H::from(81u8).nth_root(4), H::from(3u8));
        assert_eq!(H::from(42u8).nth_root(1), H::from(42u8));
        // A value with fewer than n bits roots to 1.
        assert_eq!(H::from(2u8).nth_root(100), H::from(1u8));
    }

    #[test]
    #[should_panic(expected = "nth_root: n must be non-zero")]
    fn nth_root_zero_n_panics() {
        H::from(16u8).nth_root(0);
    }

    // Newton's estimate is seeded at the operand width; the root carries it.
    #[test]
    fn nth_root_preserves_width() {
        let n = H::from(10000u16).widened(8);
        let r = n.sqrt();
        assert_eq!(r, H::from(100u8));
        assert_eq!(r.len(), 8);
    }

    #[test]
    fn root_correctness_small_range() {
        for x in 1..=200u16 {
            let xi = H::from(x);
            let s = xi.sqrt();
            assert!(
                s.pow(2) <= xi && (s + H::from(1u8)).pow(2) > xi,
                "sqrt({x})"
            );
            let c = xi.cbrt();
            assert!(
                c.pow(3) <= xi && (c + H::from(1u8)).pow(3) > xi,
                "cbrt({x})"
            );
        }
    }

    // sqrt of the max value at the exact operand width: the upper probe
    // (x+1)^2 = 2^32 overflows the 32-bit width, which must read as ">self"
    // via checked_pow rather than panicking on the Nct multiply.
    #[test]
    fn sqrt_of_max_at_exact_width_does_not_panic() {
        type H1 = HeaplessBigInt<u32, 1>; // exactly 32-bit width
        assert_eq!(H1::from(u32::MAX).sqrt(), H1::from(0xFFFFu32));
    }

    // Narrow word + tiny CAP: the Newton constants must not go through the
    // 4-byte u32 `From` (which needs 4 limbs and would panic at CAP 1).
    #[test]
    fn sqrt_narrow_word_tiny_cap() {
        type H1 = HeaplessBigInt<u8, 1>; // 8-bit numbers, CAP 1
        assert_eq!(H1::from(196u8).sqrt(), H1::from(14u8));
        assert_eq!(H1::from(255u8).sqrt(), H1::from(15u8));
        assert_eq!(H1::from(196u8).sqrt().len(), 1);
    }
}
