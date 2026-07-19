//! `num_integer::Roots` (nth_root, and the `sqrt`/`cbrt` defaults) for
//! `HeaplessBigInt<_, Nct>`.
//!
//! Newton's method, Nct-only (value-dependent convergence). The estimate
//! `x` is seeded at the operand width (`one` widened before the shift) so
//! every `pow`/`*`/`/` in the iteration resolves at the value width, bit
//! for bit with the same-width `FixedUInt`.

use super::HeaplessBigInt;
use crate::MachineWord;
use const_num_traits::{CarryingMul, Nct};
use num_integer::Roots;
use num_traits::{One, Zero};

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

        let n_val: Self = From::from(n);
        let n_minus_1: Self = From::from(n - 1);

        loop {
            let x_pow_n_minus_1 = x.pow(n - 1);
            if Zero::is_zero(&x_pow_n_minus_1) {
                break;
            }
            let quotient = *self / x_pow_n_minus_1;
            let numerator = x * n_minus_1 + quotient;
            let x_new = numerator / n_val;
            if x_new >= x {
                break;
            }
            x = x_new;
        }

        // Clamp to r^n <= self < (r+1)^n.
        while x.pow(n) > *self {
            x -= one_w;
        }
        let mut x_plus_one = x + one_w;
        while x_plus_one.pow(n) <= *self {
            x += one_w;
            x_plus_one = x + one_w;
        }

        x
    }
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
}
