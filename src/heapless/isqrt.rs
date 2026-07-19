//! `const_num_traits::Isqrt` for `HeaplessBigInt<_, Nct>`.
//!
//! Bit-by-bit floor square root, Nct-only (data-dependent comparisons).
//! The result carries the operand width: `result` and the trial bit are
//! seeded at `self.len`, so every `candidate * candidate` resolves at the
//! value width exactly as the same-width `FixedUInt` does.

use super::HeaplessBigInt;
use crate::MachineWord;
use const_num_traits::{CarryingMul, Isqrt, Nct, One, Zero};

impl<T, const CAP: usize> Isqrt for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type Output = Self;

    fn isqrt(self) -> Self {
        // Largest r such that r*r <= self. Zero is its own root (and already
        // carries the operand width, so return it unchanged).
        if <Self as Zero>::is_zero(&self) {
            return self;
        }

        let width = self.len();
        let mut result = Self::new_zero_with_len(width);
        let one_w = <Self as One>::one().widened(width);

        let start_bit = self.bit_length().div_ceil(2);
        let mut bit_pos = start_bit;
        while bit_pos > 0 {
            bit_pos -= 1;
            let candidate = result | (one_w << bit_pos);
            if candidate * candidate <= self {
                result = candidate;
            }
        }
        result
    }
}

impl<T, const CAP: usize> HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    /// Unsigned isqrt cannot fail; always `Some`. Parallels
    /// `FixedUInt::checked_isqrt` and the signed-only external
    /// `CheckedIsqrt`.
    #[must_use]
    pub fn checked_isqrt(self) -> Option<Self> {
        Some(<Self as Isqrt>::isqrt(self))
    }
}

#[cfg(test)]
mod tests {
    use super::HeaplessBigInt;
    use const_num_traits::Isqrt;

    type H = HeaplessBigInt<u8, 8>;

    #[test]
    fn isqrt_values() {
        for (n, r) in [
            (0u16, 0u16),
            (1, 1),
            (4, 2),
            (15, 3),
            (16, 4),
            (24, 4),
            (10000, 100),
            (65535, 255),
        ] {
            assert_eq!(Isqrt::isqrt(H::from(n)), H::from(r), "isqrt({n})");
        }
    }

    // The result carries the operand width, not the minimal magnitude width.
    #[test]
    fn isqrt_preserves_width() {
        let n = H::from(10000u16).widened(8);
        let r = Isqrt::isqrt(n);
        assert_eq!(r, H::from(100u8));
        assert_eq!(r.len(), 8);

        // Zero keeps its width too.
        let z = H::new_zero_with_len(8);
        assert_eq!(Isqrt::isqrt(z).len(), 8);
    }
}
