//! `const_num_traits::Isqrt` for `HeaplessBigInt<_, Nct>`.
//!
//! Digit-by-digit (base-2) floor square root, Nct-only (data-dependent
//! comparisons). Uses only add/sub/shift — no per-iteration multiply — so it
//! is O(width²) rather than the O(width³) of a `candidate * candidate` scan.
//! `res`/`bit` are seeded at the operand width, and the `>> 1` / `>> 2` are
//! sub-word shifts (never crossing a limb), so every value stays at `self.len`
//! throughout and the result carries the operand width, bit-for-bit with the
//! same-width `FixedUInt`.

use super::HeaplessBigInt;
use crate::MachineWord;
use const_num_traits::{Isqrt, Nct, One, Zero};

impl<T, const CAP: usize> Isqrt for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
{
    type Output = Self;

    fn isqrt(self) -> Self {
        // Zero is its own root and already carries the operand width.
        if <Self as Zero>::is_zero(&self) {
            return self;
        }

        let width = self.len();
        let one_w = <Self as One>::one().widened(width);
        let mut num = self;
        let mut res = Self::new_zero_with_len(width);

        // Start at the largest power of four <= self: `1 << (highest even bit)`.
        let highest_even_bit = (self.bit_length() - 1) & !1;
        let mut bit = one_w << highest_even_bit;

        while !<Self as Zero>::is_zero(&bit) {
            let sum = res + bit;
            if num >= sum {
                num -= sum;
                res = (res >> 1usize) + bit;
            } else {
                res >>= 1;
            }
            bit >>= 2;
        }
        res
    }
}

// `&Self` mirror so `(&h).isqrt()` resolves without an explicit copy.
impl<T, const CAP: usize> Isqrt for &HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
{
    type Output = HeaplessBigInt<T, CAP, Nct>;
    fn isqrt(self) -> Self::Output {
        <HeaplessBigInt<T, CAP, Nct> as Isqrt>::isqrt(*self)
    }
}

impl<T, const CAP: usize> HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
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

    // Matches a reference integer isqrt across a range, exercising the
    // digit-by-digit steps.
    #[test]
    fn isqrt_correctness_range() {
        fn ref_isqrt(n: u32) -> u32 {
            let mut r = 0u32;
            while (r + 1) * (r + 1) <= n {
                r += 1;
            }
            r
        }
        for n in 0u16..=2000 {
            let expected = ref_isqrt(u32::from(n)) as u16;
            assert_eq!(Isqrt::isqrt(H::from(n)), H::from(expected), "isqrt({n})");
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

    #[test]
    fn byref_matches_value() {
        let a = H::from(10000u16);
        assert_eq!(Isqrt::isqrt(&a), Isqrt::isqrt(a));
    }
}
