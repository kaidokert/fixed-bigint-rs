//! Differential oracle: a `HeaplessBigInt<u8, CAP>` carried at `len = k`
//! is a `k`-word integer of width `k · word_bits`, so every arithmetic op
//! must return bit-for-bit what `FixedUInt<u8, k>` returns — wrapped value
//! AND overflow/borrow flag alike. `CAP` is allocation; the words beyond
//! `len` do not exist for arithmetic.
//!
//! This is the payoff of that equivalence: the op surface is written ONCE
//! in [`assert_carrier_parity`], and both a fixed-width `FixedUInt<u8, k>`
//! and a runtime-width `HeaplessBigInt<u8, 24>` constructed at `len = k`
//! flow through it. The carrier's capacity (24) is deliberately far wider
//! than the widths under test (1, 2, 4) — if any op leaked capacity into
//! its answer, the two sides would diverge here.

#![cfg(all(feature = "heapless-runtime-len", feature = "num-traits"))]

use const_num_traits::{
    CheckedAdd, CheckedMul, Nct, OverflowingAdd, OverflowingMul, OverflowingSub, WrappingAdd,
    WrappingMul, WrappingSub,
};
use fixed_bigint::{FixedUInt, HeaplessBigInt};
use num_traits::ToPrimitive;

/// A fixed-width unsigned these differential tests can drive: build a value
/// at a chosen word-width and read it back as `u64`. `FixedUInt<u8, N>`'s
/// width is its `N` (the requested width must match); `HeaplessBigInt`
/// constructs at `len = width`.
trait WidthCarrier:
    Copy
    + WrappingAdd<Output = Self>
    + WrappingSub<Output = Self>
    + WrappingMul<Output = Self>
    + OverflowingAdd<Output = Self>
    + OverflowingSub<Output = Self>
    + OverflowingMul<Output = Self>
    + CheckedAdd<Output = Self>
    + CheckedMul<Output = Self>
{
    fn make(v: u32, width_words: usize) -> Self;
    fn read(&self) -> u64;
}

impl<const N: usize> WidthCarrier for FixedUInt<u8, N> {
    fn make(v: u32, width_words: usize) -> Self {
        assert_eq!(width_words, N, "FixedUInt<u8, N> width is fixed at N");
        FixedUInt::<u8, N>::from(v)
    }
    fn read(&self) -> u64 {
        ToPrimitive::to_u64(self).unwrap()
    }
}

impl<const CAP: usize> WidthCarrier for HeaplessBigInt<u8, CAP, Nct> {
    fn make(v: u32, width_words: usize) -> Self {
        let bytes = v.to_le_bytes();
        let mut limbs = [0u8; CAP];
        limbs[..width_words].copy_from_slice(&bytes[..width_words]);
        HeaplessBigInt::from_limbs(limbs, width_words as u16)
    }
    fn read(&self) -> u64 {
        let mut buf = [0u8; CAP];
        let s = self.to_le_bytes(&mut buf);
        // Values under test fit in u64; guard the shift past 8 bytes (the
        // high bytes are zero at these widths).
        let mut acc = 0u64;
        for (i, b) in s.iter().enumerate().take(8) {
            acc |= (*b as u64) << (8 * i);
        }
        acc
    }
}

/// Assert `Fixed` and `Heapless` agree on every op at `width` words. `Fixed`
/// is the trusted fixed-width reference; `Heapless` is the carrier under
/// test. Both wrapped value and flag must match.
fn assert_carrier_parity<Fixed, Heapless>(width: usize, mask: u32)
where
    Fixed: WidthCarrier,
    Heapless: WidthCarrier,
{
    // A spread that exercises cross-limb carries at widths 2 and 4.
    let vals: [u32; 10] = [
        0,
        1,
        5,
        7,
        0x7F,
        0xFF,
        0x0100,
        0xFFFF,
        0x0001_0000,
        0xFFFF_FFFF,
    ];

    for &ra in &vals {
        for &rb in &vals {
            let (a, b) = (ra & mask, rb & mask);
            let f = |v| Fixed::make(v, width);
            let h = |v| Heapless::make(v, width);

            assert_eq!(
                WrappingAdd::wrapping_add(f(a), f(b)).read(),
                WrappingAdd::wrapping_add(h(a), h(b)).read(),
                "wrapping_add {a}+{b} @ width {width}"
            );
            assert_eq!(
                WrappingSub::wrapping_sub(f(a), f(b)).read(),
                WrappingSub::wrapping_sub(h(a), h(b)).read(),
                "wrapping_sub {a}-{b} @ width {width}"
            );
            assert_eq!(
                WrappingMul::wrapping_mul(f(a), f(b)).read(),
                WrappingMul::wrapping_mul(h(a), h(b)).read(),
                "wrapping_mul {a}*{b} @ width {width}"
            );

            let (fa, ffl) = OverflowingAdd::overflowing_add(f(a), f(b));
            let (ha, hfl) = OverflowingAdd::overflowing_add(h(a), h(b));
            assert_eq!(
                (fa.read(), ffl),
                (ha.read(), hfl),
                "overflowing_add {a}+{b} @ width {width}"
            );

            let (fs, fsb) = OverflowingSub::overflowing_sub(f(a), f(b));
            let (hs, hsb) = OverflowingSub::overflowing_sub(h(a), h(b));
            assert_eq!(
                (fs.read(), fsb),
                (hs.read(), hsb),
                "overflowing_sub {a}-{b} @ width {width}"
            );

            let (fp, fpo) = OverflowingMul::overflowing_mul(f(a), f(b));
            let (hp, hpo) = OverflowingMul::overflowing_mul(h(a), h(b));
            assert_eq!(
                (fp.read(), fpo),
                (hp.read(), hpo),
                "overflowing_mul {a}*{b} @ width {width}"
            );

            assert_eq!(
                CheckedAdd::checked_add(f(a), f(b)).map(|x| x.read()),
                CheckedAdd::checked_add(h(a), h(b)).map(|x| x.read()),
                "checked_add {a}+{b} @ width {width}"
            );
            assert_eq!(
                CheckedMul::checked_mul(f(a), f(b)).map(|x| x.read()),
                CheckedMul::checked_mul(h(a), h(b)).map(|x| x.read()),
                "checked_mul {a}*{b} @ width {width}"
            );
        }
    }
}

#[test]
fn heapless_at_width_1_matches_fixeduint_u8_1() {
    assert_carrier_parity::<FixedUInt<u8, 1>, HeaplessBigInt<u8, 24, Nct>>(1, 0xFF);
}

#[test]
fn heapless_at_width_2_matches_fixeduint_u8_2() {
    assert_carrier_parity::<FixedUInt<u8, 2>, HeaplessBigInt<u8, 24, Nct>>(2, 0xFFFF);
}

#[test]
fn heapless_at_width_4_matches_fixeduint_u8_4() {
    assert_carrier_parity::<FixedUInt<u8, 4>, HeaplessBigInt<u8, 24, Nct>>(4, 0xFFFF_FFFF);
}
