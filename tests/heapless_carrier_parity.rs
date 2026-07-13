//! `HeaplessBigInt` inherits `FixedUInt`'s tested behavior by construction.
//!
//! A value carried at `len = k` is a `k`-word integer of width
//! `k · word_bits`, so it must return bit-for-bit what the same-width
//! `FixedUInt` returns — value AND flag — on every op. `CAP` is
//! allocation; the words beyond `len` do not exist for arithmetic.
//!
//! This inverts the usual "test the type" setup: `FixedUInt` is the
//! trusted reference (it carries fixed-bigint's own large arithmetic
//! suite), and every op is checked ONCE in [`assert_carrier_parity`] with
//! `HeaplessBigInt` driven against `FixedUInt`'s answer. Any behavior that
//! is correct for the fixed-width type is thereby demanded of the carrier
//! too, across u8/u16/u32 backings and widths up to 64 bits, inside a
//! capacity far wider than the width under test — so a capacity leak into
//! any answer diverges here.

#![cfg(all(feature = "heapless-runtime-len", feature = "num-traits"))]

use const_num_traits::{
    BitWidth, CheckedAdd, CheckedMul, FromByteSlice, Nct, OverflowingAdd, OverflowingMul,
    OverflowingSub, WrappingAdd, WrappingMul, WrappingSub,
};
use core::cmp::Ordering;
use fixed_bigint::{FixedUInt, HeaplessBigInt};
use num_traits::ToPrimitive;

/// A fixed-width unsigned these differential tests can drive: build a value
/// at a chosen word-width and read it back as `u64`. `FixedUInt<T, N>`'s
/// width is its `N`; `HeaplessBigInt<T, CAP>` constructs at `len = width`.
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
    + core::ops::Div<Output = Self>
    + core::ops::Rem<Output = Self>
    + core::ops::Shl<usize, Output = Self>
    + core::ops::Shr<usize, Output = Self>
    + core::ops::BitAnd<Output = Self>
    + core::ops::BitOr<Output = Self>
    + PartialOrd
    + BitWidth
{
    const WORD_BYTES: usize;
    fn make(v: u64, width_words: usize) -> Self;
    fn read(&self) -> u64;
}

macro_rules! impl_carrier {
    (fixed $t:ty) => {
        impl<const N: usize> WidthCarrier for FixedUInt<$t, N, Nct> {
            const WORD_BYTES: usize = core::mem::size_of::<$t>();
            fn make(v: u64, width_words: usize) -> Self {
                assert_eq!(width_words, N, "FixedUInt<T, N> width is fixed at N");
                let bytes = v.to_le_bytes();
                FromByteSlice::from_le_slice(&bytes[..N * Self::WORD_BYTES]).unwrap()
            }
            fn read(&self) -> u64 {
                ToPrimitive::to_u64(self).unwrap()
            }
        }
    };
    (heapless $t:ty) => {
        impl<const CAP: usize> WidthCarrier for HeaplessBigInt<$t, CAP, Nct> {
            const WORD_BYTES: usize = core::mem::size_of::<$t>();
            fn make(v: u64, width_words: usize) -> Self {
                let bytes = v.to_le_bytes();
                HeaplessBigInt::from_le_bytes(&bytes[..width_words * Self::WORD_BYTES])
            }
            fn read(&self) -> u64 {
                let mut buf = [0u8; 64];
                let s = self.to_le_bytes(&mut buf);
                let mut acc = 0u64;
                for (i, b) in s.iter().enumerate().take(8) {
                    acc |= (*b as u64) << (8 * i);
                }
                acc
            }
        }
    };
}

impl_carrier!(fixed u8);
impl_carrier!(fixed u16);
impl_carrier!(fixed u32);
impl_carrier!(heapless u8);
impl_carrier!(heapless u16);
impl_carrier!(heapless u32);

fn value_set(mask: u64) -> [u64; 9] {
    [
        0,
        1,
        2,
        7,
        mask,                               // all ones
        mask >> 1,                          // 0b0111..1
        (mask >> 1).wrapping_add(1) & mask, // high bit only
        0xA5A5_A5A5_A5A5_A5A5 & mask,       // alternating
        0x0F1E_2D3C_4B5A_6978 & mask,       // arbitrary spread
    ]
}

/// Assert `F` (fixed-width reference) and `H` (carrier under test) agree on
/// every op at `width_words`. Both value and flag must match.
fn assert_carrier_parity<F, H>(width_words: usize)
where
    F: WidthCarrier,
    H: WidthCarrier,
{
    assert_eq!(F::WORD_BYTES, H::WORD_BYTES);
    let width_bits = width_words * F::WORD_BYTES * 8;
    let mask = if width_bits >= 64 {
        u64::MAX
    } else {
        (1u64 << width_bits) - 1
    };
    let vals = value_set(mask);
    let f = |v| F::make(v, width_words);
    let h = |v| H::make(v, width_words);

    // Unary ops.
    for &ra in &vals {
        let a = ra & mask;
        assert_eq!(
            BitWidth::bit_width(f(a)),
            BitWidth::bit_width(h(a)),
            "bit_width {a} @ width {width_bits}"
        );
        for &sh in &[0usize, 1, width_bits / 2, width_bits.saturating_sub(1)] {
            assert_eq!(
                (f(a) << sh).read(),
                (h(a) << sh).read(),
                "shl {a} << {sh} @ width {width_bits}"
            );
            assert_eq!(
                (f(a) >> sh).read(),
                (h(a) >> sh).read(),
                "shr {a} >> {sh} @ width {width_bits}"
            );
        }
    }

    // Binary ops.
    for &ra in &vals {
        for &rb in &vals {
            let (a, b) = (ra & mask, rb & mask);

            assert_eq!(
                WrappingAdd::wrapping_add(f(a), f(b)).read(),
                WrappingAdd::wrapping_add(h(a), h(b)).read(),
                "wrapping_add {a}+{b} @ width {width_bits}"
            );
            assert_eq!(
                WrappingSub::wrapping_sub(f(a), f(b)).read(),
                WrappingSub::wrapping_sub(h(a), h(b)).read(),
                "wrapping_sub {a}-{b} @ width {width_bits}"
            );
            assert_eq!(
                WrappingMul::wrapping_mul(f(a), f(b)).read(),
                WrappingMul::wrapping_mul(h(a), h(b)).read(),
                "wrapping_mul {a}*{b} @ width {width_bits}"
            );

            let (fa, ffl) = OverflowingAdd::overflowing_add(f(a), f(b));
            let (ha, hfl) = OverflowingAdd::overflowing_add(h(a), h(b));
            assert_eq!(
                (fa.read(), ffl),
                (ha.read(), hfl),
                "overflowing_add {a}+{b} @ width {width_bits}"
            );

            let (fs, fsb) = OverflowingSub::overflowing_sub(f(a), f(b));
            let (hs, hsb) = OverflowingSub::overflowing_sub(h(a), h(b));
            assert_eq!(
                (fs.read(), fsb),
                (hs.read(), hsb),
                "overflowing_sub {a}-{b} @ width {width_bits}"
            );

            let (fp, fpo) = OverflowingMul::overflowing_mul(f(a), f(b));
            let (hp, hpo) = OverflowingMul::overflowing_mul(h(a), h(b));
            assert_eq!(
                (fp.read(), fpo),
                (hp.read(), hpo),
                "overflowing_mul {a}*{b} @ width {width_bits}"
            );

            assert_eq!(
                CheckedAdd::checked_add(f(a), f(b)).map(|x| x.read()),
                CheckedAdd::checked_add(h(a), h(b)).map(|x| x.read()),
                "checked_add {a}+{b} @ width {width_bits}"
            );
            assert_eq!(
                CheckedMul::checked_mul(f(a), f(b)).map(|x| x.read()),
                CheckedMul::checked_mul(h(a), h(b)).map(|x| x.read()),
                "checked_mul {a}*{b} @ width {width_bits}"
            );

            assert_eq!(
                (f(a) & f(b)).read(),
                (h(a) & h(b)).read(),
                "bitand {a}&{b} @ width {width_bits}"
            );
            assert_eq!(
                (f(a) | f(b)).read(),
                (h(a) | h(b)).read(),
                "bitor {a}|{b} @ width {width_bits}"
            );

            assert_eq!(
                f(a).partial_cmp(&f(b)),
                h(a).partial_cmp(&h(b)),
                "cmp {a} ? {b} @ width {width_bits}"
            );

            // Div / Rem: skip the zero divisor.
            if b != 0 {
                assert_eq!(
                    (f(a) / f(b)).read(),
                    (h(a) / h(b)).read(),
                    "div {a}/{b} @ width {width_bits}"
                );
                assert_eq!(
                    (f(a) % f(b)).read(),
                    (h(a) % h(b)).read(),
                    "rem {a}%{b} @ width {width_bits}"
                );
            }
        }
    }

    // Anchor: at least one comparison actually distinguished ordering.
    assert_ne!(
        f(vals[0] & mask).partial_cmp(&f(vals[4] & mask)),
        Some(Ordering::Equal)
    );
}

// u8 backing: widths 1, 2, 4, 8 (8 … 64 bits) in a capacity-24 carrier.
#[test]
fn u8_backed_widths_match_fixeduint() {
    assert_carrier_parity::<FixedUInt<u8, 1>, HeaplessBigInt<u8, 24, Nct>>(1);
    assert_carrier_parity::<FixedUInt<u8, 2>, HeaplessBigInt<u8, 24, Nct>>(2);
    assert_carrier_parity::<FixedUInt<u8, 4>, HeaplessBigInt<u8, 24, Nct>>(4);
    assert_carrier_parity::<FixedUInt<u8, 8>, HeaplessBigInt<u8, 24, Nct>>(8);
}

// u16 backing: widths 1, 2, 4 (16 … 64 bits) in a capacity-12 carrier.
#[test]
fn u16_backed_widths_match_fixeduint() {
    assert_carrier_parity::<FixedUInt<u16, 1>, HeaplessBigInt<u16, 12, Nct>>(1);
    assert_carrier_parity::<FixedUInt<u16, 2>, HeaplessBigInt<u16, 12, Nct>>(2);
    assert_carrier_parity::<FixedUInt<u16, 4>, HeaplessBigInt<u16, 12, Nct>>(4);
}

// u32 backing: widths 1, 2 (32 … 64 bits) in a capacity-6 carrier.
#[test]
fn u32_backed_widths_match_fixeduint() {
    assert_carrier_parity::<FixedUInt<u32, 1>, HeaplessBigInt<u32, 6, Nct>>(1);
    assert_carrier_parity::<FixedUInt<u32, 2>, HeaplessBigInt<u32, 6, Nct>>(2);
}
