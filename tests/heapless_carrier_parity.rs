//! `HeaplessBigInt` inherits `FixedUInt`'s tested behavior by construction.
//!
//! A value carried at `len = k` is a `k`-word integer of width
//! `k · word_bits`, so it must return bit-for-bit what the same-width
//! `FixedUInt` returns — value AND flag — on every op. `CAP` is
//! allocation; the words beyond `len` do not exist for arithmetic.
//!
//! `FixedUInt` is the trusted reference (it carries fixed-bigint's own
//! arithmetic suite); a `WidthCarrier` trait (build at a width / read the
//! full byte value back) drives both types through one
//! [`assert_carrier_parity`]. Comparison is over the full little-endian
//! byte value, so widths are NOT capped at 64 bits: the sub-capacity
//! multi-limb configs downstream actually deploys — notably
//! `HeaplessBigInt<u32, 16>` at `len 8` (a 255/256-bit value in a 512-bit
//! carrier, the Ed25519 verify carrier) — are exercised against the
//! matching `FixedUInt<u32, 8>` here.

#![cfg(all(feature = "heapless-runtime-len", feature = "num-traits"))]

use const_num_traits::{
    BitWidth, BitsPrecision, CarryingMul, CheckedAdd, CheckedMul, FromByteSlice, Nct,
    OverflowingAdd, OverflowingMul, OverflowingSub, WrappingAdd, WrappingMul, WrappingSub,
};
use fixed_bigint::{FixedUInt, HeaplessBigInt};

/// Byte buffer wide enough for any value or wide product under test
/// (512-bit operands → 1024-bit `carrying_mul` result = 128 bytes).
const BUF: usize = 128;

/// A fixed-width unsigned these differential tests can drive: build a value
/// at a chosen word-width from little-endian bytes, and read the full value
/// back as little-endian bytes. `FixedUInt<T, N>`'s width is its `N`;
/// `HeaplessBigInt<T, CAP>` constructs at `len = width`.
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
    + CarryingMul<Unsigned = Self, Output = Self>
    + core::ops::Div<Output = Self>
    + core::ops::Rem<Output = Self>
    + core::ops::Shl<usize, Output = Self>
    + core::ops::Shr<usize, Output = Self>
    + core::ops::BitAnd<Output = Self>
    + core::ops::BitOr<Output = Self>
    + PartialOrd
    + BitWidth
    + BitsPrecision
{
    const WORD_BYTES: usize;
    fn make_le(bytes: &[u8], width_words: usize) -> Self;
    fn read_le(&self, out: &mut [u8; BUF]);
}

macro_rules! impl_carrier {
    (fixed $t:ty) => {
        impl<const N: usize> WidthCarrier for FixedUInt<$t, N, Nct> {
            const WORD_BYTES: usize = core::mem::size_of::<$t>();
            fn make_le(bytes: &[u8], width_words: usize) -> Self {
                assert_eq!(width_words, N, "FixedUInt<T, N> width is fixed at N");
                FromByteSlice::from_le_slice(&bytes[..N * Self::WORD_BYTES]).unwrap()
            }
            fn read_le(&self, out: &mut [u8; BUF]) {
                *out = [0u8; BUF];
                self.to_le_bytes_fixed(out);
            }
        }
    };
    (heapless $t:ty) => {
        impl<const CAP: usize> WidthCarrier for HeaplessBigInt<$t, CAP, Nct> {
            const WORD_BYTES: usize = core::mem::size_of::<$t>();
            fn make_le(bytes: &[u8], width_words: usize) -> Self {
                HeaplessBigInt::from_le_bytes(&bytes[..width_words * Self::WORD_BYTES])
            }
            fn read_le(&self, out: &mut [u8; BUF]) {
                *out = [0u8; BUF];
                self.to_le_bytes(out);
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

/// Byte-pattern operands of `width_bytes` significant bytes. Multi-limb
/// patterns (not just u64-range values) so the wide configs are real.
fn value_seeds(width_bytes: usize) -> Vec<[u8; BUF]> {
    let mut out = Vec::new();
    let mut push = |f: &dyn Fn(usize) -> u8| {
        let mut b = [0u8; BUF];
        for i in 0..width_bytes {
            b[i] = f(i);
        }
        out.push(b);
    };
    push(&|_| 0); // zero
    push(&|i| if i == 0 { 1 } else { 0 }); // one
    push(&|i| if i == 0 { 2 } else { 0 }); // two
    push(&|_| 0xFF); // all ones
    push(&|i| if i + 1 == width_bytes { 0x80 } else { 0 }); // high bit only
    push(&|i| if i % 2 == 0 { 0xA5 } else { 0x5A }); // alternating
    push(&|i| (i as u8).wrapping_mul(37).wrapping_add(3)); // ramp
    push(&|i| 0xED ^ (i as u8)); // curve-ish spread
    push(&|i| if i + 1 == width_bytes { 0x7F } else { 0xFF }); // just under all-ones (p-like)
    out
}

fn is_zero(seed: &[u8; BUF], width_bytes: usize) -> bool {
    seed[..width_bytes].iter().all(|&b| b == 0)
}

/// Assert `F` (fixed-width reference) and `H` (carrier under test) agree on
/// every op at `width_words`, comparing full byte values (and flags).
fn assert_carrier_parity<F, H>(width_words: usize)
where
    F: WidthCarrier,
    H: WidthCarrier,
{
    assert_eq!(F::WORD_BYTES, H::WORD_BYTES);
    let width_bytes = width_words * F::WORD_BYTES;
    let seeds = value_seeds(width_bytes);
    let f = |s: &[u8; BUF]| F::make_le(s, width_words);
    let h = |s: &[u8; BUF]| H::make_le(s, width_words);

    // Compare the full byte value of a fixed result against a heapless one.
    let eq = |fv: &F, hv: &H, msg: &str| {
        let (mut fb, mut hb) = ([0u8; BUF], [0u8; BUF]);
        fv.read_le(&mut fb);
        hv.read_le(&mut hb);
        assert!(
            fb == hb,
            "{msg} @ width {width_bytes}B\n fixed={fb:02x?}\n  heap={hb:02x?}"
        );
    };
    let zero_f = F::make_le(&[0u8; BUF], width_words);
    let zero_h = H::make_le(&[0u8; BUF], width_words);

    // The width a value REPORTS: `bits_precision` is the operating width
    // modmath's reducer reads for R / n_prime. It must be the true width
    // (`width_bytes * 8`), never a size_of-inflated capacity — the exact
    // misread the historical Ed25519 reduce bug came from.
    assert_eq!(
        BitsPrecision::bits_precision(&h(&seeds[1])),
        (width_bytes * 8) as u32,
        "heapless bits_precision must be the width, not capacity"
    );
    assert_eq!(
        BitsPrecision::bits_precision(&f(&seeds[1])),
        BitsPrecision::bits_precision(&h(&seeds[1])),
        "bits_precision parity @ width {width_bytes}B"
    );

    // Unary: bit_width, shifts.
    for sa in &seeds {
        assert_eq!(
            BitWidth::bit_width(f(sa)),
            BitWidth::bit_width(h(sa)),
            "bit_width @ width {width_bytes}B"
        );
        let width_bits = width_bytes * 8;
        for &sh in &[
            0usize,
            1,
            width_bits / 2,
            width_bits.saturating_sub(1),
            width_bits,
        ] {
            eq(&(f(sa) << sh), &(h(sa) << sh), "shl");
            eq(&(f(sa) >> sh), &(h(sa) >> sh), "shr");
        }
    }

    // Binary.
    for sa in &seeds {
        for sb in &seeds {
            eq(
                &WrappingAdd::wrapping_add(f(sa), f(sb)),
                &WrappingAdd::wrapping_add(h(sa), h(sb)),
                "wrapping_add",
            );
            eq(
                &WrappingSub::wrapping_sub(f(sa), f(sb)),
                &WrappingSub::wrapping_sub(h(sa), h(sb)),
                "wrapping_sub",
            );
            eq(
                &WrappingMul::wrapping_mul(f(sa), f(sb)),
                &WrappingMul::wrapping_mul(h(sa), h(sb)),
                "wrapping_mul",
            );

            let (fa, ffl) = OverflowingAdd::overflowing_add(f(sa), f(sb));
            let (ha, hfl) = OverflowingAdd::overflowing_add(h(sa), h(sb));
            assert_eq!(ffl, hfl, "overflowing_add flag @ width {width_bytes}B");
            eq(&fa, &ha, "overflowing_add value");

            let (fs, fsb) = OverflowingSub::overflowing_sub(f(sa), f(sb));
            let (hs, hsb) = OverflowingSub::overflowing_sub(h(sa), h(sb));
            assert_eq!(fsb, hsb, "overflowing_sub flag @ width {width_bytes}B");
            eq(&fs, &hs, "overflowing_sub value");

            let (fp, fpo) = OverflowingMul::overflowing_mul(f(sa), f(sb));
            let (hp, hpo) = OverflowingMul::overflowing_mul(h(sa), h(sb));
            assert_eq!(fpo, hpo, "overflowing_mul flag @ width {width_bytes}B");
            eq(&fp, &hp, "overflowing_mul value");

            // carrying_mul (WideMul): both halves must match. This is the
            // op modmath's wide-REDC reduces through.
            let (flo, fhi) = CarryingMul::carrying_mul(f(sa), f(sb), zero_f);
            let (hlo, hhi) = CarryingMul::carrying_mul(h(sa), h(sb), zero_h);
            eq(&flo, &hlo, "carrying_mul lo");
            eq(&fhi, &hhi, "carrying_mul hi");

            assert_eq!(
                CheckedAdd::checked_add(f(sa), f(sb)).is_some(),
                CheckedAdd::checked_add(h(sa), h(sb)).is_some(),
                "checked_add some @ width {width_bytes}B"
            );
            assert_eq!(
                CheckedMul::checked_mul(f(sa), f(sb)).is_some(),
                CheckedMul::checked_mul(h(sa), h(sb)).is_some(),
                "checked_mul some @ width {width_bytes}B"
            );

            eq(&(f(sa) & f(sb)), &(h(sa) & h(sb)), "bitand");
            eq(&(f(sa) | f(sb)), &(h(sa) | h(sb)), "bitor");

            assert_eq!(
                f(sa).partial_cmp(&f(sb)),
                h(sa).partial_cmp(&h(sb)),
                "cmp @ width {width_bytes}B"
            );

            if !is_zero(sb, width_bytes) {
                eq(&(f(sa) / f(sb)), &(h(sa) / h(sb)), "div");
                eq(&(f(sa) % f(sb)), &(h(sa) % h(sb)), "rem");
            }
        }
    }

    let _ = (zero_f, zero_h);
}

// u8 backing in a capacity-24 carrier: widths 1, 2, 8, 16, 24 (up to len==CAP).
#[test]
fn u8_backed_widths_match_fixeduint() {
    assert_carrier_parity::<FixedUInt<u8, 1>, HeaplessBigInt<u8, 24, Nct>>(1);
    assert_carrier_parity::<FixedUInt<u8, 2>, HeaplessBigInt<u8, 24, Nct>>(2);
    assert_carrier_parity::<FixedUInt<u8, 8>, HeaplessBigInt<u8, 24, Nct>>(8);
    assert_carrier_parity::<FixedUInt<u8, 16>, HeaplessBigInt<u8, 24, Nct>>(16);
    assert_carrier_parity::<FixedUInt<u8, 24>, HeaplessBigInt<u8, 24, Nct>>(24);
}

// u16 backing in a capacity-16 carrier: widths 1, 4, 8, 16.
#[test]
fn u16_backed_widths_match_fixeduint() {
    assert_carrier_parity::<FixedUInt<u16, 1>, HeaplessBigInt<u16, 16, Nct>>(1);
    assert_carrier_parity::<FixedUInt<u16, 4>, HeaplessBigInt<u16, 16, Nct>>(4);
    assert_carrier_parity::<FixedUInt<u16, 8>, HeaplessBigInt<u16, 16, Nct>>(8);
    assert_carrier_parity::<FixedUInt<u16, 16>, HeaplessBigInt<u16, 16, Nct>>(16);
}

// u32 backing in a capacity-16 carrier: widths 1, 2, 4, and 8 — the last is
// the Ed25519 verify config (255/256-bit value at len 8, sub-CAP 16, Nct).
#[test]
fn u32_backed_widths_match_fixeduint() {
    assert_carrier_parity::<FixedUInt<u32, 1>, HeaplessBigInt<u32, 16, Nct>>(1);
    assert_carrier_parity::<FixedUInt<u32, 2>, HeaplessBigInt<u32, 16, Nct>>(2);
    assert_carrier_parity::<FixedUInt<u32, 4>, HeaplessBigInt<u32, 16, Nct>>(4);
    assert_carrier_parity::<FixedUInt<u32, 8>, HeaplessBigInt<u32, 16, Nct>>(8);
}
