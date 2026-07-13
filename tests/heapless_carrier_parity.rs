//! Width-model regression: a `HeaplessBigInt<u8, CAP>` value carried at
//! `len = k` has **width `k · word_bits`** (per the bit-vocabulary
//! canon), so it must behave like the fixed-width `FixedUInt<u8, k>` —
//! *not* like `FixedUInt<u8, CAP>`. `CAP` is capacity, invisible to
//! arithmetic; the operating width is the constructed `len`.
//!
//! This is the corrected form of an earlier test that wrongly expected
//! CAP-width / FixedUInt<u8,CAP> parity at every len. Grew out of a
//! Montgomery-multiply hunt whose real lesson was the width vs capacity
//! distinction.

#![cfg(all(feature = "heapless-runtime-len", feature = "num-traits"))]

use const_num_traits::{Nct, OverflowingSub, WrappingAdd, WrappingMul};
use fixed_bigint::{FixedUInt, HeaplessBigInt};
use num_traits::ToPrimitive;

type H = HeaplessBigInt<u8, 4, Nct>;

fn h_val(v: &H) -> u64 {
    let mut buf = [0u8; 4];
    let s = v.to_le_bytes(&mut buf);
    let mut acc = 0u64;
    for (i, b) in s.iter().enumerate() {
        acc |= (*b as u64) << (8 * i);
    }
    acc
}

// A value carried at width = k bytes.
fn h(val: u32, k: u16) -> H {
    let b = val.to_le_bytes();
    let mut limbs = [0u8; 4];
    limbs[..k as usize].copy_from_slice(&b[..k as usize]);
    H::from_limbs(limbs, k)
}

// The wrapping/overflowing ops all wrap at the operand value width, so
// each matches the same-width FixedUInt: sub's underflow-wrap,
// wrapping_add's carry-out discard, and wrapping_mul's high-half
// truncation are all fixed-width-at-`len` behaviors. (The *growing*
// variants — core::ops::+/*, checked_* — are a separate carrier feature,
// not exercised here; this file pins the value-width equivalence.)
macro_rules! width_parity {
    ($k:literal, $fixed:ty) => {{
        let mask: u32 = if $k == 4 {
            u32::MAX
        } else {
            (1u32 << (8 * $k)) - 1
        };
        let vals: [u32; 6] = [0, 1, 5, 7, 0x7F, 0xFF];
        for &a in &vals {
            for &b in &vals {
                let (a, b) = (a & mask, b & mask);

                let (hd, hb) = OverflowingSub::overflowing_sub(h(a, $k), h(b, $k));
                let (fd, fb) =
                    OverflowingSub::overflowing_sub(<$fixed>::from(a), <$fixed>::from(b));
                assert_eq!(
                    (h_val(&hd), hb),
                    (fd.to_u64().unwrap(), fb),
                    "sub {a}-{b} width={} bytes",
                    $k
                );

                let hs = WrappingAdd::wrapping_add(h(a, $k), h(b, $k));
                let fs = WrappingAdd::wrapping_add(<$fixed>::from(a), <$fixed>::from(b));
                assert_eq!(
                    h_val(&hs),
                    fs.to_u64().unwrap(),
                    "wrapping_add {a}+{b} width={} bytes",
                    $k
                );

                let hm = WrappingMul::wrapping_mul(h(a, $k), h(b, $k));
                let fm = WrappingMul::wrapping_mul(<$fixed>::from(a), <$fixed>::from(b));
                assert_eq!(
                    h_val(&hm),
                    fm.to_u64().unwrap(),
                    "wrapping_mul {a}*{b} width={} bytes",
                    $k
                );
            }
        }
    }};
}

#[test]
fn heapless_at_len_k_matches_fixeduint_of_width_k() {
    // width = len·8: HeaplessBigInt<u8,4> sub / wrapping_add / wrapping_mul
    // at len 1/2/4 wrap like FixedUInt<u8,1>/<u8,2>/<u8,4> — capacity 4
    // never enters.
    width_parity!(1u16, FixedUInt<u8, 1>);
    width_parity!(2u16, FixedUInt<u8, 2>);
    width_parity!(4u16, FixedUInt<u8, 4>);
}
