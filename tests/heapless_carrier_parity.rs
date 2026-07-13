//! Width-model regression: a `HeaplessBigInt<u8, CAP>` value carried at
//! `len = k` is a `k`-word integer of width `k · word_bits`, so every
//! arithmetic op must return bit-for-bit what `FixedUInt<u8, k>` returns
//! — wrapped value AND overflow/borrow flag alike. `CAP` is allocation,
//! invisible to arithmetic; the words beyond `len` do not exist. This
//! pins that equivalence across sub / wrapping_add / wrapping_mul /
//! overflowing_add / overflowing_mul / checked_add / checked_mul at
//! widths 1, 2, 4 inside a capacity-4 carrier.

#![cfg(all(feature = "heapless-runtime-len", feature = "num-traits"))]

use const_num_traits::{
    CheckedAdd, CheckedMul, Nct, OverflowingAdd, OverflowingMul, OverflowingSub, WrappingAdd,
    WrappingMul,
};
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

                // Overflowing add/mul: wrapped value AND the overflow flag
                // must both match the same-width FixedUInt.
                let (ha, hac) = OverflowingAdd::overflowing_add(h(a, $k), h(b, $k));
                let (fa, fac) =
                    OverflowingAdd::overflowing_add(<$fixed>::from(a), <$fixed>::from(b));
                assert_eq!(
                    (h_val(&ha), hac),
                    (fa.to_u64().unwrap(), fac),
                    "overflowing_add {a}+{b} width={} bytes",
                    $k
                );

                let (hp, hpo) = OverflowingMul::overflowing_mul(h(a, $k), h(b, $k));
                let (fp, fpo) =
                    OverflowingMul::overflowing_mul(<$fixed>::from(a), <$fixed>::from(b));
                assert_eq!(
                    (h_val(&hp), hpo),
                    (fp.to_u64().unwrap(), fpo),
                    "overflowing_mul {a}*{b} width={} bytes",
                    $k
                );

                // Checked add/mul: None iff FixedUInt is None, else equal.
                let hca = CheckedAdd::checked_add(h(a, $k), h(b, $k)).map(|v| h_val(&v));
                let fca = CheckedAdd::checked_add(<$fixed>::from(a), <$fixed>::from(b))
                    .map(|v| v.to_u64().unwrap());
                assert_eq!(hca, fca, "checked_add {a}+{b} width={} bytes", $k);

                let hcm = CheckedMul::checked_mul(h(a, $k), h(b, $k)).map(|v| h_val(&v));
                let fcm = CheckedMul::checked_mul(<$fixed>::from(a), <$fixed>::from(b))
                    .map(|v| v.to_u64().unwrap());
                assert_eq!(hcm, fcm, "checked_mul {a}*{b} width={} bytes", $k);
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
