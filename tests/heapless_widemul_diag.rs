//! `HeaplessBigInt::wide_mul` (CarryingMul) splits its (lo, hi) product
//! at the operands' VALUE width (`max(len)` words = `bits_precision`),
//! NOT at CAP. modmath's wide-REDC reconstructs `hi·2^(len·word_bits) +
//! lo`, so a CAP split on a sub-capacity field (`len < CAP`) would
//! strand the high half in `lo` and break the REDC (the RSA bug).
//!
//! The full-product VALUE matches FixedUInt, but the (lo, hi) *split
//! boundary* does not for sub-CAP operands — FixedUInt<N> always splits
//! at N, HeaplessBigInt splits at the value width. So we check the split
//! shape directly, not limb-for-limb parity with FixedUInt.

#![cfg(feature = "heapless-runtime-len")]

use const_num_traits::{CarryingMul, Nct, Zero};
use fixed_bigint::HeaplessBigInt;

type H8 = HeaplessBigInt<u32, 8, Nct>;
type H4 = HeaplessBigInt<u32, 4, Nct>;

#[test]
fn wide_mul_splits_at_value_width_rsa_repro() {
    // RSA repro: two len-2 operands in an 8-word carrier.
    // a = 0x1000_0000_0000_0003, b = 0x2_0000_0005.
    // full product = [15, 1342177286, 536870912, 0] (128-bit).
    let a = H8::from_limbs([0x0000_0003, 0x1000_0000, 0, 0, 0, 0, 0, 0], 2);
    let b = H8::from_limbs([0x5, 0x2, 0, 0, 0, 0, 0, 0], 2);
    let (lo, hi) = a.carrying_mul(b, <H8 as Zero>::zero());

    // Split at value width W=2: low 2 words in lo, high 2 words in hi.
    assert_eq!(lo.len(), 2, "lo width == value width (2 words)");
    assert_eq!(hi.len(), 2);
    assert_eq!(lo.limbs(), &[15, 1342177286]);
    assert_eq!(hi.limbs(), &[536870912, 0]);
}

#[test]
fn wide_mul_split_follows_len_not_cap() {
    // Same len-2 operands in a len-4 vs len-8 carrier must give the SAME
    // split (at value width 2) — the boundary tracks len, not CAP.
    let a8 = H8::from_limbs([7, 3, 0, 0, 0, 0, 0, 0], 2);
    let b8 = H8::from_limbs([9, 5, 0, 0, 0, 0, 0, 0], 2);
    let (lo8, hi8) = a8.carrying_mul(b8, <H8 as Zero>::zero());

    let a4 = H4::from_limbs([7, 3, 0, 0], 2);
    let b4 = H4::from_limbs([9, 5, 0, 0], 2);
    let (lo4, hi4) = a4.carrying_mul(b4, <H4 as Zero>::zero());

    assert_eq!(lo8.len(), 2);
    assert_eq!(hi8.len(), 2);
    assert_eq!(lo8.limbs(), lo4.limbs());
    assert_eq!(hi8.limbs(), hi4.limbs());
}

#[test]
fn wide_mul_high_half_lands_in_hi() {
    // 0xFFFF_FFFF * 2 at len 1 = 0x1_FFFF_FFFE. Value width 1 → the
    // carry bit is the high half → hi = 1 (not stranded in lo).
    let a = H8::from_limbs([0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0], 1);
    let b = H8::from_limbs([2, 0, 0, 0, 0, 0, 0, 0], 1);
    let (lo, hi) = a.carrying_mul(b, <H8 as Zero>::zero());
    assert_eq!(lo.len(), 1);
    assert_eq!(hi.len(), 1);
    assert_eq!(lo.limbs()[0], 0xFFFF_FFFE);
    assert_eq!(hi.limbs()[0], 1);
}
