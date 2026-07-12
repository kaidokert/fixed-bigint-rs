//! Sketch-level sanity tests: constructors work, Add/Sub/Mul produce
//! correct values against small u16/u32 inputs, PartialEq is
//! value-based across shapes, Zero/One/Default line up, and Ct paths
//! (subtle::ConstantTimeEq) agree with the value.

#![cfg(feature = "heapless-runtime-len")]

// `WrappingAdd`/`WrappingSub`/`OverflowingAdd`/`OverflowingSub` are used
// via fully-qualified paths below because they shadow the inherent
// methods on `HeaplessBigInt` when in scope — the existing `.wrapping_add(&b)`
// callers need the inherent to win method resolution.
use const_num_traits::ops::ct::CtIsZero;
use const_num_traits::{Ct, Nct, One, Parity, Zero};
use fixed_bigint::HeaplessBigInt;
use subtle::{
    Choice, ConditionallySelectable, ConstantTimeEq, ConstantTimeGreater, ConstantTimeLess,
};

type H8Nct = HeaplessBigInt<u8, 8, Nct>;
type H8Ct = HeaplessBigInt<u8, 8, Ct>;
type H4u32Nct = HeaplessBigInt<u32, 4, Nct>;

// ── Constructors ──

#[test]
fn zero_has_len_zero() {
    let z = <H8Nct as Zero>::zero();
    assert_eq!(z.len(), 0);
    assert!(z.is_empty());
    assert!(<H8Nct as Zero>::is_zero(&z));
}

#[test]
fn one_has_len_one_and_top_limb_one() {
    let o = <H8Nct as One>::one();
    assert_eq!(o.len(), 1);
    assert_eq!(o.limbs(), &[1u8]);
}

#[test]
fn default_equals_zero() {
    let d = H8Nct::default();
    let z = <H8Nct as Zero>::zero();
    assert_eq!(d.len(), z.len());
    assert_eq!(d, z);
}

#[test]
fn zero_full_cap_len_equals_cap() {
    let f = H8Nct::zero_full_cap();
    assert_eq!(f.len(), 8);
    assert_eq!(f.capacity(), 8);
    // Value-equal to Zero despite different shape.
    let z = <H8Nct as Zero>::zero();
    assert_eq!(f, z);
}

#[test]
fn from_limbs_preserves_shape() {
    let v = H4u32Nct::from_limbs([0x1234, 0x5678, 0, 0], 2);
    assert_eq!(v.len(), 2);
    assert_eq!(v.limbs(), &[0x1234, 0x5678]);
}

#[test]
#[should_panic]
fn from_limbs_rejects_nonzero_tail_in_debug() {
    // In release this passes silently (debug_assert only).
    let _ = H4u32Nct::from_limbs([1, 0, 42, 0], 1);
}

// ── Add / Sub ──

#[test]
fn add_small_values() {
    let a = H4u32Nct::from_limbs([100, 0, 0, 0], 1);
    let b = H4u32Nct::from_limbs([200, 0, 0, 0], 1);
    let s = a.wrapping_add(&b);
    assert_eq!(s.limbs()[0], 300);
}

#[test]
fn add_cross_limb_carry() {
    // (u32::MAX) + 1 = 0x1_0000_0000, spans two limbs.
    let a = H4u32Nct::from_limbs([u32::MAX, 0, 0, 0], 1);
    let b = H4u32Nct::from_limbs([1, 0, 0, 0], 1);
    let s = a.wrapping_add(&b);
    // Output len is max(1, 1) + 1 = 2.
    assert_eq!(s.len(), 2);
    assert_eq!(s.limbs()[0], 0);
    assert_eq!(s.limbs()[1], 1);
}

#[test]
fn add_overflows_when_natural_len_exceeds_cap() {
    // 2 CAP=4 32-bit values whose sum needs 5 limbs.
    let max = H4u32Nct::from_limbs([u32::MAX; 4], 4);
    let one = <H4u32Nct as One>::one();
    let (_wrapped, overflow) = max.overflowing_add(&one);
    assert!(
        overflow,
        "expected overflow when natural sum needs CAP+1 limbs"
    );
    assert_eq!(max.checked_add(&one), None);
}

#[test]
fn sub_within_range() {
    let a = H4u32Nct::from_limbs([300, 0, 0, 0], 1);
    let b = H4u32Nct::from_limbs([100, 0, 0, 0], 1);
    let d = a.wrapping_sub(&b);
    assert_eq!(d.limbs()[0], 200);
}

#[test]
fn sub_underflow_wraps_and_flags() {
    let a = H4u32Nct::from_limbs([1, 0, 0, 0], 1);
    let b = H4u32Nct::from_limbs([2, 0, 0, 0], 1);
    let (wrapped, borrow) = a.overflowing_sub(&b);
    assert!(borrow, "expected borrow on underflow");
    assert_eq!(wrapped.limbs()[0], u32::MAX);
    assert_eq!(a.checked_sub(&b), None);
}

// ── Mul ──

#[test]
fn mul_small_product_fits() {
    let a = H4u32Nct::from_limbs([100, 0, 0, 0], 1);
    let b = H4u32Nct::from_limbs([200, 0, 0, 0], 1);
    let p = a.wrapping_mul(&b);
    // Output len = min(1 + 1, 4) = 2. Value = 20_000 fits in limb 0.
    assert_eq!(p.len(), 2);
    assert_eq!(p.limbs()[0], 20_000);
    assert_eq!(p.limbs()[1], 0);
}

#[test]
fn mul_cross_limb_carry() {
    // 0x1_0000 * 0x1_0000 = 0x1_0000_0000, straddles limb boundary.
    let a = H4u32Nct::from_limbs([0x1_0000, 0, 0, 0], 1);
    let b = H4u32Nct::from_limbs([0x1_0000, 0, 0, 0], 1);
    let p = a.wrapping_mul(&b);
    assert_eq!(p.limbs()[0], 0);
    assert_eq!(p.limbs()[1], 1);
}

#[test]
fn mul_overflow_when_natural_len_exceeds_cap() {
    // len=3 * len=3 → natural product needs 6 limbs; CAP=4.
    let a = H4u32Nct::from_limbs([1, 1, 1, 0], 3);
    let b = H4u32Nct::from_limbs([1, 1, 1, 0], 3);
    let (_wrapped, overflow) = a.overflowing_mul(&b);
    assert!(
        overflow,
        "expected overflow when natural product exceeds CAP"
    );
    assert_eq!(a.checked_mul(&b), None);
}

// ── PartialEq / PartialOrd (value-based) ──

#[test]
fn eq_across_shapes_when_values_match() {
    let a = <H4u32Nct as Zero>::zero(); // len = 0
    let b = H4u32Nct::from_limbs([0, 0, 0, 0], 4); // len = 4 (all-zero)
    assert_eq!(a, b, "value-based Eq: both represent mathematical zero");
}

#[test]
fn eq_distinct_values_differ() {
    let a = H4u32Nct::from_limbs([1, 0, 0, 0], 1);
    let b = H4u32Nct::from_limbs([2, 0, 0, 0], 1);
    assert_ne!(a, b);
}

#[test]
fn ord_less_greater() {
    let a = H4u32Nct::from_limbs([100, 0, 0, 0], 1);
    let b = H4u32Nct::from_limbs([200, 0, 0, 0], 1);
    assert!(a < b);
    assert!(b > a);
}

#[test]
fn ord_by_highest_limb() {
    let a = H4u32Nct::from_limbs([u32::MAX, 0, 0, 0], 1);
    let b = H4u32Nct::from_limbs([0, 1, 0, 0], 2);
    // b has a bit set in limb 1, so b > a even though a's limb 0 > b's.
    assert!(b > a);
}

// ── Ct-personality carriers ──
//
// The impls are shared across Nct/Ct (personality dispatch enters only
// when the output shape differs). Sanity-check that Ct-typed values
// arithmetic works and produces the same values.

#[test]
fn ct_add_matches_nct() {
    let a_ct = HeaplessBigInt::<u32, 4, Ct>::from_limbs([100, 0, 0, 0], 1);
    let b_ct = HeaplessBigInt::<u32, 4, Ct>::from_limbs([200, 0, 0, 0], 1);
    let s_ct = a_ct.wrapping_add(&b_ct);
    assert_eq!(s_ct.limbs()[0], 300);
}

#[test]
fn ct_eq_agrees_with_partial_eq() {
    let a = H8Ct::from_limbs([1, 2, 3, 0, 0, 0, 0, 0], 3);
    let b = H8Ct::from_limbs([1, 2, 3, 0, 0, 0, 0, 0], 3);
    let c = H8Ct::from_limbs([1, 2, 4, 0, 0, 0, 0, 0], 3);
    assert_eq!(bool::from(a.ct_eq(&b)), true);
    assert_eq!(bool::from(a.ct_eq(&c)), false);
    assert!(a == b);
    assert!(a != c);
}

#[test]
fn ct_eq_across_shapes() {
    // Same-value, different-shape operands agree under Ct equality too.
    let a = H8Ct::zero_full_cap();
    let b = <H8Ct as Zero>::zero();
    assert_eq!(bool::from(a.ct_eq(&b)), true);
}

// ── subtle::ConditionallySelectable ──

#[test]
fn cselect_choice_1_returns_b() {
    let a = H4u32Nct::from_limbs([100, 0, 0, 0], 1);
    let b = H4u32Nct::from_limbs([200, 0, 0, 0], 1);
    let out = H4u32Nct::conditional_select(&a, &b, Choice::from(1u8));
    assert_eq!(out, b);
}

#[test]
fn cselect_choice_0_returns_a() {
    let a = H4u32Nct::from_limbs([100, 0, 0, 0], 1);
    let b = H4u32Nct::from_limbs([200, 0, 0, 0], 1);
    let out = H4u32Nct::conditional_select(&a, &b, Choice::from(0u8));
    assert_eq!(out, a);
}

#[test]
fn cselect_output_len_is_max_of_operand_lens() {
    // a.len = 1, b.len = 3 → out.len = 3 regardless of choice.
    let a = H4u32Nct::from_limbs([100, 0, 0, 0], 1);
    let b = H4u32Nct::from_limbs([1, 2, 3, 0], 3);
    let out_a = H4u32Nct::conditional_select(&a, &b, Choice::from(0u8));
    let out_b = H4u32Nct::conditional_select(&a, &b, Choice::from(1u8));
    assert_eq!(out_a.len(), 3);
    assert_eq!(out_b.len(), 3);
    // Value-check: choice=0 picks a's limbs, higher limbs come from a's
    // zero tail, so the value is still 100.
    assert_eq!(out_a.limbs(), &[100, 0, 0]);
    assert_eq!(out_b.limbs(), &[1, 2, 3]);
}

#[test]
fn cselect_preserves_zero_tail() {
    let a = H4u32Nct::from_limbs([0xAAAAAAAA, 0xBBBBBBBB, 0, 0], 2);
    let b = H4u32Nct::from_limbs([0xCCCCCCCC, 0xDDDDDDDD, 0, 0], 2);
    let out = H4u32Nct::conditional_select(&a, &b, Choice::from(1u8));
    // limbs beyond len must remain zero.
    assert_eq!(out.all_limbs()[2], 0);
    assert_eq!(out.all_limbs()[3], 0);
}

// ── CtIsZero ──

#[test]
fn ct_is_zero_true_for_zero_shapes() {
    let z = <H4u32Nct as Zero>::zero();
    let f = H4u32Nct::zero_full_cap();
    let s = H4u32Nct::from_limbs([0, 0, 0, 0], 4);
    assert!(bool::from(z.ct_is_zero()));
    assert!(bool::from(f.ct_is_zero()));
    assert!(bool::from(s.ct_is_zero()));
}

#[test]
fn ct_is_zero_false_for_nonzero() {
    let a = H4u32Nct::from_limbs([1, 0, 0, 0], 1);
    let b = H4u32Nct::from_limbs([0, 1, 0, 0], 2);
    assert!(!bool::from(a.ct_is_zero()));
    assert!(!bool::from(b.ct_is_zero()));
}

// ── ConstantTimeGreater / ConstantTimeLess ──

#[test]
fn ct_gt_matches_partial_ord() {
    let a = H4u32Nct::from_limbs([100, 0, 0, 0], 1);
    let b = H4u32Nct::from_limbs([200, 0, 0, 0], 1);
    assert!(!bool::from(a.ct_gt(&b)));
    assert!(bool::from(b.ct_gt(&a)));
    assert!(!bool::from(a.ct_gt(&a)));
}

#[test]
fn ct_gt_across_lens() {
    // b has a bit in limb 1 → b > a even though a's limb 0 > b's.
    let a = H4u32Nct::from_limbs([u32::MAX, 0, 0, 0], 1);
    let b = H4u32Nct::from_limbs([0, 1, 0, 0], 2);
    assert!(bool::from(b.ct_gt(&a)));
    assert!(!bool::from(a.ct_gt(&b)));
    assert!(bool::from(a.ct_lt(&b)));
    assert!(!bool::from(b.ct_lt(&a)));
}

#[test]
fn ct_lt_and_eq_partition_ordering() {
    let a = H4u32Nct::from_limbs([5, 0, 0, 0], 1);
    let b = H4u32Nct::from_limbs([7, 0, 0, 0], 1);
    // Exactly one of {a<b, a==b, a>b} holds.
    let lt = bool::from(a.ct_lt(&b));
    let eq = bool::from(a.ct_eq(&b));
    let gt = bool::from(a.ct_gt(&b));
    assert_eq!(lt as u8 + eq as u8 + gt as u8, 1);
    assert!(lt);
}

// ── Shl ──

#[test]
fn shl_by_zero_is_identity() {
    let a = H4u32Nct::from_limbs([0xDEADBEEF, 0, 0, 0], 1);
    let b = a << 0;
    assert_eq!(a, b);
    assert_eq!(a.len(), b.len());
}

#[test]
fn shl_within_a_limb() {
    let a = H4u32Nct::from_limbs([0x0000_00AB, 0, 0, 0], 1);
    let b = a << 8;
    // 0xAB << 8 = 0xAB00, still fits in limb 0.
    assert_eq!(b.limbs()[0], 0x0000_AB00);
}

#[test]
fn shl_crosses_a_limb() {
    // Shift a byte at bit position 24 by 8 → carries into limb 1.
    let a = H4u32Nct::from_limbs([0xAB000000, 0, 0, 0], 1);
    let b = a << 8;
    // Low limb: top byte 0xAB shifts out, low bytes are 0. New limb 0 = 0.
    // High limb: 0xAB now in the low byte of limb 1.
    assert_eq!(b.limbs()[0], 0);
    assert_eq!(b.limbs()[1], 0x000000AB);
    assert_eq!(b.len(), 2);
}

#[test]
fn shl_by_full_word() {
    let a = H4u32Nct::from_limbs([1, 2, 0, 0], 2);
    let b = a << 32;
    assert_eq!(b.limbs()[0], 0);
    assert_eq!(b.limbs()[1], 1);
    assert_eq!(b.limbs()[2], 2);
    // out_len = min(2 + 1 + 0, 4) = 3.
    assert_eq!(b.len(), 3);
}

#[test]
fn shl_beyond_capacity_truncates() {
    let a = H4u32Nct::from_limbs([1, 0, 0, 0], 1);
    // CAP=4, WORD_BITS=32 → 128 bits total. Shift by 128 → zero.
    let b = a << 128;
    assert!(<H4u32Nct as Zero>::is_zero(&b));
    assert_eq!(b.len(), 0);
}

// ── Shr ──

#[test]
fn shr_by_zero_is_identity() {
    let a = H4u32Nct::from_limbs([0xDEADBEEF, 0x12345678, 0, 0], 2);
    let b = a >> 0;
    assert_eq!(a, b);
    assert_eq!(a.len(), b.len());
}

#[test]
fn shr_within_a_limb() {
    let a = H4u32Nct::from_limbs([0x0000_AB00, 0, 0, 0], 1);
    let b = a >> 8;
    assert_eq!(b.limbs()[0], 0x0000_00AB);
}

#[test]
fn shr_crosses_a_limb() {
    let a = H4u32Nct::from_limbs([0, 0x0000_00AB, 0, 0], 2);
    let b = a >> 32;
    assert_eq!(b.limbs()[0], 0x0000_00AB);
    assert_eq!(b.len(), 1);
}

#[test]
fn shr_bit_carries_from_higher_limb() {
    // limb1 = 0x00000001. Shr by 1 puts that bit at the top of limb 0.
    let a = H4u32Nct::from_limbs([0, 1, 0, 0], 2);
    let b = a >> 1;
    assert_eq!(b.limbs()[0], 0x8000_0000);
    // out_len = self.len - word_shift = 2 - 0 = 2.
    assert_eq!(b.len(), 2);
}

#[test]
fn shr_by_more_than_value_bits_zeros() {
    let a = H4u32Nct::from_limbs([0xDEADBEEF, 0, 0, 0], 1);
    let b = a >> 64;
    assert!(<H4u32Nct as Zero>::is_zero(&b));
    assert_eq!(b.len(), 0);
}

// ── Byte serialization ──

#[test]
fn to_be_bytes_single_limb() {
    let v = H4u32Nct::from_limbs([0x12345678, 0, 0, 0], 1);
    let mut buf = [0u8; 4];
    let written = v.to_be_bytes(&mut buf);
    assert_eq!(written, &[0x12, 0x34, 0x56, 0x78]);
}

#[test]
fn to_be_bytes_multiple_limbs_high_first() {
    let v = H4u32Nct::from_limbs([0xAAAAAAAA, 0xBBBBBBBB, 0, 0], 2);
    let mut buf = [0u8; 8];
    let written = v.to_be_bytes(&mut buf);
    // Limb 1 (higher) at the front, limb 0 at the back.
    assert_eq!(written, &[0xBB, 0xBB, 0xBB, 0xBB, 0xAA, 0xAA, 0xAA, 0xAA]);
}

#[test]
fn to_le_bytes_matches_le_convention() {
    let v = H4u32Nct::from_limbs([0x12345678, 0, 0, 0], 1);
    let mut buf = [0u8; 4];
    let written = v.to_le_bytes(&mut buf);
    assert_eq!(written, &[0x78, 0x56, 0x34, 0x12]);
}

#[test]
fn to_bytes_zero_produces_empty_slice() {
    let z = <H4u32Nct as Zero>::zero();
    let mut buf = [0u8; 4];
    let written = z.to_be_bytes(&mut buf);
    assert_eq!(written.len(), 0);
    let written = z.to_le_bytes(&mut buf);
    assert_eq!(written.len(), 0);
}

#[test]
#[should_panic]
fn to_be_bytes_panics_on_undersized_buffer() {
    let v = H4u32Nct::from_limbs([1, 2, 0, 0], 2);
    let mut buf = [0u8; 4]; // needs 8
    let _ = v.to_be_bytes(&mut buf);
}

#[test]
fn from_be_bytes_word_aligned() {
    let v = H4u32Nct::from_be_bytes(&[0x12, 0x34, 0x56, 0x78]);
    assert_eq!(v.len(), 1);
    assert_eq!(v.limbs()[0], 0x12345678);
}

#[test]
fn from_be_bytes_partial_top_word_zero_pads() {
    // 5 bytes = 2 limbs. Low limb has 4 bytes, top limb has 1 byte.
    let v = H4u32Nct::from_be_bytes(&[0xAB, 0x12, 0x34, 0x56, 0x78]);
    assert_eq!(v.len(), 2);
    assert_eq!(v.limbs()[0], 0x12345678);
    assert_eq!(v.limbs()[1], 0x000000AB);
}

#[test]
fn from_le_bytes_word_aligned() {
    let v = H4u32Nct::from_le_bytes(&[0x78, 0x56, 0x34, 0x12]);
    assert_eq!(v.len(), 1);
    assert_eq!(v.limbs()[0], 0x12345678);
}

#[test]
fn from_le_bytes_partial_top_word() {
    let v = H4u32Nct::from_le_bytes(&[0x78, 0x56, 0x34, 0x12, 0xAB]);
    assert_eq!(v.len(), 2);
    assert_eq!(v.limbs()[0], 0x12345678);
    assert_eq!(v.limbs()[1], 0x000000AB);
}

#[test]
fn from_bytes_empty_gives_zero() {
    let v = H4u32Nct::from_be_bytes(&[]);
    assert_eq!(v.len(), 0);
    assert!(<H4u32Nct as Zero>::is_zero(&v));
    let v = H4u32Nct::from_le_bytes(&[]);
    assert_eq!(v.len(), 0);
}

#[test]
#[should_panic]
fn from_be_bytes_panics_on_oversized_input() {
    // CAP=4, word_size=4 → max 16 bytes. Give 17.
    let bytes = [0u8; 17];
    let _ = H4u32Nct::from_be_bytes(&bytes);
}

#[test]
fn be_round_trip() {
    let original = H4u32Nct::from_limbs([0xDEADBEEF, 0xCAFEBABE, 0x01020304, 0], 3);
    let mut buf = [0u8; 12];
    original.to_be_bytes(&mut buf);
    let back = H4u32Nct::from_be_bytes(&buf);
    assert_eq!(back.len(), 3);
    assert_eq!(back.limbs(), original.limbs());
}

#[test]
fn le_round_trip() {
    let original = H4u32Nct::from_limbs([0xDEADBEEF, 0xCAFEBABE, 0x01020304, 0], 3);
    let mut buf = [0u8; 12];
    original.to_le_bytes(&mut buf);
    let back = H4u32Nct::from_le_bytes(&buf);
    assert_eq!(back.len(), 3);
    assert_eq!(back.limbs(), original.limbs());
}

// ── bit_length / leading_zeros ──

#[test]
fn bit_length_zero_is_zero() {
    let z = <H4u32Nct as Zero>::zero();
    assert_eq!(z.bit_length(), 0);
}

#[test]
fn bit_length_one_is_one() {
    let o = <H4u32Nct as One>::one();
    assert_eq!(o.bit_length(), 1);
}

#[test]
fn bit_length_within_single_limb() {
    let a = H4u32Nct::from_limbs([0x80, 0, 0, 0], 1);
    assert_eq!(a.bit_length(), 8);
    let b = H4u32Nct::from_limbs([0xFF, 0, 0, 0], 1);
    assert_eq!(b.bit_length(), 8);
    let c = H4u32Nct::from_limbs([1u32 << 31, 0, 0, 0], 1);
    assert_eq!(c.bit_length(), 32);
}

#[test]
fn bit_length_multi_limb() {
    // Highest set bit is in limb 2, bit 0. Total = 2 * 32 + 1 = 65.
    let a = H4u32Nct::from_limbs([0, 0, 1, 0], 3);
    assert_eq!(a.bit_length(), 65);
    // Highest set bit in limb 3, bit 31. Total = 3 * 32 + 32 = 128.
    let b = H4u32Nct::from_limbs([0, 0, 0, 1u32 << 31], 4);
    assert_eq!(b.bit_length(), 128);
}

#[test]
fn bit_length_ignores_zero_high_limbs() {
    // Explicit len=4 but high limbs happen to be zero — same value as
    // a shorter `len` shape.
    let a = H4u32Nct::from_limbs([0xABCD, 0, 0, 0], 4);
    assert_eq!(a.bit_length(), 16);
}

#[test]
fn leading_zeros_zero() {
    let z = <H4u32Nct as Zero>::zero();
    // CAP=4 × 32 bits = 128.
    assert_eq!(z.leading_zeros(), 128);
}

#[test]
fn leading_zeros_full_width_value() {
    let v = H4u32Nct::from_limbs([0, 0, 0, 1u32 << 31], 4);
    assert_eq!(v.leading_zeros(), 0);
}

#[test]
fn leading_zeros_plus_bit_length_equals_cap_bits() {
    let v = H4u32Nct::from_limbs([0, 1u32 << 20, 0, 0], 2);
    assert_eq!(v.leading_zeros() + v.bit_length(), 128);
}

#[test]
fn bytes_work_across_widths() {
    // u8 backing: byte-per-limb, no cross-limb assembly.
    type H8u8Nct = HeaplessBigInt<u8, 8, Nct>;
    let v = H8u8Nct::from_be_bytes(&[0x12, 0x34, 0x56, 0x78]);
    assert_eq!(v.len(), 4);
    // BE, byte 0 = 0x12 is the highest byte → limb 3.
    assert_eq!(v.limbs(), &[0x78, 0x56, 0x34, 0x12]);

    // u64 backing: 8 bytes per limb.
    type H2u64Nct = HeaplessBigInt<u64, 2, Nct>;
    let v = H2u64Nct::from_be_bytes(&[0, 0, 0, 0, 0, 0, 0, 0x42]);
    assert_eq!(v.len(), 1);
    assert_eq!(v.limbs()[0], 0x42);
}

// ── From<u8>/<u16>/<u32> ──

#[test]
fn from_u8_matches_le_bytes() {
    let v: H4u32Nct = 0xABu8.into();
    assert_eq!(v.limbs()[0], 0xAB);
    // u32 backing, u8 source: single limb.
    assert_eq!(v.len(), 1);
}

#[test]
fn from_u16_multi_limb_when_backing_is_u8() {
    type H8u8Nct = HeaplessBigInt<u8, 8, Nct>;
    let v: H8u8Nct = 0xABCDu16.into();
    // u8 backing splits u16 across two limbs (LE).
    assert_eq!(v.limbs()[0], 0xCD);
    assert_eq!(v.limbs()[1], 0xAB);
    assert_eq!(v.len(), 2);
}

#[test]
fn from_u32_across_u8_backing() {
    type H8u8Nct = HeaplessBigInt<u8, 8, Nct>;
    let v: H8u8Nct = 0x12345678u32.into();
    assert_eq!(v.limbs(), &[0x78, 0x56, 0x34, 0x12]);
    assert_eq!(v.len(), 4);
}

#[test]
fn from_u32_single_limb_when_backing_is_u32() {
    let v: H4u32Nct = 0xDEADBEEFu32.into();
    assert_eq!(v.limbs()[0], 0xDEADBEEF);
    assert_eq!(v.len(), 1);
}

// ── Trait-form Wrapping / Overflowing Add / Sub ──

#[test]
fn trait_wrapping_add_matches_inherent() {
    use const_num_traits::WrappingAdd;
    let a: H4u32Nct = 100u32.into();
    let b: H4u32Nct = 250u32.into();
    let via_trait = <H4u32Nct as WrappingAdd>::wrapping_add(a, b);
    let via_inherent = HeaplessBigInt::wrapping_add(&a, &b);
    assert_eq!(via_trait, via_inherent);
}

#[test]
fn trait_wrapping_sub_matches_inherent() {
    use const_num_traits::WrappingSub;
    let a: H4u32Nct = 500u32.into();
    let b: H4u32Nct = 200u32.into();
    let via_trait = <H4u32Nct as WrappingSub>::wrapping_sub(a, b);
    let via_inherent = HeaplessBigInt::wrapping_sub(&a, &b);
    assert_eq!(via_trait, via_inherent);
}

#[test]
fn trait_overflowing_add_reports_overflow() {
    use const_num_traits::OverflowingAdd;
    let max = H4u32Nct::from_limbs([u32::MAX; 4], 4);
    let one: H4u32Nct = 1u8.into();
    let (_, overflow) = <H4u32Nct as OverflowingAdd>::overflowing_add(max, one);
    assert!(overflow);
}

#[test]
fn trait_overflowing_sub_reports_borrow() {
    use const_num_traits::OverflowingSub;
    let a: H4u32Nct = 1u8.into();
    let b: H4u32Nct = 2u8.into();
    let (_, borrow) = <H4u32Nct as OverflowingSub>::overflowing_sub(a, b);
    assert!(borrow);
}

// ── Parity ──

#[test]
fn parity_zero_is_even() {
    let z = <H4u32Nct as Zero>::zero();
    assert!(!z.is_odd());
    assert!(z.is_even());
}

#[test]
fn parity_reads_lowest_bit() {
    let odd: H4u32Nct = 5u32.into();
    let even: H4u32Nct = 4u32.into();
    assert!(odd.is_odd());
    assert!(!odd.is_even());
    assert!(!even.is_odd());
    assert!(even.is_even());
}

#[test]
fn parity_reads_only_lowest_limb() {
    // High limbs are non-zero; parity must still come from limb 0.
    let v = H4u32Nct::from_limbs([0xFFFF_FFFE, 0xFFFF_FFFF, 0, 0], 2);
    assert!(v.is_even()); // low bit of 0xFFFF_FFFE is 0
}

// ── Div / Rem ──

#[test]
fn div_rem_dividend_less_than_divisor() {
    let a: H4u32Nct = 3u8.into();
    let b: H4u32Nct = 10u8.into();
    assert_eq!(a / b, <H4u32Nct as Zero>::zero());
    assert_eq!(a % b, a);
}

#[test]
fn div_rem_equal() {
    let a: H4u32Nct = 42u32.into();
    let b: H4u32Nct = 42u32.into();
    assert_eq!(a / b, <H4u32Nct as One>::one());
    assert_eq!(a % b, <H4u32Nct as Zero>::zero());
}

#[test]
fn div_rem_small_values() {
    let a: H4u32Nct = 100u32.into();
    let b: H4u32Nct = 7u8.into();
    // 100 = 14*7 + 2.
    let expected_q: H4u32Nct = 14u32.into();
    let expected_r: H4u32Nct = 2u8.into();
    assert_eq!(a / b, expected_q);
    assert_eq!(a % b, expected_r);
}

#[test]
fn div_rem_cross_limb() {
    // 0x1_0000_0000 / 3 = 0x5555_5555 rem 1.
    let a = H4u32Nct::from_limbs([0, 1, 0, 0], 2);
    let b: H4u32Nct = 3u32.into();
    let q = a / b;
    let r = a % b;
    let expected_q: H4u32Nct = 0x5555_5555u32.into();
    let expected_r: H4u32Nct = 1u8.into();
    assert_eq!(q, expected_q);
    assert_eq!(r, expected_r);
}

#[test]
#[should_panic]
fn div_by_zero_panics() {
    let a: H4u32Nct = 5u8.into();
    let b = <H4u32Nct as Zero>::zero();
    let _ = a / b;
}

#[test]
fn div_rem_ref_variants_agree_with_owned() {
    let a: H4u32Nct = 100u32.into();
    let b: H4u32Nct = 7u8.into();
    assert_eq!(a / b, (&a) / (&b));
    assert_eq!(a % b, (&a) % (&b));
    assert_eq!(a / b, a / &b);
    assert_eq!(a % b, a % &b);
    assert_eq!(a / b, (&a) / b);
    assert_eq!(a % b, (&a) % b);
}

#[test]
fn div_rem_round_trip_identity() {
    // For any a, b > 0: (a / b) * b + (a % b) == a.
    let a = H4u32Nct::from_limbs([0xDEAD_BEEFu32, 0x1234_5678u32, 0, 0], 2);
    let b: H4u32Nct = 0xABCDu32.into();
    let q = a / b;
    let r = a % b;
    // Sanity-check: q * b + r == a. Use inherent wrapping_mul + wrapping_add.
    let product = q.wrapping_mul(&b);
    let reconstructed = product.wrapping_add(&r);
    assert_eq!(reconstructed, a);
}

// ── HasPersonality projection ──

#[test]
fn has_personality_projects_declared_type() {
    use const_num_traits::HasPersonality;
    fn assert_nct<T: HasPersonality<P = Nct>>() {}
    fn assert_ct<T: HasPersonality<P = Ct>>() {}
    assert_nct::<H4u32Nct>();
    assert_ct::<HeaplessBigInt<u32, 4, Ct>>();
}

// ── RemAssign / DivAssign ──

#[test]
fn rem_assign_owned_matches_rem() {
    let a: H4u32Nct = 100u32.into();
    let b: H4u32Nct = 7u8.into();
    let mut x = a;
    x %= b;
    assert_eq!(x, a % b);
}

#[test]
fn rem_assign_ref_matches_rem() {
    let a: H4u32Nct = 100u32.into();
    let b: H4u32Nct = 7u8.into();
    let mut x = a;
    x %= &b;
    assert_eq!(x, a % &b);
}

#[test]
fn div_assign_owned_matches_div() {
    let a: H4u32Nct = 100u32.into();
    let b: H4u32Nct = 7u8.into();
    let mut x = a;
    x /= b;
    assert_eq!(x, a / b);
}

#[test]
fn div_assign_ref_matches_div() {
    let a: H4u32Nct = 100u32.into();
    let b: H4u32Nct = 7u8.into();
    let mut x = a;
    x /= &b;
    assert_eq!(x, a / &b);
}

// ── Value + mixed core::ops receiver variants ──

#[test]
fn add_owned_owned_matches_ref_ref() {
    let a: H4u32Nct = 100u32.into();
    let b: H4u32Nct = 200u32.into();
    assert_eq!(a + b, &a + &b);
    assert_eq!(a + &b, &a + &b);
    assert_eq!(&a + b, &a + &b);
}

#[test]
fn sub_owned_owned_matches_ref_ref() {
    let a: H4u32Nct = 500u32.into();
    let b: H4u32Nct = 200u32.into();
    assert_eq!(a - b, &a - &b);
    assert_eq!(a - &b, &a - &b);
    assert_eq!(&a - b, &a - &b);
}

#[test]
fn mul_owned_owned_matches_ref_ref() {
    let a: H4u32Nct = 13u8.into();
    let b: H4u32Nct = 17u8.into();
    assert_eq!(a * b, &a * &b);
    assert_eq!(a * &b, &a * &b);
    assert_eq!(&a * b, &a * &b);
}

// ── ShrAssign / ShlAssign ──

#[test]
fn shr_assign_matches_shr() {
    let a: H4u32Nct = 0xABCD_EF01u32.into();
    let mut x = a;
    x >>= 8;
    assert_eq!(x, a >> 8);
}

#[test]
fn shl_assign_matches_shl() {
    let a: H4u32Nct = 0xABCDu32.into();
    let mut x = a;
    x <<= 12;
    assert_eq!(x, a << 12);
}

// ── WrappingMul trait ──

#[test]
fn wrapping_mul_trait_matches_inherent() {
    use const_num_traits::WrappingMul;
    let a: H4u32Nct = 13u8.into();
    let b: H4u32Nct = 17u8.into();
    let via_trait = <H4u32Nct as WrappingMul>::wrapping_mul(a, b);
    let via_inherent = HeaplessBigInt::wrapping_mul(&a, &b);
    assert_eq!(via_trait, via_inherent);
}

// ── CarryingMul at the bigint level ──

#[test]
fn carrying_mul_small_no_overflow() {
    use const_num_traits::CarryingMul;
    // 5 * 7 + 3 = 38. Fits in one limb, hi = 0.
    let a: H4u32Nct = 5u8.into();
    let b: H4u32Nct = 7u8.into();
    let c: H4u32Nct = 3u8.into();
    let (lo, hi) = a.carrying_mul(b, c);
    let expected_lo: H4u32Nct = 38u8.into();
    assert_eq!(lo, expected_lo);
    assert!(<H4u32Nct as const_num_traits::Zero>::is_zero(&hi));
}

#[test]
fn carrying_mul_produces_high_half() {
    use const_num_traits::CarryingMul;
    // MAX-limb value squared should populate hi. CAP=4, u32 → 128 bits.
    // Use (2^127) * (2^1) = 2^128 → hi = 1.
    let a = H4u32Nct::from_limbs([0, 0, 0, 1u32 << 31], 4); // 2^127
    let b: H4u32Nct = 2u8.into(); // 2^1
    let zero_v = <H4u32Nct as Zero>::zero();
    let (lo, hi) = a.carrying_mul(b, zero_v);
    // 2^128 = hi contribution of 1 at limb 0; lo is 0.
    assert!(<H4u32Nct as const_num_traits::Zero>::is_zero(&lo));
    assert_eq!(hi.all_limbs()[0], 1);
}

#[test]
fn carrying_mul_add_two_adders() {
    use const_num_traits::CarryingMul;
    // 5 * 7 + 3 + 4 = 42.
    let a: H4u32Nct = 5u8.into();
    let b: H4u32Nct = 7u8.into();
    let c: H4u32Nct = 3u8.into();
    let d: H4u32Nct = 4u8.into();
    let (lo, hi) = a.carrying_mul_add(b, c, d);
    let expected_lo: H4u32Nct = 42u8.into();
    assert_eq!(lo, expected_lo);
    assert!(<H4u32Nct as const_num_traits::Zero>::is_zero(&hi));
}

// ── BorrowingSub at the bigint level ──

#[test]
fn borrowing_sub_no_borrow_in() {
    use const_num_traits::BorrowingSub;
    let a: H4u32Nct = 100u32.into();
    let b: H4u32Nct = 40u32.into();
    let (diff, borrow) = a.borrowing_sub(b, false);
    let expected: H4u32Nct = 60u8.into();
    assert_eq!(diff, expected);
    assert!(!borrow);
}

#[test]
fn borrowing_sub_with_borrow_in() {
    use const_num_traits::BorrowingSub;
    // 100 - 40 - 1 = 59.
    let a: H4u32Nct = 100u32.into();
    let b: H4u32Nct = 40u32.into();
    let (diff, borrow) = a.borrowing_sub(b, true);
    let expected: H4u32Nct = 59u8.into();
    assert_eq!(diff, expected);
    assert!(!borrow);
}

#[test]
fn borrowing_sub_underflow_reports_borrow_out() {
    use const_num_traits::BorrowingSub;
    let a: H4u32Nct = 1u8.into();
    let b: H4u32Nct = 2u8.into();
    let (_, borrow) = a.borrowing_sub(b, false);
    assert!(borrow);
}

// ── Nct value-aware checked_mul + trim ──

type H4u8Nct = HeaplessBigInt<u8, 4, Nct>;

#[test]
fn checked_mul_returns_some_when_value_fits_but_shape_overflows_nct() {
    // Two operands whose `len` sum exceeds CAP but whose true product
    // still fits — the shape check would falsely reject, but the value
    // check accepts.
    //
    // Set up: build values with inflated len (all-zero high limbs).
    let a = H4u8Nct::from_limbs([5, 0, 0, 0], 4); // value 5, shape len=4
    let b = H4u8Nct::from_limbs([7, 0, 0, 0], 4); // value 7, shape len=4
    // len sum = 8 > CAP=4, but 5*7 = 35 fits.
    let out = a
        .checked_mul(&b)
        .expect("value fits, checked_mul should accept");
    assert_eq!(out.limbs()[0], 35);
    // Nct path trims: len reflects value.
    assert_eq!(out.len(), 1);
}

#[test]
fn checked_mul_returns_none_when_value_truly_overflows() {
    // 2^24 (limb 3) * 2^16 (limb 2) = 2^40 — doesn't fit in u8*4 = 32 bits.
    let a = H4u8Nct::from_limbs([0, 0, 0, 1], 4); // 2^24
    let b = H4u8Nct::from_limbs([0, 0, 1, 0], 3); // 2^16
    assert!(a.checked_mul(&b).is_none());
}

#[test]
fn checked_mul_chain_survives_shape_inflation() {
    // The "modmath EEA" pattern that would panic under a shape-based
    // check: multiply small values that keep growing `len` under the
    // untrimmed shape but whose true values stay small.
    let start: H4u8Nct = 1u8.into();
    let a: H4u8Nct = 3u8.into();
    let b: H4u8Nct = 5u8.into();
    let c: H4u8Nct = 7u8.into();
    // start * a * b * c = 105. Fits trivially in one u8 limb.
    let p1 = start.checked_mul(&a).unwrap();
    let p2 = p1.checked_mul(&b).unwrap();
    let p3 = p2.checked_mul(&c).unwrap();
    assert_eq!(p3.limbs()[0], 105);
    assert_eq!(p3.len(), 1);
}

#[test]
fn trim_normalises_inflated_shape() {
    // Inflated len=4, only limb 0 non-zero.
    let v = H4u8Nct::from_limbs([42, 0, 0, 0], 4);
    let t = v.trim();
    assert_eq!(t.len(), 1);
    assert_eq!(t.limbs()[0], 42);
    // Value equality preserved.
    assert_eq!(t, v);
}

#[test]
fn trim_zero_gives_len_zero() {
    let z = H4u8Nct::from_limbs([0; 4], 4);
    let t = z.trim();
    assert_eq!(t.len(), 0);
    assert!(<H4u8Nct as Zero>::is_zero(&t));
}

#[test]
fn trim_leaves_content_untouched() {
    // len already tight; trim is a no-op.
    let v = H4u8Nct::from_limbs([0xAB, 0xCD, 0, 0], 2);
    let t = v.trim();
    assert_eq!(t.len(), 2);
    assert_eq!(t.limbs(), v.limbs());
}

// ── const_num_traits CheckedAdd / CheckedMul trait forms (Nct) ──

#[test]
fn trait_checked_add_matches_inherent() {
    use const_num_traits::CheckedAdd;
    let a: H4u32Nct = 100u32.into();
    let b: H4u32Nct = 250u32.into();
    let via_trait = <H4u32Nct as CheckedAdd>::checked_add(a, b);
    let via_inherent = HeaplessBigInt::checked_add(&a, &b);
    assert_eq!(via_trait, via_inherent);
    assert_eq!(via_trait, Some(HeaplessBigInt::from(350u32)));
}

#[test]
fn trait_checked_add_reports_overflow() {
    use const_num_traits::CheckedAdd;
    let max = H4u32Nct::from_limbs([u32::MAX; 4], 4);
    let one: H4u32Nct = 1u8.into();
    assert_eq!(<H4u32Nct as CheckedAdd>::checked_add(max, one), None);
}

#[test]
fn trait_checked_mul_matches_inherent() {
    use const_num_traits::CheckedMul;
    let a: H4u32Nct = 13u8.into();
    let b: H4u32Nct = 17u8.into();
    let via_trait = <H4u32Nct as CheckedMul>::checked_mul(a, b);
    let via_inherent = HeaplessBigInt::checked_mul(&a, &b);
    assert_eq!(via_trait, via_inherent);
    assert_eq!(via_trait, Some(HeaplessBigInt::from(221u32)));
}

#[test]
fn trait_checked_mul_is_value_aware_through_the_trait() {
    // The whole point of routing modmath's inv through the trait: a
    // value that fits despite shape-len overrun returns Some via the
    // trait form, not just the inherent.
    use const_num_traits::CheckedMul;
    let a = H4u8Nct::from_limbs([5, 0, 0, 0], 4); // value 5, shape len=4
    let b = H4u8Nct::from_limbs([7, 0, 0, 0], 4); // value 7, shape len=4
    let out = <H4u8Nct as CheckedMul>::checked_mul(a, b).expect("value fits");
    assert_eq!(out.limbs()[0], 35);
    assert_eq!(out.len(), 1);
}

#[test]
fn trait_checked_mul_reports_true_overflow() {
    use const_num_traits::CheckedMul;
    let a = H4u8Nct::from_limbs([0, 0, 0, 1], 4); // 2^24
    let b = H4u8Nct::from_limbs([0, 0, 1, 0], 3); // 2^16
    assert_eq!(<H4u8Nct as CheckedMul>::checked_mul(a, b), None);
}

// ── BitAnd ──

#[test]
fn bitand_masks_bits() {
    let a: H4u32Nct = 0xF0F0_F0F0u32.into();
    let mask: H4u32Nct = 0x00FF_00FFu32.into();
    let out = a & mask;
    assert_eq!(out.limbs()[0], 0x00F0_00F0);
}

#[test]
fn bitand_output_len_is_min_of_operand_lens() {
    // a spans 3 limbs, mask spans 1 → result can only have limb 0 set.
    let a = H4u32Nct::from_limbs([0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0], 3);
    let mask: H4u32Nct = 0x0000_00FFu32.into(); // len 1
    let out = &a & &mask;
    assert_eq!(out.len(), 1);
    assert_eq!(out.limbs()[0], 0x0000_00FF);
}

#[test]
fn bitand_preserves_zero_tail() {
    let a = H4u32Nct::from_limbs([0xAAAA_AAAA, 0xBBBB_BBBB, 0, 0], 2);
    let b = H4u32Nct::from_limbs([0xFFFF_0000, 0x0000_FFFF, 0, 0], 2);
    let out = a & b;
    assert_eq!(out.all_limbs()[2], 0);
    assert_eq!(out.all_limbs()[3], 0);
}

#[test]
fn bitand_all_receiver_forms_agree() {
    let a: H4u32Nct = 0xF0F0_F0F0u32.into();
    let b: H4u32Nct = 0x00FF_00FFu32.into();
    let ref_ref = &a & &b;
    assert_eq!(a & b, ref_ref);
    assert_eq!(a & &b, ref_ref);
    assert_eq!(&a & b, ref_ref);
}

#[test]
fn bitand_with_full_width_mask() {
    // Masking a short value by a full-CAP all-ones mask returns the value.
    let v: H4u32Nct = 0x1234_5678u32.into(); // len 1
    let mask = H4u32Nct::from_limbs([u32::MAX; 4], 4);
    let out = v & mask;
    assert_eq!(out.limbs()[0], 0x1234_5678);
    assert_eq!(out.len(), 1);
}
