//! Sketch-level sanity tests: constructors work, Add/Sub/Mul produce
//! correct values against small u16/u32 inputs, PartialEq is
//! value-based across shapes, Zero/One/Default line up, and Ct paths
//! (subtle::ConstantTimeEq) agree with the value.

#![cfg(feature = "heapless-runtime-len")]

use const_num_traits::{Ct, Nct, One, Zero};
use fixed_bigint::HeaplessBigInt;
use subtle::ConstantTimeEq;

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
