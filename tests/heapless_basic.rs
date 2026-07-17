//! Sanity tests: constructors work, Add/Sub/Mul produce correct values
//! against small u16/u32 inputs, PartialEq is value-based across shapes,
//! Zero/One/Default line up, and Ct paths (subtle::ConstantTimeEq) agree
//! with the value.

// Several tests deliberately spell out `&a op &b` (and the mixed receiver
// forms) to check that every operator impl — value/value, value/ref,
// ref/value, ref/ref — agrees. That is the point, so `op_ref` is allowed.
#![allow(clippy::op_ref)]

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
fn from_limbs_rejects_nonzero_tail() {
    // The tail check is unconditional, so this panics in release too.
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
    // (u32::MAX) + 1 = 0x1_0000_0000 at width 1 (len 1). The carry is out
    // of the width, reported as a flag, result wraps to 0 — exactly like
    // FixedUInt<u32,1>. No limb growth: the words beyond len do not exist.
    let a = H4u32Nct::from_limbs([u32::MAX, 0, 0, 0], 1);
    let b = H4u32Nct::from_limbs([1, 0, 0, 0], 1);
    let w = a.wrapping_add(&b);
    assert_eq!(w.len(), 1);
    assert_eq!(w.limbs()[0], 0);

    let (res, overflow) = a.overflowing_add(&b);
    assert!(overflow, "carry out of width 1");
    assert_eq!(res.len(), 1);
    assert_eq!(res.limbs()[0], 0);
    assert_eq!(a.checked_add(&b), None);
}

#[test]
fn add_overflow_at_operand_width() {
    // Sum overflowing the operands' width flags, regardless of capacity:
    // here width == 4 (== CAP), but the rule is width, not CAP.
    let max = H4u32Nct::from_limbs([u32::MAX; 4], 4);
    let one = <H4u32Nct as One>::one();
    let (_wrapped, overflow) = max.overflowing_add(&one);
    assert!(
        overflow,
        "expected overflow when the sum exceeds the operand width"
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

#[test]
fn sub_underflow_wraps_at_operand_width_not_cap() {
    // A HeaplessBigInt's width is len·word_bits, not CAP. Underflow wraps
    // at the operands' width (max len), leaving CAP out of it: 5 - 7 at
    // len 1 (u32 backing → width 32) is a 32-bit wrap, and the result
    // stays len 1 — the high CAP limbs are untouched.
    let a: H4u32Nct = 5u32.into(); // len 1, width 32
    let b: H4u32Nct = 7u32.into();
    let w = a.wrapping_sub(&b);
    assert_eq!(w.len(), 1);
    assert_eq!(w.limbs()[0], u32::MAX - 1); // 2^32 - 2
    assert_eq!(w.all_limbs()[1], 0); // CAP limbs beyond the width stay zero
}

// ── Mul ──

#[test]
fn mul_small_product_fits() {
    // 100 * 200 = 20_000 < 2^32, so at value width 1 it fits in one limb
    // with no wrap. wrapping_mul stays len 1 (like FixedUInt<u32,1>).
    let a = H4u32Nct::from_limbs([100, 0, 0, 0], 1);
    let b = H4u32Nct::from_limbs([200, 0, 0, 0], 1);
    let p = a.wrapping_mul(&b);
    assert_eq!(p.len(), 1);
    assert_eq!(p.limbs()[0], 20_000);
}

#[test]
fn mul_cross_limb_carry() {
    // 0x1_0000 * 0x1_0000 = 2^32. At width 1 (len 1) the product exceeds
    // the width: wrapping_mul → 0, overflowing_mul flags, checked_mul is
    // None — exactly like FixedUInt<u32,1>. The high half beyond the
    // width does not exist here; WideMul is the op that returns it.
    let a = H4u32Nct::from_limbs([0x1_0000, 0, 0, 0], 1);
    let b = H4u32Nct::from_limbs([0x1_0000, 0, 0, 0], 1);
    let w = a.wrapping_mul(&b);
    assert_eq!(w.len(), 1);
    assert_eq!(w.limbs()[0], 0);

    let (_res, overflow) = a.overflowing_mul(&b);
    assert!(overflow, "2^32 overflows width 1");
    assert_eq!(a.checked_mul(&b), None);
}

#[test]
fn mul_overflow_at_operand_width() {
    // len=3 * len=3 → product exceeds width 3, so it flags — the rule is
    // the operand width, not CAP (here CAP=4 also fits fewer than 6 words,
    // but that is not what decides it).
    let a = H4u32Nct::from_limbs([1, 1, 1, 0], 3);
    let b = H4u32Nct::from_limbs([1, 1, 1, 0], 3);
    let (_wrapped, overflow) = a.overflowing_mul(&b);
    assert!(
        overflow,
        "expected overflow when the product exceeds the operand width"
    );
    assert_eq!(a.checked_mul(&b), None);
}

#[test]
fn wrapping_ops_do_not_grow_width() {
    // Wrapping ops must keep the value width fixed so iterative modular
    // algorithms stay self-consistent: one + one = 2 at len 1 (not [2,0]
    // at len 2).
    let one = <H4u32Nct as One>::one();
    let two = one.wrapping_add(&one);
    assert_eq!(two.len(), 1);
    assert_eq!(two.limbs()[0], 2);

    // A newton-style step at a fixed width-1 modulus: 2 - (m*x) stays
    // len 1 through wrapping_mul / wrapping_sub, matching the width-1
    // FixedUInt arithmetic the parity test pins. Here m=35, x=1.
    let m = H4u32Nct::from_limbs([35, 0, 0, 0], 1);
    let x = one;
    let mx = m.wrapping_mul(&x);
    assert_eq!(mx.len(), 1);
    let r = two.wrapping_sub(&mx);
    assert_eq!(r.len(), 1);
    assert_eq!(r.limbs()[0], 2u32.wrapping_sub(35)); // wraps at 2^32
}

#[test]
fn carrying_add_reports_width_carry_without_growing() {
    use const_num_traits::CarryingAdd;
    // Symmetric to borrowing_sub: value-width add-with-carry. The carry
    // out of the width is a flag, not a grown limb — what wide-REDC needs.
    // u32::MAX + 1 at len 1 → (0, carry=true), stays len 1.
    let a = H4u32Nct::from_limbs([u32::MAX, 0, 0, 0], 1);
    let b = H4u32Nct::from_limbs([1, 0, 0, 0], 1);
    let (sum, carry) = CarryingAdd::carrying_add(a, b, false);
    assert!(carry);
    assert_eq!(sum.len(), 1);
    assert_eq!(sum.limbs()[0], 0);

    // carry_in threads through: 5 + 2 + carry = 8, no carry-out.
    let (s2, c2) = CarryingAdd::carrying_add(
        H4u32Nct::from_limbs([5, 0, 0, 0], 1),
        H4u32Nct::from_limbs([2, 0, 0, 0], 1),
        true,
    );
    assert!(!c2);
    assert_eq!(s2.limbs()[0], 8);
}

#[test]
fn accumulator_must_be_width_pinned() {
    use const_num_traits::OverflowingAdd;
    // Horner-style doubling: acc = acc*2, repeated. The width is whatever
    // acc is carried at — value-width ops resolve at max(operand len), so
    // a value grown from a narrow seed stays narrow and wraps early
    // (exactly like a narrow FixedUInt). A width-pinned seed carries the
    // full width, like FixedUInt<u32,8>.
    let double = |acc: H4u32Nct| OverflowingAdd::overflowing_add(acc, acc).0;

    // Start from 1, double 40 times → 2^40, which needs limb 1.
    let start = H4u32Nct::from_limbs([1, 0, 0, 0], 1); // narrow: len 1
    let mut narrow = start;
    for _ in 0..40 {
        narrow = double(narrow);
    }
    // Narrow stayed len 1 and wrapped at 2^32 → 0.
    assert_eq!(narrow.len(), 1);
    assert!(<H4u32Nct as Zero>::is_zero(&narrow));

    // Pin to width 2 (64 bits) up front; 2^40 now fits.
    let mut wide = start.widened(2);
    for _ in 0..40 {
        wide = double(wide);
    }
    assert_eq!(wide.len(), 2);
    assert_eq!(wide.limbs()[0], 0); // low 32 bits of 2^40
    assert_eq!(wide.limbs()[1], 1 << 8); // 2^40 = 2^8 · 2^32
}

#[test]
fn wrapping_sub_preserves_width_no_stale_len() {
    use const_num_traits::{OverflowingAdd, WrappingSub};
    // A wrapping_sub whose result is numerically small keeps the operands'
    // width — len is NOT trimmed to the value. So a later doubling still has
    // room and retains the carry: there is no "stale/shrunk len" feeding a
    // truncated add. (len IS the width, like the 8 in u8 — not value-tight
    // metadata.)
    let big = H4u32Nct::from_limbs([0x9807_72de, 5, 0, 0], 2); // width 2
    let sub = H4u32Nct::from_limbs([0, 5, 0, 0], 2); // width 2
    let small = WrappingSub::wrapping_sub(big, sub); // value 0x980772de
    assert_eq!(
        small.len(),
        2,
        "wrapping_sub keeps width, does not trim len"
    );
    assert_eq!(small.limbs()[0], 0x9807_72de);
    assert_eq!(small.limbs()[1], 0);

    // Doubling the "shrunk" value still carries into limb 1 (width 2 room).
    let (dbl, _) = OverflowingAdd::overflowing_add(small, small);
    assert_eq!(dbl.len(), 2);
    assert_eq!(dbl.limbs()[0], 0x9807_72deu32.wrapping_shl(1));
    assert_eq!(
        dbl.limbs()[1],
        1,
        "carry retained after sub->double at width 2"
    );
}

#[test]
fn with_precision_seeds_at_witness_width() {
    use const_num_traits::{BitsPrecision, WithPrecision, WrappingSub};
    // A witness (stand-in modulus) carried at len 3 (sub-CAP, CAP=4).
    let q = H4u32Nct::from_limbs([7, 0, 5, 0], 3);

    // zero_with_precision_of(&q): a zero pinned at q's width (len 3), NOT the
    // minimal-width len-0 zero(). Named replacement for the
    // `wrapping_sub(q, q)` seed idiom — identical result.
    let z = <H4u32Nct as WithPrecision>::zero_with_precision_of(&q);
    assert!(<H4u32Nct as Zero>::is_zero(&z));
    assert_eq!(z.len(), 3);
    assert_eq!(
        BitsPrecision::bits_precision(&z),
        BitsPrecision::bits_precision(&q)
    );
    let idiom = WrappingSub::wrapping_sub(q, q);
    assert_eq!(z, idiom);
    assert_eq!(z.len(), idiom.len());

    // one_with_precision_of(&q): value 1 at q's width.
    let one = <H4u32Nct as WithPrecision>::one_with_precision_of(&q);
    assert_eq!(one.len(), 3);
    assert_eq!(one.limbs()[0], 1);

    // widen_to_precision_of: grow a narrow value to the witness width,
    // value preserved.
    let small = H4u32Nct::from_limbs([42, 0, 0, 0], 1);
    let widened = <H4u32Nct as WithPrecision>::widen_to_precision_of(small, &q);
    assert_eq!(widened.len(), 3);
    assert_eq!(widened.limbs()[0], 42);
    assert_eq!(small, widened); // same value, wider carrier

    // Grow-only: widening to a narrower witness keeps the current width.
    let narrow_witness = H4u32Nct::from_limbs([1, 0, 0, 0], 1);
    let kept = <H4u32Nct as WithPrecision>::widen_to_precision_of(widened, &narrow_witness);
    assert_eq!(kept.len(), 3);
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
// Shared ops dispatch on `P` where the Ct arm must avoid value-dependent
// control flow (arithmetic panics, compare/is_zero short-circuits, Debug).
// The Ct arm produces the same values as Nct; these check that plus the
// constant-time-shaped behavior (wrap instead of panic, opaque Debug).

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
    assert!(bool::from(a.ct_eq(&b)));
    assert!(!bool::from(a.ct_eq(&c)));
    assert!(a == b);
    assert!(a != c);
}

#[test]
fn ct_eq_across_shapes() {
    // Same-value, different-shape operands agree under Ct equality too.
    let a = H8Ct::zero_full_cap();
    let b = <H8Ct as Zero>::zero();
    assert!(bool::from(a.ct_eq(&b)));
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
fn shl_crosses_a_limb_within_width() {
    // Width-preserving: at width 1 (len 1) the top byte shifts out, like
    // FixedUInt<u32,1>. 0xAB000000 << 8 = 0 (mod 2^32).
    let a = H4u32Nct::from_limbs([0xAB000000, 0, 0, 0], 1);
    let b = a << 8;
    assert_eq!(b.len(), 1);
    assert_eq!(b.limbs()[0], 0);

    // At width 2 (len 2) the same byte has room to carry into limb 1.
    let a2 = H4u32Nct::from_limbs([0xAB000000, 0, 0, 0], 2);
    let b2 = a2 << 8;
    assert_eq!(b2.len(), 2);
    assert_eq!(b2.limbs()[0], 0);
    assert_eq!(b2.limbs()[1], 0x000000AB);
}

#[test]
fn shl_by_full_word_preserves_width() {
    // Width 2 (len 2): << 32 shifts limb 0 into limb 1; the old limb 1
    // (value 2) shifts out of the width. Matches FixedUInt<u32,2>.
    let a = H4u32Nct::from_limbs([1, 2, 0, 0], 2);
    let b = a << 32;
    assert_eq!(b.len(), 2);
    assert_eq!(b.limbs()[0], 0);
    assert_eq!(b.limbs()[1], 1);
}

#[test]
fn shl_beyond_width_is_zero() {
    // Width 1 (len 1, 32 bits): shifting by >= the width gives zero, like
    // FixedUInt<u32,1>. Width is preserved (len stays 1); CAP is irrelevant.
    let a = H4u32Nct::from_limbs([1, 0, 0, 0], 1);
    let b = a << 128;
    assert!(<H4u32Nct as Zero>::is_zero(&b));
    assert_eq!(b.len(), 1);
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
fn leading_zeros_zero_is_zero_width() {
    // Zero has len 0 → width 0 → no leading zeros (CAP does not enter).
    let z = <H4u32Nct as Zero>::zero();
    assert_eq!(z.leading_zeros(), 0);
}

#[test]
fn leading_zeros_full_width_value() {
    // len 4 → width 128, top bit set → 0 leading zeros.
    let v = H4u32Nct::from_limbs([0, 0, 0, 1u32 << 31], 4);
    assert_eq!(v.leading_zeros(), 0);
}

#[test]
fn leading_zeros_plus_bit_length_equals_width() {
    // width = len·word_bits = 2·32 = 64 (not CAP·32 = 128).
    let v = H4u32Nct::from_limbs([0, 1u32 << 20, 0, 0], 2);
    assert_eq!(v.leading_zeros() + v.bit_length(), 64);
    // And that equals bits_precision().
    assert_eq!(
        v.leading_zeros() + v.bit_length(),
        <H4u32Nct as const_num_traits::BitsPrecision>::bits_precision(&v) as usize
    );
}

// ── BitsPrecision (width = len·word_bits) / BitWidth (bit-length) ──

#[test]
fn bits_precision_is_len_times_word_bits_not_cap() {
    use const_num_traits::BitsPrecision;
    // u32 backing: width = len * 32, tracks the constructed len, never CAP.
    assert_eq!(
        BitsPrecision::bits_precision(&H4u32Nct::from_limbs([1, 0, 0, 0], 1)),
        32
    );
    assert_eq!(
        BitsPrecision::bits_precision(&H4u32Nct::from_limbs([1, 2, 0, 0], 2)),
        64
    );
    assert_eq!(
        BitsPrecision::bits_precision(&H4u32Nct::from_limbs([1, 2, 3, 4], 4)),
        128
    );
    // len 0 (mathematical zero) → width 0.
    assert_eq!(
        BitsPrecision::bits_precision(&<H4u32Nct as Zero>::zero()),
        0
    );
    // u8 backing: width = len * 8.
    type H8u8 = HeaplessBigInt<u8, 8, Nct>;
    assert_eq!(
        BitsPrecision::bits_precision(&H8u8::from_be_bytes(&[1, 2, 3])),
        24
    );
}

#[test]
fn bits_precision_via_reference() {
    use const_num_traits::BitsPrecision;
    let v = H4u32Nct::from_limbs([1, 2, 0, 0], 2);
    assert_eq!(<&H4u32Nct as BitsPrecision>::bits_precision(&&v), 64);
}

#[test]
fn bit_width_is_bit_length() {
    use const_num_traits::BitWidth;
    // Magnitude (top set bit), <= bits_precision.
    assert_eq!(BitWidth::bit_width(<H4u32Nct as Zero>::zero()), 0);
    assert_eq!(
        BitWidth::bit_width(H4u32Nct::from_limbs([0b101, 0, 0, 0], 1)),
        3
    );
    // A value at len 2 (width 64) whose magnitude is small: bit_width < precision.
    let v = H4u32Nct::from_limbs([0xFF, 0, 0, 0], 2);
    assert_eq!(BitWidth::bit_width(v), 8);
    assert_eq!(
        <H4u32Nct as const_num_traits::BitsPrecision>::bits_precision(&v),
        64
    );
    assert!(BitWidth::bit_width(v) <= const_num_traits::BitsPrecision::bits_precision(&v));
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

#[test]
fn carrying_mul_splits_at_value_width_not_cap() {
    use const_num_traits::CarryingMul;
    // WideMul splits at the operands' value width (max len), so (lo, hi)
    // reconstruct as `hi·2^(len·word_bits) + lo`, matching bits_precision
    // and the primitive (200u8.wide_mul(200) = (64, 156), split at 8
    // bits). At len 1 (width 8) in an 8-word carrier, 40000 must split
    // into (64, 156), NOT stay whole in lo at CAP — a CAP split strands
    // the high half and misplaces hi in the REDC.
    type H4u8 = HeaplessBigInt<u8, 4, Nct>;
    let a = H4u8::from_limbs([200, 0, 0, 0], 1);
    let b = H4u8::from_limbs([200, 0, 0, 0], 1);
    let (lo, hi) = a.carrying_mul(b, <H4u8 as Zero>::zero());
    assert_eq!(lo.len(), 1, "split at value width (1 word), not CAP");
    assert_eq!(hi.len(), 1);
    assert_eq!(lo.limbs()[0], 64); // 40000 & 0xFF
    assert_eq!(hi.limbs()[0], 156); // 40000 >> 8
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

// ── checked_mul (behaves like the same-width FixedUInt) + trim ──

type H4u8Nct = HeaplessBigInt<u8, 4, Nct>;

#[test]
fn checked_mul_at_operand_width_like_fixeduint() {
    // A value carried at len=4 IS a 4-word (32-bit) integer, so checked_mul
    // behaves exactly like FixedUInt<u8,4>: 5 * 7 = 35 fits in width 4 →
    // Some(35) at len 4 (the operating width). No trim: those words are the
    // value's real width, not inflation, and capacity never enters.
    let a = H4u8Nct::from_limbs([5, 0, 0, 0], 4);
    let b = H4u8Nct::from_limbs([7, 0, 0, 0], 4);
    let out = a.checked_mul(&b).expect("35 fits in width 4");
    assert_eq!(out.len(), 4);
    assert_eq!(out.limbs()[0], 35);
}

#[test]
fn checked_mul_returns_none_when_value_overflows_width() {
    // 2^24 (limb 3) * 2^16 (limb 2) = 2^40 — exceeds the 32-bit operand
    // width (u8*4), so None, exactly as FixedUInt<u8,4> would report.
    let a = H4u8Nct::from_limbs([0, 0, 0, 1], 4); // 2^24
    let b = H4u8Nct::from_limbs([0, 0, 1, 0], 3); // 2^16
    assert!(a.checked_mul(&b).is_none());
}

#[test]
fn checked_mul_chain_stays_within_width() {
    // Chained small products, each staying within the operand width, so
    // the chain never falsely overflows.
    let start: H4u8Nct = 1u8.into();
    let a: H4u8Nct = 3u8.into();
    let b: H4u8Nct = 5u8.into();
    let c: H4u8Nct = 7u8.into();
    // 1 * 3 * 5 * 7 = 105, fits in width 1.
    let p1 = start.checked_mul(&a).unwrap();
    let p2 = p1.checked_mul(&b).unwrap();
    let p3 = p2.checked_mul(&c).unwrap();
    assert_eq!(p3.limbs()[0], 105);
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
fn trait_checked_mul_matches_fixeduint_width_behavior() {
    // Through the trait form: checked_mul at the operand width, same as
    // FixedUInt<u8,4>. 5 * 7 = 35 fits in width 4.
    use const_num_traits::CheckedMul;
    let a = H4u8Nct::from_limbs([5, 0, 0, 0], 4);
    let b = H4u8Nct::from_limbs([7, 0, 0, 0], 4);
    let out = <H4u8Nct as CheckedMul>::checked_mul(a, b).expect("35 fits in width 4");
    assert_eq!(out.len(), 4);
    assert_eq!(out.limbs()[0], 35);
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

// ── BitOr ──

#[test]
fn bitor_sets_bits() {
    let a: H4u32Nct = 0xF0F0_0000u32.into();
    let b: H4u32Nct = 0x0000_0F0Fu32.into();
    assert_eq!((a | b).limbs()[0], 0xF0F0_0F0F);
}

#[test]
fn bitor_output_len_is_max_of_operand_lens() {
    // a spans 1 limb, b spans 3 → result spans 3 (OR sets bits in the
    // wider operand's limbs, which the shorter operand's zero-tail leaves).
    let a: H4u32Nct = 0x0000_00FFu32.into(); // len 1
    let b = H4u32Nct::from_limbs([0xFF00, 0xAAAA, 0xBBBB, 0], 3);
    let out = &a | &b;
    assert_eq!(out.len(), 3);
    assert_eq!(out.limbs(), &[0x0000_FFFF, 0xAAAA, 0xBBBB]);
}

#[test]
fn bitor_preserves_zero_tail() {
    let a = H4u32Nct::from_limbs([0xAAAA, 0xBBBB, 0, 0], 2);
    let b = H4u32Nct::from_limbs([0x5555, 0x4444, 0, 0], 2);
    let out = a | b;
    assert_eq!(out.all_limbs()[2], 0);
    assert_eq!(out.all_limbs()[3], 0);
}

#[test]
fn bitor_all_receiver_forms_agree() {
    let a: H4u32Nct = 0xF0F0_F0F0u32.into();
    let b: H4u32Nct = 0x0F0F_0F0Fu32.into();
    let ref_ref = &a | &b;
    assert_eq!(a | b, ref_ref);
    assert_eq!(a | &b, ref_ref);
    assert_eq!(&a | b, ref_ref);
    // Full-width OR.
    assert_eq!(ref_ref.limbs()[0], 0xFFFF_FFFF);
}

#[test]
fn bitor_with_zero_is_identity() {
    let a = H4u32Nct::from_limbs([0x1234, 0x5678, 0, 0], 2);
    let z = <H4u32Nct as Zero>::zero();
    assert_eq!((&a | &z), a);
    assert_eq!((&z | &a), a);
}

// ── FromByteSlice ──

#[test]
fn from_be_slice_exact_and_short() {
    use const_num_traits::FromByteSlice;
    // Exact width.
    let v = H4u32Nct::from_be_slice(&[0x12, 0x34, 0x56, 0x78]).unwrap();
    assert_eq!(v.limbs()[0], 0x12345678);
    // Short input zero-extends (BE reads the trailing window).
    let v = H4u32Nct::from_be_slice(&[0x12, 0x34]).unwrap();
    assert_eq!(v.limbs()[0], 0x1234);
}

#[test]
fn from_le_slice_exact_and_short() {
    use const_num_traits::FromByteSlice;
    let v = H4u32Nct::from_le_slice(&[0x78, 0x56, 0x34, 0x12]).unwrap();
    assert_eq!(v.limbs()[0], 0x12345678);
    let v = H4u32Nct::from_le_slice(&[0x34, 0x12]).unwrap();
    assert_eq!(v.limbs()[0], 0x1234);
}

#[test]
fn from_slice_rejects_empty_and_overflow() {
    use const_num_traits::FromByteSlice;
    type H4u8 = HeaplessBigInt<u8, 4, Nct>; // 4-byte container
    assert!(H4u8::from_be_slice(&[]).is_err()); // empty
    assert!(H4u8::from_le_slice(&[]).is_err());
    assert!(H4u8::from_be_slice(&[1, 2, 3, 4, 5]).is_err()); // wider than 4 bytes
    assert!(H4u8::from_le_slice(&[1, 2, 3, 4, 5]).is_err());
    // Exactly the width is accepted.
    assert!(H4u8::from_be_slice(&[1, 2, 3, 4]).is_ok());
}

// ── DefaultIsZeroes / Zeroize ──

#[cfg(feature = "zeroize")]
#[test]
fn zeroize_wipes_value() {
    use zeroize::Zeroize;
    let mut v = H4u32Nct::from_limbs([0xDEAD_BEEF, 0xCAFE_BABE, 0, 0], 2);
    v.zeroize();
    assert!(<H4u32Nct as Zero>::is_zero(&v));
    // Default-is-zero: wiped value equals Default.
    assert_eq!(v, H4u32Nct::default());
    assert_eq!(v.len(), 0);
}

// ── const_num_traits::ToBytes / FromBytes (needs BytesHolder) ──

#[cfg(any(feature = "use-unsafe", feature = "nightly"))]
mod to_from_bytes {
    use super::*;
    use const_num_traits::{FromBytes, ToBytes};

    #[test]
    fn to_be_bytes_is_full_container_width() {
        // len=1 value in a CAP=4 u32 container → 16 bytes, left-padded.
        let v: H4u32Nct = 0x1234_5678u32.into();
        let bytes = ToBytes::to_be_bytes(v);
        assert_eq!(bytes.as_ref().len(), 16);
        // High 12 bytes zero, low 4 = the value big-endian.
        assert_eq!(&bytes.as_ref()[..12], &[0u8; 12]);
        assert_eq!(&bytes.as_ref()[12..], &[0x12, 0x34, 0x56, 0x78]);
    }

    #[test]
    fn to_le_bytes_is_full_container_width() {
        let v: H4u32Nct = 0x1234_5678u32.into();
        let bytes = ToBytes::to_le_bytes(v);
        assert_eq!(bytes.as_ref().len(), 16);
        assert_eq!(&bytes.as_ref()[..4], &[0x78, 0x56, 0x34, 0x12]);
        assert_eq!(&bytes.as_ref()[4..], &[0u8; 12]);
    }

    #[test]
    fn be_round_trip_through_holder() {
        let v = H4u32Nct::from_limbs([0xDEAD_BEEF, 0xCAFE_BABE, 0x0102_0304, 0], 3);
        let bytes = ToBytes::to_be_bytes(v);
        let back = <H4u32Nct as FromBytes>::from_be_bytes(&bytes);
        // FromBytes reconstructs at full width (len = CAP); trim to compare value.
        assert_eq!(back.trim(), v);
    }

    #[test]
    fn le_round_trip_through_holder() {
        let v = H4u32Nct::from_limbs([0xDEAD_BEEF, 0xCAFE_BABE, 0x0102_0304, 0], 3);
        let bytes = ToBytes::to_le_bytes(v);
        let back = <H4u32Nct as FromBytes>::from_le_bytes(&bytes);
        assert_eq!(back.trim(), v);
    }

    #[test]
    fn ref_tobytes_matches_owned() {
        let v: H4u32Nct = 0xABCD_1234u32.into();
        let owned = ToBytes::to_be_bytes(v);
        let by_ref = ToBytes::to_be_bytes(&v);
        assert_eq!(owned.as_ref(), by_ref.as_ref());
    }

    #[test]
    fn byte_shape_matches_fixeduint_same_params() {
        // The whole point of the full-width representation: a HeaplessBigInt
        // and a FixedUInt of the same <T, CAP> serialise identically, so a
        // carrier-generic consumer round-trips a modulus the same way.
        use fixed_bigint::FixedUInt;
        let h: H4u32Nct = 0x1234_5678u32.into();
        let f = FixedUInt::<u32, 4>::from(0x1234_5678u32);
        let hb = ToBytes::to_be_bytes(h);
        let fb = <FixedUInt<u32, 4> as ToBytes>::to_be_bytes(f);
        assert_eq!(hb.as_ref(), fb.as_ref());
    }

    #[test]
    fn works_across_widths() {
        type H8u8 = HeaplessBigInt<u8, 8, Nct>;
        let v = H8u8::from_be_bytes(&[0x11, 0x22, 0x33, 0x44]);
        let bytes = ToBytes::to_be_bytes(v);
        assert_eq!(bytes.as_ref().len(), 8);
        assert_eq!(bytes.as_ref(), &[0, 0, 0, 0, 0x11, 0x22, 0x33, 0x44]);
    }
}

// ── Ct constant-time contract (regression for the PR #138 review) ──

// `+` on Ct must not panic on a data-dependent overflow: it wraps, like
// `wrapping_add`. The same operands panic under Nct.
#[test]
fn ct_add_overflow_wraps_instead_of_panicking() {
    let a = HeaplessBigInt::<u8, 8, Ct>::from_limbs([0xff, 0, 0, 0, 0, 0, 0, 0], 1);
    let b = HeaplessBigInt::<u8, 8, Ct>::from_limbs([1, 0, 0, 0, 0, 0, 0, 0], 1);
    let s = &a + &b; // width 1: 0x100 wraps to 0
    assert_eq!(s.len(), 1);
    assert_eq!(s.limbs()[0], 0);
}

#[test]
#[should_panic]
fn nct_add_overflow_panics() {
    let a = H8Nct::from_limbs([0xff, 0, 0, 0, 0, 0, 0, 0], 1);
    let b = H8Nct::from_limbs([1, 0, 0, 0, 0, 0, 0, 0], 1);
    let _ = &a + &b;
}

// Ct Debug is opaque; Nct still prints limbs.
#[test]
fn ct_debug_is_opaque() {
    let ct = HeaplessBigInt::<u32, 4, Ct>::from_limbs([0xdead_beef, 0, 0, 0], 1);
    let s = format!("{ct:?}");
    assert_eq!(s, "HeaplessBigInt<…>");
    assert!(!s.contains("beef"));

    let nct = H4u32Nct::from_limbs([0xdead_beef, 0, 0, 0], 1);
    assert!(format!("{nct:?}").contains("limbs"));
}

// Ct compare and is_zero/is_one return the same answers as Nct.
#[test]
fn ct_cmp_and_predicates_match_values() {
    let a = HeaplessBigInt::<u32, 4, Ct>::from_limbs([5, 7, 0, 0], 2);
    let b = HeaplessBigInt::<u32, 4, Ct>::from_limbs([9, 7, 0, 0], 2);
    assert!(a < b);
    assert!(b > a);
    assert_eq!(a.cmp(&a), core::cmp::Ordering::Equal);

    let z = <HeaplessBigInt<u32, 4, Ct> as Zero>::zero();
    let one = <HeaplessBigInt<u32, 4, Ct> as One>::one();
    assert!(<HeaplessBigInt<u32, 4, Ct> as Zero>::is_zero(&z));
    assert!(!<HeaplessBigInt<u32, 4, Ct> as Zero>::is_zero(&a));
    assert!(<HeaplessBigInt<u32, 4, Ct> as One>::is_one(&one));
    assert!(!<HeaplessBigInt<u32, 4, Ct> as One>::is_one(&a));
}

// Div/Rem early-return paths carry the operands' width, like the general
// path — otherwise `x / x` would come back one word wide.
#[test]
fn div_rem_early_returns_preserve_width() {
    // Equal: quotient 1, remainder 0, both at work_len = 2.
    let x = H4u32Nct::from_limbs([5, 7, 0, 0], 2);
    let q = x / x;
    let r = x % x;
    assert_eq!(q.len(), 2);
    assert_eq!(r.len(), 2);
    assert_eq!(q, H4u32Nct::from(1u32));
    assert!(<H4u32Nct as Zero>::is_zero(&r));

    // Less: quotient 0, remainder == dividend, both at work_len = 2.
    let a = H4u32Nct::from_limbs([3, 0, 0, 0], 1);
    let b = H4u32Nct::from_limbs([5, 7, 0, 0], 2);
    let q = a / b;
    let r = a % b;
    assert_eq!(q.len(), 2);
    assert_eq!(r.len(), 2);
    assert!(<H4u32Nct as Zero>::is_zero(&q));
    assert_eq!(r, a);
}
