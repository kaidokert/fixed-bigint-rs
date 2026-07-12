//! Sanity tests for the `CiosRowOps` impl on `HeaplessBigInt`.
//!
//! Verifies the trait's contract at the primitive level (small numeric
//! examples where the expected value is checked by hand) — the full
//! CIOS driver is exercised in modmath's own integration.

#![cfg(all(feature = "heapless-runtime-len", feature = "cios"))]

use const_num_traits::Nct;
use fixed_bigint::HeaplessBigInt;
use modmath_cios::CiosRowOps;

type H4u32 = HeaplessBigInt<u32, 4, Nct>;
type H2u32 = HeaplessBigInt<u32, 2, Nct>;

#[test]
fn word_count_matches_len() {
    let v = H4u32::from_limbs([1, 2, 3, 0], 3);
    assert_eq!(v.word_count(), 3);
}

#[test]
fn word_reads_the_indexed_limb() {
    let v = H4u32::from_limbs([100, 200, 300, 0], 3);
    assert_eq!(v.word(0), 100);
    assert_eq!(v.word(1), 200);
    assert_eq!(v.word(2), 300);
}

#[test]
fn cios_accumulator_matches_operand_width_and_is_zero() {
    // Runtime-width carrier: accumulator len must equal operand len,
    // not fall back to `Default` (which is len=0).
    let modulus = H4u32::from_limbs([0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0], 3);
    let acc = modulus.cios_accumulator();
    assert_eq!(acc.word_count(), 3);
    for i in 0..acc.word_count() {
        assert_eq!(acc.word(i), 0);
    }
}

#[test]
fn mul_acc_row_single_limb_no_carry() {
    // W=1: acc = 0 + 3*4 + 0 = 12, carry = 0.
    let mult = H2u32::from_limbs([3, 0], 1);
    let mut acc = mult.cios_accumulator();
    let carry_out = <H2u32 as CiosRowOps>::mul_acc_row(4, &mult, &mut acc, 0);
    assert_eq!(acc.word(0), 12);
    assert_eq!(carry_out, 0);
}

#[test]
fn mul_acc_row_single_limb_produces_carry() {
    // W=1: acc = 0 + u32::MAX * 2 + 0 = 2^33 - 2.
    // Low: 0xFFFFFFFE. High (carry): 1.
    let mult = H2u32::from_limbs([u32::MAX, 0], 1);
    let mut acc = mult.cios_accumulator();
    let carry_out = <H2u32 as CiosRowOps>::mul_acc_row(2, &mult, &mut acc, 0);
    assert_eq!(acc.word(0), 0xFFFF_FFFE);
    assert_eq!(carry_out, 1);
}

#[test]
fn mul_acc_row_multi_limb_carries_across() {
    // mult = 0xFFFF_FFFF_FFFF_FFFF (two u32 limbs).
    // scalar = 2. Product = 2^33 - 2 spans both limbs into a third position.
    // acc = 0 + 2 * (2^64 - 1) = 2^65 - 2 → 3 * 2^32 words:
    //   limb[0] = 0xFFFF_FFFE
    //   limb[1] = 0xFFFF_FFFF
    //   carry_out = 1
    let mult = H2u32::from_limbs([u32::MAX, u32::MAX], 2);
    let mut acc = mult.cios_accumulator();
    let carry_out = <H2u32 as CiosRowOps>::mul_acc_row(2, &mult, &mut acc, 0);
    assert_eq!(acc.word(0), 0xFFFF_FFFE);
    assert_eq!(acc.word(1), 0xFFFF_FFFF);
    assert_eq!(carry_out, 1);
}

#[test]
fn mul_acc_row_uses_carry_in() {
    // W=1: acc = 5 + 3*4 + 7 = 24. No overflow.
    let mult = H2u32::from_limbs([3, 0], 1);
    let mut acc = H2u32::from_limbs([5, 0], 1);
    let carry_out = <H2u32 as CiosRowOps>::mul_acc_row(4, &mult, &mut acc, 7);
    assert_eq!(acc.word(0), 24);
    assert_eq!(carry_out, 0);
}

#[test]
fn mul_acc_shift_row_single_limb() {
    // Match modmath-cios's primitive-impl semantics.
    // scalar=2, mult=3, acc=1, acc_hi=0.
    // product = 6. total = acc + product = 7. total_hi = 0.
    // sum = total_hi + acc_hi = 0. acc = 0. return (sum >> b) = 0.
    let mult = H2u32::from_limbs([3, 0], 1);
    let mut acc = H2u32::from_limbs([1, 0], 1);
    let ret = <H2u32 as CiosRowOps>::mul_acc_shift_row(2, &mult, &mut acc, 0);
    assert_eq!(acc.word(0), 0);
    assert_eq!(ret, 0);
}

#[test]
fn mul_acc_shift_row_produces_nonzero_top() {
    // scalar=u32::MAX, mult=u32::MAX, acc=0, acc_hi=0.
    // product = (2^32 - 1)^2 = 2^64 - 2^33 + 1. Split as (t_lo, t_hi) =
    // (1, 2^32 - 2). total (acc + product) same. total_hi = t_hi + c_from_lo_add.
    // c_from_lo_add = (0 + 1 >= 2^32)? no, so c = 0. total_hi = 2^32 - 2.
    // sum = total_hi + acc_hi = 2^32 - 2. top_hi_bit = 0.
    // acc[0] = top_low = 2^32 - 2. Return 0.
    let mult = H2u32::from_limbs([u32::MAX, 0], 1);
    let mut acc = H2u32::from_limbs([0, 0], 1);
    let ret = <H2u32 as CiosRowOps>::mul_acc_shift_row(u32::MAX, &mult, &mut acc, 0);
    assert_eq!(acc.word(0), 0xFFFF_FFFE);
    assert_eq!(ret, 0);
}

#[test]
fn mul_acc_shift_row_multi_limb_shifts_low_limb_out() {
    // W=2 mult = [1, 0], scalar = 1, acc = [0, 0], acc_hi = 0.
    // Phase 1: acc[0] += 1*1 = 1. acc[1] += 1*0 = 0 (with carry from mul: 0).
    // carry after phase 1: 0.
    // top_low = 0 + acc_hi = 0. top_hi_bit = 0.
    // Shift: acc[0] = acc[1] = 0. acc[1] = top_low = 0.
    // Result: acc = [0, 0], ret = 0.
    let mult = H2u32::from_limbs([1, 0], 2);
    let mut acc = H2u32::from_limbs([0, 0], 2);
    let ret = <H2u32 as CiosRowOps>::mul_acc_shift_row(1, &mult, &mut acc, 0);
    assert_eq!(acc.word(0), 0);
    assert_eq!(acc.word(1), 0);
    assert_eq!(ret, 0);
}

#[test]
fn mul_acc_shift_row_carries_top_bit() {
    // scalar=u32::MAX, mult=[u32::MAX], acc=[0, 0], acc_hi=u32::MAX.
    // W=1 (mult len).
    // Phase 1: (t_lo, t_hi) = MAX * MAX + 0 = (1, MAX - 1). acc[0]+t_lo: sum=1, c=0.
    // acc[0] = 1. carry = t_hi + c = MAX - 1.
    // Combine: top_low, top_hi_bit = (MAX - 1) + MAX = 2 * MAX - 1 = 2^33 - 3.
    //   → top_low = 2^32 - 3 = 0xFFFF_FFFD, top_hi_bit = 1.
    // Shift: n=1, no shuffling. acc[0] = top_low = 0xFFFF_FFFD.
    // Return: 1.
    let mult = H2u32::from_limbs([u32::MAX, 0], 1);
    let mut acc = H2u32::from_limbs([0, 0], 1);
    let ret = <H2u32 as CiosRowOps>::mul_acc_shift_row(u32::MAX, &mult, &mut acc, u32::MAX);
    assert_eq!(acc.word(0), 0xFFFF_FFFD);
    assert_eq!(ret, 1);
}
