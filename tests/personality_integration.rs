use const_num_traits::{Ct, Nct};
use fixed_bigint::{FixedUInt, MulAccOps};
use num_traits::Zero;
use subtle::{
    Choice, ConditionallySelectable, ConstantTimeEq, ConstantTimeGreater, ConstantTimeLess,
};

// ---------------------------------------------------------------------------
// Default `P = Nct` preserves existing shape.
// ---------------------------------------------------------------------------

#[test]
fn existing_shape_still_compiles_under_default() {
    // The classic two-parameter form resolves to Nct via the default.
    let a: FixedUInt<u8, 4> = FixedUInt::from([1u8, 2, 3, 4]);
    let b: FixedUInt<u8, 4, Nct> = a; // type-system sanity
    assert_eq!(b, FixedUInt::from([1u8, 2, 3, 4]));
}

// ---------------------------------------------------------------------------
// Conversions: Nct -> Ct free (safe), Ct -> Nct via explicit forget_ct.
// ---------------------------------------------------------------------------

#[test]
fn nct_to_ct_is_free_from_impl() {
    let n: FixedUInt<u8, 4, Nct> = FixedUInt::from([0xDEu8, 0xAD, 0xBE, 0xEF]);
    let c: FixedUInt<u8, 4, Ct> = n.into();
    // Round-trip via forget_ct for value equality (the variants are
    // intentionally distinct types, so `assert_eq!(n, c)` wouldn't typecheck).
    let n2: FixedUInt<u8, 4, Nct> = c.forget_ct();
    assert_eq!(n, n2);
}

#[test]
fn forget_ct_is_an_explicit_named_method() {
    // The Ct -> Nct direction is *not* `From`/`Into` — it's a named method.
    // The following would not compile if it were `From`:
    //     let n: FixedUInt<u8, 4, Nct> = c.into();  // (error: no impl)
    let c: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from([1u8, 2, 3, 4]).into();
    let n: FixedUInt<u8, 4, Nct> = c.forget_ct();
    assert_eq!(n, FixedUInt::from([1u8, 2, 3, 4]));
}

// ---------------------------------------------------------------------------
// subtle integration — Ct variant only.
// ---------------------------------------------------------------------------

#[test]
fn ct_variant_has_constant_time_eq() {
    let a: FixedUInt<u32, 4, Ct> = FixedUInt::<u32, 4, Nct>::from([1u32, 2, 3, 4]).into();
    let b: FixedUInt<u32, 4, Ct> = FixedUInt::<u32, 4, Nct>::from([1u32, 2, 3, 4]).into();
    let c: FixedUInt<u32, 4, Ct> = FixedUInt::<u32, 4, Nct>::from([1u32, 2, 3, 5]).into();
    assert!(bool::from(a.ct_eq(&b)));
    assert!(!bool::from(a.ct_eq(&c)));
}

#[test]
fn ct_variant_has_conditional_select() {
    let a: FixedUInt<u32, 4, Ct> = FixedUInt::<u32, 4, Nct>::from([0xAAu32, 0, 0, 0]).into();
    let b: FixedUInt<u32, 4, Ct> = FixedUInt::<u32, 4, Nct>::from([0xBBu32, 0, 0, 0]).into();
    let pick_a = <FixedUInt<u32, 4, Ct> as ConditionallySelectable>::conditional_select(
        &a,
        &b,
        Choice::from(0),
    );
    let pick_b = <FixedUInt<u32, 4, Ct> as ConditionallySelectable>::conditional_select(
        &a,
        &b,
        Choice::from(1),
    );
    assert_eq!(pick_a.forget_ct(), a.forget_ct());
    assert_eq!(pick_b.forget_ct(), b.forget_ct());
}

#[test]
fn nct_variant_does_not_have_constant_time_eq() {
    // The following SHOULD fail to compile if uncommented — Nct lacks the
    // subtle impls by design:
    //
    //     let n: FixedUInt<u32, 4, Nct> = FixedUInt::from([1u8, 2, 3, 4]);
    //     let _ = <FixedUInt<u32, 4, Nct> as ConstantTimeEq>::ct_eq(&n, &n);
    //     // error: ConstantTimeEq is not implemented for FixedUInt<_, _, Nct>
    //
    // We can't write a runtime test that asserts a trait isn't implemented,
    // but the compile-error fallback test was verified manually.
}

// ---------------------------------------------------------------------------
// MulAccOps demo migration: get_word returns Option for Nct, CtOption for Ct.
// ---------------------------------------------------------------------------

#[test]
fn mul_acc_ops_get_word_nct_returns_option() {
    let val: FixedUInt<u8, 4, Nct> = FixedUInt::from([0x78u8, 0x56, 0x34, 0x12]);
    let w0 = <FixedUInt<u8, 4, Nct> as MulAccOps>::get_word(&val, 0);
    let w3 = <FixedUInt<u8, 4, Nct> as MulAccOps>::get_word(&val, 3);
    let oob = <FixedUInt<u8, 4, Nct> as MulAccOps>::get_word(&val, 4);
    // Plain Option — Some/None.
    assert_eq!(w0, Some(0x78u8));
    assert_eq!(w3, Some(0x12u8));
    assert_eq!(oob, None);
}

#[test]
fn mul_acc_ops_get_word_ct_returns_ctoption() {
    let val: FixedUInt<u8, 4, Ct> =
        FixedUInt::<u8, 4, Nct>::from([0x78u8, 0x56, 0x34, 0x12]).into();
    let w0 = <FixedUInt<u8, 4, Ct> as MulAccOps>::get_word(&val, 0);
    let w3 = <FixedUInt<u8, 4, Ct> as MulAccOps>::get_word(&val, 3);
    let oob = <FixedUInt<u8, 4, Ct> as MulAccOps>::get_word(&val, 4);
    // CtOption — validity is a Choice, not an enum discriminant.
    assert!(bool::from(w0.is_some()));
    assert!(bool::from(w3.is_some()));
    assert!(!bool::from(oob.is_some()));
    assert_eq!(w0.unwrap_or(0u8), 0x78u8);
    assert_eq!(w3.unwrap_or(0u8), 0x12u8);
    // Out-of-range gives the default; validity bit says don't use it.
    assert_eq!(oob.unwrap_or(0xAAu8), 0xAAu8);
}

// ---------------------------------------------------------------------------
// Combined-binary scenario: Nct and Ct in the same test.
// ---------------------------------------------------------------------------

#[test]
fn nct_and_ct_coexist_as_distinct_types() {
    type FastU32 = FixedUInt<u8, 4, Nct>;
    type CtU32 = FixedUInt<u8, 4, Ct>;

    let fast: FastU32 = FixedUInt::from([0x01u8, 0x02, 0x03, 0x04]);
    let ct: CtU32 = FixedUInt::<u8, 4, Nct>::from([0x01u8, 0x02, 0x03, 0x04]).into();

    // Each gets the right MulAccOps::get_word return type.
    let _w_fast: Option<u8> = <FastU32 as MulAccOps>::get_word(&fast, 0);
    let _w_ct: subtle::CtOption<u8> = <CtU32 as MulAccOps>::get_word(&ct, 0);

    // They're distinct types — no accidental interchange. The following
    // SHOULD fail to compile if uncommented:
    //     let _: FastU32 = ct;  // mismatched types
    //     let _: CtU32 = fast;  // mismatched types
}

// ---------------------------------------------------------------------------
// Zero / One delegation still works through the personality default.
// ---------------------------------------------------------------------------

#[test]
fn zero_via_num_traits_still_resolves() {
    let z: FixedUInt<u32, 4> = FixedUInt::zero();
    assert!(z.is_zero());
}

#[test]
fn ct_variant_supports_add() {
    let a: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from(100u8).into();
    let b: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from(50u8).into();
    let sum = a + b;
    assert_eq!(sum.forget_ct(), FixedUInt::from(150u8));
}

#[test]
fn ct_variant_supports_sub() {
    let a: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from(100u8).into();
    let b: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from(30u8).into();
    let diff = a - b;
    assert_eq!(diff.forget_ct(), FixedUInt::from(70u8));
}

#[test]
fn ct_variant_supports_mul() {
    let a: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from(7u8).into();
    let b: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from(13u8).into();
    let product = a * b;
    assert_eq!(product.forget_ct(), FixedUInt::from(91u8));
}

#[test]
fn ct_variant_supports_bitwise() {
    let a: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from(0b1100_1010u8).into();
    let b: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from(0b1010_1100u8).into();
    let and = a & b;
    let or = a | b;
    let xor = a ^ b;
    assert_eq!(and.forget_ct(), FixedUInt::from(0b1000_1000u8));
    assert_eq!(or.forget_ct(), FixedUInt::from(0b1110_1110u8));
    assert_eq!(xor.forget_ct(), FixedUInt::from(0b0110_0110u8));
}

#[test]
fn ct_variant_supports_eq_via_partialeq() {
    let a: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from(42u8).into();
    let b: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from(42u8).into();
    let c: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from(43u8).into();
    // PartialEq works (delegates to the generalized impl).
    assert!(a == b);
    assert!(a != c);
}

#[test]
fn is_zero_works_correctly_under_both_personalities() {
    use fixed_bigint::const_numtraits::{ConstZero, Zero};

    let z_nct: FixedUInt<u8, 4, Nct> = FixedUInt::from(0u8);
    let nz_nct: FixedUInt<u8, 4, Nct> = FixedUInt::from(42u8);
    // Non-zero in the high limb to exercise the difference between
    // short-circuit (Nct) and OR-fold (Ct) bodies.
    let high_nz_nct: FixedUInt<u8, 4, Nct> = FixedUInt::from([0u8, 0, 0, 1]);

    assert!(<FixedUInt<u8, 4, Nct> as Zero>::is_zero(&z_nct));
    assert!(!<FixedUInt<u8, 4, Nct> as Zero>::is_zero(&nz_nct));
    assert!(!<FixedUInt<u8, 4, Nct> as Zero>::is_zero(&high_nz_nct));

    let z_ct: FixedUInt<u8, 4, Ct> = z_nct.into();
    let nz_ct: FixedUInt<u8, 4, Ct> = nz_nct.into();
    let high_nz_ct: FixedUInt<u8, 4, Ct> = high_nz_nct.into();

    // Same answers as Nct — different code path under the hood
    // (`match P::TAG` selects `const_is_zero_ct` here).
    assert!(<FixedUInt<u8, 4, Ct> as Zero>::is_zero(&z_ct));
    assert!(!<FixedUInt<u8, 4, Ct> as Zero>::is_zero(&nz_ct));
    assert!(!<FixedUInt<u8, 4, Ct> as Zero>::is_zero(&high_nz_ct));
}

#[test]
fn is_one_works_correctly_under_both_personalities() {
    use fixed_bigint::const_numtraits::{ConstOne, One};

    let one_nct: FixedUInt<u8, 4, Nct> = FixedUInt::from(1u8);
    let zero_nct: FixedUInt<u8, 4, Nct> = FixedUInt::from(0u8);
    let two_nct: FixedUInt<u8, 4, Nct> = FixedUInt::from(2u8);
    // High-limb-set distinguishes short-circuit from OR-fold timing.
    let high_set_nct: FixedUInt<u8, 4, Nct> = FixedUInt::from([1u8, 0, 0, 1]);

    assert!(<FixedUInt<u8, 4, Nct> as One>::is_one(&one_nct));
    assert!(!<FixedUInt<u8, 4, Nct> as One>::is_one(&zero_nct));
    assert!(!<FixedUInt<u8, 4, Nct> as One>::is_one(&two_nct));
    assert!(!<FixedUInt<u8, 4, Nct> as One>::is_one(&high_set_nct));

    let one_ct: FixedUInt<u8, 4, Ct> = one_nct.into();
    let zero_ct: FixedUInt<u8, 4, Ct> = zero_nct.into();
    let two_ct: FixedUInt<u8, 4, Ct> = two_nct.into();
    let high_set_ct: FixedUInt<u8, 4, Ct> = high_set_nct.into();

    // Same answers as Nct — different code path under the hood
    // (`match P::TAG` selects `const_is_one_ct` here).
    assert!(<FixedUInt<u8, 4, Ct> as One>::is_one(&one_ct));
    assert!(!<FixedUInt<u8, 4, Ct> as One>::is_one(&zero_ct));
    assert!(!<FixedUInt<u8, 4, Ct> as One>::is_one(&two_ct));
    assert!(!<FixedUInt<u8, 4, Ct> as One>::is_one(&high_set_ct));
}

#[test]
fn nct_and_ct_arithmetic_are_distinct() {
    // The type system prevents mixing personalities in operators — these
    // SHOULD fail to compile if uncommented:
    //
    //     let n: FixedUInt<u8, 4, Nct> = FixedUInt::from(1u8);
    //     let c: FixedUInt<u8, 4, Ct>  = FixedUInt::<u8, 4, Nct>::from(2u8).into();
    //     let _ = n + c;  // error: mismatched types
    //
    // Both variants individually have arithmetic; mixing requires an
    // explicit conversion. This is the property we want — accidentally
    // mixing a CT value into an NCT operation can't happen silently.

    // Within-personality arithmetic does work, end-to-end:
    let n: FixedUInt<u8, 4, Nct> = FixedUInt::from(2u8) * FixedUInt::from(3u8);
    let c: FixedUInt<u8, 4, Ct> = {
        let a: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from(2u8).into();
        let b: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from(3u8).into();
        a * b
    };
    assert_eq!(n, FixedUInt::from(6u8));
    assert_eq!(c.forget_ct(), FixedUInt::from(6u8));
}

#[test]
fn ct_variant_supports_constant_time_greater() {
    let small: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from([1u8, 0, 0, 0]).into();
    let big: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from([0u8, 0, 0, 1]).into();
    let same: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from([1u8, 0, 0, 0]).into();

    assert_eq!(big.ct_gt(&small).unwrap_u8(), 1);
    assert_eq!(small.ct_gt(&big).unwrap_u8(), 0);
    assert_eq!(small.ct_gt(&same).unwrap_u8(), 0); // equal is not strictly greater
}

#[test]
fn ct_variant_supports_constant_time_less() {
    let small: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from([1u8, 0, 0, 0]).into();
    let big: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from([0u8, 0, 0, 1]).into();
    let same: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from([1u8, 0, 0, 0]).into();

    assert_eq!(small.ct_lt(&big).unwrap_u8(), 1);
    assert_eq!(big.ct_lt(&small).unwrap_u8(), 0);
    assert_eq!(small.ct_lt(&same).unwrap_u8(), 0); // equal is not strictly less
}

#[test]
fn ct_compare_decides_on_high_limb_first() {
    // Demonstrates correctness of the high-to-low scan: the decision
    // is locked by the first differing limb, even if a lower limb
    // would have suggested the opposite ordering.
    let a: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from([255u8, 0, 0, 1]).into();
    let b: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from([0u8, 0, 0, 2]).into();
    // a's low limb is huge but b's high limb is bigger — b > a wins.
    assert_eq!(b.ct_gt(&a).unwrap_u8(), 1);
    assert_eq!(a.ct_gt(&b).unwrap_u8(), 0);
}

#[test]
fn nct_variant_does_not_have_ct_gt() {
    // `ConstantTimeGreater` is only impl'd on the Ct variant — uncommenting
    // this would fail to compile, which is the additive-API guarantee.
    //
    //     let n: FixedUInt<u8, 4, Nct> = FixedUInt::from(1u8);
    //     let _ = n.ct_gt(&n);  // error: method `ct_gt` is not in scope
}

#[test]
fn leading_zeros_works_under_both_personalities() {
    use fixed_bigint::PrimBits;

    // Zero: full word_bits * N leading zeros.
    let z_nct: FixedUInt<u8, 4, Nct> = FixedUInt::from(0u8);
    let z_ct: FixedUInt<u8, 4, Ct> = z_nct.into();
    assert_eq!(z_nct.leading_zeros(), 32);
    assert_eq!(z_ct.leading_zeros(), 32);

    // Single low-limb value: leading_zeros depends only on that limb plus
    // the empty high limbs.
    let low_nct: FixedUInt<u8, 4, Nct> = FixedUInt::from([0x80u8, 0, 0, 0]);
    let low_ct: FixedUInt<u8, 4, Ct> = low_nct.into();
    assert_eq!(low_nct.leading_zeros(), 24); // 3 zero high limbs + 0 in MSB of 0x80
    assert_eq!(low_ct.leading_zeros(), 24);

    // High-limb-set: 0 leading zeros at the very top.
    let high_nct: FixedUInt<u8, 4, Nct> = FixedUInt::from([0, 0, 0, 0x80u8]);
    let high_ct: FixedUInt<u8, 4, Ct> = high_nct.into();
    assert_eq!(high_nct.leading_zeros(), 0);
    assert_eq!(high_ct.leading_zeros(), 0);

    // Middle: 0x01 in second-from-top limb.
    let mid_nct: FixedUInt<u8, 4, Nct> = FixedUInt::from([0, 0, 0x01u8, 0]);
    let mid_ct: FixedUInt<u8, 4, Ct> = mid_nct.into();
    assert_eq!(mid_nct.leading_zeros(), 15); // 1 full zero high limb + 7 zeros in 0x01
    assert_eq!(mid_ct.leading_zeros(), 15);
}

#[test]
fn trailing_zeros_works_under_both_personalities() {
    use fixed_bigint::PrimBits;

    // Zero: full width.
    let z_nct: FixedUInt<u8, 4, Nct> = FixedUInt::from(0u8);
    let z_ct: FixedUInt<u8, 4, Ct> = z_nct.into();
    assert_eq!(z_nct.trailing_zeros(), 32);
    assert_eq!(z_ct.trailing_zeros(), 32);

    // 0x01 in lowest limb: 0 trailing zeros.
    let one_nct: FixedUInt<u8, 4, Nct> = FixedUInt::from(1u8);
    let one_ct: FixedUInt<u8, 4, Ct> = one_nct.into();
    assert_eq!(one_nct.trailing_zeros(), 0);
    assert_eq!(one_ct.trailing_zeros(), 0);

    // 0x80 in lowest limb: 7 trailing zeros.
    let high_bit_nct: FixedUInt<u8, 4, Nct> = FixedUInt::from(0x80u8);
    let high_bit_ct: FixedUInt<u8, 4, Ct> = high_bit_nct.into();
    assert_eq!(high_bit_nct.trailing_zeros(), 7);
    assert_eq!(high_bit_ct.trailing_zeros(), 7);

    // 0x01 in third limb: 16 trailing zeros (two empty limbs + 0 within 0x01).
    let mid_nct: FixedUInt<u8, 4, Nct> = FixedUInt::from([0, 0, 0x01u8, 0]);
    let mid_ct: FixedUInt<u8, 4, Ct> = mid_nct.into();
    assert_eq!(mid_nct.trailing_zeros(), 16);
    assert_eq!(mid_ct.trailing_zeros(), 16);

    // 0x80 in top limb: 31 trailing zeros (3 empty + 7 within 0x80).
    let top_nct: FixedUInt<u8, 4, Nct> = FixedUInt::from([0, 0, 0, 0x80u8]);
    let top_ct: FixedUInt<u8, 4, Ct> = top_nct.into();
    assert_eq!(top_nct.trailing_zeros(), 31);
    assert_eq!(top_ct.trailing_zeros(), 31);
}

#[test]
fn bit_length_works_under_both_personalities() {
    // bit_length = total_bits - leading_zeros, so it inherits the dispatch.
    let z_nct: FixedUInt<u8, 4, Nct> = FixedUInt::from(0u8);
    let z_ct: FixedUInt<u8, 4, Ct> = z_nct.into();
    assert_eq!(z_nct.bit_length(), 0);
    assert_eq!(z_ct.bit_length(), 0);

    let v_nct: FixedUInt<u8, 4, Nct> = FixedUInt::from([0, 0, 0x01u8, 0]);
    let v_ct: FixedUInt<u8, 4, Ct> = v_nct.into();
    assert_eq!(v_nct.bit_length(), 17); // top bit at position 16 → length 17
    assert_eq!(v_ct.bit_length(), 17);

    let full_nct: FixedUInt<u8, 4, Nct> = FixedUInt::from([0xFF, 0xFF, 0xFF, 0xFFu8]);
    let full_ct: FixedUInt<u8, 4, Ct> = full_nct.into();
    assert_eq!(full_nct.bit_length(), 32);
    assert_eq!(full_ct.bit_length(), 32);
}

#[test]
fn shl_works_under_both_personalities() {
    // Direct sanity: small shifts produce the same value.
    for shift in [0usize, 1, 3, 7, 8, 15, 16, 23, 24, 31] {
        let nct: FixedUInt<u8, 4, Nct> = FixedUInt::from([0x12u8, 0x34, 0x56, 0x78]);
        let ct: FixedUInt<u8, 4, Ct> = nct.into();
        let nct_shifted = nct << shift;
        let ct_shifted = ct << shift;
        assert_eq!(
            nct_shifted,
            ct_shifted.forget_ct(),
            "shl mismatch at shift={}",
            shift
        );
    }

    // Edge cases at and above bit_size (32 for u8*4).
    for shift in [32usize, 33, 47, 64, 100, 1024] {
        let nct: FixedUInt<u8, 4, Nct> = FixedUInt::from([0x12u8, 0x34, 0x56, 0x78]);
        let ct: FixedUInt<u8, 4, Ct> = nct.into();
        let nct_shifted = nct << shift;
        let ct_shifted = ct << shift;
        assert_eq!(
            nct_shifted,
            ct_shifted.forget_ct(),
            "shl mismatch at oversized shift={}",
            shift
        );
        // For shifts >= bit_size, both bodies must zero the result.
        assert!(num_traits::Zero::is_zero(&nct_shifted));
        assert!(num_traits::Zero::is_zero(&ct_shifted.forget_ct()));
    }
}

#[test]
fn shl_shr_u32_overflow_returns_zero() {
    // Shl<u32>/Shr<u32> previously did `bits as usize`, truncating on
    // 16-bit-usize targets. The fix routes through normalize_shift_amount.
    // Regression-check the semantics: any u32 shift >= BIT_SIZE produces 0.
    let v: FixedUInt<u8, 4, Nct> = FixedUInt::from([0x12u8, 0x34, 0x56, 0x78]);
    let vc: FixedUInt<u8, 4, Ct> = v.into();
    for shift in [32u32, 33, 100, 1024, u32::MAX] {
        assert!(num_traits::Zero::is_zero(&(v << shift)));
        assert!(num_traits::Zero::is_zero(&(v >> shift)));
        assert!(num_traits::Zero::is_zero(&((vc << shift).forget_ct())));
        assert!(num_traits::Zero::is_zero(&((vc >> shift).forget_ct())));
    }
}

#[test]
fn resize_preserves_personality() {
    // Regression: resize() used to return FixedUInt<T, N2> (defaulted to Nct),
    // silently stripping Ct. Now it preserves P. The CT-typed bindings below
    // would not type-check if resize defaulted back to Nct.
    let c: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from([1u8, 2, 3, 4]).into();
    let grown: FixedUInt<u8, 6, Ct> = c.resize();
    let shrunk: FixedUInt<u8, 2, Ct> = c.resize();
    assert_eq!(grown.forget_ct(), FixedUInt::from([1u8, 2, 3, 4, 0, 0]));
    assert_eq!(shrunk.forget_ct(), FixedUInt::from([1u8, 2]));

    // Nct path still resolves to Nct without needing a turbofish.
    let n: FixedUInt<u8, 4, Nct> = FixedUInt::from([9u8, 8, 7, 6]);
    let n2: FixedUInt<u8, 3, Nct> = n.resize();
    assert_eq!(n2, FixedUInt::from([9u8, 8, 7]));
}

#[test]
fn shr_works_under_both_personalities() {
    for shift in [0usize, 1, 3, 7, 8, 15, 16, 23, 24, 31] {
        let nct: FixedUInt<u8, 4, Nct> = FixedUInt::from([0x12u8, 0x34, 0x56, 0x78]);
        let ct: FixedUInt<u8, 4, Ct> = nct.into();
        let nct_shifted = nct >> shift;
        let ct_shifted = ct >> shift;
        assert_eq!(
            nct_shifted,
            ct_shifted.forget_ct(),
            "shr mismatch at shift={}",
            shift
        );
    }

    for shift in [32usize, 33, 47, 64, 100, 1024] {
        let nct: FixedUInt<u8, 4, Nct> = FixedUInt::from([0x12u8, 0x34, 0x56, 0x78]);
        let ct: FixedUInt<u8, 4, Ct> = nct.into();
        let nct_shifted = nct >> shift;
        let ct_shifted = ct >> shift;
        assert_eq!(
            nct_shifted,
            ct_shifted.forget_ct(),
            "shr mismatch at oversized shift={}",
            shift
        );
        assert!(num_traits::Zero::is_zero(&nct_shifted));
        assert!(num_traits::Zero::is_zero(&ct_shifted.forget_ct()));
    }
}

#[test]
fn is_power_of_two_works_under_both_personalities() {
    use fixed_bigint::const_numtraits::{IsPowerOfTwo, NextPowerOfTwo};

    // Zero is not a power of two — exercises the `n == 0` short-circuit path
    // on Nct and the unconditional fallback on Ct.
    let z_nct: FixedUInt<u8, 4, Nct> = FixedUInt::from(0u8);
    let z_ct: FixedUInt<u8, 4, Ct> = z_nct.into();
    assert!(!z_nct.is_power_of_two());
    assert!(!z_ct.is_power_of_two());

    // Exact powers of two — both arms agree.
    for v in [1u8, 2, 4, 8, 16, 32, 64, 128] {
        let n: FixedUInt<u8, 4, Nct> = FixedUInt::from(v);
        let c: FixedUInt<u8, 4, Ct> = n.into();
        assert!(n.is_power_of_two(), "Nct: {} should be a power of two", v);
        assert!(c.is_power_of_two(), "Ct: {} should be a power of two", v);
    }

    // Powers of two in higher limbs.
    let high_pow_nct: FixedUInt<u8, 4, Nct> = FixedUInt::from([0u8, 0, 0, 0x40]); // 2^30
    let high_pow_ct: FixedUInt<u8, 4, Ct> = high_pow_nct.into();
    assert!(high_pow_nct.is_power_of_two());
    assert!(high_pow_ct.is_power_of_two());

    // Non-powers of two — both arms agree.
    for v in [3u8, 5, 6, 7, 9, 15, 100, 255] {
        let n: FixedUInt<u8, 4, Nct> = FixedUInt::from(v);
        let c: FixedUInt<u8, 4, Ct> = n.into();
        assert!(
            !n.is_power_of_two(),
            "Nct: {} should not be a power of two",
            v
        );
        assert!(
            !c.is_power_of_two(),
            "Ct: {} should not be a power of two",
            v
        );
    }

    // Non-power-of-two with bits in multiple limbs.
    let multi_nct: FixedUInt<u8, 4, Nct> = FixedUInt::from([0x01u8, 0, 0, 0x01]);
    let multi_ct: FixedUInt<u8, 4, Ct> = multi_nct.into();
    assert!(!multi_nct.is_power_of_two());
    assert!(!multi_ct.is_power_of_two());
}

#[test]
fn pow_works_on_nct() {
    use num_traits::PrimInt;

    let cases: [(u8, u32, u32); 7] = [
        (2, 0, 1),
        (2, 1, 2),
        (2, 4, 16),
        (2, 7, 128),
        (3, 5, 243),
        (5, 3, 125),
        (10, 4, 10000),
    ];
    for (base, exp, expected) in cases {
        let n: FixedUInt<u32, 4, Nct> = FixedUInt::from(base as u32);
        let want: FixedUInt<u32, 4, Nct> = FixedUInt::from(expected);
        assert_eq!(
            PrimInt::pow(n, exp),
            want,
            "Nct {} ^ {} = {}",
            base,
            exp,
            expected
        );
    }
}

#[test]
fn pow_handles_exp_zero_and_one_on_nct() {
    use num_traits::PrimInt;

    let zero_nct: FixedUInt<u32, 4, Nct> = FixedUInt::from(0u32);
    let one: FixedUInt<u32, 4, Nct> = FixedUInt::from(1u32);
    assert_eq!(PrimInt::pow(zero_nct, 0), one);

    let x_nct: FixedUInt<u32, 4, Nct> = FixedUInt::from(42u32);
    assert_eq!(PrimInt::pow(x_nct, 1), x_nct);
}

#[test]
fn ct_add_wraps_instead_of_panicking() {
    // Under Nct, Add+overflow panics in debug. Under Ct, it should wrap
    // silently — the maybe_panic call is bypassed by `maybe_panic_if`.
    let max_ct: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(0xFFFFu16).into();
    let one_ct: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(1u8).into();
    // Would panic under Nct (overflow); under Ct it wraps to 0.
    let result = max_ct + one_ct;
    assert_eq!(
        result.forget_ct(),
        FixedUInt::<u8, 2, Nct>::from(0u8),
        "Ct add should wrap"
    );
}

#[test]
fn ct_sub_wraps_instead_of_panicking() {
    let zero_ct: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(0u8).into();
    let one_ct: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(1u8).into();
    // 0 - 1 would underflow-panic under Nct; under Ct it wraps to MAX.
    let result = zero_ct - one_ct;
    assert_eq!(
        result.forget_ct(),
        FixedUInt::<u8, 2, Nct>::from(0xFFFFu16),
        "Ct sub should wrap"
    );
}

#[test]
fn ct_saturating_add_uses_ct_select() {
    use num_traits::SaturatingAdd;

    // Below saturation: behaves identically.
    let a_ct: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(100u8).into();
    let b_ct: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(200u8).into();
    let sum = SaturatingAdd::saturating_add(&a_ct, &b_ct);
    assert_eq!(sum.forget_ct(), FixedUInt::<u8, 2, Nct>::from(300u16));

    // At saturation: same result as Nct (max_value), different code path.
    let max_ct: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(0xFFFFu16).into();
    let one_ct: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(1u8).into();
    let sat = SaturatingAdd::saturating_add(&max_ct, &one_ct);
    assert_eq!(sat.forget_ct(), FixedUInt::<u8, 2, Nct>::from(0xFFFFu16));
}

#[test]
fn ct_saturating_sub_uses_ct_select() {
    use num_traits::SaturatingSub;

    let a_ct: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(200u8).into();
    let b_ct: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(100u8).into();
    let diff = SaturatingSub::saturating_sub(&a_ct, &b_ct);
    assert_eq!(diff.forget_ct(), FixedUInt::<u8, 2, Nct>::from(100u8));

    // Underflow saturates to zero.
    let zero_ct: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(0u8).into();
    let one_ct: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(1u8).into();
    let sat = SaturatingSub::saturating_sub(&zero_ct, &one_ct);
    assert_eq!(sat.forget_ct(), FixedUInt::<u8, 2, Nct>::from(0u8));
}

#[test]
fn ct_checked_add_returns_ctoption() {
    let a: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(100u8).into();
    let b: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(200u8).into();

    // No overflow: result valid and equals the expected sum.
    let ok = a.ct_checked_add(&b);
    assert!(bool::from(ok.is_some()));
    assert_eq!(ok.unwrap_or(a).forget_ct(), FixedUInt::from(300u16));

    // Overflow: validity Choice is 0.
    let max: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(0xFFFFu16).into();
    let one: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(1u8).into();
    let bad = max.ct_checked_add(&one);
    assert!(!bool::from(bad.is_some()));
}

#[test]
fn ct_checked_sub_returns_ctoption() {
    let a: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(200u8).into();
    let b: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(100u8).into();
    let ok = a.ct_checked_sub(&b);
    assert!(bool::from(ok.is_some()));
    assert_eq!(ok.unwrap_or(a).forget_ct(), FixedUInt::from(100u8));

    // Underflow case.
    let zero: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(0u8).into();
    let one: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(1u8).into();
    let bad = zero.ct_checked_sub(&one);
    assert!(!bool::from(bad.is_some()));
}

#[test]
fn ct_checked_mul_returns_ctoption() {
    let a: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(0x100u16).into();
    let b: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(0x100u16).into();
    // 0x100 * 0x100 = 0x10000, exceeds u16::MAX → overflow.
    let near = a.ct_checked_mul(&b);
    assert!(!bool::from(near.is_some()));

    let small_a: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(10u8).into();
    let small_b: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(20u8).into();
    let ok = small_a.ct_checked_mul(&small_b);
    assert!(bool::from(ok.is_some()));
    assert_eq!(ok.unwrap_or(small_a).forget_ct(), FixedUInt::from(200u8));
}

#[test]
fn abs_diff_works_under_both_personalities() {
    use fixed_bigint::const_numtraits::AbsDiff;

    let cases: [(u8, u8, u8); 6] = [
        (10, 3, 7), // a > b
        (3, 10, 7), // a < b
        (5, 5, 0),  // equal
        (0, 100, 100),
        (255, 0, 255),
        (200, 100, 100),
    ];

    for (a, b, expected) in cases {
        let an: FixedUInt<u8, 2, Nct> = FixedUInt::from(a);
        let bn: FixedUInt<u8, 2, Nct> = FixedUInt::from(b);
        let ac: FixedUInt<u8, 2, Ct> = an.into();
        let bc: FixedUInt<u8, 2, Ct> = bn.into();
        let want: FixedUInt<u8, 2, Nct> = FixedUInt::from(expected);
        assert_eq!(
            AbsDiff::abs_diff(an, bn),
            want,
            "Nct abs_diff({}, {}) = {}",
            a,
            b,
            expected
        );
        assert_eq!(
            AbsDiff::abs_diff(ac, bc).forget_ct(),
            want,
            "Ct abs_diff({}, {}) = {}",
            a,
            b,
            expected
        );
    }
}

#[test]
fn ct_checked_pow_returns_ctoption() {
    // No overflow: result valid and equals 2^8 = 256.
    let two_ct: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(2u8).into();
    let ok = two_ct.ct_checked_pow(8);
    assert!(bool::from(ok.is_some()));
    assert_eq!(ok.unwrap_or(two_ct).forget_ct(), FixedUInt::from(256u16));

    // Just-fits: 2^15 = 32768, fits in u16.
    let big = two_ct.ct_checked_pow(15);
    assert!(bool::from(big.is_some()));
    assert_eq!(big.unwrap_or(two_ct).forget_ct(), FixedUInt::from(32768u16));

    // Overflow: 2^16 = 65536, exceeds u16::MAX.
    let overflow = two_ct.ct_checked_pow(16);
    assert!(!bool::from(overflow.is_some()));

    // Overflow via base, not exponent: 256^2 = 65536.
    let base_overflow_ct: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(256u16).into();
    let bo = base_overflow_ct.ct_checked_pow(2);
    assert!(!bool::from(bo.is_some()));

    // Exp = 0 always succeeds, returns 1.
    let any_ct: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(42u8).into();
    let one = any_ct.ct_checked_pow(0);
    assert!(bool::from(one.is_some()));
    assert_eq!(one.unwrap_or(any_ct).forget_ct(), FixedUInt::from(1u8));
}

#[test]
fn ct_partial_eq_uses_or_fold() {
    // Nct array equality short-circuits at first differing limb. Ct
    // OR-folds all XOR-diffs so equality timing is independent of where
    // values differ. Same answer; different code path.
    let a_ct: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from([1u8, 2, 3, 4]).into();
    let same_ct: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from([1u8, 2, 3, 4]).into();
    let low_diff_ct: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from([2u8, 2, 3, 4]).into();
    let high_diff_ct: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from([1u8, 2, 3, 5]).into();
    assert_eq!(a_ct, same_ct);
    assert_ne!(a_ct, low_diff_ct); // differs in limb 0
    assert_ne!(a_ct, high_diff_ct); // differs in limb 3 (high)
}

#[test]
fn ct_display_and_hex_do_not_compile() {
    // These would expose limb values; the restriction to Nct-only means
    // they now fail to compile on Ct values. Verified manually; we can't
    // runtime-test that something doesn't compile.
    //
    //     let c: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from(42u8).into();
    //     let _ = format!("{}", c);    // error: Display not impl for Ct
    //     let _ = format!("{:x}", c);  // error: LowerHex not impl for Ct
    //     let _ = format!("{:X}", c);  // error: UpperHex not impl for Ct
    //
    // To format a Ct value the caller must `forget_ct()` first — making
    // the leak an explicit, greppable decision rather than an accident.
    let c: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from(42u8).into();
    let nct = c.forget_ct();
    assert_eq!(format!("{}", nct), "42");
    assert_eq!(format!("{:x}", nct), "2a");
}

#[test]
fn ct_debug_redacts_limb_values() {
    // Nct: standard derived-style Debug exposes limbs (intentional, for
    // development convenience). Ct: redacted to a placeholder so panic
    // messages / dbg! / logs can never leak secret values.
    let nct: FixedUInt<u8, 4, Nct> = FixedUInt::from([0xDE, 0xAD, 0xBE, 0xEF]);
    let ct: FixedUInt<u8, 4, Ct> = nct.into();
    let nct_dbg = format!("{:?}", nct);
    let ct_dbg = format!("{:?}", ct);
    // Only the two properties we actually care about: Nct exposes something
    // (so the two formats are distinguishable), Ct is the exact placeholder.
    assert!(!nct_dbg.is_empty());
    assert_ne!(nct_dbg, ct_dbg);
    assert_eq!(ct_dbg, "FixedUInt<…>");
    // Sanity: redaction doesn't depend on byte content — all-zero is also redacted.
    let zero_ct: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from(0u8).into();
    assert_eq!(format!("{:?}", zero_ct), "FixedUInt<…>");
}

#[test]
fn next_power_of_two_works_under_both_personalities() {
    use fixed_bigint::const_numtraits::{IsPowerOfTwo, NextPowerOfTwo};
    for (input, expected) in [
        (0u16, 1u16),
        (1, 1),
        (2, 2),
        (3, 4),
        (5, 8),
        (100, 128),
        (128, 128),
    ] {
        let n: FixedUInt<u8, 2, Nct> = FixedUInt::from(input);
        let c: FixedUInt<u8, 2, Ct> = n.into();
        assert_eq!(
            NextPowerOfTwo::next_power_of_two(n),
            FixedUInt::from(expected),
            "Nct next_power_of_two({}) = {}",
            input,
            expected,
        );
        assert_eq!(
            NextPowerOfTwo::next_power_of_two(c).forget_ct(),
            FixedUInt::from(expected),
            "Ct next_power_of_two({}) = {}",
            input,
            expected,
        );
    }
}

#[test]
fn ct_checked_next_power_of_two_returns_ctoption() {
    // Zero → 1, valid.
    let z: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(0u8).into();
    let r0 = z.ct_checked_next_power_of_two();
    assert!(bool::from(r0.is_some()));
    assert_eq!(r0.unwrap_or(z).forget_ct(), FixedUInt::from(1u8));

    // Just fits: 32768 is itself 2^15, the next-power-of-two is itself.
    let big: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(32768u16).into();
    let rbig = big.ct_checked_next_power_of_two();
    assert!(bool::from(rbig.is_some()));
    assert_eq!(rbig.unwrap_or(big).forget_ct(), FixedUInt::from(32768u16));

    // Overflow: 32769 → needs 2^16 = 65536 which is u16::MAX + 1.
    let overflow: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(32769u16).into();
    let rov = overflow.ct_checked_next_power_of_two();
    assert!(!bool::from(rov.is_some()));

    // 100 → 128.
    let v: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(100u8).into();
    let rv = v.ct_checked_next_power_of_two();
    assert!(bool::from(rv.is_some()));
    assert_eq!(rv.unwrap_or(v).forget_ct(), FixedUInt::from(128u8));
}

#[test]
fn ct_checked_shl_shr_return_ctoption() {
    let v: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(0x1234u16).into();

    // Within range: payloads match the expected wrapping shifts.
    let ok_l = v.ct_checked_shl(4);
    assert!(bool::from(ok_l.is_some()));
    assert_eq!(ok_l.unwrap_or(v).forget_ct(), FixedUInt::from(0x2340u16));
    let ok_r = v.ct_checked_shr(4);
    assert!(bool::from(ok_r.is_some()));
    assert_eq!(ok_r.unwrap_or(v).forget_ct(), FixedUInt::from(0x0123u16));

    // Beyond bit_size (= 16 for u8*2).
    let bad_l = v.ct_checked_shl(32);
    assert!(!bool::from(bad_l.is_some()));
    let bad_r = v.ct_checked_shr(32);
    assert!(!bool::from(bad_r.is_some()));
}

#[test]
fn ct_checked_composes_with_conditional_select() {
    use subtle::ConditionallySelectable;

    // The motivating shape: try a CT add; if it overflows, fall back to
    // a known-safe value. All decisions branch-free.
    let max: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(0xFFFFu16).into();
    let one: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(1u8).into();
    let fallback: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(42u8).into();

    let attempt = max.ct_checked_add(&one);
    // CtOption::unwrap_or under the hood is conditional_select between the
    // contained value and the fallback, gated by the validity Choice.
    let result = attempt.unwrap_or(fallback);

    assert_eq!(
        result.forget_ct(),
        FixedUInt::<u8, 2, Nct>::from(42u8),
        "overflow → fallback"
    );

    // No-overflow path: keep the result.
    let a: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(10u8).into();
    let b: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(20u8).into();
    let ok = a.ct_checked_add(&b);
    let kept = ok.unwrap_or(fallback);
    let _ = ConditionallySelectable::conditional_select(&kept, &fallback, subtle::Choice::from(0));
    assert_eq!(kept.forget_ct(), FixedUInt::<u8, 2, Nct>::from(30u8));
}

#[test]
fn ct_shr_by_trailing_zeros_pattern() {
    // The motivating modular-inverse use case: shr by tz(x), where
    // tz is a secret count. Both halves of the operation are CT under
    // Ct personality. Verifies the pieces compose correctly.
    use fixed_bigint::PrimBits;

    // Pick a value with a known trailing-zero count.
    // 0x10000000 = bit 28 set, so trailing_zeros == 28.
    let v_ct: FixedUInt<u8, 4, Ct> =
        FixedUInt::<u8, 4, Nct>::from([0x00u8, 0x00, 0x00, 0x10]).into();
    let tz = v_ct.trailing_zeros();
    assert_eq!(tz, 28);

    // shr by tz should normalize v_ct to its odd part (which is 1 here).
    let normalized: FixedUInt<u8, 4, Ct> = v_ct >> (tz as usize);
    let one: FixedUInt<u8, 4, Nct> = FixedUInt::from(1u8);
    assert_eq!(normalized.forget_ct(), one);
}

#[test]
fn ct_montgomery_conditional_subtract_pattern() {
    // The motivating use case: "if x >= N, subtract N" — the standard
    // Montgomery reduction tail. The CT idiom composes `ct_lt` with
    // `ConditionallySelectable`, never branching on a magnitude bit.
    //
    // Pick N = 100, then check that both inputs land in [0, N).
    let n_val: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from(100u8).into();

    let cases: [(u8, u8); 4] = [
        (50, 50),   // x < N: no subtraction
        (100, 0),   // x == N: subtract once (>=, not >)
        (150, 50),  // x > N: subtract once
        (200, 100), // x > N: subtract once
    ];

    for (x, expected) in cases {
        let x_ct: FixedUInt<u8, 4, Ct> = FixedUInt::<u8, 4, Nct>::from(x).into();
        // wrapping_sub is the CT-friendly subtractor — it never branches on
        // the result, so we compute the difference unconditionally and let
        // `conditional_select` discard it when geq is false.
        let diff_ct: FixedUInt<u8, 4, Ct> = num_traits::WrappingSub::wrapping_sub(&x_ct, &n_val);

        // geq = !lt  — both x > N and x == N should trigger subtraction
        let lt: Choice = x_ct.ct_lt(&n_val);
        let geq: Choice = !lt;

        // CT pick: if geq then diff else x
        let result: FixedUInt<u8, 4, Ct> = FixedUInt::conditional_select(&x_ct, &diff_ct, geq);

        let expected_nct: FixedUInt<u8, 4, Nct> = FixedUInt::from(expected);
        assert_eq!(
            result.forget_ct(),
            expected_nct,
            "x = {} expected {} got {:?}",
            x,
            expected,
            result.forget_ct()
        );
    }
}

#[test]
fn shl_assign_dispatches_under_both_personalities() {
    // Regression: assigns previously hard-wired the Nct shifter even on Ct,
    // leaking the secret shift amount. Verify behavioural parity with the
    // non-assign form across both arms.
    for shift in [0usize, 1, 7, 8, 15, 24, 31, 32, 33, 64, 1024] {
        let nct: FixedUInt<u8, 4, Nct> = FixedUInt::from([0x12u8, 0x34, 0x56, 0x78]);
        let ct: FixedUInt<u8, 4, Ct> = nct.into();
        let mut nct_a = nct;
        let mut ct_a = ct;
        nct_a <<= shift;
        ct_a <<= shift;
        assert_eq!(
            nct_a,
            ct_a.forget_ct(),
            "shl_assign mismatch shift={}",
            shift
        );
        assert_eq!(
            nct_a,
            nct << shift,
            "shl_assign vs shl mismatch shift={}",
            shift
        );
    }
}

#[test]
fn shr_assign_dispatches_under_both_personalities() {
    for shift in [0usize, 1, 7, 8, 15, 24, 31, 32, 33, 64, 1024] {
        let nct: FixedUInt<u8, 4, Nct> = FixedUInt::from([0x12u8, 0x34, 0x56, 0x78]);
        let ct: FixedUInt<u8, 4, Ct> = nct.into();
        let mut nct_a = nct;
        let mut ct_a = ct;
        nct_a >>= shift;
        ct_a >>= shift;
        assert_eq!(
            nct_a,
            ct_a.forget_ct(),
            "shr_assign mismatch shift={}",
            shift
        );
        assert_eq!(
            nct_a,
            nct >> shift,
            "shr_assign vs shr mismatch shift={}",
            shift
        );
    }
}

#[test]
fn ord_on_ct_agrees_with_nct() {
    // Regression: Ord::cmp on Ct used to call the short-circuiting const_cmp;
    // it now dispatches to a full-width scan via match P::TAG. Result must
    // still match Nct's ordering across positions where the decisive limb
    // varies.
    let cases: [([u8; 4], [u8; 4]); 6] = [
        ([1, 2, 3, 4], [1, 2, 3, 4]),    // equal
        ([1, 2, 3, 4], [1, 2, 3, 5]),    // differs at top (Less)
        ([1, 2, 3, 5], [1, 2, 3, 4]),    // differs at top (Greater)
        ([255, 0, 0, 1], [0, 0, 0, 2]),  // low-limb noise; top decides
        ([0, 0, 0xFF, 0], [0, 0, 0, 1]), // differs at second-from-top
        ([0xAA, 0xBB, 0xCC, 0xDD], [0xAA, 0xBB, 0xCC, 0xDD]),
    ];
    for (a, b) in cases {
        let an: FixedUInt<u8, 4, Nct> = FixedUInt::from(a);
        let bn: FixedUInt<u8, 4, Nct> = FixedUInt::from(b);
        let ac: FixedUInt<u8, 4, Ct> = an.into();
        let bc: FixedUInt<u8, 4, Ct> = bn.into();
        assert_eq!(ac.cmp(&bc), an.cmp(&bn), "cmp mismatch a={:?} b={:?}", a, b);
        assert_eq!(
            ac.partial_cmp(&bc),
            an.partial_cmp(&bn),
            "partial_cmp mismatch a={:?} b={:?}",
            a,
            b
        );
        // Cross-check against the CT-Choice comparators.
        assert_eq!(
            (ac.cmp(&bc) == core::cmp::Ordering::Greater),
            bool::from(ac.ct_gt(&bc)),
            "cmp/ct_gt disagree a={:?} b={:?}",
            a,
            b
        );
        assert_eq!(
            (ac.cmp(&bc) == core::cmp::Ordering::Less),
            bool::from(ac.ct_lt(&bc)),
            "cmp/ct_lt disagree a={:?} b={:?}",
            a,
            b
        );
    }
}

#[test]
fn next_power_of_two_saturates_to_max_on_ct_overflow() {
    use fixed_bigint::const_numtraits::{Bounded, IsPowerOfTwo, NextPowerOfTwo};

    // u16 type with Ct personality. Inputs whose next_power_of_two exceeds
    // u16::MAX should saturate to MAX, not silently return 0.
    let max_u16: FixedUInt<u8, 2, Ct> = <FixedUInt<u8, 2, Ct> as Bounded>::max_value();

    for input in [0x8001u16, 0xC000, 0xFFFF] {
        let v: FixedUInt<u8, 2, Ct> = FixedUInt::<u8, 2, Nct>::from(input).into();
        let r = NextPowerOfTwo::next_power_of_two(v);
        assert_eq!(
            r.forget_ct(),
            max_u16.forget_ct(),
            "Ct next_power_of_two({:#x}) should saturate to MAX",
            input
        );
    }

    // Non-overflow inputs still produce the exact power of two on both arms.
    for (input, expected) in [(0u16, 1u16), (1, 1), (5, 8), (100, 128), (32768, 32768)] {
        let n: FixedUInt<u8, 2, Nct> = FixedUInt::from(input);
        let c: FixedUInt<u8, 2, Ct> = n.into();
        assert_eq!(
            NextPowerOfTwo::next_power_of_two(n),
            FixedUInt::from(expected),
            "Nct next_power_of_two({})",
            input
        );
        assert_eq!(
            NextPowerOfTwo::next_power_of_two(c).forget_ct(),
            FixedUInt::from(expected),
            "Ct next_power_of_two({})",
            input
        );
    }
}
