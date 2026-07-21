use crate::harness::*;

#[test]
fn add() {
    fn body<C: Carrier>() {
        let a = C::from_u32(100);
        let b = C::from_u32(50);
        assert_eq!(a + b, C::from_u32(150));
        assert_eq!(WrappingAdd::wrapping_add(a, b), C::from_u32(150));
        assert_eq!(
            OverflowingAdd::overflowing_add(a, b),
            (C::from_u32(150), false)
        );
        assert_eq!(CheckedAdd::checked_add(a, b), Some(C::from_u32(150)));
        let mut m = a;
        m += b;
        assert_eq!(m, C::from_u32(150));

        // Overflow at the shared 32-bit width.
        let max = C::from_u32(MAX32);
        let one = C::from_u32(1);
        assert_eq!(WrappingAdd::wrapping_add(max, one), C::from_u32(0));
        assert_eq!(
            OverflowingAdd::overflowing_add(max, one),
            (C::from_u32(0), true)
        );
        assert_eq!(CheckedAdd::checked_add(max, one), None);
    }
    for_both_carriers!(body);
}

#[test]
fn sub() {
    fn body<C: Carrier>() {
        let a = C::from_u32(500);
        let b = C::from_u32(200);
        assert_eq!(a - b, C::from_u32(300));
        assert_eq!(WrappingSub::wrapping_sub(a, b), C::from_u32(300));
        assert_eq!(
            OverflowingSub::overflowing_sub(a, b),
            (C::from_u32(300), false)
        );
        assert_eq!(CheckedSub::checked_sub(a, b), Some(C::from_u32(300)));
        let mut m = a;
        m -= b;
        assert_eq!(m, C::from_u32(300));

        // Underflow wraps at 32 bits and reports a borrow.
        let one = C::from_u32(1);
        let two = C::from_u32(2);
        assert_eq!(WrappingSub::wrapping_sub(one, two), C::from_u32(MAX32));
        assert_eq!(
            OverflowingSub::overflowing_sub(one, two),
            (C::from_u32(MAX32), true)
        );
        assert_eq!(CheckedSub::checked_sub(one, two), None);
    }
    for_both_carriers!(body);
}

#[test]
fn mul() {
    fn body<C: Carrier>() {
        let a = C::from_u32(13);
        let b = C::from_u32(17);
        assert_eq!(a * b, C::from_u32(221));
        assert_eq!(WrappingMul::wrapping_mul(a, b), C::from_u32(221));
        assert_eq!(
            OverflowingMul::overflowing_mul(a, b),
            (C::from_u32(221), false)
        );
        assert_eq!(CheckedMul::checked_mul(a, b), Some(C::from_u32(221)));
        let mut m = a;
        m *= b;
        assert_eq!(m, C::from_u32(221));

        // 0x10000 * 0x10000 = 2^32 overflows 32 bits.
        let x = C::from_u32(0x1_0000);
        assert_eq!(WrappingMul::wrapping_mul(x, x), C::from_u32(0));
        assert_eq!(
            OverflowingMul::overflowing_mul(x, x),
            (C::from_u32(0), true)
        );
        assert_eq!(CheckedMul::checked_mul(x, x), None);
    }
    for_both_carriers!(body);
}

#[test]
fn carrying_mul_high_half() {
    fn body<C: Carrier>() {
        // 0x10000 * 0x10000 = 2^32: low half 0, high half 1.
        let x = C::from_u32(0x1_0000);
        let (lo, hi) = CarryingMul::carrying_mul(x, x, C::from_u32(0));
        assert_eq!(lo, C::from_u32(0));
        assert_eq!(hi, C::from_u32(1));
        // No overflow: 5 * 7 + 3 = 38, high half 0.
        let (lo, hi) = CarryingMul::carrying_mul(C::from_u32(5), C::from_u32(7), C::from_u32(3));
        assert_eq!(lo, C::from_u32(38));
        assert_eq!(hi, C::from_u32(0));
    }
    for_both_carriers!(body);
}

#[test]
fn div_rem() {
    fn body<C: Carrier>() {
        let a = C::from_u32(100);
        let b = C::from_u32(7);
        assert_eq!(a / b, C::from_u32(14));
        assert_eq!(a % b, C::from_u32(2));
        // Round-trip: (a / b) * b + a % b == a.
        assert_eq!((a / b) * b + a % b, a);
        // Dividend < divisor.
        assert_eq!(C::from_u32(3) / C::from_u32(10), C::from_u32(0));
        assert_eq!(C::from_u32(3) % C::from_u32(10), C::from_u32(3));
        // Boundary identities at the max width.
        let max = C::from_u32(MAX32);
        let one = C::from_u32(1);
        assert_eq!(max / one, max);
        assert_eq!(max % one, C::from_u32(0));
        assert_eq!(max / max, one);
        assert_eq!(max % max, C::from_u32(0));

        let mut q = a;
        q /= b;
        assert_eq!(q, C::from_u32(14));
        let mut r = a;
        r %= b;
        assert_eq!(r, C::from_u32(2));
    }
    for_both_carriers!(body);
}

#[test]
fn saturating() {
    fn body<C: Carrier>() {
        let max = C::from_u32(MAX32);
        let one = C::from_u32(1);
        // add saturates up to the width max
        assert_eq!(SaturatingAdd::saturating_add(max, one), max);
        assert_eq!(
            SaturatingAdd::saturating_add(C::from_u32(100), C::from_u32(50)),
            C::from_u32(150)
        );
        // sub clamps to zero
        assert_eq!(
            SaturatingSub::saturating_sub(one, C::from_u32(2)),
            C::from_u32(0)
        );
        assert_eq!(
            SaturatingSub::saturating_sub(C::from_u32(500), C::from_u32(200)),
            C::from_u32(300)
        );
        // 2^16 * 2^16 = 2^32 overflows the width → saturates up
        let x = C::from_u32(0x1_0000);
        assert_eq!(SaturatingMul::saturating_mul(x, x), max);
        assert_eq!(
            SaturatingMul::saturating_mul(C::from_u32(13), C::from_u32(17)),
            C::from_u32(221)
        );
    }
    for_both_carriers!(body);
}

#[test]
fn checked_div_rem() {
    fn body<C: Carrier>() {
        let a = C::from_u32(100);
        let b = C::from_u32(7);
        assert_eq!(CheckedDiv::checked_div(a, b), Some(C::from_u32(14)));
        assert_eq!(CheckedRem::checked_rem(a, b), Some(C::from_u32(2)));
        // divide by zero → None (not a panic)
        let zero = C::from_u32(0);
        assert_eq!(CheckedDiv::checked_div(a, zero), None);
        assert_eq!(CheckedRem::checked_rem(a, zero), None);
    }
    for_both_carriers!(body);
}

// Display is tested in the num-traits harness (carrier_num_traits.rs): FixedUInt
// only implements Display when `num-traits` is on, so a Display bound here would
// break the feature-free build. HeaplessBigInt's own feature-independent Display
// is covered in tests/heapless_string.rs.

#[test]
fn pow() {
    fn body<C: Carrier>() {
        assert_eq!(
            CheckedPow::checked_pow(C::from_u32(2), 10),
            Some(C::from_u32(1024))
        );
        assert_eq!(
            CheckedPow::checked_pow(C::from_u32(3), 0),
            Some(C::from_u32(1))
        ); // x^0 = 1
        assert_eq!(
            CheckedPow::checked_pow(C::from_u32(5), 1),
            Some(C::from_u32(5))
        );
        assert_eq!(
            CheckedPow::checked_pow(C::from_u32(7), 3),
            Some(C::from_u32(343))
        );
        // 2^32 overflows the 32-bit width → None.
        assert_eq!(CheckedPow::checked_pow(C::from_u32(2), 32), None);
        // strict_pow returns the value when it fits.
        assert_eq!(StrictPow::strict_pow(C::from_u32(2), 10), C::from_u32(1024));
    }
    for_both_carriers!(body);
}

// The `strict_*` family returns the value on the in-range path (the overflow
// panic is width-dependent, so it lives in each carrier's own suite).
#[test]
fn strict_arithmetic() {
    fn body<C: Carrier>() {
        assert_eq!(
            StrictAdd::strict_add(C::from_u32(100), C::from_u32(50)),
            C::from_u32(150)
        );
        assert_eq!(
            StrictSub::strict_sub(C::from_u32(150), C::from_u32(50)),
            C::from_u32(100)
        );
        assert_eq!(
            StrictMul::strict_mul(C::from_u32(13), C::from_u32(17)),
            C::from_u32(221)
        );
        assert_eq!(
            StrictDiv::strict_div(C::from_u32(221), C::from_u32(17)),
            C::from_u32(13)
        );
        assert_eq!(
            StrictRem::strict_rem(C::from_u32(223), C::from_u32(17)),
            C::from_u32(2)
        );
        assert_eq!(
            StrictShl::strict_shl(C::from_u32(1), 8),
            C::from_u32(0x0000_0100)
        );
        assert_eq!(
            StrictShr::strict_shr(C::from_u32(0x0000_0100), 8),
            C::from_u32(1)
        );
    }
    for_both_carriers!(body);
}

// Extended add/sub with carry/borrow in and out, at the 32-bit width boundary.
#[test]
fn carrying_add_borrowing_sub() {
    fn body<C: Carrier>() {
        let (s, c) = CarryingAdd::carrying_add(C::from_u32(100), C::from_u32(50), false);
        assert_eq!((s, c), (C::from_u32(150), false));
        let (s, c) = CarryingAdd::carrying_add(C::from_u32(100), C::from_u32(50), true);
        assert_eq!((s, c), (C::from_u32(151), false));
        // width max + 1 carries out, wrapping to zero.
        let (s, c) = CarryingAdd::carrying_add(C::from_u32(MAX32), C::from_u32(1), false);
        assert_eq!((s, c), (C::from_u32(0), true));
        // carry_in alone tips width max over: max + 0 + 1 wraps to zero, carries.
        let (s, c) = CarryingAdd::carrying_add(C::from_u32(MAX32), C::from_u32(0), true);
        assert_eq!((s, c), (C::from_u32(0), true));
        // max + max + 1 = 2^33 - 1: low half is max, carries out.
        let (s, c) = CarryingAdd::carrying_add(C::from_u32(MAX32), C::from_u32(MAX32), true);
        assert_eq!((s, c), (C::from_u32(MAX32), true));

        let (d, b) = BorrowingSub::borrowing_sub(C::from_u32(150), C::from_u32(50), false);
        assert_eq!((d, b), (C::from_u32(100), false));
        let (d, b) = BorrowingSub::borrowing_sub(C::from_u32(150), C::from_u32(50), true);
        assert_eq!((d, b), (C::from_u32(99), false));
        // 0 - 1 borrows out, wrapping to the width max.
        let (d, b) = BorrowingSub::borrowing_sub(C::from_u32(0), C::from_u32(1), false);
        assert_eq!((d, b), (C::from_u32(MAX32), true));
        // borrow_in alone underflows zero: 0 - 0 - 1 wraps to width max, borrows.
        let (d, b) = BorrowingSub::borrowing_sub(C::from_u32(0), C::from_u32(0), true);
        assert_eq!((d, b), (C::from_u32(MAX32), true));
        // 0 - max - 1 = -2^32: wraps back to zero, still borrows.
        let (d, b) = BorrowingSub::borrowing_sub(C::from_u32(0), C::from_u32(MAX32), true);
        assert_eq!((d, b), (C::from_u32(0), true));
    }
    for_both_carriers!(body);
}

// Ceiling division: rounds up on any remainder.
#[test]
fn div_ceil() {
    fn body<C: Carrier>() {
        assert_eq!(
            DivCeil::div_ceil(C::from_u32(10), C::from_u32(5)),
            C::from_u32(2)
        );
        assert_eq!(
            DivCeil::div_ceil(C::from_u32(11), C::from_u32(5)),
            C::from_u32(3)
        );
        assert_eq!(
            DivCeil::div_ceil(C::from_u32(0), C::from_u32(5)),
            C::from_u32(0)
        );
        // Dividend below divisor still rounds up to one.
        assert_eq!(
            DivCeil::div_ceil(C::from_u32(3), C::from_u32(10)),
            C::from_u32(1)
        );
        assert_eq!(
            DivCeil::div_ceil(C::from_u32(MAX32), C::from_u32(1)),
            C::from_u32(MAX32)
        );
    }
    for_both_carriers!(body);
}
