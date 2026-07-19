//! `num_traits` foundation shared by both carriers — written once as a generic
//! body and run for `FixedUInt` and `HeaplessBigInt`.
//!
//! The sibling `carrier_generic.rs` stays feature-free (const-only surface);
//! this file is its `feature = "num-traits"` counterpart, same shape. Values
//! are pinned to a 32-bit width so the two carriers' `Bounded`/overflow
//! boundaries line up. Heapless-only behavior (natural-width construction,
//! sub-capacity widths) lives in `src/heapless/num_traits_bridge.rs`.

#![cfg(feature = "num-traits")]

use const_num_traits::{CarryingMul, Nct, WithPrecision};
use fixed_bigint::{FixedUInt, HeaplessBigInt, MachineWord};
use num_traits::{
    Bounded, CheckedDiv, CheckedRem, CheckedShl, CheckedShr, FromPrimitive, Num, NumCast, One,
    PrimInt, Saturating, ToPrimitive, WrappingShl, WrappingShr, Zero,
};

/// The num_traits foundation both carriers implement, pinned to 32 bits.
trait NumCarrier:
    Copy
    + core::fmt::Debug
    + PartialEq
    + Zero
    + One
    + Bounded
    + ToPrimitive
    + FromPrimitive
    + NumCast
    + Saturating
    + CheckedDiv
    + CheckedRem
    + Num<FromStrRadixErr = core::num::ParseIntError>
    + core::str::FromStr<Err = core::num::ParseIntError>
    + core::fmt::Display
    + PrimInt
    + num_integer::Integer
    + num_integer::Roots
    + WrappingShl
    + WrappingShr
    + CheckedShl
    + CheckedShr
    + From<u32>
    + WithPrecision
{
    /// Build `v` at the carrier's full 32-bit width (see `carrier_generic.rs`).
    fn at32(v: u32) -> Self {
        <Self as From<u32>>::from(v).widen_to_precision(32)
    }
}

impl<T: MachineWord + CarryingMul<Unsigned = T, Output = T> + core::fmt::Debug, const N: usize>
    NumCarrier for FixedUInt<T, N, Nct>
{
}
impl<T: MachineWord + CarryingMul<Unsigned = T, Output = T> + core::fmt::Debug, const CAP: usize>
    NumCarrier for HeaplessBigInt<T, CAP, Nct>
{
}

/// Run a generic body for both carriers across three 32-bit backings.
macro_rules! for_both_carriers {
    ($body:ident) => {{
        $body::<FixedUInt<u8, 4, Nct>>();
        $body::<HeaplessBigInt<u8, 4, Nct>>();
        $body::<FixedUInt<u16, 2, Nct>>();
        $body::<HeaplessBigInt<u16, 2, Nct>>();
        $body::<FixedUInt<u32, 1, Nct>>();
        $body::<HeaplessBigInt<u32, 1, Nct>>();
    }};
}

#[test]
fn zero_one() {
    fn body<C: NumCarrier>() {
        assert!(<C as Zero>::zero().is_zero());
        assert_eq!(<C as Zero>::zero().to_u64(), Some(0));
        assert!(!<C as One>::one().is_zero());
        assert_eq!(<C as One>::one().to_u64(), Some(1));
    }
    for_both_carriers!(body);
}

#[test]
fn bounded() {
    fn body<C: NumCarrier>() {
        // All three backings are 32-bit wide, so max = u32::MAX.
        assert_eq!(<C as Bounded>::max_value().to_u64(), Some(0xFFFF_FFFF));
        assert!(<C as Bounded>::min_value().is_zero());
    }
    for_both_carriers!(body);
}

#[test]
fn to_from_primitive_roundtrip() {
    fn body<C: NumCarrier>() {
        for v in [0u64, 1, 0xFF, 0x1234, 0xFFFF_FFFF] {
            assert_eq!(C::from_u64(v).unwrap().to_u64(), Some(v));
        }
        // Above the 32-bit width → rejected, not truncated.
        assert!(C::from_u64(0x1_0000_0000).is_none());
        // The unsigned carriers never claim i64.
        assert_eq!(C::at32(5).to_i64(), None);
        assert_eq!(C::from_i64(5), None);
    }
    for_both_carriers!(body);
}

#[test]
fn numcast() {
    fn body<C: NumCarrier>() {
        let a: C = NumCast::from(255u32).unwrap();
        assert_eq!(a.to_u64(), Some(255));
        assert!(<C as NumCast>::from(0x1_0000_0000u64).is_none());
    }
    for_both_carriers!(body);
}

#[test]
#[allow(deprecated)] // num_traits::Saturating is deprecated but PrimInt needs it
fn saturating_and_checked_div() {
    fn body<C: NumCarrier>() {
        let max = C::at32(0xFFFF_FFFF);
        // num_traits::Saturating (add/sub only)
        assert_eq!(Saturating::saturating_add(max, C::at32(1)), max);
        assert_eq!(
            Saturating::saturating_sub(C::at32(1), C::at32(2)),
            C::at32(0)
        );
        // num_traits::CheckedDiv / CheckedRem, incl. the divide-by-zero None
        let a = C::at32(100);
        assert_eq!(CheckedDiv::checked_div(&a, &C::at32(7)), Some(C::at32(14)));
        assert_eq!(CheckedRem::checked_rem(&a, &C::at32(7)), Some(C::at32(2)));
        assert_eq!(CheckedDiv::checked_div(&a, &C::at32(0)), None);
        assert_eq!(CheckedRem::checked_rem(&a, &C::at32(0)), None);
    }
    for_both_carriers!(body);
}

#[test]
fn num_from_str_radix_and_fromstr() {
    fn body<C: NumCarrier>() {
        // decimal + hex parse
        assert_eq!(Num::from_str_radix("255", 10), Ok(C::at32(255)));
        assert_eq!(Num::from_str_radix("ff", 16), Ok(C::at32(255)));
        assert_eq!(Num::from_str_radix("FF", 16), Ok(C::at32(255))); // uppercase hex
        assert_eq!(Num::from_str_radix("0", 10), Ok(C::at32(0)));
        // leading zeros are stripped
        assert_eq!(Num::from_str_radix("000255", 10), Ok(C::at32(255)));
        assert_eq!(Num::from_str_radix("0000", 10), Ok(C::at32(0)));
        // FromStr is decimal
        assert_eq!("4294967295".parse::<C>(), Ok(C::at32(0xFFFF_FFFF)));
        // errors: empty, bad char, both radix bounds, and 32-bit overflow
        assert!(<C as Num>::from_str_radix("", 10).is_err());
        assert!(<C as Num>::from_str_radix("12x", 10).is_err());
        assert!(<C as Num>::from_str_radix("1", 1).is_err()); // radix < 2
        assert!(<C as Num>::from_str_radix("1", 99).is_err()); // radix > 16
        assert!(<C as Num>::from_str_radix("4294967296", 10).is_err()); // 2^32 > width
    }
    for_both_carriers!(body);
}

#[test]
fn display_decimal() {
    fn body<C: NumCarrier>() {
        assert_eq!(std::format!("{}", C::at32(0)), "0");
        assert_eq!(std::format!("{}", C::at32(1)), "1");
        assert_eq!(std::format!("{}", C::at32(0xDEAD_BEEF)), "3735928559");
        assert_eq!(std::format!("{}", C::at32(0xFFFF_FFFF)), "4294967295");
    }
    for_both_carriers!(body);
}

#[test]
fn prim_int() {
    fn body<C: NumCarrier>() {
        // Delegates to PrimBits; pow to the shared kernel. reverse_bits uses
        // the num_traits default (as FixedUInt does) — verify it here too.
        assert_eq!(PrimInt::count_ones(C::at32(0b1011)), 3);
        assert_eq!(PrimInt::leading_zeros(C::at32(1)), 31);
        assert_eq!(PrimInt::trailing_zeros(C::at32(0b1000)), 3);
        assert_eq!(PrimInt::rotate_left(C::at32(1), 4), C::at32(16));
        assert_eq!(
            PrimInt::swap_bytes(C::at32(0x0000_00FF)),
            C::at32(0xFF00_0000)
        );
        assert_eq!(PrimInt::reverse_bits(C::at32(1)), C::at32(0x8000_0000));
        assert_eq!(PrimInt::pow(C::at32(2), 10), C::at32(1024));
        assert_eq!(PrimInt::pow(C::at32(7), 3), C::at32(343));

        // Shifts (delegated via PrimBits): unsigned == signed for the unsigned
        // carrier, and both stay fixed-width.
        assert_eq!(PrimInt::unsigned_shl(C::at32(1), 31), C::at32(0x8000_0000));
        assert_eq!(PrimInt::unsigned_shr(C::at32(0x8000_0000), 31), C::at32(1));
        assert_eq!(PrimInt::signed_shl(C::at32(1), 31), C::at32(0x8000_0000));
        assert_eq!(PrimInt::signed_shr(C::at32(0x8000_0000), 31), C::at32(1));

        // Endianness conversions round-trip.
        let v = C::at32(0x1234_5678);
        assert_eq!(PrimInt::from_be(PrimInt::to_be(v)), v);
        assert_eq!(PrimInt::from_le(PrimInt::to_le(v)), v);
    }
    for_both_carriers!(body);
}

#[test]
fn integer_gcd_lcm() {
    fn body<C: NumCarrier>() {
        // Integer methods come in via the NumCarrier: Integer bound.
        // gcd / lcm
        assert_eq!(C::at32(12).gcd(&C::at32(18)), C::at32(6));
        assert_eq!(C::at32(12).lcm(&C::at32(18)), C::at32(36));
        assert_eq!(C::at32(17).gcd(&C::at32(5)), C::at32(1)); // coprime
        assert_eq!(C::at32(0).gcd(&C::at32(9)), C::at32(9)); // gcd(0, x) = x
        assert_eq!(C::at32(0).lcm(&C::at32(0)), C::at32(0));
        // div_floor / mod_floor / div_rem (unsigned: floor == truncating)
        assert_eq!(C::at32(17).div_floor(&C::at32(5)), C::at32(3));
        assert_eq!(C::at32(17).mod_floor(&C::at32(5)), C::at32(2));
        assert_eq!(C::at32(17).div_rem(&C::at32(5)), (C::at32(3), C::at32(2)));
        // divisibility / parity
        assert!(C::at32(12).is_multiple_of(&C::at32(4)));
        assert!(!C::at32(13).is_multiple_of(&C::at32(4)));
        assert!(C::at32(12).is_even());
        assert!(C::at32(13).is_odd());
        assert!(C::at32(0).is_even());
    }
    for_both_carriers!(body);
}

#[test]
fn roots_sqrt_cbrt_nth() {
    fn body<C: NumCarrier>() {
        // Roots methods come in via the NumCarrier: Roots bound.
        assert_eq!(C::at32(0).sqrt(), C::at32(0));
        assert_eq!(C::at32(15).sqrt(), C::at32(3));
        assert_eq!(C::at32(1_000_000).sqrt(), C::at32(1000));
        assert_eq!(C::at32(27).cbrt(), C::at32(3));
        assert_eq!(C::at32(63).cbrt(), C::at32(3));
        assert_eq!(C::at32(81).nth_root(4), C::at32(3));
        assert_eq!(C::at32(2).nth_root(100), C::at32(1));
        // r^n <= x < (r+1)^n across a small range.
        for x in 1..=200u32 {
            let xi = C::at32(x);
            let s = xi.sqrt();
            assert!(s.pow(2) <= xi && (s + C::at32(1)).pow(2) > xi, "sqrt({x})");
        }
    }
    for_both_carriers!(body);
}

#[test]
fn num_traits_shift_wrappers() {
    fn body<C: NumCarrier>() {
        // num_traits shift methods take &self and mask the amount.
        assert_eq!(WrappingShl::wrapping_shl(&C::at32(1), 4), C::at32(16));
        assert_eq!(WrappingShl::wrapping_shl(&C::at32(1), 32), C::at32(1));
        assert_eq!(WrappingShr::wrapping_shr(&C::at32(16), 2), C::at32(4));
        assert_eq!(CheckedShl::checked_shl(&C::at32(1), 5), Some(C::at32(32)));
        assert_eq!(CheckedShl::checked_shl(&C::at32(1), 32), None);
        assert_eq!(CheckedShr::checked_shr(&C::at32(1), 32), None);
    }
    for_both_carriers!(body);
}
