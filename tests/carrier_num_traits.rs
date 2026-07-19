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
use num_traits::{Bounded, FromPrimitive, NumCast, One, ToPrimitive, Zero};

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
