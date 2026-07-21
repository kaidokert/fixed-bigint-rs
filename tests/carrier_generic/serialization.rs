//! Formatting and string-parsing parity. FixedUInt gates its whole
//! `string_conversion` module (Display/hex/FromStr) on `num-traits`, so every
//! test here is gated to match.
//!
//! Byte serialization is deliberately not covered here: `ToBytes`/`FromBytes`
//! (and the shared `BytesHolder`) live behind `any(feature = "nightly",
//! feature = "use-unsafe")` — the stable path reinterprets limbs via unsafe
//! `from_raw_parts` — so a shared byte-round-trip test would need a compound
//! feature gate for little gain over each carrier's own byte-round-trip suite.

#![cfg(feature = "num-traits")]

use crate::harness::*;

// Both carriers format identically: minimal decimal (`0` for zero) and minimal
// lower/upper hex. Absolute expected strings, so FixedUInt and HeaplessBigInt
// are checked against the same truth.
#[test]
fn formatting() {
    fn body<C: Carrier + core::fmt::Display + core::fmt::LowerHex + core::fmt::UpperHex>() {
        assert_eq!(format!("{}", C::from_u32(0)), "0");
        assert_eq!(format!("{}", C::from_u32(4660)), "4660");
        assert_eq!(format!("{}", C::from_u32(MAX32)), "4294967295");

        // Hex suppresses leading zeros on both carriers, so zero renders as
        // the empty string (not "0") — pin that shared, non-standard quirk.
        assert_eq!(format!("{:x}", C::from_u32(0)), "");
        assert_eq!(format!("{:X}", C::from_u32(0)), "");
        assert_eq!(format!("{:x}", C::from_u32(0x1234)), "1234");
        assert_eq!(format!("{:x}", C::from_u32(0xDEAD_BEEF)), "deadbeef");
        assert_eq!(format!("{:X}", C::from_u32(0xDEAD_BEEF)), "DEADBEEF");
    }
    for_both_carriers!(body);
}

// `FromStr` (decimal) and `num_traits::Num::from_str_radix` (2..=16).
#[test]
fn parse_decimal_and_radix() {
    fn body<C>()
    where
        C: Carrier + core::str::FromStr + num_traits::Num,
        <C as core::str::FromStr>::Err: core::fmt::Debug,
        <C as num_traits::Num>::FromStrRadixErr: core::fmt::Debug,
    {
        assert_eq!("0".parse::<C>().unwrap(), C::from_u32(0));
        assert_eq!("4660".parse::<C>().unwrap(), C::from_u32(4660));
        assert_eq!("4294967295".parse::<C>().unwrap(), C::from_u32(MAX32));

        // Leading zeros are tolerated on the decimal path.
        assert_eq!("00010".parse::<C>().unwrap(), C::from_u32(10));

        // Every radix in the supported 2..=16 span: "100" in base r is r^2.
        for r in 2u32..=16 {
            assert_eq!(
                <C as num_traits::Num>::from_str_radix("100", r).unwrap(),
                C::from_u32(r * r)
            );
        }

        // Spot-checks with leading-zero and uppercase-digit variants for hex.
        assert_eq!(
            <C as num_traits::Num>::from_str_radix("1010", 2).unwrap(),
            C::from_u32(10)
        );
        assert_eq!(
            <C as num_traits::Num>::from_str_radix("777", 8).unwrap(),
            C::from_u32(511)
        );
        assert_eq!(
            <C as num_traits::Num>::from_str_radix("123", 10).unwrap(),
            C::from_u32(123)
        );
        assert_eq!(
            <C as num_traits::Num>::from_str_radix("ff", 16).unwrap(),
            C::from_u32(255)
        );
        assert_eq!(
            <C as num_traits::Num>::from_str_radix("00FF", 16).unwrap(),
            C::from_u32(255)
        );
        assert_eq!(
            <C as num_traits::Num>::from_str_radix("deadbeef", 16).unwrap(),
            C::from_u32(0xDEAD_BEEF)
        );

        // Error paths: empty, invalid digit, over-width value, out-of-range
        // radix. Both carriers are 32-bit here, so 2^32 overflows.
        assert!("".parse::<C>().is_err());
        assert!("abc".parse::<C>().is_err());
        assert!("12a34".parse::<C>().is_err());
        assert!("4294967296".parse::<C>().is_err());
        assert!(<C as num_traits::Num>::from_str_radix("1", 1).is_err());
        assert!(<C as num_traits::Num>::from_str_radix("1", 17).is_err());
        assert!(<C as num_traits::Num>::from_str_radix("2", 2).is_err());
    }
    for_both_carriers!(body);
}
