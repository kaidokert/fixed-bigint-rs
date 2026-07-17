//! Cross-crate coverage for `FixedUInt`'s const `ToBytes`/`FromBytes`
//! (nightly `generic_const_exprs`).
//!
//! As a downstream crate it must enable `generic_const_exprs` itself — the
//! associated-type bound is viral; without it the well-formedness check can't
//! complete and rustc emits a confusing `error[E0275]`. See
//! `src/fixeduint/const_to_from_bytes.rs`.
#![cfg(feature = "nightly")]
#![cfg_attr(feature = "nightly", feature(generic_const_exprs))]
#![cfg_attr(feature = "nightly", allow(incomplete_features))]

use const_num_traits::{FromBytes, ToBytes};
use fixed_bigint::FixedUInt;

#[test]
fn cross_crate_roundtrip_u8() {
    let n = FixedUInt::<u8, 4>::from(0x0403_0201u32);
    let le = <FixedUInt<u8, 4> as ToBytes>::to_le_bytes(n);
    assert_eq!(le.as_ref(), &[0x01, 0x02, 0x03, 0x04]);
    let be = <FixedUInt<u8, 4> as ToBytes>::to_be_bytes(n);
    assert_eq!(be.as_ref(), &[0x04, 0x03, 0x02, 0x01]);
    assert_eq!(<FixedUInt<u8, 4> as FromBytes>::from_le_bytes(&le), n);
    assert_eq!(<FixedUInt<u8, 4> as FromBytes>::from_be_bytes(&be), n);
}

#[test]
fn cross_crate_roundtrip_u16() {
    let n = FixedUInt::<u16, 4>::from(0x0403_0201u32);
    let le = <FixedUInt<u16, 4> as ToBytes>::to_le_bytes(n);
    assert_eq!(le.as_ref(), &[0x01, 0x02, 0x03, 0x04, 0, 0, 0, 0]);
    let be = <FixedUInt<u16, 4> as ToBytes>::to_be_bytes(n);
    assert_eq!(be.as_ref(), &[0, 0, 0, 0, 0x04, 0x03, 0x02, 0x01]);
    assert_eq!(<FixedUInt<u16, 4> as FromBytes>::from_le_bytes(&le), n);
    assert_eq!(<FixedUInt<u16, 4> as FromBytes>::from_be_bytes(&be), n);
}

#[test]
fn cross_crate_roundtrip_u32() {
    let n = FixedUInt::<u32, 4>::from(0x1234_5678u32);
    let mut le_expected = [0u8; 16];
    le_expected[..4].copy_from_slice(&[0x78, 0x56, 0x34, 0x12]);
    let le = <FixedUInt<u32, 4> as ToBytes>::to_le_bytes(n);
    assert_eq!(le.as_ref(), &le_expected);

    let mut be_expected = [0u8; 16];
    be_expected[12..].copy_from_slice(&[0x12, 0x34, 0x56, 0x78]);
    let be = <FixedUInt<u32, 4> as ToBytes>::to_be_bytes(n);
    assert_eq!(be.as_ref(), &be_expected);

    assert_eq!(<FixedUInt<u32, 4> as FromBytes>::from_le_bytes(&le), n);
    assert_eq!(<FixedUInt<u32, 4> as FromBytes>::from_be_bytes(&be), n);
}
