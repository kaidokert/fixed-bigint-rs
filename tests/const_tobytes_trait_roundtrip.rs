//! Cross-crate coverage for `FixedUInt`'s const `ToBytes`/`FromBytes`
//! (the nightly `generic_const_exprs` path).
//!
//! This is a *downstream* crate, so it must enable `generic_const_exprs`
//! itself — the associated-type bound is viral. Without the feature the
//! compiler cannot finish the well-formedness check and emits a confusing
//! `error[E0275]`. This file is the coverage that was missing: the impls'
//! in-crate tests never exercised the cross-crate path, so the viral-feature
//! requirement (and the misleading `E0275` when it's forgotten) shipped
//! undocumented. See `src/fixeduint/const_to_from_bytes.rs`.
#![cfg(feature = "nightly")]
#![feature(generic_const_exprs)]
#![allow(incomplete_features)]

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
    assert_eq!(le.as_ref().len(), 8);
    assert_eq!(<FixedUInt<u16, 4> as FromBytes>::from_le_bytes(&le), n);
}

#[test]
fn cross_crate_roundtrip_u32() {
    let n = FixedUInt::<u32, 4>::from(0x1234_5678u32);
    let be = <FixedUInt<u32, 4> as ToBytes>::to_be_bytes(n);
    assert_eq!(be.as_ref().len(), 16);
    assert_eq!(<FixedUInt<u32, 4> as FromBytes>::from_be_bytes(&be), n);
}
