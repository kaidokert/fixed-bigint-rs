// TODO

#[cfg(test)]
use fixed_bigint::FixedUInt as Bn;

use num_traits::{FromPrimitive, ToPrimitive};
use std::ops::{BitXor, BitXorAssign};

#[test]
fn test_xor() {
	let a: Bn<u8, 1> = 2u8.into();
    let b: Bn<u8, 1> = 3u8.into();
    assert_eq!(a ^ b, 1u8.into());
    assert_ne!(a ^ b, 5u8.into());
    assert_eq!(a.bitxor(b), 1u8.into());
    assert_ne!(a.bitxor(b), 5u8.into());
}

#[test]
fn test_xor_assign() {
	let mut a: Bn<u8, 1> = 2u8.into();
    let b: Bn<u8, 1> = 3u8.into();
    a ^= b;
    assert_eq!(a, 1u8.into());
    assert_ne!(a, 5u8.into());
    
    let mut a: Bn<u8, 1> = 2u8.into();
    let b: Bn<u8, 1> = 3u8.into();
    a.bitxor_assign(b);
    assert_eq!(a, 1u8.into());
    assert_ne!(a, 5u8.into());
}