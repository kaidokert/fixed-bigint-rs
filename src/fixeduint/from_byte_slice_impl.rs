//! `const_num_traits::FromByteSlice` for FixedUInt.
//!
//! Parses a big/little-endian byte slice of *arbitrary* length up to
//! `Self::BYTE_WIDTH`, zero-extending shorter input and rejecting
//! wider input with `ByteSliceErrorKind::Overflow`. Empty input is
//! `ByteSliceErrorKind::Empty` per upstream — a missing buffer
//! shouldn't masquerade as zero.
//!
//! This is the additive first hop of the byte-trait alignment across
//! `fixed-bigint` / `rsa/new_reduce` / `ed25519_heapless`. Enables
//! downstream to drop the `<T as FromBytes>::Bytes: Default +
//! AsMut<[u8]>` padding-and-dance idiom and bind a single
//! `T: FromByteSlice` supertrait instead.

use super::{FixedUInt, MachineWord};
use const_num_traits::{ByteSliceError, ByteSliceErrorKind, FromByteSlice, Personality};

impl<T: MachineWord, const N: usize, P: Personality> FromByteSlice for FixedUInt<T, N, P> {
    fn from_be_slice(bytes: &[u8]) -> Result<Self, ByteSliceError> {
        if bytes.is_empty() {
            return Err(ByteSliceError {
                kind: ByteSliceErrorKind::Empty,
            });
        }
        if bytes.len() > Self::BYTE_WIDTH {
            return Err(ByteSliceError {
                kind: ByteSliceErrorKind::Overflow,
            });
        }
        // `from_be_bytes` already zero-extends shorter input (BE
        // reads from the trailing window and initialises the array
        // to zero).
        Ok(Self::from_be_bytes(bytes))
    }

    fn from_le_slice(bytes: &[u8]) -> Result<Self, ByteSliceError> {
        if bytes.is_empty() {
            return Err(ByteSliceError {
                kind: ByteSliceErrorKind::Empty,
            });
        }
        if bytes.len() > Self::BYTE_WIDTH {
            return Err(ByteSliceError {
                kind: ByteSliceErrorKind::Overflow,
            });
        }
        Ok(Self::from_le_bytes(bytes))
    }
}

// No `&FixedUInt: FromByteSlice` mirror — an associated fn returning
// `Self = &FixedUInt` has no storage source. Consumers who want to
// parse into an owned `FixedUInt` bind on `FixedUInt: FromByteSlice`;
// no reference-projection bound is needed on the read side.

#[cfg(test)]
mod tests {
    use super::*;

    type U16 = FixedUInt<u8, 2>;
    type U32 = FixedUInt<u8, 4>;

    #[test]
    fn from_be_slice_exact() {
        assert_eq!(U16::from_be_slice(&[0x12, 0x34]), Ok(U16::from(0x1234u16)));
    }

    #[test]
    fn from_be_slice_short_zero_extends() {
        // Two-byte target reading one byte: value is 0x00_12.
        assert_eq!(U16::from_be_slice(&[0x12]), Ok(U16::from(0x12u8)));
    }

    #[test]
    fn from_be_slice_overflow() {
        assert!(matches!(
            U16::from_be_slice(&[1, 2, 3]),
            Err(ByteSliceError {
                kind: ByteSliceErrorKind::Overflow
            })
        ));
    }

    #[test]
    fn from_be_slice_empty() {
        assert!(matches!(
            U16::from_be_slice(&[]),
            Err(ByteSliceError {
                kind: ByteSliceErrorKind::Empty
            })
        ));
    }

    #[test]
    fn from_le_slice_exact() {
        assert_eq!(
            U32::from_le_slice(&[1, 2, 3, 4]),
            Ok(U32::from(0x04030201u32))
        );
    }

    #[test]
    fn from_le_slice_short_zero_extends() {
        // Four-byte target reading two bytes: value is 0x00_00_02_01.
        assert_eq!(U32::from_le_slice(&[1, 2]), Ok(U32::from(0x0201u16)));
    }

    #[test]
    fn from_le_slice_overflow() {
        assert!(matches!(
            U32::from_le_slice(&[1, 2, 3, 4, 5]),
            Err(ByteSliceError {
                kind: ByteSliceErrorKind::Overflow
            })
        ));
    }

    #[test]
    fn from_le_slice_empty() {
        assert!(matches!(
            U32::from_le_slice(&[]),
            Err(ByteSliceError {
                kind: ByteSliceErrorKind::Empty
            })
        ));
    }

    #[test]
    fn le_be_roundtrip_matches_slice_readers() {
        // Cross-check: FromByteSlice::from_*_slice for exact-width
        // input agrees with the inherent from_*_bytes.
        let bytes = [0x12u8, 0x34, 0x56, 0x78];
        assert_eq!(
            U32::from_be_slice(&bytes).unwrap(),
            U32::from_be_bytes(&bytes)
        );
        assert_eq!(
            U32::from_le_slice(&bytes).unwrap(),
            U32::from_le_bytes(&bytes)
        );
    }
}
