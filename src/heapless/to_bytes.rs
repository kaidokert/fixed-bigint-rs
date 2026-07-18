//! `const_num_traits::ToBytes` / `FromBytes` for `HeaplessBigInt`.
//!
//! Reuses `FixedUInt`'s `BytesHolder<T, CAP>` as the owned `Bytes`
//! associated type — on stable, an owned byte holder for a `T`/`CAP`-
//! generic type is only representable via the `unsafe` slice reinterpret
//! `BytesHolder` already carries, so this module rides the same
//! `nightly | use-unsafe` gate that guards `BytesHolder`.
//!
//! The `ToBytes` representation is **capacity-width** (`CAP *
//! size_of::<T>()` bytes): all `CAP` limbs are serialised, high
//! (zero-tail) limbs producing leading zero bytes for BE / trailing for
//! LE. This is the one place the carrier's `CAP` is intentionally exposed:
//! an *owned* fixed holder cannot be sized to the runtime width, so it
//! reports capacity. That matches `FixedUInt<T, CAP>`'s bytes — a
//! carrier-generic consumer round-trips a full-precision operand (e.g. a
//! crypto modulus, constructed at `len == CAP`) identically on either type.
//! A caller that needs **width-based** (`len * word_size`) bytes uses the
//! inherent `to_be_bytes(&mut [u8]) -> &[u8]` / `to_le_bytes` instead.

use super::HeaplessBigInt;
use crate::MachineWord;
use crate::fixeduint::BytesHolder;
use const_num_traits::{FromBytes, Personality, ToBytes};

impl<T, const CAP: usize, P: Personality> HeaplessBigInt<T, CAP, P>
where
    T: MachineWord + core::fmt::Debug,
{
    // Full-width big-endian holder: highest limb first, each limb's own
    // bytes big-endian. Byte writes go through `as_byte_slice_mut` so the
    // sequence is host-endianness-independent (the `[T; CAP]` typing is
    // incidental storage for the byte pattern).
    fn holder_be(&self) -> BytesHolder<T, CAP> {
        let mut ret = BytesHolder::default();
        let word_size = core::mem::size_of::<T>();
        for (chunk, word) in ret
            .as_byte_slice_mut()
            .chunks_exact_mut(word_size)
            .zip(self.limbs.iter().rev())
        {
            let word_bytes = word.to_be_bytes();
            for (dst, src) in chunk.iter_mut().zip(word_bytes.as_ref()) {
                *dst = *src;
            }
        }
        ret
    }

    fn holder_le(&self) -> BytesHolder<T, CAP> {
        let mut ret = BytesHolder::default();
        let word_size = core::mem::size_of::<T>();
        for (chunk, word) in ret
            .as_byte_slice_mut()
            .chunks_exact_mut(word_size)
            .zip(self.limbs.iter())
        {
            let word_bytes = word.to_le_bytes();
            for (dst, src) in chunk.iter_mut().zip(word_bytes.as_ref()) {
                *dst = *src;
            }
        }
        ret
    }
}

/// **Capacity-width** serialization — see the [module docs](super). For
/// value-width bytes use the inherent
/// [`to_le_bytes`](HeaplessBigInt::to_le_bytes) / `to_be_bytes(&mut [u8])`.
impl<T, const CAP: usize, P: Personality> ToBytes for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord + core::fmt::Debug,
{
    type Bytes = BytesHolder<T, CAP>;
    fn to_be_bytes(self) -> Self::Bytes {
        self.holder_be()
    }
    fn to_le_bytes(self) -> Self::Bytes {
        self.holder_le()
    }
}

// `ToBytes for &HeaplessBigInt` — mirrors `FixedUInt`; lets a caller
// serialise without moving the value (relevant to Ct roles where the
// operand lives behind a wrapper).
impl<T, const CAP: usize, P: Personality> ToBytes for &HeaplessBigInt<T, CAP, P>
where
    T: MachineWord + core::fmt::Debug,
{
    type Bytes = BytesHolder<T, CAP>;
    fn to_be_bytes(self) -> Self::Bytes {
        self.holder_be()
    }
    fn to_le_bytes(self) -> Self::Bytes {
        self.holder_le()
    }
}

/// **Capacity-width** deserialization — the fixed-size `BytesHolder` yields a
/// value at `len == CAP` (see the [module docs](super)). To parse a shorter
/// fixed encoding at its own width, use the inherent
/// [`from_le_bytes`](HeaplessBigInt::from_le_bytes) / `from_be_bytes(&[u8])`
/// on a slice of the exact length.
impl<T, const CAP: usize, P: Personality> FromBytes for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord + core::fmt::Debug,
{
    type Bytes = BytesHolder<T, CAP>;
    fn from_be_bytes(bytes: &Self::Bytes) -> Self {
        // Reconstructs at len = CAP from the holder's full byte sequence.
        Self::from_be_bytes(bytes.as_ref())
    }
    fn from_le_bytes(bytes: &Self::Bytes) -> Self {
        Self::from_le_bytes(bytes.as_ref())
    }
}
