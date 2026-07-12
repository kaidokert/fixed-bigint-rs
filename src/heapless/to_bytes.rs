//! `const_num_traits::ToBytes` / `FromBytes` for `HeaplessBigInt`.
//!
//! Reuses `FixedUInt`'s `BytesHolder<T, CAP>` as the owned `Bytes`
//! associated type — on stable, an owned byte holder for a `T`/`CAP`-
//! generic type is only representable via the `unsafe` slice reinterpret
//! `BytesHolder` already carries, so this module rides the same
//! `nightly | use-unsafe` gate that guards `BytesHolder`.
//!
//! The representation is **full container width** (`CAP * size_of::<T>()`
//! bytes): all `CAP` limbs are serialised, high (zero-tail) limbs
//! producing leading zero bytes for BE / trailing for LE. This matches
//! `FixedUInt<T, CAP>`'s byte shape, so a modmath consumer generic over
//! the carrier round-trips a modulus/scalar identically on either type.

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
    // incidental storage for the byte pattern). Zip byte-loop copy — no
    // `copy_from_slice` length assert to fold.
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

impl<T, const CAP: usize, P: Personality> FromBytes for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord + core::fmt::Debug,
{
    type Bytes = BytesHolder<T, CAP>;
    fn from_be_bytes(bytes: &Self::Bytes) -> Self {
        // `as_ref()` yields the full `CAP * word_size` byte sequence the
        // holder was built from; the inherent slice reader reconstructs
        // the value (len = CAP).
        Self::from_be_bytes(bytes.as_ref())
    }
    fn from_le_bytes(bytes: &Self::Bytes) -> Self {
        Self::from_le_bytes(bytes.as_ref())
    }
}
