//! Byte serialization for `HeaplessBigInt`.
//!
//! The written byte count is `self.len * word_size` — public shape,
//! derived from the public `len`. Callers own the output buffer; the
//! methods panic if it is too small (checked at runtime, no `Result`).
//!
//! Layout matches `FixedUInt`'s slice-based conventions: BE writes the
//! high-order word's high byte at index 0, LE writes the low-order
//! word's low byte at index 0.
//!
//! Per-word reads are bit-shifted rather than `T::from_be_bytes`, so `T`
//! needs only `MachineWord`, not a byte-conversion trait bound.

use super::{HeaplessBigInt, zero};
use crate::MachineWord;
use const_num_traits::{ByteSliceError, ByteSliceErrorKind, FromByteSlice, Personality};
use core::marker::PhantomData;

// Read MSB-first bytes into a T, zero-padding the high side if
// `bytes.len() < size_of::<T>()`. Skips the shift on the first iteration
// because a `T::BITS`-wide shift is UB — matters at `size_of::<T>() == 1`
// (u8 backing) where the loop runs exactly once.
#[inline]
fn read_be_word<T: MachineWord>(bytes: &[u8]) -> T {
    let mut val = zero::<T>();
    let mut first = true;
    for &b in bytes {
        if !first {
            val <<= 8;
        }
        val |= <T as From<u8>>::from(b);
        first = false;
    }
    val
}

// LE counterpart: byte `i` of the input contributes at bit position `i*8`.
#[inline]
fn read_le_word<T: MachineWord>(bytes: &[u8]) -> T {
    let mut val = zero::<T>();
    let mut shift = 0;
    for &b in bytes {
        val |= <T as From<u8>>::from(b) << shift;
        shift += 8;
    }
    val
}

impl<T: MachineWord, const CAP: usize, P: Personality> HeaplessBigInt<T, CAP, P> {
    /// Serialize into `out` as big-endian bytes. Writes `self.len *
    /// size_of::<T>()` bytes into `out[..byte_count]` and returns that
    /// slice. Panics if `out.len() < byte_count`.
    pub fn to_be_bytes<'a>(&self, out: &'a mut [u8]) -> &'a [u8] {
        let word_size = core::mem::size_of::<T>();
        let byte_count = self.len as usize * word_size;
        assert!(
            out.len() >= byte_count,
            "HeaplessBigInt::to_be_bytes: out.len() < required ({byte_count} bytes)"
        );
        for (chunk, word) in out[..byte_count]
            .chunks_exact_mut(word_size)
            .zip(self.limbs[..self.len as usize].iter().rev())
        {
            let word_bytes = word.to_be_bytes();
            for (dst, src) in chunk.iter_mut().zip(word_bytes.as_ref()) {
                *dst = *src;
            }
        }
        &out[..byte_count]
    }

    /// Serialize into `out` as little-endian bytes. Same size + panic
    /// contract as [`to_be_bytes`](Self::to_be_bytes).
    pub fn to_le_bytes<'a>(&self, out: &'a mut [u8]) -> &'a [u8] {
        let word_size = core::mem::size_of::<T>();
        let byte_count = self.len as usize * word_size;
        assert!(
            out.len() >= byte_count,
            "HeaplessBigInt::to_le_bytes: out.len() < required ({byte_count} bytes)"
        );
        for (chunk, word) in out[..byte_count]
            .chunks_exact_mut(word_size)
            .zip(self.limbs[..self.len as usize].iter())
        {
            let word_bytes = word.to_le_bytes();
            for (dst, src) in chunk.iter_mut().zip(word_bytes.as_ref()) {
                *dst = *src;
            }
        }
        &out[..byte_count]
    }

    /// Deserialize a big-endian byte slice. Output `len =
    /// ceil(bytes.len() / word_size)`, capped at `CAP`. A partial top
    /// word (input length not a multiple of `word_size`) leaves the
    /// missing high bytes zero — matches the BE convention. Panics if
    /// `bytes.len() > CAP * word_size`.
    pub fn from_be_bytes(bytes: &[u8]) -> Self {
        let word_size = core::mem::size_of::<T>();
        let max_bytes = CAP * word_size;
        assert!(
            bytes.len() <= max_bytes,
            "HeaplessBigInt::from_be_bytes: input {} bytes > CAP * word_size ({max_bytes})",
            bytes.len()
        );
        let byte_count = bytes.len();
        let out_len = byte_count.div_ceil(word_size);

        let mut limbs = [zero::<T>(); CAP];
        // Fill limbs from limb 0, consuming `bytes` back-to-front (a
        // partial chunk, if any, lands at the high end).
        let mut hi = byte_count;
        let mut word_idx = 0;
        while hi > 0 {
            let take = core::cmp::min(word_size, hi);
            let lo = hi - take;
            limbs[word_idx] = read_be_word::<T>(&bytes[lo..hi]);
            word_idx += 1;
            hi = lo;
        }

        Self {
            limbs,
            len: out_len as u16,
            _p: PhantomData,
        }
    }

    /// Deserialize a little-endian byte slice. Same size contract as
    /// [`from_be_bytes`](Self::from_be_bytes).
    pub fn from_le_bytes(bytes: &[u8]) -> Self {
        let word_size = core::mem::size_of::<T>();
        let max_bytes = CAP * word_size;
        assert!(
            bytes.len() <= max_bytes,
            "HeaplessBigInt::from_le_bytes: input {} bytes > CAP * word_size ({max_bytes})",
            bytes.len()
        );
        let byte_count = bytes.len();
        let out_len = byte_count.div_ceil(word_size);

        let mut limbs = [zero::<T>(); CAP];
        let mut offset = 0;
        let mut word_idx = 0;
        while offset < byte_count {
            let take = core::cmp::min(word_size, byte_count - offset);
            limbs[word_idx] = read_le_word::<T>(&bytes[offset..offset + take]);
            word_idx += 1;
            offset += take;
        }

        Self {
            limbs,
            len: out_len as u16,
            _p: PhantomData,
        }
    }
}

// ── const_num_traits::FromByteSlice ──
//
// Result-returning slice parse: empty → `Empty`, wider than the
// container → `Overflow`, shorter → zero-extended. The inherent
// `from_be_bytes`/`from_le_bytes` already zero-extend; the length
// guard converts their panic-on-oversize into the `Overflow` error.

impl<T: MachineWord, const CAP: usize, P: Personality> HeaplessBigInt<T, CAP, P> {
    #[inline]
    fn check_slice_len(len: usize) -> Result<(), ByteSliceError> {
        if len == 0 {
            return Err(ByteSliceError {
                kind: ByteSliceErrorKind::Empty,
            });
        }
        if len > CAP * core::mem::size_of::<T>() {
            return Err(ByteSliceError {
                kind: ByteSliceErrorKind::Overflow,
            });
        }
        Ok(())
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> FromByteSlice for HeaplessBigInt<T, CAP, P> {
    fn from_be_slice(bytes: &[u8]) -> Result<Self, ByteSliceError> {
        Self::check_slice_len(bytes.len())?;
        Ok(Self::from_be_bytes(bytes))
    }

    fn from_le_slice(bytes: &[u8]) -> Result<Self, ByteSliceError> {
        Self::check_slice_len(bytes.len())?;
        Ok(Self::from_le_bytes(bytes))
    }
}
