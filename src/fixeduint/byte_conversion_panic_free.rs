// Copyright 2021 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Fixed-size byte conversion: typed buffers, compile-time size check.
//!
//! Panic-free-signature counterparts to the slice-based
//! `FixedUInt::{to,from}_{le,be}_bytes`. Take `&[u8; M]` / `&mut [u8; M]`
//! and verify `M >= BYTE_WIDTH` at monomorphization; wrong-size callers
//! fail at compile time. The signature guarantee is "no `Result`, no
//! `.unwrap()` at the boundary" — not "no `panic_fmt` in the linked
//! binary": `copy_from_slice` still carries a length check LLVM can't
//! elide through the trait boundary.
//!
//! Truncation convention when `M > BYTE_WIDTH` matches the slice-based
//! methods: LE reads the first `BYTE_WIDTH` bytes, BE reads the last.

// `let _ = <T as AssertBufferFits<M>>::CHECK;` forces the const to
// evaluate at monomorphization; a bare path-statement isn't a reliable
// substitute across rustc versions.
#![allow(clippy::let_unit_value)]

use super::{FixedUInt, MachineWord, impl_from_be_bytes_slice, impl_from_le_bytes_slice};
use const_num_traits::Personality;

/// Type-level compile-time assertion that buffer-of-length-`M` fits a
/// `FixedUInt<T,N,P>`'s byte width. The associated const `CHECK` evaluates
/// to a `()`-or-compile-error: on a monomorphization where `M >= BYTE_WIDTH`
/// the body of `assert!` is a no-op; otherwise it is a const-eval error
/// that aborts compilation with the diagnostic message.
///
/// Why a trait + associated const instead of a `const { assert!(...) }`
/// block: on nightly with `generic_const_exprs` enabled, in-fn
/// `const { … M … }` blocks become "generic constants" that the compiler
/// rejects with "overly complex generic constant". Moving the assertion
/// to an associated const on a trait impl sidesteps that — the impl
/// header carries the generics, and the const item body is a plain
/// expression referencing them.
trait AssertBufferFits<const M: usize> {
    const CHECK: ();
}

impl<T: MachineWord, const N: usize, P: Personality, const M: usize> AssertBufferFits<M>
    for FixedUInt<T, N, P>
{
    const CHECK: () = assert!(
        M >= Self::BYTE_WIDTH,
        "*_bytes_fixed: buffer size M must be >= FixedUInt::BYTE_WIDTH (= N * size_of::<T>())",
    );
}

impl<T: MachineWord, const N: usize, P: Personality> FixedUInt<T, N, P> {
    /// Serialize little-endian into a fixed-size buffer. The const
    /// `M >= BYTE_WIDTH` precondition fires at monomorphization, so
    /// wrong-size callers fail at compile time and the produced binary
    /// contains no runtime panic path from this method.
    ///
    /// Returns the written prefix (`&out[..BYTE_WIDTH]`). If
    /// `M > BYTE_WIDTH`, the trailing bytes of `out` are left untouched.
    ///
    /// ```
    /// use fixed_bigint::FixedUInt;
    /// type U16 = FixedUInt<u8, 2>;
    /// let v = U16::from(0x1234u16);
    /// let mut buf = [0u8; U16::BYTE_WIDTH];
    /// let bytes = v.to_le_bytes_fixed(&mut buf);
    /// assert_eq!(bytes, &[0x34, 0x12]);
    /// ```
    #[inline]
    pub fn to_le_bytes_fixed<'a, const M: usize>(&self, out: &'a mut [u8; M]) -> &'a [u8] {
        let _ = <Self as AssertBufferFits<M>>::CHECK;
        let word_size = Self::WORD_SIZE;
        for (chunk, word) in out
            .chunks_exact_mut(word_size)
            .take(N)
            .zip(self.array.iter())
        {
            chunk.copy_from_slice(word.to_le_bytes().as_ref());
        }
        &out[..Self::BYTE_WIDTH]
    }

    /// Big-endian counterpart of [`to_le_bytes_fixed`](Self::to_le_bytes_fixed);
    /// same const-asserted size guarantee and same panic-free intent.
    ///
    /// ```
    /// use fixed_bigint::FixedUInt;
    /// type U16 = FixedUInt<u8, 2>;
    /// let v = U16::from(0x1234u16);
    /// let mut buf = [0u8; U16::BYTE_WIDTH];
    /// let bytes = v.to_be_bytes_fixed(&mut buf);
    /// assert_eq!(bytes, &[0x12, 0x34]);
    /// ```
    #[inline]
    pub fn to_be_bytes_fixed<'a, const M: usize>(&self, out: &'a mut [u8; M]) -> &'a [u8] {
        let _ = <Self as AssertBufferFits<M>>::CHECK;
        let word_size = Self::WORD_SIZE;
        // Walk words from MSB to LSB so the output is BE.
        for (chunk, word) in out
            .chunks_exact_mut(word_size)
            .take(N)
            .zip(self.array.iter().rev())
        {
            chunk.copy_from_slice(word.to_be_bytes().as_ref());
        }
        &out[..Self::BYTE_WIDTH]
    }

    /// Deserialize from a fixed-size little-endian buffer. The const
    /// `M >= BYTE_WIDTH` precondition fires at monomorphization. Reads
    /// the first `BYTE_WIDTH` bytes (LE low-order bytes are at the
    /// front); trailing bytes if `M > BYTE_WIDTH` are ignored.
    ///
    /// ```
    /// use fixed_bigint::FixedUInt;
    /// type U16 = FixedUInt<u8, 2>;
    /// let buf = [0x34u8, 0x12];
    /// let v = U16::from_le_bytes_fixed(&buf);
    /// assert_eq!(v, U16::from(0x1234u16));
    /// ```
    #[inline]
    pub fn from_le_bytes_fixed<const M: usize>(bytes: &[u8; M]) -> Self {
        let _ = <Self as AssertBufferFits<M>>::CHECK;
        // The helper takes `&[u8]` and bounds its loop by
        // `min(bytes.len(), capacity)`; passing the full M-byte slice
        // means `bytes.len() == M >= BYTE_WIDTH == capacity`, so the
        // loop bound is BYTE_WIDTH and every indexed read is in range.
        Self::from_array(impl_from_le_bytes_slice::<T, N>(bytes))
    }

    /// Deserialize from a fixed-size big-endian buffer. The const
    /// `M >= BYTE_WIDTH` precondition fires at monomorphization. Reads
    /// the last `BYTE_WIDTH` bytes (BE low-order bytes are at the end);
    /// leading bytes if `M > BYTE_WIDTH` are ignored.
    ///
    /// ```
    /// use fixed_bigint::FixedUInt;
    /// type U16 = FixedUInt<u8, 2>;
    /// let buf = [0x12u8, 0x34];
    /// let v = U16::from_be_bytes_fixed(&buf);
    /// assert_eq!(v, U16::from(0x1234u16));
    /// ```
    #[inline]
    pub fn from_be_bytes_fixed<const M: usize>(bytes: &[u8; M]) -> Self {
        let _ = <Self as AssertBufferFits<M>>::CHECK;
        // The BE helper already handles the `bytes.len() > capacity`
        // case by reading the trailing `capacity` bytes (BE low-order
        // bytes are at the end). With M >= BYTE_WIDTH it picks the
        // right window without our needing to compute `start` here.
        Self::from_array(impl_from_be_bytes_slice::<T, N>(bytes))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type U16 = FixedUInt<u8, 2>;
    type U32 = FixedUInt<u32, 1>; // single-limb u32 backing
    type U64 = FixedUInt<u32, 2>; // two-limb u32 backing

    // ─── to_le_bytes_fixed ────────────────────────────────────────────

    #[test]
    fn to_le_bytes_fixed_exact_size_round_trips() {
        let v = U16::from(0x1234u16);
        let mut buf = [0u8; U16::BYTE_WIDTH];
        let written = v.to_le_bytes_fixed(&mut buf);
        assert_eq!(written, &[0x34, 0x12]);
        assert_eq!(buf, [0x34, 0x12]);
    }

    #[test]
    fn to_le_bytes_fixed_oversized_leaves_trailing_untouched() {
        let v = U16::from(0x1234u16);
        let mut buf = [0xFFu8; 4]; // BYTE_WIDTH == 2; M == 4
        let written = v.to_le_bytes_fixed(&mut buf);
        // Returned slice is the written prefix.
        assert_eq!(written, &[0x34, 0x12]);
        // Trailing bytes left as 0xFF.
        assert_eq!(buf, [0x34, 0x12, 0xFF, 0xFF]);
    }

    #[test]
    fn to_le_bytes_fixed_matches_slice_method() {
        let v = U64::from_array([0xDEADBEEFu32, 0xCAFEBABEu32]);
        let mut a = [0u8; U64::BYTE_WIDTH];
        let mut b = [0u8; U64::BYTE_WIDTH];
        let fixed = v.to_le_bytes_fixed(&mut a);
        let slice = v.to_le_bytes(&mut b).unwrap();
        assert_eq!(fixed, slice);
    }

    // ─── to_be_bytes_fixed ────────────────────────────────────────────

    #[test]
    fn to_be_bytes_fixed_exact_size_round_trips() {
        let v = U16::from(0x1234u16);
        let mut buf = [0u8; U16::BYTE_WIDTH];
        let written = v.to_be_bytes_fixed(&mut buf);
        assert_eq!(written, &[0x12, 0x34]);
        assert_eq!(buf, [0x12, 0x34]);
    }

    #[test]
    fn to_be_bytes_fixed_matches_slice_method() {
        let v = U64::from_array([0xDEADBEEFu32, 0xCAFEBABEu32]);
        let mut a = [0u8; U64::BYTE_WIDTH];
        let mut b = [0u8; U64::BYTE_WIDTH];
        let fixed = v.to_be_bytes_fixed(&mut a);
        let slice = v.to_be_bytes(&mut b).unwrap();
        assert_eq!(fixed, slice);
    }

    #[test]
    fn to_be_bytes_fixed_oversized_leaves_trailing_untouched() {
        let v = U16::from(0x1234u16);
        let mut buf = [0xFFu8; 4];
        let written = v.to_be_bytes_fixed(&mut buf);
        assert_eq!(written, &[0x12, 0x34]);
        assert_eq!(buf, [0x12, 0x34, 0xFF, 0xFF]);
    }

    // ─── from_le_bytes_fixed ──────────────────────────────────────────

    #[test]
    fn from_le_bytes_fixed_exact_size() {
        let buf = [0x34u8, 0x12];
        let v: U16 = U16::from_le_bytes_fixed(&buf);
        assert_eq!(v, U16::from(0x1234u16));
    }

    #[test]
    fn from_le_bytes_fixed_oversized_takes_low_bytes() {
        // U16 wants 2 bytes; provide 4. LE convention: take first 2.
        let buf = [0x34u8, 0x12, 0xFF, 0xFF];
        let v: U16 = U16::from_le_bytes_fixed(&buf);
        assert_eq!(v, U16::from(0x1234u16));
    }

    #[test]
    fn from_le_bytes_fixed_matches_slice_method() {
        let buf = [0xEF, 0xBE, 0xAD, 0xDE, 0xBE, 0xBA, 0xFE, 0xCA];
        let fixed: U64 = U64::from_le_bytes_fixed(&buf);
        let slice: U64 = U64::from_le_bytes(&buf[..]);
        assert_eq!(fixed, slice);
    }

    // ─── from_be_bytes_fixed ──────────────────────────────────────────

    #[test]
    fn from_be_bytes_fixed_exact_size() {
        let buf = [0x12u8, 0x34];
        let v: U16 = U16::from_be_bytes_fixed(&buf);
        assert_eq!(v, U16::from(0x1234u16));
    }

    #[test]
    fn from_be_bytes_fixed_oversized_takes_trailing_bytes() {
        // U16 wants 2 bytes; provide 4. BE convention: take last 2.
        let buf = [0xFFu8, 0xFF, 0x12, 0x34];
        let v: U16 = U16::from_be_bytes_fixed(&buf);
        assert_eq!(v, U16::from(0x1234u16));
    }

    #[test]
    fn from_be_bytes_fixed_matches_slice_method() {
        let buf = [0xDE, 0xAD, 0xBE, 0xEF, 0xCA, 0xFE, 0xBA, 0xBE];
        let fixed: U64 = U64::from_be_bytes_fixed(&buf);
        let slice: U64 = U64::from_be_bytes(&buf[..]);
        assert_eq!(fixed, slice);
    }

    // ─── round-trip across all four ───────────────────────────────────

    #[test]
    fn round_trip_le_fixed() {
        let original = U64::from_array([0xDEADBEEFu32, 0xCAFEBABEu32]);
        let mut buf = [0u8; U64::BYTE_WIDTH];
        let _ = original.to_le_bytes_fixed(&mut buf);
        let back: U64 = U64::from_le_bytes_fixed(&buf);
        assert_eq!(back, original);
    }

    #[test]
    fn round_trip_be_fixed() {
        let original = U64::from_array([0xDEADBEEFu32, 0xCAFEBABEu32]);
        let mut buf = [0u8; U64::BYTE_WIDTH];
        let _ = original.to_be_bytes_fixed(&mut buf);
        let back: U64 = U64::from_be_bytes_fixed(&buf);
        assert_eq!(back, original);
    }

    // ─── wider carrier (sanity-check word stride math) ────────────────

    #[test]
    fn u32_single_limb_le() {
        let v = U32::from(0x12345678u32);
        let mut buf = [0u8; U32::BYTE_WIDTH]; // 4
        let written = v.to_le_bytes_fixed(&mut buf);
        assert_eq!(written, &[0x78, 0x56, 0x34, 0x12]);
        let back: U32 = U32::from_le_bytes_fixed(&buf);
        assert_eq!(back, v);
    }

    #[test]
    fn u32_single_limb_be() {
        let v = U32::from(0x12345678u32);
        let mut buf = [0u8; U32::BYTE_WIDTH];
        let written = v.to_be_bytes_fixed(&mut buf);
        assert_eq!(written, &[0x12, 0x34, 0x56, 0x78]);
        let back: U32 = U32::from_be_bytes_fixed(&buf);
        assert_eq!(back, v);
    }

    // ─── const-context callability (the whole point) ──────────────────
    //
    // These are NOT c0nst — the bodies use `chunks_exact_mut` which
    // isn't const-fn — but exercising them in #[test] form alongside
    // the inherent-const `BYTE_WIDTH` confirms the buffer-sizing
    // pattern downstream callers want.

    #[test]
    fn byte_width_is_usable_as_array_length() {
        // The whole API ergonomic ask: `[0u8; T::BYTE_WIDTH]` works.
        const BUF_LEN: usize = U64::BYTE_WIDTH;
        let mut buf = [0u8; BUF_LEN];
        let v = U64::from(42u32);
        let _ = v.to_le_bytes_fixed(&mut buf);
        // First byte of the value is the LE low byte.
        assert_eq!(buf[0], 42);
    }
}
