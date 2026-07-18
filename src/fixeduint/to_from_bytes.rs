use core::borrow::{Borrow, BorrowMut};
use core::hash::Hash;

use super::{FixedUInt, MachineWord};
use crate::machineword::ConstMachineWord;
use const_num_traits::Personality;

// Helper, holds an owned copy of returned bytes.
//
// Not `Copy`: when the `zeroize` feature is enabled this type carries
// a `Drop` impl that wipes its contents, so copy semantics are not
// available.  Consumers that previously relied on implicit `BytesHolder:
// Copy` need an explicit `.clone()`.
#[derive(Eq, PartialEq, Clone, PartialOrd, Ord, Debug)]
pub struct BytesHolder<T: MachineWord, const N: usize> {
    array: [T; N],
}

c0nst::c0nst! {
    // `c0nst Default` so this is callable from a `const` context on
    // nightly (the `nightly` feature pulls in `feature(const_default)`).
    // On stable the c0nst macro renders the same impl as plain
    // `impl Default`, so downstream `BytesHolder::default()` callers see
    // no behavior change. Body uses the `[<T as ConstZero>::ZERO; N]`
    // initializer rather than `core::array::from_fn(...)` because the
    // closure-based helper isn't const-callable.
    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> Default for BytesHolder<T, N> {
        fn default() -> Self {
            Self::from_array([<T as const_num_traits::ConstZero>::ZERO; N])
        }
    }
}

impl<T: MachineWord, const N: usize> BytesHolder<T, N> {
    pub(crate) const fn from_array(array: [T; N]) -> Self {
        Self { array }
    }
    // Converts internal storage to a mutable byte slice.
    // `pub(crate)` so the `heapless` module can build a holder from its
    // own limb array with the same endianness discipline.
    pub(crate) fn as_byte_slice_mut(&mut self) -> &mut [u8] {
        // SAFETY: This is safe because the size of the array is the same as the size of the slice
        unsafe {
            core::slice::from_raw_parts_mut(
                &mut self.array as *mut T as *mut u8,
                N * core::mem::size_of::<T>(),
            )
        }
    }
    fn as_byte_slice(&self) -> &[u8] {
        // SAFETY: This is safe because the size of the array is the same as the size of the slice
        unsafe {
            core::slice::from_raw_parts(
                &self.array as *const T as *const u8,
                N * core::mem::size_of::<T>(),
            )
        }
    }
}

impl<T: MachineWord, const N: usize> Borrow<[u8]> for BytesHolder<T, N> {
    fn borrow(&self) -> &[u8] {
        self.as_byte_slice()
    }
}
impl<T: MachineWord, const N: usize> BorrowMut<[u8]> for BytesHolder<T, N> {
    fn borrow_mut(&mut self) -> &mut [u8] {
        self.as_byte_slice_mut()
    }
}
impl<T: MachineWord, const N: usize> AsRef<[u8]> for BytesHolder<T, N> {
    fn as_ref(&self) -> &[u8] {
        self.as_byte_slice()
    }
}
impl<T: MachineWord, const N: usize> AsMut<[u8]> for BytesHolder<T, N> {
    fn as_mut(&mut self) -> &mut [u8] {
        self.as_byte_slice_mut()
    }
}
impl<T: MachineWord, const N: usize> Hash for BytesHolder<T, N> {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.as_byte_slice().hash(state)
    }
}

#[cfg(feature = "zeroize")]
impl<T: MachineWord, const N: usize> zeroize::Zeroize for BytesHolder<T, N> {
    fn zeroize(&mut self) {
        // Wipe via the byte view so the guarantee covers the actual
        // memory representation, not just per-word `T::zeroize` (which
        // could be sub-word-granular for composite limb types).
        self.as_byte_slice_mut().zeroize();
    }
}

#[cfg(feature = "zeroize")]
impl<T: MachineWord, const N: usize> zeroize::ZeroizeOnDrop for BytesHolder<T, N> {}

#[cfg(feature = "zeroize")]
impl<T: MachineWord, const N: usize> Drop for BytesHolder<T, N> {
    fn drop(&mut self) {
        use zeroize::Zeroize;
        self.zeroize();
    }
}

// ── num_traits + const_num_traits ToBytes/FromBytes ──────────────────
//
// Full-width holder builders, shared by `FixedUInt`'s and
// `HeaplessBigInt`'s `ToBytes` paths (they differ only in `self.array` vs
// `self.limbs`). Byte writes go through `as_byte_slice_mut`, so the byte
// sequence is host-endianness-independent. The zip byte-loop needs no
// length proof, so it stays panic-free on every toolchain — unlike
// `chunk.copy_from_slice(word_bytes)`, whose length assert DCEs on only a
// subset of monomorphizations on stable rustc through MSRV.

/// Big-endian: highest limb first, each limb's own bytes big-endian.
pub(crate) fn holder_be_from_limbs<T: MachineWord, const N: usize>(
    limbs: &[T; N],
) -> BytesHolder<T, N> {
    let mut ret = BytesHolder::default();
    let word_size = core::mem::size_of::<T>();
    // Guard against a future `as_byte_slice_mut` desync silently truncating.
    debug_assert_eq!(ret.as_byte_slice_mut().len(), N * word_size);
    for (chunk, word) in ret
        .as_byte_slice_mut()
        .chunks_exact_mut(word_size)
        .zip(limbs.iter().rev())
    {
        let word_bytes = word.to_be_bytes();
        for (dst, src) in chunk.iter_mut().zip(word_bytes.as_ref()) {
            *dst = *src;
        }
    }
    ret
}

/// Little-endian: lowest limb first, each limb's own bytes little-endian.
pub(crate) fn holder_le_from_limbs<T: MachineWord, const N: usize>(
    limbs: &[T; N],
) -> BytesHolder<T, N> {
    let mut ret = BytesHolder::default();
    let word_size = core::mem::size_of::<T>();
    debug_assert_eq!(ret.as_byte_slice_mut().len(), N * word_size);
    for (chunk, word) in ret
        .as_byte_slice_mut()
        .chunks_exact_mut(word_size)
        .zip(limbs.iter())
    {
        let word_bytes = word.to_le_bytes();
        for (dst, src) in chunk.iter_mut().zip(word_bytes.as_ref()) {
            *dst = *src;
        }
    }
    ret
}

// The two `ToBytes` traits differ only in receiver (`&self` vs `self`)
// and the two `FromBytes` traits do the same. Delegate through
// crate-private helpers on `FixedUInt` to keep them in lockstep. Both
// use `BytesHolder<T, N>` as the associated `Bytes` type; the
// const-num-traits variants are `#[cfg(not(feature = "nightly"))]`
// because `const_to_from_bytes.rs` provides better nightly impls via
// `ConstBytesHolder` + `generic_const_exprs`.

#[cfg(any(feature = "num-traits", not(feature = "nightly")))]
impl<T: MachineWord, const N: usize, P: Personality> FixedUInt<T, N, P>
where
    T: core::fmt::Debug,
{
    // `holder_*` build a `BytesHolder` from a `&[T; N]` (never
    // `from_array(self.array)`, which Copy-materialises the referenced array
    // on the stack and defeats the by-ref impl's CT / Zeroize-wrapper intent).
    #[inline]
    fn holder_be(&self) -> BytesHolder<T, N> {
        super::holder_be_from_limbs(&self.array)
    }

    #[inline]
    fn holder_le(&self) -> BytesHolder<T, N> {
        super::holder_le_from_limbs(&self.array)
    }
}

#[cfg(feature = "num-traits")]
impl<T: MachineWord, const N: usize, P: Personality> num_traits::ToBytes for FixedUInt<T, N, P>
where
    T: core::fmt::Debug,
{
    type Bytes = BytesHolder<T, N>;
    fn to_be_bytes(&self) -> Self::Bytes {
        self.holder_be()
    }
    fn to_le_bytes(&self) -> Self::Bytes {
        self.holder_le()
    }
}

#[cfg(feature = "num-traits")]
impl<T: MachineWord, const N: usize, P: Personality> num_traits::FromBytes for FixedUInt<T, N, P>
where
    T: core::fmt::Debug,
{
    type Bytes = BytesHolder<T, N>;
    fn from_be_bytes(bytes: &Self::Bytes) -> Self {
        Self::from_be_bytes(bytes.as_ref())
    }
    fn from_le_bytes(bytes: &Self::Bytes) -> Self {
        Self::from_le_bytes(bytes.as_ref())
    }
}

#[cfg(not(feature = "nightly"))]
impl<T: MachineWord, const N: usize, P: Personality> const_num_traits::ToBytes
    for FixedUInt<T, N, P>
where
    T: core::fmt::Debug,
{
    type Bytes = BytesHolder<T, N>;
    fn to_be_bytes(self) -> Self::Bytes {
        self.holder_be()
    }
    fn to_le_bytes(self) -> Self::Bytes {
        self.holder_le()
    }
}

// `ToBytes for &FixedUInt` — needed by CT nonce paths where the value
// lives behind `Zeroizing<T>` and `(*r).to_le_bytes()` would deref-copy
// an unwrapped secret onto the stack. `<&T as ToBytes>::to_le_bytes(&*r)`
// reads through the reference; only the output `BytesHolder` is
// unwrapped material and the caller can wrap that (or rely on the
// crate-side `ZeroizeOnDrop` when the feature is on).
#[cfg(not(feature = "nightly"))]
impl<T: MachineWord, const N: usize, P: Personality> const_num_traits::ToBytes
    for &FixedUInt<T, N, P>
where
    T: core::fmt::Debug,
{
    type Bytes = BytesHolder<T, N>;
    fn to_be_bytes(self) -> Self::Bytes {
        self.holder_be()
    }
    fn to_le_bytes(self) -> Self::Bytes {
        self.holder_le()
    }
}

#[cfg(not(feature = "nightly"))]
impl<T: MachineWord, const N: usize, P: Personality> const_num_traits::FromBytes
    for FixedUInt<T, N, P>
where
    T: core::fmt::Debug,
{
    type Bytes = BytesHolder<T, N>;

    fn from_be_bytes(bytes: &Self::Bytes) -> Self {
        Self::from_be_bytes(bytes.as_ref())
    }

    fn from_le_bytes(bytes: &Self::Bytes) -> Self {
        Self::from_le_bytes(bytes.as_ref())
    }
}

#[cfg(test)]
#[cfg(feature = "num-traits")]
mod tests {
    use super::*;
    use num_traits::FromPrimitive;

    fn test_helper<T: num_traits::ToBytes>(input: &T, expected_be: &[u8]) {
        let mut buffer = [0u8; 256];
        buffer[..expected_be.len()].copy_from_slice(expected_be);
        let expected_le = &mut buffer[..expected_be.len()];
        expected_le.reverse();

        let out = input.to_be_bytes();
        assert_eq!(out.as_ref(), expected_be);
        let out = input.to_le_bytes();
        assert_eq!(out.as_ref(), expected_le);
    }

    #[test]
    fn test_to_bytes() {
        test_helper(&0xAB_u8, &[0xAB_u8]);
        test_helper(&0xABCD_u16, &[0xAB, 0xCD]);
        test_helper(
            &FixedUInt::<u8, 4>::from_u32(0x12345678).unwrap(),
            &[0x12, 0x34, 0x56, 0x78],
        );
        test_helper(
            &FixedUInt::<u16, 2>::from_u32(0x12345678).unwrap(),
            &[0x12, 0x34, 0x56, 0x78],
        );
        test_helper(
            &FixedUInt::<u32, 1>::from_u32(0x12345678).unwrap(),
            &[0x12, 0x34, 0x56, 0x78],
        );
    }

    fn from_helper<T>(input: &[u8], expected: T)
    where
        T: num_traits::FromBytes + core::fmt::Debug + core::cmp::PartialEq,
        T::Bytes: num_traits::ops::bytes::NumBytes + Default + core::fmt::Debug,
    {
        let mut bytes = T::Bytes::default();
        bytes.as_mut().copy_from_slice(input);
        let result = T::from_be_bytes(&bytes);
        assert_eq!(result, expected);
        bytes.as_mut().reverse();
        let result = T::from_le_bytes(&bytes);
        assert_eq!(result, expected);
    }

    #[cfg(feature = "zeroize")]
    #[test]
    fn test_zeroize_wipes_byte_view() {
        use zeroize::Zeroize;

        let value = FixedUInt::<u32, 4>::from_u32(0xDEAD_BEEF).unwrap();
        let mut bytes = <FixedUInt<u32, 4> as num_traits::ToBytes>::to_be_bytes(&value);
        // Seed every byte before the wipe — `from_u32` only fills the
        // low limb, leaving most of the 16-byte holder already zero.
        // A buggy `zeroize` that wiped only the populated bytes would
        // pass an `all-zero` check without the seed.
        for (index, byte) in bytes.as_mut().iter_mut().enumerate() {
            *byte = (index as u8).wrapping_add(1);
        }
        assert!(bytes.as_ref().iter().all(|b| *b != 0));
        bytes.zeroize();
        assert!(bytes.as_ref().iter().all(|b| *b == 0));
    }

    #[test]
    fn test_from_bytes() {
        from_helper(&[0xAB_u8], 0xAB_u8);
        from_helper(&[0xAB, 0xCD], 0xABCD_u16);
        from_helper(&[0x12, 0x34, 0x56, 0x78], 0x12345678_u32);
        from_helper(
            &[0x12, 0x34, 0x56, 0x78],
            FixedUInt::<u8, 4>::from_u32(0x12345678).unwrap(),
        );
        from_helper(
            &[0x12, 0x34, 0x56, 0x78],
            FixedUInt::<u16, 2>::from_u32(0x12345678).unwrap(),
        );
        from_helper(
            &[0x12, 0x34, 0x56, 0x78],
            FixedUInt::<u32, 1>::from_u32(0x12345678).unwrap(),
        );
    }

    #[test]
    fn nightly_const_eval_default() {
        let h: BytesHolder<u8, 4> = Default::default();
        assert_eq!(h.array, [0u8; 4]);

        #[cfg(feature = "nightly")]
        {
            const DEFAULT_U8X4: BytesHolder<u8, 4> = Default::default();
            const DEFAULT_U16X2: BytesHolder<u16, 2> = Default::default();
            const DEFAULT_U32X1: BytesHolder<u32, 1> = Default::default();
            assert_eq!(DEFAULT_U8X4.array, [0u8; 4]);
            assert_eq!(DEFAULT_U16X2.array, [0u16; 2]);
            assert_eq!(DEFAULT_U32X1.array, [0u32; 1]);
        }
    }
}
