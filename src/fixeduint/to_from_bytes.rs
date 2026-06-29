use super::MachineWord;

use core::borrow::{Borrow, BorrowMut};

use core::hash::Hash;

use super::FixedUInt;
use crate::personality::Personality;

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

impl<T: MachineWord, const N: usize> Default for BytesHolder<T, N> {
    fn default() -> Self {
        Self::from_array(core::array::from_fn(|_| T::default()))
    }
}

impl<T: MachineWord, const N: usize> BytesHolder<T, N> {
    pub(crate) fn from_array(array: [T; N]) -> Self {
        Self { array }
    }
    // Converts internal storage to a mutable byte slice
    fn as_byte_slice_mut(&mut self) -> &mut [u8] {
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

impl<T: MachineWord, const N: usize, P: Personality> num_traits::ToBytes for FixedUInt<T, N, P>
where
    T: core::fmt::Debug,
{
    type Bytes = BytesHolder<T, N>;

    fn to_be_bytes(&self) -> Self::Bytes {
        let mut ret = Self::Bytes::from_array(self.array);
        let _ = self.to_be_bytes(ret.as_byte_slice_mut());
        ret
    }

    fn to_le_bytes(&self) -> Self::Bytes {
        let mut ret = Self::Bytes::from_array(self.array);
        let _ = self.to_le_bytes(ret.as_byte_slice_mut());
        ret
    }
}

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

#[cfg(test)]
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
}
