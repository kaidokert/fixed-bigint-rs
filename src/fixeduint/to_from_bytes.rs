use super::MachineWord;

#[cfg(feature = "use-unsafe")]
use core::{
    borrow::{Borrow, BorrowMut},
    hash::Hash,
};

#[cfg(feature = "zeroize")]
use zeroize::DefaultIsZeroes;

#[cfg(any(feature = "use-unsafe", feature = "zeroize"))]
use super::FixedUInt;

#[cfg(feature = "zeroize")]
impl<T: MachineWord, const N: usize> DefaultIsZeroes for FixedUInt<T, N> {}

// Helper, holds an owned copy of returned bytes
#[derive(Eq, PartialEq, Clone, Copy, PartialOrd, Ord, Debug)]
pub struct BytesHolder<T: MachineWord, const N: usize> {
    array: [T; N],
}

impl<T: MachineWord, const N: usize> Default for BytesHolder<T, N> {
    fn default() -> Self {
        Self {
            array: core::array::from_fn(|_| T::default()),
        }
    }
}

#[cfg(feature = "use-unsafe")]
impl<T: MachineWord, const N: usize> BytesHolder<T, N> {
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

#[cfg(feature = "use-unsafe")]
impl<T: MachineWord, const N: usize> Borrow<[u8]> for BytesHolder<T, N> {
    fn borrow(&self) -> &[u8] {
        self.as_byte_slice()
    }
}
#[cfg(feature = "use-unsafe")]
impl<T: MachineWord, const N: usize> BorrowMut<[u8]> for BytesHolder<T, N> {
    fn borrow_mut(&mut self) -> &mut [u8] {
        self.as_byte_slice_mut()
    }
}
#[cfg(feature = "use-unsafe")]
impl<T: MachineWord, const N: usize> AsRef<[u8]> for BytesHolder<T, N> {
    fn as_ref(&self) -> &[u8] {
        self.as_byte_slice()
    }
}
#[cfg(feature = "use-unsafe")]
impl<T: MachineWord, const N: usize> AsMut<[u8]> for BytesHolder<T, N> {
    fn as_mut(&mut self) -> &mut [u8] {
        self.as_byte_slice_mut()
    }
}
#[cfg(feature = "use-unsafe")]
impl<T: MachineWord, const N: usize> Hash for BytesHolder<T, N> {
    fn hash<H: core::hash::Hasher>(&self, _state: &mut H) {
        todo!()
    }
}

#[cfg(feature = "use-unsafe")]
impl<T: MachineWord, const N: usize> num_traits::ToBytes for FixedUInt<T, N>
where
    T: core::fmt::Debug,
{
    type Bytes = BytesHolder<T, N>;

    fn to_be_bytes(&self) -> Self::Bytes {
        let mut ret = Self::Bytes { array: self.array };
        let _ = self.to_be_bytes(ret.as_byte_slice_mut());
        ret
    }

    fn to_le_bytes(&self) -> Self::Bytes {
        let mut ret = Self::Bytes { array: self.array };
        let _ = self.to_le_bytes(ret.as_byte_slice_mut());
        ret
    }
}

#[cfg(feature = "use-unsafe")]
impl<T: MachineWord, const N: usize> num_traits::FromBytes for FixedUInt<T, N>
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
#[cfg(feature = "use-unsafe")]
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
