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

//! Const-compatible ToBytes/FromBytes implementation for FixedUInt.
//!
//! This module requires the `nightly` feature and uses `generic_const_exprs`
//! to compute byte array sizes at compile time without unsafe code.

use super::{FixedUInt, MachineWord};
use crate::const_numtrait::ConstToBytes;
use crate::machineword::ConstMachineWord;
use core::mem::size_of;

/// Byte array type for FixedUInt<T, N> with computed size.
/// Size = N * size_of::<T>() bytes.
#[derive(Eq, PartialEq, Clone, Copy, PartialOrd, Ord, Debug, Hash)]
pub struct ConstBytesHolder<const SIZE: usize> {
    bytes: [u8; SIZE],
}

impl<const SIZE: usize> Default for ConstBytesHolder<SIZE> {
    fn default() -> Self {
        Self { bytes: [0u8; SIZE] }
    }
}

impl<const SIZE: usize> From<[u8; SIZE]> for ConstBytesHolder<SIZE> {
    fn from(bytes: [u8; SIZE]) -> Self {
        Self { bytes }
    }
}

impl<const SIZE: usize> From<ConstBytesHolder<SIZE>> for [u8; SIZE] {
    fn from(holder: ConstBytesHolder<SIZE>) -> Self {
        holder.bytes
    }
}

impl<const SIZE: usize> const AsRef<[u8]> for ConstBytesHolder<SIZE> {
    fn as_ref(&self) -> &[u8] {
        &self.bytes
    }
}

impl<const SIZE: usize> const AsMut<[u8]> for ConstBytesHolder<SIZE> {
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.bytes
    }
}

impl<const SIZE: usize> core::borrow::Borrow<[u8]> for ConstBytesHolder<SIZE> {
    fn borrow(&self) -> &[u8] {
        &self.bytes
    }
}

impl<const SIZE: usize> core::borrow::BorrowMut<[u8]> for ConstBytesHolder<SIZE> {
    fn borrow_mut(&mut self) -> &mut [u8] {
        &mut self.bytes
    }
}

c0nst::c0nst! {
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstToBytes for FixedUInt<T, N>
    where
        [(); N * size_of::<T>()]:,
    {
        type Bytes = ConstBytesHolder<{ N * size_of::<T>() }>;

        fn to_le_bytes(&self) -> Self::Bytes {
            let mut result = ConstBytesHolder { bytes: [0u8; N * size_of::<T>()] };
            let word_size = size_of::<T>();
            let mut i = 0;
            while i < N {
                let word_bytes = ConstToBytes::to_le_bytes(&self.array[i]);
                let src = word_bytes.as_ref();
                let mut j = 0;
                while j < word_size {
                    result.bytes[i * word_size + j] = src[j];
                    j += 1;
                }
                i += 1;
            }
            result
        }

        fn to_be_bytes(&self) -> Self::Bytes {
            let mut result = ConstBytesHolder { bytes: [0u8; N * size_of::<T>()] };
            let word_size = size_of::<T>();
            let mut i = 0;
            while i < N {
                // For big-endian, reverse word order: highest word first
                let word_idx = N - 1 - i;
                let word_bytes = ConstToBytes::to_be_bytes(&self.array[word_idx]);
                let src = word_bytes.as_ref();
                let mut j = 0;
                while j < word_size {
                    result.bytes[i * word_size + j] = src[j];
                    j += 1;
                }
                i += 1;
            }
            result
        }
    }
}

// num_traits::ToBytes implementation - delegates to ConstToBytes
impl<T: MachineWord, const N: usize> num_traits::ToBytes for FixedUInt<T, N>
where
    [(); N * size_of::<T>()]:,
{
    type Bytes = ConstBytesHolder<{ N * size_of::<T>() }>;

    fn to_be_bytes(&self) -> Self::Bytes {
        ConstToBytes::to_be_bytes(self)
    }

    fn to_le_bytes(&self) -> Self::Bytes {
        ConstToBytes::to_le_bytes(self)
    }
}

// num_traits::FromBytes implementation - delegates to inherent FixedUInt methods
impl<T: MachineWord, const N: usize> num_traits::FromBytes for FixedUInt<T, N>
where
    [(); N * size_of::<T>()]:,
{
    type Bytes = ConstBytesHolder<{ N * size_of::<T>() }>;

    fn from_be_bytes(bytes: &Self::Bytes) -> Self {
        // Use UFCS to call the inherent method, not this trait method
        FixedUInt::<T, N>::from_be_bytes(&bytes.bytes)
    }

    fn from_le_bytes(bytes: &Self::Bytes) -> Self {
        // Use UFCS to call the inherent method, not this trait method
        FixedUInt::<T, N>::from_le_bytes(&bytes.bytes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_const_to_le_bytes() {
        let val: FixedUInt<u8, 4> = FixedUInt::from(0x04030201u32);
        let bytes = ConstToBytes::to_le_bytes(&val);
        assert_eq!(bytes.as_ref(), &[0x01, 0x02, 0x03, 0x04]);
    }

    #[test]
    fn test_const_to_be_bytes() {
        let val: FixedUInt<u8, 4> = FixedUInt::from(0x04030201u32);
        let bytes = ConstToBytes::to_be_bytes(&val);
        assert_eq!(bytes.as_ref(), &[0x04, 0x03, 0x02, 0x01]);
    }

    #[test]
    fn test_const_to_bytes_u32_words() {
        let val: FixedUInt<u32, 2> = FixedUInt {
            array: [0x04030201, 0x08070605],
        };
        let le_bytes = ConstToBytes::to_le_bytes(&val);
        assert_eq!(
            le_bytes.as_ref(),
            &[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]
        );

        let be_bytes = ConstToBytes::to_be_bytes(&val);
        assert_eq!(
            be_bytes.as_ref(),
            &[0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01]
        );
    }

    // Test that it works in const context
    const CONST_LE_BYTES: [u8; 4] = {
        let val: FixedUInt<u8, 4> = FixedUInt {
            array: [0x01, 0x02, 0x03, 0x04],
        };
        let holder = ConstToBytes::to_le_bytes(&val);
        holder.bytes
    };

    #[test]
    fn test_const_context() {
        assert_eq!(CONST_LE_BYTES, [0x01, 0x02, 0x03, 0x04]);
    }
}
