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

/// Enum to specify byte order.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum Endianness {
    Big,
    Little,
    Native,
}

/// Represents a CPU native word, from 8-bit to 32-bit, with corresponding
/// double-word to hold multiplication/division products.
pub trait MachineWord:
    num_traits::PrimInt
    + num_traits::ops::overflowing::OverflowingAdd
    + num_traits::ops::overflowing::OverflowingSub
    + From<u8>
    + core::ops::BitAndAssign
    + core::ops::BitOrAssign
    + core::ops::BitXorAssign
    + num_traits::FromBytes
    + num_traits::ToBytes
{
    type DoubleWord: num_traits::PrimInt;
    fn to_double(self) -> Self::DoubleWord;
    fn from_double(word: Self::DoubleWord) -> Self;

    // Todo: get rid of this, single use
    fn to_ne_bytes(self) -> [u8; 8];

    #[cfg(feature = "use-unsafe")]
    fn to_byte_buffer<'a, const N: usize>(array: &'a [Self; N], endianness: Endianness)
        -> &'a [u8];
    #[cfg(feature = "use-unsafe")]
    fn to_byte_buffer_mut<'a, const N: usize>(
        array: &'a mut [Self; N],
        endianness: Endianness,
    ) -> &'a mut [u8];
}

impl MachineWord for u8 {
    type DoubleWord = u16;
    fn to_double(self) -> u16 {
        self as u16
    }
    fn from_double(word: u16) -> u8 {
        word as u8
    }
    fn to_ne_bytes(self) -> [u8; 8] {
        let mut ret = [0; 8];
        ret[0] = self;
        ret
    }
    #[cfg(feature = "use-unsafe")]
    fn to_byte_buffer<'a, const N: usize>(
        array: &'a [Self; N],
        _endianness: Endianness,
    ) -> &'a [u8] {
        array
    }
    #[cfg(feature = "use-unsafe")]
    fn to_byte_buffer_mut<'a, const N: usize>(
        array: &'a mut [u8; N],
        _endianness: Endianness,
    ) -> &'a mut [u8] {
        array
    }
}
impl MachineWord for u16 {
    type DoubleWord = u32;
    fn to_double(self) -> u32 {
        self as u32
    }
    fn from_double(word: u32) -> u16 {
        word as u16
    }
    fn to_ne_bytes(self) -> [u8; 8] {
        let mut ret = [0; 8];
        let halfslice = &mut ret[0..2];
        halfslice.copy_from_slice(&self.to_ne_bytes());
        ret
    }
    #[cfg(feature = "use-unsafe")]
    fn to_byte_buffer<'a, const N: usize>(
        array: &'a [Self; N],
        endianness: Endianness,
    ) -> &'a [u8] {
        let buffer = array.map(|word| match endianness {
            Endianness::Big => word.to_be_bytes(),
            Endianness::Little => word.to_le_bytes(),
            Endianness::Native => word.to_ne_bytes(),
        });
        unsafe { core::slice::from_raw_parts(buffer.as_ptr() as *const u8, N * 2) }
    }
    #[cfg(feature = "use-unsafe")]
    fn to_byte_buffer_mut<'a, const N: usize>(
        array: &'a mut [u16; N],
        endianness: Endianness,
    ) -> &'a mut [u8] {
        let mut buffer = array.map(|word| match endianness {
            Endianness::Big => word.to_be_bytes(),
            Endianness::Little => word.to_le_bytes(),
            Endianness::Native => word.to_ne_bytes(),
        });
        unsafe { core::slice::from_raw_parts_mut(buffer.as_mut_ptr() as *mut u8, N * 2) }
    }
}
impl MachineWord for u32 {
    type DoubleWord = u64;
    fn to_double(self) -> u64 {
        self as u64
    }
    fn from_double(word: u64) -> u32 {
        word as u32
    }
    fn to_ne_bytes(self) -> [u8; 8] {
        let mut ret = [0; 8];
        let halfslice = &mut ret[0..4];
        halfslice.copy_from_slice(&self.to_ne_bytes());
        ret
    }
    #[cfg(feature = "use-unsafe")]
    fn to_byte_buffer<'a, const N: usize>(
        array: &'a [Self; N],
        endianness: Endianness,
    ) -> &'a [u8] {
        let buffer = array.map(|word| match endianness {
            Endianness::Big => word.to_be_bytes(),
            Endianness::Little => word.to_le_bytes(),
            Endianness::Native => word.to_ne_bytes(),
        });
        unsafe { core::slice::from_raw_parts(buffer.as_ptr() as *const u8, N * 4) }
    }
    #[cfg(feature = "use-unsafe")]
    fn to_byte_buffer_mut<'a, const N: usize>(
        array: &'a mut [u32; N],
        endianness: Endianness,
    ) -> &'a mut [u8] {
        let mut buffer = array.map(|word| match endianness {
            Endianness::Big => word.to_be_bytes(),
            Endianness::Little => word.to_le_bytes(),
            Endianness::Native => word.to_ne_bytes(),
        });
        unsafe { core::slice::from_raw_parts_mut(buffer.as_mut_ptr() as *mut u8, N * 4) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn machineword_to_ne() {
        fn compare<T: MachineWord>(input: T, reference: [u8; 8]) {
            assert_eq!(input.to_ne_bytes(), reference);
        }
        compare(1u8, [1u8, 0, 0, 0, 0, 0, 0, 0]);
        compare(2u8, [2u8, 0, 0, 0, 0, 0, 0, 0]);
        compare(255u8, [255u8, 0, 0, 0, 0, 0, 0, 0]);
        compare(0xa3f4u16, [0xf4, 0xa3, 0, 0, 0, 0, 0, 0]);
        compare(2u16, [2u8, 0, 0, 0, 0, 0, 0, 0]);
        compare(257u16, [1u8, 1, 0, 0, 0, 0, 0, 0]);
        compare(2u32, [2u8, 0, 0, 0, 0, 0, 0, 0]);
        compare(65537u32, [1u8, 0, 1, 0, 0, 0, 0, 0]);
    }

    #[cfg(feature = "use-unsafe")]
    #[test]
    fn test_to_byte_buffer() {
        const N: usize = 3;
        let words_u8: [u8; N] = [1; N];
        let words_u16: [u16; N] = [256; N];
        let words_u32: [u32; N] = [65536; N];

        let buffer_u8 = <u8 as MachineWord>::to_byte_buffer(&words_u8, Endianness::Native);
        let buffer_u16 = <u16 as MachineWord>::to_byte_buffer(&words_u16, Endianness::Native);
        let buffer_u32 = <u32 as MachineWord>::to_byte_buffer(&words_u32, Endianness::Native);

        assert_eq!(buffer_u8.len(), N);
        assert_eq!(buffer_u16.len(), N * 2);
        assert_eq!(buffer_u32.len(), N * 4);
    }
    #[cfg(feature = "use-unsafe")]
    #[test]
    fn test_to_mut_byte_buffer() {
        const N: usize = 3;
        let mut words_u8: [u8; N] = [1; N];
        let mut words_u16: [u16; N] = [256; N];
        let mut words_u32: [u32; N] = [65536; N];

        let buffer_u8 = <u8 as MachineWord>::to_byte_buffer_mut(&mut words_u8, Endianness::Native);
        let buffer_u16 =
            <u16 as MachineWord>::to_byte_buffer_mut(&mut words_u16, Endianness::Native);
        let buffer_u32 =
            <u32 as MachineWord>::to_byte_buffer_mut(&mut words_u32, Endianness::Native);

        buffer_u8[0] = 42;
        buffer_u16[0] = 42;
        buffer_u32[0] = 42;
        assert_eq!(buffer_u8.len(), N);
        assert_eq!(buffer_u16.len(), N * 2);
        assert_eq!(buffer_u32.len(), N * 4);
    }
    #[cfg(feature = "use-unsafe")]
    #[test]
    fn test_actual_correctness_of_to_byte_buffer() {
        const N: usize = 3;
        let words_u8: [u8; N] = [1, 2, 3];
        let words_u16: [u16; N] = [256, 257, 258];
        let words_u32: [u32; N] = [65536, 65537, 65538];

        let buffer_u8 = <u8 as MachineWord>::to_byte_buffer(&words_u8, Endianness::Native);
        let buffer_u16 = <u16 as MachineWord>::to_byte_buffer(&words_u16, Endianness::Big);
        let buffer_u32 = <u32 as MachineWord>::to_byte_buffer(&words_u32, Endianness::Native);

        assert_eq!(buffer_u8, &[1, 2, 3]);
        //assert_eq!(buffer_u16, &[0, 1, 0, 1, 2, 1]);
        // assert_eq!(buffer_u32, &[0, 1, 0, 0, 1, 0, 0, 2, 1, 0, 0, 3]);
    }
}
