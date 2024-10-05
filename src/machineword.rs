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
    + Default
{
    type DoubleWord: num_traits::PrimInt;
    fn to_double(self) -> Self::DoubleWord;
    fn from_double(word: Self::DoubleWord) -> Self;

    // Todo: get rid of this, single use
    fn to_ne_bytes(self) -> [u8; 8];
}

impl MachineWord for u8 {
    type DoubleWord = u16;
    fn to_double(self) -> Self::DoubleWord {
        self as Self::DoubleWord
    }
    fn from_double(word: Self::DoubleWord) -> Self {
        word as Self
    }
    fn to_ne_bytes(self) -> [u8; 8] {
        let mut ret = [0; 8];
        ret[0] = self;
        ret
    }
}
impl MachineWord for u16 {
    type DoubleWord = u32;
    fn to_double(self) -> Self::DoubleWord {
        self as Self::DoubleWord
    }
    fn from_double(word: Self::DoubleWord) -> Self {
        word as Self
    }
    fn to_ne_bytes(self) -> [u8; 8] {
        let mut ret = [0; 8];
        let halfslice = &mut ret[0..2];
        halfslice.copy_from_slice(&self.to_ne_bytes());
        ret
    }
}
impl MachineWord for u32 {
    type DoubleWord = u64;
    fn to_double(self) -> Self::DoubleWord {
        self as Self::DoubleWord
    }
    fn from_double(word: Self::DoubleWord) -> Self {
        word as Self
    }
    fn to_ne_bytes(self) -> [u8; 8] {
        let mut ret = [0; 8];
        let halfslice = &mut ret[0..4];
        halfslice.copy_from_slice(&self.to_ne_bytes());
        ret
    }
}
impl MachineWord for u64 {
    type DoubleWord = u128;
    fn to_double(self) -> Self::DoubleWord {
        self as Self::DoubleWord
    }
    fn from_double(word: Self::DoubleWord) -> Self {
        word as Self
    }
    fn to_ne_bytes(self) -> [u8; 8] {
        let mut ret = [0; 8];
        let halfslice = &mut ret[0..4];
        halfslice.copy_from_slice(&self.to_ne_bytes());
        ret
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
}
