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

// Note: in the future, #![feature(const_trait_impl)] should allow
// turning this into a const trait

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
    + core::hash::Hash
{
    type DoubleWord: num_traits::PrimInt;
    fn to_double(self) -> Self::DoubleWord;
    fn from_double(word: Self::DoubleWord) -> Self;
}

impl MachineWord for u8 {
    type DoubleWord = u16;
    fn to_double(self) -> Self::DoubleWord {
        self as Self::DoubleWord
    }
    fn from_double(word: Self::DoubleWord) -> Self {
        word as Self
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
}
impl MachineWord for u32 {
    type DoubleWord = u64;
    fn to_double(self) -> Self::DoubleWord {
        self as Self::DoubleWord
    }
    fn from_double(word: Self::DoubleWord) -> Self {
        word as Self
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
}
