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
    + num_traits::Unsigned
    + num_traits::ops::overflowing::OverflowingAdd
    + num_traits::ops::overflowing::OverflowingSub
    + From<u8>
    + num_traits::WrappingShl
    + OverflowingShl
    + OverflowingShr
    + core::fmt::Debug
{
    type DoubleWord: num_traits::PrimInt
        + num_traits::Unsigned
        + num_traits::WrappingAdd
        + num_traits::WrappingSub
        + OverflowingShl;
    fn to_double(self) -> Self::DoubleWord;
    fn from_double(word: Self::DoubleWord) -> Self;

    // Todo: get rid of this, single use
    fn to_ne_bytes(self) -> [u8; 8];
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
}

// These should be in num_traits
pub trait OverflowingShl: Sized {
    fn overflowing_shl(self, rhs: u32) -> (Self, bool);
}
pub trait OverflowingShr: Sized {
    fn overflowing_shr(self, rhs: u32) -> (Self, bool);
}

macro_rules! overflowing_shift_impl {
    ($trait_name:ident, $method:ident, $t:ty) => {
        impl $trait_name for $t {
            #[inline]
            fn $method(self, rhs: u32) -> ($t, bool) {
                <$t>::$method(self, rhs)
            }
        }
    };
}

overflowing_shift_impl!(OverflowingShl, overflowing_shl, u8);
overflowing_shift_impl!(OverflowingShl, overflowing_shl, u16);
overflowing_shift_impl!(OverflowingShl, overflowing_shl, u32);
overflowing_shift_impl!(OverflowingShl, overflowing_shl, u64);

overflowing_shift_impl!(OverflowingShr, overflowing_shr, u8);
overflowing_shift_impl!(OverflowingShr, overflowing_shr, u16);
overflowing_shift_impl!(OverflowingShr, overflowing_shr, u32);
overflowing_shift_impl!(OverflowingShr, overflowing_shr, u64);

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
