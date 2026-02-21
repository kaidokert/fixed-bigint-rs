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

pub use crate::const_numtrait::ConstPrimInt;
use crate::const_numtrait::{
    ConstOverflowingAdd, ConstOverflowingSub, ConstToBytes, ConstWideningMul,
};

c0nst::c0nst! {
    /// A const-friendly trait for MachineWord operations.
    /// Extends ConstWideningMul to provide widening multiplication.
    pub c0nst trait ConstMachineWord:
        [c0nst] ConstPrimInt +
        [c0nst] ConstOverflowingAdd +
        [c0nst] ConstOverflowingSub +
        [c0nst] ConstToBytes +
        [c0nst] ConstWideningMul
    {
        type ConstDoubleWord: [c0nst] ConstPrimInt;
        fn to_double(self) -> Self::ConstDoubleWord;
        fn from_double(word: Self::ConstDoubleWord) -> Self;
    }

    impl c0nst ConstMachineWord for u8 {
        type ConstDoubleWord = u16;
        fn to_double(self) -> u16 { self as u16 }
        fn from_double(word: u16) -> u8 { word as u8 }
    }
    impl c0nst ConstMachineWord for u16 {
        type ConstDoubleWord = u32;
        fn to_double(self) -> u32 { self as u32 }
        fn from_double(word: u32) -> u16 { word as u16 }
    }
    impl c0nst ConstMachineWord for u32 {
        type ConstDoubleWord = u64;
        fn to_double(self) -> u64 { self as u64 }
        fn from_double(word: u64) -> u32 { word as u32 }
    }
    impl c0nst ConstMachineWord for u64 {
        type ConstDoubleWord = u128;
        fn to_double(self) -> u128 { self as u128 }
        fn from_double(word: u128) -> u64 { word as u64 }
    }
}

/// Represents a CPU native word, from 8-bit to 64-bit, with corresponding
/// double-word to hold multiplication/division products.
///
/// This trait is intentionally sealed via the `ConstMachineWord` supertrait,
/// as custom implementations are not supported.
pub trait MachineWord:
    ConstMachineWord<ConstDoubleWord = Self::DoubleWord> + core::hash::Hash + num_traits::ToPrimitive
{
    type DoubleWord: ConstPrimInt;
}

impl MachineWord for u8 {
    type DoubleWord = u16;
}
impl MachineWord for u16 {
    type DoubleWord = u32;
}
impl MachineWord for u32 {
    type DoubleWord = u64;
}
impl MachineWord for u64 {
    type DoubleWord = u128;
}

#[cfg(test)]
mod tests {
    use super::*;

    c0nst::c0nst! {
        pub c0nst fn to_double<T: [c0nst] ConstMachineWord>(a: T) -> T::ConstDoubleWord {
            a.to_double()
        }
    }

    #[test]
    fn test_constmachineword_ops() {
        assert_eq!(to_double(200u8), 200u16);

        #[cfg(feature = "nightly")]
        {
            const DOUBLE_RES: u16 = to_double(200u8);
            assert_eq!(DOUBLE_RES, 200u16);
        }
    }
}
