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

pub use const_num_traits::PrimInt;
use const_num_traits::{BorrowingSub, CarryingAdd, OverflowingSub, ToBytes};

c0nst::c0nst! {
    /// Const-friendly aggregate trait bundling the arithmetic, bit,
    /// shift, and byte-conversion capabilities every limb type has to
    /// carry to serve as a `FixedUInt`'s `T`.
    ///
    /// The bit/shift `*Assign` supertraits are added explicitly:
    /// `PrimBits`/`PrimInt` provide the by-value bit/shift ops but
    /// not the `*Assign` counterparts, which the per-limb loops in
    /// `fixeduint.rs`/`bit_ops_impl.rs` use (`|=` / `^=` / `<<=` /
    /// `>>=` / `&=` on `T`). Arithmetic `*Assign` and `WideningMul`
    /// are intentionally NOT here — no limb-loop uses `T += T` /
    /// `T -= T`, and the crate doesn't call `T::widening_mul`
    /// anywhere (the CarryingMul impls route through the
    /// `ConstDoubleWord` associated type).
    pub c0nst trait ConstMachineWord:
        [c0nst] PrimInt +
        [c0nst] OverflowingSub<Output = Self> +
        [c0nst] CarryingAdd<Output = Self> +
        [c0nst] BorrowingSub<Output = Self> +
        [c0nst] ToBytes +
        [c0nst] core::ops::BitAndAssign +
        [c0nst] core::ops::BitOrAssign +
        [c0nst] core::ops::BitXorAssign +
        [c0nst] core::ops::ShlAssign<usize> +
        [c0nst] core::ops::ShrAssign<usize> +
        [c0nst] From<u8>
    {
        type ConstDoubleWord: [c0nst] PrimInt
            + [c0nst] core::ops::BitAndAssign
            + [c0nst] core::ops::AddAssign;
        fn to_double(self) -> Self::ConstDoubleWord;
        fn from_double(word: Self::ConstDoubleWord) -> Self;
    }

    c0nst impl ConstMachineWord for u8 {
        type ConstDoubleWord = u16;
        fn to_double(self) -> u16 { self as u16 }
        fn from_double(word: u16) -> u8 { word as u8 }
    }
    c0nst impl ConstMachineWord for u16 {
        type ConstDoubleWord = u32;
        fn to_double(self) -> u32 { self as u32 }
        fn from_double(word: u32) -> u16 { word as u16 }
    }
    c0nst impl ConstMachineWord for u32 {
        type ConstDoubleWord = u64;
        fn to_double(self) -> u64 { self as u64 }
        fn from_double(word: u64) -> u32 { word as u32 }
    }
    c0nst impl ConstMachineWord for u64 {
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
    ConstMachineWord<ConstDoubleWord = Self::DoubleWord>
    + core::hash::Hash
    + const_num_traits::ToPrimitive
{
    type DoubleWord: PrimInt;
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
