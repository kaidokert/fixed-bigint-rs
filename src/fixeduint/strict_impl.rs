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

//! `Strict*` implementations for FixedUInt.
//!
//! The strict family panics on overflow regardless of debug/release.
//! That semantic is intrinsically value-dependent — incompatible with
//! constant-time guarantees — so impls are gated on `P = Nct`. Bodies
//! delegate to the existing `Overflowing*` / `Checked*` paths and
//! convert the overflow flag into a `panic!`.

use super::{FixedUInt, MachineWord};
use crate::const_numtraits::{
    CheckedPow, OverflowingAdd, OverflowingMul, OverflowingSub, StrictAdd, StrictDiv, StrictMul,
    StrictPow, StrictRem, StrictShl, StrictShr, StrictSub,
};
use crate::machineword::ConstMachineWord;
use crate::personality::Nct;

c0nst::c0nst! {
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst StrictAdd for FixedUInt<T, N, Nct> {
        fn strict_add(self, v: Self) -> Self {
            let (res, overflow) = <Self as OverflowingAdd>::overflowing_add(self, v);
            if overflow {
                panic!("FixedUInt: strict_add overflowed");
            }
            res
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst StrictSub for FixedUInt<T, N, Nct> {
        fn strict_sub(self, v: Self) -> Self {
            let (res, overflow) = <Self as OverflowingSub>::overflowing_sub(self, v);
            if overflow {
                panic!("FixedUInt: strict_sub underflowed");
            }
            res
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst StrictMul for FixedUInt<T, N, Nct> {
        fn strict_mul(self, v: Self) -> Self {
            let (res, overflow) = <Self as OverflowingMul>::overflowing_mul(self, v);
            if overflow {
                panic!("FixedUInt: strict_mul overflowed");
            }
            res
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst StrictDiv for FixedUInt<T, N, Nct> {
        fn strict_div(self, v: Self) -> Self {
            // For unsigned `MIN / -1` is N/A; the only overflow mode is `v == 0`,
            // which `Div<Self>` already panics on. Delegate.
            self / v
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst StrictRem for FixedUInt<T, N, Nct> {
        fn strict_rem(self, v: Self) -> Self {
            self % v
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst StrictShl for FixedUInt<T, N, Nct> {
        fn strict_shl(self, rhs: u32) -> Self {
            if (rhs as usize) >= Self::BIT_SIZE {
                panic!("FixedUInt: strict_shl shift exceeds bit width");
            }
            self << (rhs as usize)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst StrictShr for FixedUInt<T, N, Nct> {
        fn strict_shr(self, rhs: u32) -> Self {
            if (rhs as usize) >= Self::BIT_SIZE {
                panic!("FixedUInt: strict_shr shift exceeds bit width");
            }
            self >> (rhs as usize)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst StrictPow for FixedUInt<T, N, Nct> {
        fn strict_pow(self, exp: u32) -> Self {
            match <Self as CheckedPow>::checked_pow(self, exp) {
                Some(v) => v,
                None => panic!("FixedUInt: strict_pow overflowed"),
            }
        }
    }

    // --- Reference-receiver mirrors -----------------------------------------

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst StrictAdd for &FixedUInt<T, N, Nct> {
        fn strict_add(self, v: Self) -> FixedUInt<T, N, Nct> {
            <FixedUInt<T, N, Nct> as StrictAdd>::strict_add(*self, *v)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst StrictSub for &FixedUInt<T, N, Nct> {
        fn strict_sub(self, v: Self) -> FixedUInt<T, N, Nct> {
            <FixedUInt<T, N, Nct> as StrictSub>::strict_sub(*self, *v)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst StrictMul for &FixedUInt<T, N, Nct> {
        fn strict_mul(self, v: Self) -> FixedUInt<T, N, Nct> {
            <FixedUInt<T, N, Nct> as StrictMul>::strict_mul(*self, *v)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst StrictDiv for &FixedUInt<T, N, Nct> {
        fn strict_div(self, v: Self) -> FixedUInt<T, N, Nct> {
            <FixedUInt<T, N, Nct> as StrictDiv>::strict_div(*self, *v)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst StrictRem for &FixedUInt<T, N, Nct> {
        fn strict_rem(self, v: Self) -> FixedUInt<T, N, Nct> {
            <FixedUInt<T, N, Nct> as StrictRem>::strict_rem(*self, *v)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst StrictShl for &FixedUInt<T, N, Nct> {
        fn strict_shl(self, rhs: u32) -> FixedUInt<T, N, Nct> {
            <FixedUInt<T, N, Nct> as StrictShl>::strict_shl(*self, rhs)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst StrictShr for &FixedUInt<T, N, Nct> {
        fn strict_shr(self, rhs: u32) -> FixedUInt<T, N, Nct> {
            <FixedUInt<T, N, Nct> as StrictShr>::strict_shr(*self, rhs)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst StrictPow for &FixedUInt<T, N, Nct> {
        fn strict_pow(self, exp: u32) -> FixedUInt<T, N, Nct> {
            <FixedUInt<T, N, Nct> as StrictPow>::strict_pow(*self, exp)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type U16 = FixedUInt<u8, 2, Nct>;

    #[test]
    fn strict_add_ok() {
        assert_eq!(StrictAdd::strict_add(U16::from(10u8), U16::from(20u8)), U16::from(30u8));
    }

    #[test]
    #[should_panic(expected = "strict_add overflowed")]
    fn strict_add_overflows() {
        let _ = StrictAdd::strict_add(U16::from(0xFFFFu16), U16::from(1u8));
    }

    #[test]
    fn strict_sub_ok() {
        assert_eq!(StrictSub::strict_sub(U16::from(30u8), U16::from(10u8)), U16::from(20u8));
    }

    #[test]
    #[should_panic(expected = "strict_sub underflowed")]
    fn strict_sub_underflows() {
        let _ = StrictSub::strict_sub(U16::from(0u8), U16::from(1u8));
    }

    #[test]
    fn strict_mul_ok() {
        assert_eq!(StrictMul::strict_mul(U16::from(7u8), U16::from(13u8)), U16::from(91u8));
    }

    #[test]
    #[should_panic(expected = "strict_mul overflowed")]
    fn strict_mul_overflows() {
        let _ = StrictMul::strict_mul(U16::from(0x1000u16), U16::from(0x1000u16));
    }

    #[test]
    fn strict_shl_ok() {
        assert_eq!(StrictShl::strict_shl(U16::from(1u8), 8), U16::from(256u16));
    }

    #[test]
    #[should_panic(expected = "strict_shl shift exceeds bit width")]
    fn strict_shl_too_wide() {
        let _ = StrictShl::strict_shl(U16::from(1u8), 16);
    }

    #[test]
    #[should_panic(expected = "strict_shr shift exceeds bit width")]
    fn strict_shr_too_wide() {
        let _ = StrictShr::strict_shr(U16::from(1u8), 16);
    }

    #[test]
    fn strict_pow_ok() {
        assert_eq!(StrictPow::strict_pow(U16::from(2u8), 8), U16::from(256u16));
    }

    #[test]
    #[should_panic(expected = "strict_pow overflowed")]
    fn strict_pow_overflows() {
        let _ = StrictPow::strict_pow(U16::from(2u8), 16);
    }

    #[test]
    fn strict_ref() {
        let a = U16::from(10u8);
        let b = U16::from(20u8);
        assert_eq!(StrictAdd::strict_add(&a, &b), U16::from(30u8));
    }
}
