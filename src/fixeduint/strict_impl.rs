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
use crate::machineword::ConstMachineWord;
use const_num_traits::Nct;
use const_num_traits::{
    CheckedPow, OverflowingAdd, OverflowingMul, OverflowingSub, StrictAdd, StrictDiv, StrictMul,
    StrictPow, StrictRem, StrictShl, StrictShr, StrictSub,
};

c0nst::c0nst! {
    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> StrictAdd for FixedUInt<T, N, Nct> {
        type Output = FixedUInt<T, N, Nct>;
        fn strict_add(self, v: Self) -> Self {
            let (res, overflow) = <Self as OverflowingAdd>::overflowing_add(self, v);
            if overflow {
                panic!("FixedUInt: strict_add overflowed");
            }
            res
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> StrictSub for FixedUInt<T, N, Nct> {
        type Output = FixedUInt<T, N, Nct>;
        fn strict_sub(self, v: Self) -> Self {
            let (res, overflow) = <Self as OverflowingSub>::overflowing_sub(self, v);
            if overflow {
                panic!("FixedUInt: strict_sub underflowed");
            }
            res
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> StrictMul for FixedUInt<T, N, Nct> {
        type Output = FixedUInt<T, N, Nct>;
        fn strict_mul(self, v: Self) -> Self {
            let (res, overflow) = <Self as OverflowingMul>::overflowing_mul(self, v);
            if overflow {
                panic!("FixedUInt: strict_mul overflowed");
            }
            res
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> StrictDiv for FixedUInt<T, N, Nct> {
        type Output = FixedUInt<T, N, Nct>;
        fn strict_div(self, v: Self) -> Self {
            // For unsigned `MIN / -1` is N/A; the only overflow mode is `v == 0`,
            // which `Div<Self>` already panics on. Delegate.
            self / v
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> StrictRem for FixedUInt<T, N, Nct> {
        type Output = FixedUInt<T, N, Nct>;
        fn strict_rem(self, v: Self) -> Self {
            self % v
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> StrictShl for FixedUInt<T, N, Nct> {
        type Output = FixedUInt<T, N, Nct>;
        fn strict_shl(self, rhs: u32) -> Self {
            let shift = rhs as usize;
            if shift >= Self::BIT_SIZE {
                panic!("FixedUInt: strict_shl shift exceeds bit width");
            }
            self << shift
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> StrictShr for FixedUInt<T, N, Nct> {
        type Output = FixedUInt<T, N, Nct>;
        fn strict_shr(self, rhs: u32) -> Self {
            let shift = rhs as usize;
            if shift >= Self::BIT_SIZE {
                panic!("FixedUInt: strict_shr shift exceeds bit width");
            }
            self >> shift
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> StrictPow for FixedUInt<T, N, Nct> {
        type Output = FixedUInt<T, N, Nct>;
        fn strict_pow(self, exp: u32) -> Self {
            match <Self as CheckedPow>::checked_pow(self, exp) {
                Some(v) => v,
                None => panic!("FixedUInt: strict_pow overflowed"),
            }
        }
    }

    // --- Reference-receiver mirrors -----------------------------------------

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> StrictAdd for &FixedUInt<T, N, Nct> {
        type Output = FixedUInt<T, N, Nct>;
        fn strict_add(self, v: Self) -> FixedUInt<T, N, Nct> {
            <FixedUInt<T, N, Nct> as StrictAdd>::strict_add(*self, *v)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> StrictSub for &FixedUInt<T, N, Nct> {
        type Output = FixedUInt<T, N, Nct>;
        fn strict_sub(self, v: Self) -> FixedUInt<T, N, Nct> {
            <FixedUInt<T, N, Nct> as StrictSub>::strict_sub(*self, *v)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> StrictMul for &FixedUInt<T, N, Nct> {
        type Output = FixedUInt<T, N, Nct>;
        fn strict_mul(self, v: Self) -> FixedUInt<T, N, Nct> {
            <FixedUInt<T, N, Nct> as StrictMul>::strict_mul(*self, *v)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> StrictDiv for &FixedUInt<T, N, Nct> {
        type Output = FixedUInt<T, N, Nct>;
        fn strict_div(self, v: Self) -> FixedUInt<T, N, Nct> {
            <FixedUInt<T, N, Nct> as StrictDiv>::strict_div(*self, *v)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> StrictRem for &FixedUInt<T, N, Nct> {
        type Output = FixedUInt<T, N, Nct>;
        fn strict_rem(self, v: Self) -> FixedUInt<T, N, Nct> {
            <FixedUInt<T, N, Nct> as StrictRem>::strict_rem(*self, *v)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> StrictShl for &FixedUInt<T, N, Nct> {
        type Output = FixedUInt<T, N, Nct>;
        fn strict_shl(self, rhs: u32) -> FixedUInt<T, N, Nct> {
            <FixedUInt<T, N, Nct> as StrictShl>::strict_shl(*self, rhs)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> StrictShr for &FixedUInt<T, N, Nct> {
        type Output = FixedUInt<T, N, Nct>;
        fn strict_shr(self, rhs: u32) -> FixedUInt<T, N, Nct> {
            <FixedUInt<T, N, Nct> as StrictShr>::strict_shr(*self, rhs)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> StrictPow for &FixedUInt<T, N, Nct> {
        type Output = FixedUInt<T, N, Nct>;
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
        assert_eq!(
            StrictAdd::strict_add(U16::from(10u8), U16::from(20u8)),
            U16::from(30u8)
        );
    }

    #[test]
    #[should_panic(expected = "strict_add overflowed")]
    fn strict_add_overflows() {
        let _ = StrictAdd::strict_add(U16::from(0xFFFFu16), U16::from(1u8));
    }

    #[test]
    fn strict_sub_ok() {
        assert_eq!(
            StrictSub::strict_sub(U16::from(30u8), U16::from(10u8)),
            U16::from(20u8)
        );
    }

    #[test]
    #[should_panic(expected = "strict_sub underflowed")]
    fn strict_sub_underflows() {
        let _ = StrictSub::strict_sub(U16::from(0u8), U16::from(1u8));
    }

    #[test]
    fn strict_mul_ok() {
        assert_eq!(
            StrictMul::strict_mul(U16::from(7u8), U16::from(13u8)),
            U16::from(91u8)
        );
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
    fn strict_shr_ok() {
        assert_eq!(StrictShr::strict_shr(U16::from(256u16), 4), U16::from(16u8));
    }

    #[test]
    #[should_panic(expected = "strict_shr shift exceeds bit width")]
    fn strict_shr_too_wide() {
        let _ = StrictShr::strict_shr(U16::from(1u8), 16);
    }

    #[test]
    fn strict_div_ok() {
        assert_eq!(
            StrictDiv::strict_div(U16::from(100u8), U16::from(10u8)),
            U16::from(10u8)
        );
    }

    #[test]
    fn strict_rem_ok() {
        assert_eq!(
            StrictRem::strict_rem(U16::from(100u8), U16::from(7u8)),
            U16::from(2u8)
        );
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

    // --- Const-eval smoke ---------------------------------------------------
    c0nst::c0nst! {
        pub c0nst fn const_strict_add<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(a: FixedUInt<T, N, Nct>, b: FixedUInt<T, N, Nct>) -> FixedUInt<T, N, Nct> {
            StrictAdd::strict_add(a, b)
        }
        pub c0nst fn const_strict_sub<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(a: FixedUInt<T, N, Nct>, b: FixedUInt<T, N, Nct>) -> FixedUInt<T, N, Nct> {
            StrictSub::strict_sub(a, b)
        }
        pub c0nst fn const_strict_mul<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(a: FixedUInt<T, N, Nct>, b: FixedUInt<T, N, Nct>) -> FixedUInt<T, N, Nct> {
            StrictMul::strict_mul(a, b)
        }
        pub c0nst fn const_strict_div<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(a: FixedUInt<T, N, Nct>, b: FixedUInt<T, N, Nct>) -> FixedUInt<T, N, Nct> {
            StrictDiv::strict_div(a, b)
        }
        pub c0nst fn const_strict_rem<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(a: FixedUInt<T, N, Nct>, b: FixedUInt<T, N, Nct>) -> FixedUInt<T, N, Nct> {
            StrictRem::strict_rem(a, b)
        }
        pub c0nst fn const_strict_shl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(a: FixedUInt<T, N, Nct>, rhs: u32) -> FixedUInt<T, N, Nct> {
            StrictShl::strict_shl(a, rhs)
        }
        pub c0nst fn const_strict_shr<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(a: FixedUInt<T, N, Nct>, rhs: u32) -> FixedUInt<T, N, Nct> {
            StrictShr::strict_shr(a, rhs)
        }
        pub c0nst fn const_strict_pow<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(a: FixedUInt<T, N, Nct>, exp: u32) -> FixedUInt<T, N, Nct> {
            StrictPow::strict_pow(a, exp)
        }
    }

    #[test]
    fn nightly_const_eval_strict() {
        assert_eq!(
            const_strict_add(U16::from(10u8), U16::from(20u8)),
            U16::from(30u8)
        );
        assert_eq!(
            const_strict_mul(U16::from(6u8), U16::from(7u8)),
            U16::from(42u8)
        );
        assert_eq!(const_strict_shl(U16::from(1u8), 4), U16::from(16u8));
        assert_eq!(const_strict_pow(U16::from(2u8), 8), U16::from(256u16));

        #[cfg(feature = "nightly")]
        {
            const A: U16 = FixedUInt::from_array([10, 0]);
            const B: U16 = FixedUInt::from_array([20, 0]);
            const TWO: U16 = FixedUInt::from_array([2, 0]);
            const THIRTY: U16 = FixedUInt::from_array([30, 0]);
            const TEN: U16 = FixedUInt::from_array([10, 0]);
            const TWO_HUNDRED: U16 = FixedUInt::from_array([200, 0]);
            const SIXTEEN: U16 = FixedUInt::from_array([16, 0]);
            const TWO_FIFTY_SIX: U16 = FixedUInt::from_array([0, 1]);

            const ADD: U16 = const_strict_add(A, B);
            const SUB: U16 = const_strict_sub(THIRTY, A);
            const MUL: U16 = const_strict_mul(TEN, TWO);
            const DIV: U16 = const_strict_div(TWO_HUNDRED, TEN);
            const REM: U16 = const_strict_rem(TWO_HUNDRED, FixedUInt::from_array([7, 0]));
            const SHL: U16 = const_strict_shl(TWO, 3);
            const SHR: U16 = const_strict_shr(SIXTEEN, 2);
            const POW: U16 = const_strict_pow(TWO, 8);

            assert_eq!(ADD, FixedUInt::from_array([30, 0]));
            assert_eq!(SUB, FixedUInt::from_array([20, 0]));
            assert_eq!(MUL, FixedUInt::from_array([20, 0]));
            assert_eq!(DIV, FixedUInt::from_array([20, 0]));
            assert_eq!(REM, FixedUInt::from_array([4, 0]));
            assert_eq!(SHL, FixedUInt::from_array([16, 0]));
            assert_eq!(SHR, FixedUInt::from_array([4, 0]));
            assert_eq!(POW, TWO_FIFTY_SIX);
        }
    }
}
