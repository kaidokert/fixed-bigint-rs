use num_traits::Zero;

use super::{
    const_div, const_is_zero, const_mul, maybe_panic, FixedUInt, MachineWord, PanicReason,
};
use crate::const_numtrait::{
    ConstBounded, ConstCheckedMul, ConstOverflowingMul, ConstSaturatingMul, ConstWrappingMul,
};
use crate::machineword::ConstMachineWord;

impl<T: MachineWord, const N: usize> num_traits::ops::overflowing::OverflowingMul
    for FixedUInt<T, N>
{
    fn overflowing_mul(&self, other: &Self) -> (Self, bool) {
        <Self as ConstOverflowingMul>::overflowing_mul(self, other)
    }
}

c0nst::c0nst! {
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstOverflowingMul for FixedUInt<T, N> {
        fn overflowing_mul(&self, other: &Self) -> (Self, bool) {
            let (array, overflow) = const_mul::<T, N, true>(&self.array, &other.array, Self::WORD_BITS);
            (Self { array }, overflow)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstWrappingMul for FixedUInt<T, N> {
        fn wrapping_mul(&self, other: &Self) -> Self {
            let (array, _) = const_mul::<T, N, false>(&self.array, &other.array, Self::WORD_BITS);
            Self { array }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstCheckedMul for FixedUInt<T, N> {
        fn checked_mul(&self, other: &Self) -> Option<Self> {
            let (res, overflow) = <Self as ConstOverflowingMul>::overflowing_mul(self, other);
            if overflow { None } else { Some(res) }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstSaturatingMul for FixedUInt<T, N> {
        fn saturating_mul(&self, other: &Self) -> Self {
            let (res, overflow) = <Self as ConstOverflowingMul>::overflowing_mul(self, other);
            if overflow { <Self as ConstBounded>::max_value() } else { res }
        }
    }
}

c0nst::c0nst! {
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Mul for FixedUInt<T, N> {
        type Output = Self;
        fn mul(self, other: Self) -> Self::Output {
            let (array, overflow) = const_mul::<T, N, true>(&self.array, &other.array, Self::WORD_BITS);
            if overflow {
                maybe_panic(PanicReason::Mul);
            }
            Self { array }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Mul<&FixedUInt<T, N>> for FixedUInt<T, N> {
        type Output = Self;
        fn mul(self, other: &FixedUInt<T, N>) -> Self::Output {
            let (array, overflow) = const_mul::<T, N, true>(&self.array, &other.array, Self::WORD_BITS);
            if overflow {
                maybe_panic(PanicReason::Mul);
            }
            Self { array }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Mul<FixedUInt<T, N>> for &FixedUInt<T, N> {
        type Output = FixedUInt<T, N>;
        fn mul(self, other: FixedUInt<T, N>) -> Self::Output {
            let (array, overflow) = const_mul::<T, N, true>(&self.array, &other.array, Self::Output::WORD_BITS);
            if overflow {
                maybe_panic(PanicReason::Mul);
            }
            FixedUInt { array }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Mul<&FixedUInt<T, N>> for &FixedUInt<T, N> {
        type Output = FixedUInt<T, N>;
        fn mul(self, other: &FixedUInt<T, N>) -> Self::Output {
            let (array, overflow) = const_mul::<T, N, true>(&self.array, &other.array, Self::Output::WORD_BITS);
            if overflow {
                maybe_panic(PanicReason::Mul);
            }
            FixedUInt { array }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Mul<&&FixedUInt<T, N>> for &FixedUInt<T, N> {
        type Output = FixedUInt<T, N>;
        fn mul(self, other: &&FixedUInt<T, N>) -> Self::Output {
            let (array, overflow) = const_mul::<T, N, true>(&self.array, &other.array, Self::Output::WORD_BITS);
            if overflow {
                maybe_panic(PanicReason::Mul);
            }
            FixedUInt { array }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::MulAssign for FixedUInt<T, N> {
        fn mul_assign(&mut self, other: Self) {
            let (array, overflow) = const_mul::<T, N, true>(&self.array, &other.array, Self::WORD_BITS);
            if overflow {
                maybe_panic(PanicReason::Mul);
            }
            *self = Self { array };
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::MulAssign<&FixedUInt<T, N>> for FixedUInt<T, N> {
        fn mul_assign(&mut self, other: &FixedUInt<T, N>) {
            let (array, overflow) = const_mul::<T, N, true>(&self.array, &other.array, Self::WORD_BITS);
            if overflow {
                maybe_panic(PanicReason::Mul);
            }
            *self = Self { array };
        }
    }
}

// num_traits wrappers - delegate to const versions
impl<T: MachineWord, const N: usize> num_traits::WrappingMul for FixedUInt<T, N> {
    fn wrapping_mul(&self, other: &Self) -> Self {
        <Self as ConstWrappingMul>::wrapping_mul(self, other)
    }
}

impl<T: MachineWord, const N: usize> num_traits::CheckedMul for FixedUInt<T, N> {
    fn checked_mul(&self, other: &Self) -> Option<Self> {
        <Self as ConstCheckedMul>::checked_mul(self, other)
    }
}

impl<T: MachineWord, const N: usize> num_traits::ops::saturating::SaturatingMul
    for FixedUInt<T, N>
{
    fn saturating_mul(&self, other: &Self) -> Self {
        <Self as ConstSaturatingMul>::saturating_mul(self, other)
    }
}

c0nst::c0nst! {
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Div for FixedUInt<T, N> {
        type Output = Self;
        fn div(self, other: Self) -> Self::Output {
            if const_is_zero(&other.array) {
                maybe_panic(PanicReason::DivByZero)
            }
            let mut dividend = self.array;
            const_div::<T, N>(&mut dividend, &other.array);
            Self { array: dividend }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Div<&FixedUInt<T, N>> for FixedUInt<T, N> {
        type Output = Self;
        fn div(self, other: &FixedUInt<T, N>) -> Self::Output {
            if const_is_zero(&other.array) {
                maybe_panic(PanicReason::DivByZero)
            }
            let mut dividend = self.array;
            const_div::<T, N>(&mut dividend, &other.array);
            Self { array: dividend }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Div<FixedUInt<T, N>> for &FixedUInt<T, N> {
        type Output = FixedUInt<T, N>;
        fn div(self, other: FixedUInt<T, N>) -> Self::Output {
            if const_is_zero(&other.array) {
                maybe_panic(PanicReason::DivByZero)
            }
            let mut dividend = self.array;
            const_div::<T, N>(&mut dividend, &other.array);
            FixedUInt { array: dividend }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Div<&FixedUInt<T, N>> for &FixedUInt<T, N> {
        type Output = FixedUInt<T, N>;
        fn div(self, other: &FixedUInt<T, N>) -> Self::Output {
            if const_is_zero(&other.array) {
                maybe_panic(PanicReason::DivByZero)
            }
            let mut dividend = self.array;
            const_div::<T, N>(&mut dividend, &other.array);
            FixedUInt { array: dividend }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::DivAssign for FixedUInt<T, N> {
        fn div_assign(&mut self, other: Self) {
            if const_is_zero(&other.array) {
                maybe_panic(PanicReason::DivByZero)
            }
            const_div::<T, N>(&mut self.array, &other.array);
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::DivAssign<&FixedUInt<T, N>> for FixedUInt<T, N> {
        fn div_assign(&mut self, other: &FixedUInt<T, N>) {
            if const_is_zero(&other.array) {
                maybe_panic(PanicReason::DivByZero)
            }
            const_div::<T, N>(&mut self.array, &other.array);
        }
    }
}

impl<T: MachineWord, const N: usize> num_traits::CheckedDiv for FixedUInt<T, N> {
    fn checked_div(&self, other: &Self) -> Option<Self> {
        if other.is_zero() {
            None
        } else {
            Some(core::ops::Div::<Self>::div(*self, *other))
        }
    }
}

c0nst::c0nst! {
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Rem for FixedUInt<T, N> {
        type Output = Self;
        fn rem(self, other: Self) -> Self::Output {
            if const_is_zero(&other.array) {
                maybe_panic(PanicReason::RemByZero)
            }
            let mut dividend = self.array;
            let remainder = const_div::<T, N>(&mut dividend, &other.array);
            Self { array: remainder }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Rem<&FixedUInt<T, N>> for FixedUInt<T, N> {
        type Output = Self;
        fn rem(self, other: &FixedUInt<T, N>) -> Self::Output {
            if const_is_zero(&other.array) {
                maybe_panic(PanicReason::RemByZero)
            }
            let mut dividend = self.array;
            let remainder = const_div::<T, N>(&mut dividend, &other.array);
            Self { array: remainder }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Rem<FixedUInt<T, N>> for &FixedUInt<T, N> {
        type Output = FixedUInt<T, N>;
        fn rem(self, other: FixedUInt<T, N>) -> Self::Output {
            if const_is_zero(&other.array) {
                maybe_panic(PanicReason::RemByZero)
            }
            let mut dividend = self.array;
            let remainder = const_div::<T, N>(&mut dividend, &other.array);
            FixedUInt { array: remainder }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Rem<&FixedUInt<T, N>> for &FixedUInt<T, N> {
        type Output = FixedUInt<T, N>;
        fn rem(self, other: &FixedUInt<T, N>) -> Self::Output {
            if const_is_zero(&other.array) {
                maybe_panic(PanicReason::RemByZero)
            }
            let mut dividend = self.array;
            let remainder = const_div::<T, N>(&mut dividend, &other.array);
            FixedUInt { array: remainder }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::RemAssign for FixedUInt<T, N> {
        fn rem_assign(&mut self, other: Self) {
            if const_is_zero(&other.array) {
                maybe_panic(PanicReason::RemByZero)
            }
            let mut dividend = self.array;
            self.array = const_div::<T, N>(&mut dividend, &other.array);
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::RemAssign<&FixedUInt<T, N>> for FixedUInt<T, N> {
        fn rem_assign(&mut self, other: &FixedUInt<T, N>) {
            if const_is_zero(&other.array) {
                maybe_panic(PanicReason::RemByZero)
            }
            let mut dividend = self.array;
            self.array = const_div::<T, N>(&mut dividend, &other.array);
        }
    }
}

impl<T: MachineWord, const N: usize> num_traits::CheckedRem for FixedUInt<T, N> {
    fn checked_rem(&self, other: &Self) -> Option<Self> {
        if other.is_zero() {
            None
        } else {
            Some(core::ops::Rem::<Self>::rem(*self, *other))
        }
    }
}

// Test wrappers for const mul traits
#[cfg(test)]
c0nst::c0nst! {
    pub c0nst fn const_wrapping_mul<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
        a: &FixedUInt<T, N>,
        b: &FixedUInt<T, N>
    ) -> FixedUInt<T, N> {
        <FixedUInt<T, N> as ConstWrappingMul>::wrapping_mul(a, b)
    }

    pub c0nst fn const_checked_mul<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
        a: &FixedUInt<T, N>,
        b: &FixedUInt<T, N>
    ) -> Option<FixedUInt<T, N>> {
        <FixedUInt<T, N> as ConstCheckedMul>::checked_mul(a, b)
    }

    pub c0nst fn const_saturating_mul<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
        a: &FixedUInt<T, N>,
        b: &FixedUInt<T, N>
    ) -> FixedUInt<T, N> {
        <FixedUInt<T, N> as ConstSaturatingMul>::saturating_mul(a, b)
    }

    pub c0nst fn const_overflowing_mul<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
        a: &FixedUInt<T, N>,
        b: &FixedUInt<T, N>
    ) -> (FixedUInt<T, N>, bool) {
        <FixedUInt<T, N> as ConstOverflowingMul>::overflowing_mul(a, b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_mul() {
        let a = FixedUInt::<u8, 2>::from(123u8);
        let b = FixedUInt::<u8, 2>::from(234u8);
        let c = a * b;
        assert_eq!(c, FixedUInt::<u8, 2>::from(28782u16));
    }

    #[test]
    fn test_mul_combinations() {
        let a = FixedUInt::<u8, 2>::from(12u8);
        let b = FixedUInt::<u8, 2>::from(3u8);
        let expected = FixedUInt::<u8, 2>::from(36u8);

        // value * value
        assert_eq!(a * b, expected);
        // value * ref
        assert_eq!(a * &b, expected);
        // ref * value
        assert_eq!(&a * b, expected);
        // ref * ref
        assert_eq!(&a * &b, expected);
    }

    #[test]
    fn test_div_combinations() {
        let a = FixedUInt::<u8, 2>::from(36u8);
        let b = FixedUInt::<u8, 2>::from(3u8);
        let expected = FixedUInt::<u8, 2>::from(12u8);

        // value / value
        assert_eq!(a / b, expected);
        // value / ref
        assert_eq!(a / &b, expected);
        // ref / value
        assert_eq!(&a / b, expected);
        // ref / ref
        assert_eq!(&a / &b, expected);
    }

    #[test]
    fn test_rem_combinations() {
        let a = FixedUInt::<u8, 2>::from(37u8);
        let b = FixedUInt::<u8, 2>::from(3u8);
        let expected = FixedUInt::<u8, 2>::from(1u8); // 37 % 3 = 1

        // value % value
        assert_eq!(a % b, expected);
        // value % ref
        assert_eq!(a % &b, expected);
        // ref % value
        assert_eq!(&a % b, expected);
        // ref % ref
        assert_eq!(&a % &b, expected);
    }

    #[test]
    fn test_const_mul_traits() {
        let a = FixedUInt::<u8, 2>::from(12u8);
        let b = FixedUInt::<u8, 2>::from(3u8);
        let expected = FixedUInt::<u8, 2>::from(36u8);

        // ConstWrappingMul
        assert_eq!(const_wrapping_mul(&a, &b), expected);

        // ConstCheckedMul - no overflow
        assert_eq!(const_checked_mul(&a, &b), Some(expected));

        // ConstSaturatingMul - no overflow
        assert_eq!(const_saturating_mul(&a, &b), expected);

        // ConstOverflowingMul - no overflow
        let (result, overflow) = const_overflowing_mul(&a, &b);
        assert_eq!(result, expected);
        assert!(!overflow);

        // Test overflow cases: 256 * 256 = 65536 which overflows 16 bits
        let large = FixedUInt::<u8, 2>::from(256u16); // 0x100

        // ConstCheckedMul - with overflow
        assert_eq!(const_checked_mul(&large, &large), None);

        // ConstSaturatingMul - with overflow saturates to max
        let saturated = const_saturating_mul(&large, &large);
        assert_eq!(saturated, FixedUInt::<u8, 2>::from(0xFFFFu16));

        // ConstOverflowingMul - with overflow
        let (_, overflow) = const_overflowing_mul(&large, &large);
        assert!(overflow);

        #[cfg(feature = "nightly")]
        {
            const A: FixedUInt<u8, 2> = FixedUInt { array: [12, 0] };
            const B: FixedUInt<u8, 2> = FixedUInt { array: [3, 0] };

            const WRAPPING_RESULT: FixedUInt<u8, 2> = const_wrapping_mul(&A, &B);
            assert_eq!(WRAPPING_RESULT.array, [36, 0]);

            const CHECKED_RESULT: Option<FixedUInt<u8, 2>> = const_checked_mul(&A, &B);
            assert!(CHECKED_RESULT.is_some());

            const SATURATING_RESULT: FixedUInt<u8, 2> = const_saturating_mul(&A, &B);
            assert_eq!(SATURATING_RESULT.array, [36, 0]);

            const OVERFLOWING_RESULT: (FixedUInt<u8, 2>, bool) = const_overflowing_mul(&A, &B);
            assert_eq!(OVERFLOWING_RESULT.0.array, [36, 0]);
            assert!(!OVERFLOWING_RESULT.1);
        }
    }
}
