use num_traits::ops::overflowing::OverflowingMul;
use num_traits::{Bounded, Zero};

use super::{const_array_mul, maybe_panic, FixedUInt, MachineWord, PanicReason};
use crate::machineword::ConstMachineWord;

impl<T: MachineWord, const N: usize> num_traits::ops::overflowing::OverflowingMul
    for FixedUInt<T, N>
{
    fn overflowing_mul(&self, other: &Self) -> (Self, bool) {
        Self::mul_impl::<true>(self, other)
    }
}

c0nst::c0nst! {
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Mul for FixedUInt<T, N> {
        type Output = Self;
        fn mul(self, other: Self) -> Self::Output {
            let (array, overflow) = const_array_mul::<T, N, true>(&self.array, &other.array, Self::WORD_BITS);
            if overflow {
                maybe_panic(PanicReason::Mul);
            }
            Self { array }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Mul<&FixedUInt<T, N>> for FixedUInt<T, N> {
        type Output = Self;
        fn mul(self, other: &FixedUInt<T, N>) -> Self::Output {
            let (array, overflow) = const_array_mul::<T, N, true>(&self.array, &other.array, Self::WORD_BITS);
            if overflow {
                maybe_panic(PanicReason::Mul);
            }
            Self { array }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Mul<FixedUInt<T, N>> for &FixedUInt<T, N> {
        type Output = FixedUInt<T, N>;
        fn mul(self, other: FixedUInt<T, N>) -> Self::Output {
            let (array, overflow) = const_array_mul::<T, N, true>(&self.array, &other.array, Self::Output::WORD_BITS);
            if overflow {
                maybe_panic(PanicReason::Mul);
            }
            FixedUInt { array }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Mul<&FixedUInt<T, N>> for &FixedUInt<T, N> {
        type Output = FixedUInt<T, N>;
        fn mul(self, other: &FixedUInt<T, N>) -> Self::Output {
            let (array, overflow) = const_array_mul::<T, N, true>(&self.array, &other.array, Self::Output::WORD_BITS);
            if overflow {
                maybe_panic(PanicReason::Mul);
            }
            FixedUInt { array }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Mul<&&FixedUInt<T, N>> for &FixedUInt<T, N> {
        type Output = FixedUInt<T, N>;
        fn mul(self, other: &&FixedUInt<T, N>) -> Self::Output {
            let (array, overflow) = const_array_mul::<T, N, true>(&self.array, &other.array, Self::Output::WORD_BITS);
            if overflow {
                maybe_panic(PanicReason::Mul);
            }
            FixedUInt { array }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::MulAssign for FixedUInt<T, N> {
        fn mul_assign(&mut self, other: Self) {
            let (array, overflow) = const_array_mul::<T, N, true>(&self.array, &other.array, Self::WORD_BITS);
            if overflow {
                maybe_panic(PanicReason::Mul);
            }
            *self = Self { array };
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::MulAssign<&FixedUInt<T, N>> for FixedUInt<T, N> {
        fn mul_assign(&mut self, other: &FixedUInt<T, N>) {
            let (array, overflow) = const_array_mul::<T, N, true>(&self.array, &other.array, Self::WORD_BITS);
            if overflow {
                maybe_panic(PanicReason::Mul);
            }
            *self = Self { array };
        }
    }
}

// num_traits wrappers - not constified (external traits)
impl<T: MachineWord, const N: usize> num_traits::WrappingMul for FixedUInt<T, N> {
    fn wrapping_mul(&self, other: &Self) -> Self {
        Self::mul_impl::<false>(self, other).0
    }
}

impl<T: MachineWord, const N: usize> num_traits::CheckedMul for FixedUInt<T, N> {
    fn checked_mul(&self, other: &Self) -> Option<Self> {
        let res = self.overflowing_mul(other);
        if res.1 {
            None
        } else {
            Some(res.0)
        }
    }
}

impl<T: MachineWord, const N: usize> num_traits::ops::saturating::SaturatingMul
    for FixedUInt<T, N>
{
    fn saturating_mul(&self, other: &Self) -> Self {
        let res = self.overflowing_mul(other);
        if res.1 {
            Self::max_value()
        } else {
            res.0
        }
    }
}

impl<T: MachineWord, const N: usize> core::ops::Div for FixedUInt<T, N> {
    type Output = Self;
    fn div(self, other: Self) -> <Self as core::ops::Div<Self>>::Output {
        if other.is_zero() {
            maybe_panic(PanicReason::DivByZero)
        }
        Self::div_impl(&self, &other)
    }
}

impl<T: MachineWord, const N: usize> core::ops::Div<&'_ Self> for FixedUInt<T, N> {
    type Output = Self;
    fn div(self, other: &Self) -> <Self as core::ops::Div<Self>>::Output {
        if other.is_zero() {
            maybe_panic(PanicReason::DivByZero)
        }
        Self::div_impl(&self, other)
    }
}

impl<T: MachineWord, const N: usize> core::ops::Div<Self> for &FixedUInt<T, N> {
    type Output = FixedUInt<T, N>;
    fn div(self, other: Self) -> Self::Output {
        if other.is_zero() {
            maybe_panic(PanicReason::DivByZero)
        }
        Self::Output::div_impl(self, other)
    }
}

impl<T: MachineWord, const N: usize> core::ops::Div<&Self> for &FixedUInt<T, N> {
    type Output = FixedUInt<T, N>;
    fn div(self, other: &Self) -> Self::Output {
        if other.is_zero() {
            maybe_panic(PanicReason::DivByZero)
        }
        Self::Output::div_impl(self, other)
    }
}

impl<T: MachineWord, const N: usize> core::ops::Div<FixedUInt<T, N>> for &FixedUInt<T, N> {
    type Output = FixedUInt<T, N>;
    fn div(self, other: FixedUInt<T, N>) -> Self::Output {
        if other.is_zero() {
            maybe_panic(PanicReason::DivByZero)
        }
        Self::Output::div_impl(self, &other)
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

impl<T: MachineWord, const N: usize> core::ops::DivAssign<Self> for FixedUInt<T, N> {
    fn div_assign(&mut self, other: Self) {
        if other.is_zero() {
            maybe_panic(PanicReason::DivByZero)
        }
        Self::div_assign_impl(self, &other);
    }
}

impl<T: MachineWord, const N: usize> core::ops::DivAssign<&'_ Self> for FixedUInt<T, N> {
    fn div_assign(&mut self, other: &Self) {
        if other.is_zero() {
            maybe_panic(PanicReason::DivByZero)
        }
        Self::div_assign_impl(self, other);
    }
}

impl<T: MachineWord, const N: usize> core::ops::Rem for FixedUInt<T, N> {
    type Output = Self;
    fn rem(self, other: Self) -> Self {
        if other.is_zero() {
            maybe_panic(PanicReason::RemByZero)
        }
        self.div_rem(&other).1
    }
}

impl<T: MachineWord, const N: usize> core::ops::Rem<&'_ Self> for FixedUInt<T, N> {
    type Output = Self;
    fn rem(self, other: &Self) -> Self {
        if other.is_zero() {
            maybe_panic(PanicReason::RemByZero)
        }
        self.div_rem(other).1
    }
}

impl<T: MachineWord, const N: usize> core::ops::Rem<Self> for &FixedUInt<T, N> {
    type Output = FixedUInt<T, N>;
    fn rem(self, other: Self) -> Self::Output {
        if other.is_zero() {
            maybe_panic(PanicReason::RemByZero)
        }
        self.div_rem(other).1
    }
}

impl<T: MachineWord, const N: usize> core::ops::Rem<&Self> for &FixedUInt<T, N> {
    type Output = FixedUInt<T, N>;
    fn rem(self, other: &Self) -> Self::Output {
        if other.is_zero() {
            maybe_panic(PanicReason::RemByZero)
        }
        self.div_rem(other).1
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

impl<T: MachineWord, const N: usize> core::ops::RemAssign<Self> for FixedUInt<T, N> {
    fn rem_assign(&mut self, other: Self) {
        if other.is_zero() {
            maybe_panic(PanicReason::RemByZero)
        }
        *self = self.div_rem(&other).1;
    }
}

impl<T: MachineWord, const N: usize> core::ops::RemAssign<&'_ Self> for FixedUInt<T, N> {
    fn rem_assign(&mut self, other: &Self) {
        if other.is_zero() {
            maybe_panic(PanicReason::RemByZero)
        }
        *self = self.div_rem(other).1;
    }
}

impl<T: MachineWord, const N: usize> core::ops::Rem<FixedUInt<T, N>> for &FixedUInt<T, N> {
    type Output = FixedUInt<T, N>;
    fn rem(self, other: FixedUInt<T, N>) -> Self::Output {
        if other.is_zero() {
            maybe_panic(PanicReason::RemByZero)
        }
        self.div_rem(&other).1
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
}
