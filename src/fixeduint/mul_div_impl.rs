use num_traits::ops::overflowing::OverflowingMul;
use num_traits::{Bounded, Zero};

use super::{maybe_panic, FixedUInt, MachineWord, PanicReason};

impl<T: MachineWord, const N: usize> num_traits::ops::overflowing::OverflowingMul
    for FixedUInt<T, N>
{
    fn overflowing_mul(&self, other: &Self) -> (Self, bool) {
        Self::mul_impl::<true>(self, other)
    }
}

impl<T: MachineWord, const N: usize> core::ops::Mul for FixedUInt<T, N> {
    type Output = Self;
    fn mul(self, other: Self) -> <Self as core::ops::Mul<Self>>::Output {
        let res = self.overflowing_mul(&other);
        if res.1 {
            maybe_panic(PanicReason::Mul);
        }
        res.0
    }
}

impl<T: MachineWord, const N: usize> core::ops::Mul<&'_ Self> for FixedUInt<T, N> {
    type Output = Self;
    fn mul(self, other: &Self) -> <Self as core::ops::Mul<Self>>::Output {
        let res = self.overflowing_mul(other);
        if res.1 {
            maybe_panic(PanicReason::Mul);
        }
        res.0
    }
}

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

impl<T: MachineWord, const N: usize> core::ops::MulAssign<Self> for FixedUInt<T, N> {
    fn mul_assign(&mut self, other: Self) {
        let res = self.overflowing_mul(&other);
        *self = res.0;
        if res.1 {
            maybe_panic(PanicReason::Mul);
        }
    }
}

impl<T: MachineWord, const N: usize> core::ops::MulAssign<&'_ Self> for FixedUInt<T, N> {
    fn mul_assign(&mut self, other: &Self) {
        let res = self.overflowing_mul(other);
        *self = res.0;
        if res.1 {
            maybe_panic(PanicReason::Mul);
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
        *self = Self::div_impl(self, &other);
    }
}

impl<T: MachineWord, const N: usize> core::ops::DivAssign<&'_ Self> for FixedUInt<T, N> {
    fn div_assign(&mut self, other: &Self) {
        if other.is_zero() {
            maybe_panic(PanicReason::DivByZero)
        }
        *self = Self::div_impl(self, other);
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
