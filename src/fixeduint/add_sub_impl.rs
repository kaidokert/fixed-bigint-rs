use super::{maybe_panic, FixedUInt, MachineWord, PanicReason};

use num_traits::ops::overflowing::{OverflowingAdd, OverflowingSub};

impl<T: MachineWord, const N: usize> num_traits::ops::overflowing::OverflowingAdd
    for FixedUInt<T, N>
{
    fn overflowing_add(&self, other: &Self) -> (Self, bool) {
        let mut ret = *self;
        let overflow = Self::add_impl(&mut ret, other);
        (ret, overflow)
    }
}

impl<T: MachineWord, const N: usize> core::ops::Add for FixedUInt<T, N> {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        let (res, overflow) = self.overflowing_add(&other);
        if overflow {
            maybe_panic(PanicReason::Add);
        }
        res
    }
}

impl<T: MachineWord, const N: usize> core::ops::Add<&'_ Self> for FixedUInt<T, N> {
    type Output = Self;
    fn add(self, other: &Self) -> Self {
        let (res, overflow) = self.overflowing_add(other);
        if overflow {
            maybe_panic(PanicReason::Add);
        }
        res
    }
}

impl<T: MachineWord, const N: usize> num_traits::WrappingAdd for FixedUInt<T, N> {
    fn wrapping_add(&self, other: &Self) -> Self {
        self.overflowing_add(other).0
    }
}

impl<T: MachineWord, const N: usize> num_traits::CheckedAdd for FixedUInt<T, N> {
    fn checked_add(&self, other: &Self) -> Option<Self> {
        let res = self.overflowing_add(other);
        if res.1 {
            None
        } else {
            Some(res.0)
        }
    }
}

impl<T: MachineWord, const N: usize> num_traits::ops::saturating::SaturatingAdd
    for FixedUInt<T, N>
{
    /// Saturating addition operator. Returns a+b, saturating at the numeric bounds instead of overflowing.
    fn saturating_add(&self, other: &Self) -> Self {
        self.saturating_add_impl(other)
    }
}

impl<T: MachineWord, const N: usize> core::ops::AddAssign<Self> for FixedUInt<T, N> {
    fn add_assign(&mut self, other: Self) {
        if Self::add_impl(self, &other) {
            maybe_panic(PanicReason::Add);
        }
    }
}

impl<T: MachineWord, const N: usize> core::ops::AddAssign<&'_ Self> for FixedUInt<T, N> {
    fn add_assign(&mut self, other: &Self) {
        if Self::add_impl(self, other) {
            maybe_panic(PanicReason::Add);
        }
    }
}

impl<T: MachineWord, const N: usize> num_traits::ops::overflowing::OverflowingSub
    for FixedUInt<T, N>
{
    fn overflowing_sub(&self, other: &Self) -> (Self, bool) {
        let mut ret = *self;
        let overflow = Self::sub_impl(&mut ret, other);
        (ret, overflow)
    }
}

impl<T: MachineWord, const N: usize> core::ops::Sub for FixedUInt<T, N> {
    type Output = Self;
    fn sub(self, other: Self) -> <Self as core::ops::Sub<Self>>::Output {
        let (res, overflow) = self.overflowing_sub(&other);
        if overflow {
            maybe_panic(PanicReason::Sub);
        }
        res
    }
}

impl<T: MachineWord, const N: usize> core::ops::Sub<&'_ Self> for FixedUInt<T, N> {
    type Output = Self;
    fn sub(self, other: &Self) -> Self {
        let (res, overflow) = self.overflowing_sub(other);
        if overflow {
            maybe_panic(PanicReason::Sub);
        }
        res
    }
}

impl<T: MachineWord, const N: usize> num_traits::WrappingSub for FixedUInt<T, N> {
    fn wrapping_sub(&self, other: &Self) -> Self {
        self.overflowing_sub(other).0
    }
}

impl<T: MachineWord, const N: usize> num_traits::CheckedSub for FixedUInt<T, N> {
    fn checked_sub(&self, other: &Self) -> Option<Self> {
        let res = self.overflowing_sub(other);
        if res.1 {
            None
        } else {
            Some(res.0)
        }
    }
}

impl<T: MachineWord, const N: usize> num_traits::ops::saturating::SaturatingSub
    for FixedUInt<T, N>
{
    /// Saturating subtraction operator. Returns a-b, saturating at the numeric bounds instead of overflowing.
    fn saturating_sub(&self, other: &Self) -> Self {
        self.saturating_sub_impl(other)
    }
}

impl<T: MachineWord, const N: usize> core::ops::SubAssign<Self> for FixedUInt<T, N> {
    fn sub_assign(&mut self, other: Self) {
        if Self::sub_impl(self, &other) {
            maybe_panic(PanicReason::Sub);
        }
    }
}

impl<T: MachineWord, const N: usize> core::ops::SubAssign<&'_ Self> for FixedUInt<T, N> {
    fn sub_assign(&mut self, other: &Self) {
        if Self::sub_impl(self, other) {
            maybe_panic(PanicReason::Sub);
        }
    }
}

/// Note: This is marked deprecated, but still used by PrimInt
impl<T: MachineWord, const N: usize> num_traits::Saturating for FixedUInt<T, N> {
    /// Saturating addition operator. Returns a+b, saturating at the numeric bounds instead of overflowing.
    fn saturating_add(self, other: Self) -> Self {
        self.saturating_add_impl(&other)
    }

    /// Saturating subtraction operator. Returns a-b, saturating at the numeric bounds instead of overflowing.
    fn saturating_sub(self, other: Self) -> Self {
        self.saturating_sub_impl(&other)
    }
}
