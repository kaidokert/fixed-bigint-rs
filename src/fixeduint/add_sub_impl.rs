use super::{add_impl, maybe_panic, sub_impl, FixedUInt, MachineWord, PanicReason};
use crate::machineword::ConstMachineWord;

use num_traits::ops::overflowing::{OverflowingAdd, OverflowingSub};

c0nst::c0nst! {
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst crate::const_numtrait::ConstOverflowingAdd for FixedUInt<T, N> {
        fn overflowing_add(&self, other: &Self) -> (Self, bool) {
            let mut ret = *self;
            let overflow = add_impl(&mut ret.array, &other.array);
            (ret, overflow)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst crate::const_numtrait::ConstOverflowingSub for FixedUInt<T, N> {
        fn overflowing_sub(&self, other: &Self) -> (Self, bool) {
            let mut ret = *self;
            let overflow = sub_impl(&mut ret.array, &other.array);
            (ret, overflow)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Add for FixedUInt<T, N> {
        type Output = Self;
        fn add(self, other: Self) -> Self {
            let (res, overflow) = <Self as crate::const_numtrait::ConstOverflowingAdd>::overflowing_add(&self, &other);
            if overflow {
                maybe_panic(PanicReason::Add);
            }
            res
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Sub for FixedUInt<T, N> {
        type Output = Self;
        fn sub(self, other: Self) -> Self {
            let (res, overflow) = <Self as crate::const_numtrait::ConstOverflowingSub>::overflowing_sub(&self, &other);
            if overflow {
                maybe_panic(PanicReason::Sub);
            }
            res
        }
    }
}

impl<T: MachineWord, const N: usize> num_traits::ops::overflowing::OverflowingAdd
    for FixedUInt<T, N>
{
    fn overflowing_add(&self, other: &Self) -> (Self, bool) {
        <Self as crate::const_numtrait::ConstOverflowingAdd>::overflowing_add(self, other)
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

impl<T: MachineWord, const N: usize> core::ops::Add<FixedUInt<T, N>> for &FixedUInt<T, N> {
    type Output = FixedUInt<T, N>;
    fn add(self, other: FixedUInt<T, N>) -> Self::Output {
        let (res, overflow) = self.overflowing_add(&other);
        if overflow {
            maybe_panic(PanicReason::Add);
        }
        res
    }
}

impl<T: MachineWord, const N: usize> core::ops::Add<Self> for &FixedUInt<T, N> {
    type Output = FixedUInt<T, N>;
    fn add(self, other: Self) -> Self::Output {
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
        if add_impl(&mut self.array, &other.array) {
            maybe_panic(PanicReason::Add);
        }
    }
}

impl<T: MachineWord, const N: usize> core::ops::AddAssign<&'_ Self> for FixedUInt<T, N> {
    fn add_assign(&mut self, other: &Self) {
        if add_impl(&mut self.array, &other.array) {
            maybe_panic(PanicReason::Add);
        }
    }
}

impl<T: MachineWord, const N: usize> num_traits::ops::overflowing::OverflowingSub
    for FixedUInt<T, N>
{
    fn overflowing_sub(&self, other: &Self) -> (Self, bool) {
        <Self as crate::const_numtrait::ConstOverflowingSub>::overflowing_sub(self, other)
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

impl<T: MachineWord, const N: usize> core::ops::Sub<FixedUInt<T, N>> for &FixedUInt<T, N> {
    type Output = FixedUInt<T, N>;
    fn sub(self, other: FixedUInt<T, N>) -> Self::Output {
        let (res, overflow) = self.overflowing_sub(&other);
        if overflow {
            maybe_panic(PanicReason::Sub);
        }
        res
    }
}

impl<T: MachineWord, const N: usize> core::ops::Sub<Self> for &FixedUInt<T, N> {
    type Output = FixedUInt<T, N>;
    fn sub(self, other: Self) -> Self::Output {
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
        if sub_impl(&mut self.array, &other.array) {
            maybe_panic(PanicReason::Sub);
        }
    }
}

impl<T: MachineWord, const N: usize> core::ops::SubAssign<&'_ Self> for FixedUInt<T, N> {
    fn sub_assign(&mut self, other: &Self) {
        if sub_impl(&mut self.array, &other.array) {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::const_numtrait::{ConstOverflowingAdd, ConstOverflowingSub};
    use crate::machineword::ConstMachineWord;
    use num_traits::Bounded;

    c0nst::c0nst! {
        /// Test wrapper for ConstOverflowingAdd
        pub c0nst fn const_overflowing_add<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            a: &FixedUInt<T, N>,
            b: &FixedUInt<T, N>
        ) -> (FixedUInt<T, N>, bool) {
            <FixedUInt<T, N> as ConstOverflowingAdd>::overflowing_add(a, b)
        }

        /// Test wrapper for ConstOverflowingSub
        pub c0nst fn const_overflowing_sub<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            a: &FixedUInt<T, N>,
            b: &FixedUInt<T, N>
        ) -> (FixedUInt<T, N>, bool) {
            <FixedUInt<T, N> as ConstOverflowingSub>::overflowing_sub(a, b)
        }

        /// Test wrapper for const Add
        pub c0nst fn const_add<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            a: FixedUInt<T, N>,
            b: FixedUInt<T, N>
        ) -> FixedUInt<T, N> {
            a + b
        }

        /// Test wrapper for const Sub
        pub c0nst fn const_sub<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            a: FixedUInt<T, N>,
            b: FixedUInt<T, N>
        ) -> FixedUInt<T, N> {
            a - b
        }
    }

    #[test]
    fn test_add_combinations() {
        let a = FixedUInt::<u8, 2>::from(12u8);
        let b = FixedUInt::<u8, 2>::from(3u8);
        let expected = FixedUInt::<u8, 2>::from(15u8);

        // value + value
        assert_eq!(a + b, expected);
        // value + ref
        assert_eq!(a + &b, expected);
        // ref + value
        assert_eq!(&a + b, expected);
        // ref + ref
        assert_eq!(&a + &b, expected);
    }

    #[test]
    fn test_sub_combinations() {
        let a = FixedUInt::<u8, 2>::from(15u8);
        let b = FixedUInt::<u8, 2>::from(3u8);
        let expected = FixedUInt::<u8, 2>::from(12u8);

        // value - value
        assert_eq!(a - b, expected);
        // value - ref
        assert_eq!(a - &b, expected);
        // ref - value
        assert_eq!(&a - b, expected);
        // ref - ref
        assert_eq!(&a - &b, expected);
    }

    #[test]
    fn test_const_overflowing_add() {
        // No overflow
        let a = FixedUInt::<u8, 2>::from(12u8);
        let b = FixedUInt::<u8, 2>::from(3u8);
        let (result, overflow) = const_overflowing_add(&a, &b);
        assert_eq!(result, FixedUInt::<u8, 2>::from(15u8));
        assert!(!overflow);

        // With overflow
        let a = FixedUInt::<u8, 2>::from(255u8);
        let b = FixedUInt::<u8, 2>::from(255u8);
        let a = a + FixedUInt::<u8, 2>::from(1u8); // 256
        let (result, overflow) = const_overflowing_add(&a, &b);
        assert!(overflow || result > FixedUInt::<u8, 2>::from(0u8)); // Either overflows or wraps

        // Max value overflow
        let max = FixedUInt::<u8, 2>::max_value();
        let one = FixedUInt::<u8, 2>::from(1u8);
        let (_, overflow) = const_overflowing_add(&max, &one);
        assert!(overflow);

        #[cfg(feature = "nightly")]
        {
            const A: FixedUInt<u8, 2> = FixedUInt { array: [12, 0] };
            const B: FixedUInt<u8, 2> = FixedUInt { array: [3, 0] };
            const RESULT: (FixedUInt<u8, 2>, bool) = const_overflowing_add(&A, &B);
            assert_eq!(RESULT.0.array, [15, 0]);
            assert!(!RESULT.1);
        }
    }

    #[test]
    fn test_const_overflowing_sub() {
        // No overflow
        let a = FixedUInt::<u8, 2>::from(15u8);
        let b = FixedUInt::<u8, 2>::from(3u8);
        let (result, overflow) = const_overflowing_sub(&a, &b);
        assert_eq!(result, FixedUInt::<u8, 2>::from(12u8));
        assert!(!overflow);

        // With underflow
        let a = FixedUInt::<u8, 2>::from(0u8);
        let b = FixedUInt::<u8, 2>::from(1u8);
        let (_, overflow) = const_overflowing_sub(&a, &b);
        assert!(overflow);

        #[cfg(feature = "nightly")]
        {
            const A: FixedUInt<u8, 2> = FixedUInt { array: [15, 0] };
            const B: FixedUInt<u8, 2> = FixedUInt { array: [3, 0] };
            const RESULT: (FixedUInt<u8, 2>, bool) = const_overflowing_sub(&A, &B);
            assert_eq!(RESULT.0.array, [12, 0]);
            assert!(!RESULT.1);
        }
    }

    #[test]
    fn test_const_add_op() {
        let a = FixedUInt::<u8, 2>::from(12u8);
        let b = FixedUInt::<u8, 2>::from(3u8);
        let result = const_add(a, b);
        assert_eq!(result, FixedUInt::<u8, 2>::from(15u8));

        // Test with u32 word type
        let a = FixedUInt::<u32, 2>::from(100u32);
        let b = FixedUInt::<u32, 2>::from(200u32);
        let result = const_add(a, b);
        assert_eq!(result, FixedUInt::<u32, 2>::from(300u32));

        #[cfg(feature = "nightly")]
        {
            const A: FixedUInt<u8, 2> = FixedUInt { array: [12, 0] };
            const B: FixedUInt<u8, 2> = FixedUInt { array: [3, 0] };
            const RESULT: FixedUInt<u8, 2> = const_add(A, B);
            assert_eq!(RESULT.array, [15, 0]);
        }
    }

    #[test]
    fn test_const_sub_op() {
        let a = FixedUInt::<u8, 2>::from(15u8);
        let b = FixedUInt::<u8, 2>::from(3u8);
        let result = const_sub(a, b);
        assert_eq!(result, FixedUInt::<u8, 2>::from(12u8));

        // Test with u32 word type
        let a = FixedUInt::<u32, 2>::from(300u32);
        let b = FixedUInt::<u32, 2>::from(100u32);
        let result = const_sub(a, b);
        assert_eq!(result, FixedUInt::<u32, 2>::from(200u32));

        #[cfg(feature = "nightly")]
        {
            const A: FixedUInt<u8, 2> = FixedUInt { array: [15, 0] };
            const B: FixedUInt<u8, 2> = FixedUInt { array: [3, 0] };
            const RESULT: FixedUInt<u8, 2> = const_sub(A, B);
            assert_eq!(RESULT.array, [12, 0]);
        }
    }
}
