use super::{add_impl, maybe_panic, sub_impl, FixedUInt, MachineWord, PanicReason};
use crate::const_numtrait::{
    ConstCheckedAdd, ConstCheckedSub, ConstOverflowingAdd, ConstOverflowingSub, ConstWrappingAdd,
    ConstWrappingSub,
};
use crate::machineword::ConstMachineWord;

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

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstWrappingAdd for FixedUInt<T, N> {
        fn wrapping_add(&self, other: &Self) -> Self {
            <Self as ConstOverflowingAdd>::overflowing_add(self, other).0
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstWrappingSub for FixedUInt<T, N> {
        fn wrapping_sub(&self, other: &Self) -> Self {
            <Self as ConstOverflowingSub>::overflowing_sub(self, other).0
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstCheckedAdd for FixedUInt<T, N> {
        fn checked_add(&self, other: &Self) -> Option<Self> {
            let (res, overflow) = <Self as ConstOverflowingAdd>::overflowing_add(self, other);
            if overflow { None } else { Some(res) }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstCheckedSub for FixedUInt<T, N> {
        fn checked_sub(&self, other: &Self) -> Option<Self> {
            let (res, overflow) = <Self as ConstOverflowingSub>::overflowing_sub(self, other);
            if overflow { None } else { Some(res) }
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

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Add<&'_ Self> for FixedUInt<T, N> {
        type Output = Self;
        fn add(self, other: &Self) -> Self {
            let (res, overflow) = <Self as crate::const_numtrait::ConstOverflowingAdd>::overflowing_add(&self, other);
            if overflow {
                maybe_panic(PanicReason::Add);
            }
            res
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Add<FixedUInt<T, N>> for &FixedUInt<T, N> {
        type Output = FixedUInt<T, N>;
        fn add(self, other: FixedUInt<T, N>) -> Self::Output {
            let (res, overflow) = <FixedUInt<T, N> as crate::const_numtrait::ConstOverflowingAdd>::overflowing_add(self, &other);
            if overflow {
                maybe_panic(PanicReason::Add);
            }
            res
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Add<Self> for &FixedUInt<T, N> {
        type Output = FixedUInt<T, N>;
        fn add(self, other: Self) -> Self::Output {
            let (res, overflow) = <FixedUInt<T, N> as crate::const_numtrait::ConstOverflowingAdd>::overflowing_add(self, other);
            if overflow {
                maybe_panic(PanicReason::Add);
            }
            res
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Sub<&'_ Self> for FixedUInt<T, N> {
        type Output = Self;
        fn sub(self, other: &Self) -> Self {
            let (res, overflow) = <Self as crate::const_numtrait::ConstOverflowingSub>::overflowing_sub(&self, other);
            if overflow {
                maybe_panic(PanicReason::Sub);
            }
            res
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Sub<FixedUInt<T, N>> for &FixedUInt<T, N> {
        type Output = FixedUInt<T, N>;
        fn sub(self, other: FixedUInt<T, N>) -> Self::Output {
            let (res, overflow) = <FixedUInt<T, N> as crate::const_numtrait::ConstOverflowingSub>::overflowing_sub(self, &other);
            if overflow {
                maybe_panic(PanicReason::Sub);
            }
            res
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Sub<Self> for &FixedUInt<T, N> {
        type Output = FixedUInt<T, N>;
        fn sub(self, other: Self) -> Self::Output {
            let (res, overflow) = <FixedUInt<T, N> as crate::const_numtrait::ConstOverflowingSub>::overflowing_sub(self, other);
            if overflow {
                maybe_panic(PanicReason::Sub);
            }
            res
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::AddAssign<Self> for FixedUInt<T, N> {
        fn add_assign(&mut self, other: Self) {
            if add_impl(&mut self.array, &other.array) {
                maybe_panic(PanicReason::Add);
            }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::AddAssign<&'_ Self> for FixedUInt<T, N> {
        fn add_assign(&mut self, other: &Self) {
            if add_impl(&mut self.array, &other.array) {
                maybe_panic(PanicReason::Add);
            }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::SubAssign<Self> for FixedUInt<T, N> {
        fn sub_assign(&mut self, other: Self) {
            if sub_impl(&mut self.array, &other.array) {
                maybe_panic(PanicReason::Sub);
            }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::SubAssign<&'_ Self> for FixedUInt<T, N> {
        fn sub_assign(&mut self, other: &Self) {
            if sub_impl(&mut self.array, &other.array) {
                maybe_panic(PanicReason::Sub);
            }
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

impl<T: MachineWord, const N: usize> num_traits::WrappingAdd for FixedUInt<T, N> {
    fn wrapping_add(&self, other: &Self) -> Self {
        <Self as ConstWrappingAdd>::wrapping_add(self, other)
    }
}

impl<T: MachineWord, const N: usize> num_traits::CheckedAdd for FixedUInt<T, N> {
    fn checked_add(&self, other: &Self) -> Option<Self> {
        <Self as ConstCheckedAdd>::checked_add(self, other)
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

impl<T: MachineWord, const N: usize> num_traits::ops::overflowing::OverflowingSub
    for FixedUInt<T, N>
{
    fn overflowing_sub(&self, other: &Self) -> (Self, bool) {
        <Self as crate::const_numtrait::ConstOverflowingSub>::overflowing_sub(self, other)
    }
}

impl<T: MachineWord, const N: usize> num_traits::WrappingSub for FixedUInt<T, N> {
    fn wrapping_sub(&self, other: &Self) -> Self {
        <Self as ConstWrappingSub>::wrapping_sub(self, other)
    }
}

impl<T: MachineWord, const N: usize> num_traits::CheckedSub for FixedUInt<T, N> {
    fn checked_sub(&self, other: &Self) -> Option<Self> {
        <Self as ConstCheckedSub>::checked_sub(self, other)
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
    use crate::const_numtrait::{
        ConstCheckedAdd, ConstCheckedSub, ConstOverflowingAdd, ConstOverflowingSub,
        ConstWrappingAdd, ConstWrappingSub,
    };
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

        /// Test wrapper for ConstWrappingAdd
        pub c0nst fn const_wrapping_add<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            a: &FixedUInt<T, N>,
            b: &FixedUInt<T, N>
        ) -> FixedUInt<T, N> {
            <FixedUInt<T, N> as ConstWrappingAdd>::wrapping_add(a, b)
        }

        /// Test wrapper for ConstWrappingSub
        pub c0nst fn const_wrapping_sub<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            a: &FixedUInt<T, N>,
            b: &FixedUInt<T, N>
        ) -> FixedUInt<T, N> {
            <FixedUInt<T, N> as ConstWrappingSub>::wrapping_sub(a, b)
        }

        /// Test wrapper for ConstCheckedAdd
        pub c0nst fn const_checked_add<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            a: &FixedUInt<T, N>,
            b: &FixedUInt<T, N>
        ) -> Option<FixedUInt<T, N>> {
            <FixedUInt<T, N> as ConstCheckedAdd>::checked_add(a, b)
        }

        /// Test wrapper for ConstCheckedSub
        pub c0nst fn const_checked_sub<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            a: &FixedUInt<T, N>,
            b: &FixedUInt<T, N>
        ) -> Option<FixedUInt<T, N>> {
            <FixedUInt<T, N> as ConstCheckedSub>::checked_sub(a, b)
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

        // With overflow: max + max wraps to max-1 with overflow
        let a = FixedUInt::<u8, 2>::max_value();
        let b = FixedUInt::<u8, 2>::max_value();
        let (result, overflow) = const_overflowing_add(&a, &b);
        // 0xFFFF + 0xFFFF = 0x1FFFE, which wraps to 0xFFFE with overflow
        assert_eq!(result, FixedUInt::<u8, 2>::from(u16::MAX - 1));
        assert!(overflow);

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

    #[test]
    fn test_const_wrapping_checked() {
        // Test wrapping_add without overflow
        let a = FixedUInt::<u8, 2>::from(100u8);
        let b = FixedUInt::<u8, 2>::from(50u8);
        let result = const_wrapping_add(&a, &b);
        assert_eq!(result, FixedUInt::<u8, 2>::from(150u8));

        // Test wrapping_add with overflow
        let max = FixedUInt::<u8, 2>::max_value();
        let one = FixedUInt::<u8, 2>::from(1u8);
        let result = const_wrapping_add(&max, &one);
        assert_eq!(result, FixedUInt::<u8, 2>::from(0u8));

        // Test wrapping_sub without overflow
        let a = FixedUInt::<u8, 2>::from(100u8);
        let b = FixedUInt::<u8, 2>::from(50u8);
        let result = const_wrapping_sub(&a, &b);
        assert_eq!(result, FixedUInt::<u8, 2>::from(50u8));

        // Test wrapping_sub with underflow
        let zero = FixedUInt::<u8, 2>::from(0u8);
        let one = FixedUInt::<u8, 2>::from(1u8);
        let result = const_wrapping_sub(&zero, &one);
        assert_eq!(result, FixedUInt::<u8, 2>::max_value());

        // Test checked_add without overflow
        let a = FixedUInt::<u8, 2>::from(100u8);
        let b = FixedUInt::<u8, 2>::from(50u8);
        let result = const_checked_add(&a, &b);
        assert_eq!(result, Some(FixedUInt::<u8, 2>::from(150u8)));

        // Test checked_add with overflow
        let max = FixedUInt::<u8, 2>::max_value();
        let one = FixedUInt::<u8, 2>::from(1u8);
        let result = const_checked_add(&max, &one);
        assert_eq!(result, None);

        // Test checked_sub without overflow
        let a = FixedUInt::<u8, 2>::from(100u8);
        let b = FixedUInt::<u8, 2>::from(50u8);
        let result = const_checked_sub(&a, &b);
        assert_eq!(result, Some(FixedUInt::<u8, 2>::from(50u8)));

        // Test checked_sub with underflow
        let zero = FixedUInt::<u8, 2>::from(0u8);
        let one = FixedUInt::<u8, 2>::from(1u8);
        let result = const_checked_sub(&zero, &one);
        assert_eq!(result, None);

        #[cfg(feature = "nightly")]
        {
            const A: FixedUInt<u8, 2> = FixedUInt { array: [100, 0] };
            const B: FixedUInt<u8, 2> = FixedUInt { array: [50, 0] };

            const WRAP_ADD: FixedUInt<u8, 2> = const_wrapping_add(&A, &B);
            const WRAP_SUB: FixedUInt<u8, 2> = const_wrapping_sub(&A, &B);
            const CHECK_ADD: Option<FixedUInt<u8, 2>> = const_checked_add(&A, &B);
            const CHECK_SUB: Option<FixedUInt<u8, 2>> = const_checked_sub(&A, &B);

            assert_eq!(WRAP_ADD.array, [150, 0]);
            assert_eq!(WRAP_SUB.array, [50, 0]);
            assert!(CHECK_ADD.is_some());
            assert!(CHECK_SUB.is_some());

            const MAX: FixedUInt<u8, 2> = FixedUInt { array: [255, 255] };
            const ONE: FixedUInt<u8, 2> = FixedUInt { array: [1, 0] };
            const CHECK_ADD_OVERFLOW: Option<FixedUInt<u8, 2>> = const_checked_add(&MAX, &ONE);
            assert!(CHECK_ADD_OVERFLOW.is_none());
        }
    }
}
