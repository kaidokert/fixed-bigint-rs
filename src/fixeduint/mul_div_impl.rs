use super::{
    const_ct_select, const_div_rem, const_mul, maybe_panic_if, FixedUInt, MachineWord, PanicReason,
};
use crate::const_numtraits::{
    ConstBounded, ConstCheckedDiv, ConstCheckedMul, ConstCheckedRem, ConstOverflowingMul,
    ConstSaturatingMul, ConstWrappingMul, ConstZero,
};
use crate::machineword::ConstMachineWord;
use crate::personality::{Nct, Personality, PersonalityTag};

impl<T: MachineWord, const N: usize, P: Personality> num_traits::ops::overflowing::OverflowingMul
    for FixedUInt<T, N, P>
{
    fn overflowing_mul(&self, other: &Self) -> (Self, bool) {
        <Self as ConstOverflowingMul>::overflowing_mul(self, other)
    }
}

c0nst::c0nst! {
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst ConstOverflowingMul for FixedUInt<T, N, P> {
        fn overflowing_mul(&self, other: &Self) -> (Self, bool) {
            let (array, overflow) = const_mul::<T, N, true>(&self.array, &other.array, Self::WORD_BITS);
            (Self::from_array(array), overflow)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst ConstWrappingMul for FixedUInt<T, N, P> {
        fn wrapping_mul(&self, other: &Self) -> Self {
            let (array, _) = const_mul::<T, N, false>(&self.array, &other.array, Self::WORD_BITS);
            Self::from_array(array)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst ConstCheckedMul for FixedUInt<T, N, P> {
        fn checked_mul(&self, other: &Self) -> Option<Self> {
            let (res, overflow) = <Self as ConstOverflowingMul>::overflowing_mul(self, other);
            if overflow { None } else { Some(res) }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst ConstSaturatingMul for FixedUInt<T, N, P> {
        fn saturating_mul(&self, other: &Self) -> Self {
            let (res, overflow) = <Self as ConstOverflowingMul>::overflowing_mul(self, other);
            match P::TAG {
                PersonalityTag::Nct => if overflow { <Self as ConstBounded>::max_value() } else { res },
                PersonalityTag::Ct => const_ct_select(res, <Self as ConstBounded>::max_value(), overflow as u8),
            }
        }
    }
}

c0nst::c0nst! {
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::Mul for FixedUInt<T, N, P> {
        type Output = Self;
        fn mul(self, other: Self) -> Self::Output {
            let (array, overflow) = const_mul::<T, N, true>(&self.array, &other.array, Self::WORD_BITS);
            maybe_panic_if::<P>(overflow, PanicReason::Mul);
            Self::from_array(array)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::Mul<&FixedUInt<T, N, P>> for FixedUInt<T, N, P> {
        type Output = Self;
        fn mul(self, other: &FixedUInt<T, N, P>) -> Self::Output {
            let (array, overflow) = const_mul::<T, N, true>(&self.array, &other.array, Self::WORD_BITS);
            maybe_panic_if::<P>(overflow, PanicReason::Mul);
            Self::from_array(array)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::Mul<FixedUInt<T, N, P>> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn mul(self, other: FixedUInt<T, N, P>) -> Self::Output {
            let (array, overflow) = const_mul::<T, N, true>(&self.array, &other.array, Self::Output::WORD_BITS);
            maybe_panic_if::<P>(overflow, PanicReason::Mul);
            FixedUInt::from_array(array)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::Mul<&FixedUInt<T, N, P>> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn mul(self, other: &FixedUInt<T, N, P>) -> Self::Output {
            let (array, overflow) = const_mul::<T, N, true>(&self.array, &other.array, Self::Output::WORD_BITS);
            maybe_panic_if::<P>(overflow, PanicReason::Mul);
            FixedUInt::from_array(array)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::Mul<&&FixedUInt<T, N, P>> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn mul(self, other: &&FixedUInt<T, N, P>) -> Self::Output {
            let (array, overflow) = const_mul::<T, N, true>(&self.array, &other.array, Self::Output::WORD_BITS);
            maybe_panic_if::<P>(overflow, PanicReason::Mul);
            FixedUInt::from_array(array)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::MulAssign for FixedUInt<T, N, P> {
        fn mul_assign(&mut self, other: Self) {
            let (array, overflow) = const_mul::<T, N, true>(&self.array, &other.array, Self::WORD_BITS);
            maybe_panic_if::<P>(overflow, PanicReason::Mul);
            *self = Self::from_array(array);
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::MulAssign<&FixedUInt<T, N, P>> for FixedUInt<T, N, P> {
        fn mul_assign(&mut self, other: &FixedUInt<T, N, P>) {
            let (array, overflow) = const_mul::<T, N, true>(&self.array, &other.array, Self::WORD_BITS);
            maybe_panic_if::<P>(overflow, PanicReason::Mul);
            *self = Self::from_array(array);
        }
    }
}

// num_traits wrappers - delegate to const versions
impl<T: MachineWord, const N: usize, P: Personality> num_traits::WrappingMul
    for FixedUInt<T, N, P>
{
    fn wrapping_mul(&self, other: &Self) -> Self {
        <Self as ConstWrappingMul>::wrapping_mul(self, other)
    }
}

impl<T: MachineWord, const N: usize, P: Personality> num_traits::CheckedMul for FixedUInt<T, N, P> {
    fn checked_mul(&self, other: &Self) -> Option<Self> {
        <Self as ConstCheckedMul>::checked_mul(self, other)
    }
}

impl<T: MachineWord, const N: usize, P: Personality> num_traits::ops::saturating::SaturatingMul
    for FixedUInt<T, N, P>
{
    fn saturating_mul(&self, other: &Self) -> Self {
        <Self as ConstSaturatingMul>::saturating_mul(self, other)
    }
}

c0nst::c0nst! {
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Div for FixedUInt<T, N, Nct> {
        type Output = Self;
        fn div(self, other: Self) -> Self::Output {
            Self::from_array(const_div_rem(&self.array, &other.array).0)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Div<&FixedUInt<T, N, Nct>> for FixedUInt<T, N, Nct> {
        type Output = Self;
        fn div(self, other: &FixedUInt<T, N, Nct>) -> Self::Output {
            Self::from_array(const_div_rem(&self.array, &other.array).0)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Div<FixedUInt<T, N, Nct>> for &FixedUInt<T, N, Nct> {
        type Output = FixedUInt<T, N, Nct>;
        fn div(self, other: FixedUInt<T, N, Nct>) -> Self::Output {
            Self::Output::from_array(const_div_rem(&self.array, &other.array).0)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Div<&FixedUInt<T, N, Nct>> for &FixedUInt<T, N, Nct> {
        type Output = FixedUInt<T, N, Nct>;
        fn div(self, other: &FixedUInt<T, N, Nct>) -> Self::Output {
            Self::Output::from_array(const_div_rem(&self.array, &other.array).0)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::DivAssign for FixedUInt<T, N, Nct> {
        fn div_assign(&mut self, other: Self) {
            self.array = const_div_rem(&self.array, &other.array).0;
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::DivAssign<&FixedUInt<T, N, Nct>> for FixedUInt<T, N, Nct> {
        fn div_assign(&mut self, other: &FixedUInt<T, N, Nct>) {
            self.array = const_div_rem(&self.array, &other.array).0;
        }
    }
}

c0nst::c0nst! {
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstCheckedDiv for FixedUInt<T, N, Nct> {
        fn checked_div(&self, other: &Self) -> Option<Self> {
            if <Self as ConstZero>::is_zero(other) {
                None
            } else {
                Some(*self / *other)
            }
        }
    }
}

impl<T: MachineWord, const N: usize> num_traits::CheckedDiv for FixedUInt<T, N, Nct> {
    fn checked_div(&self, other: &Self) -> Option<Self> {
        <Self as ConstCheckedDiv>::checked_div(self, other)
    }
}

c0nst::c0nst! {
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Rem for FixedUInt<T, N, Nct> {
        type Output = Self;
        fn rem(self, other: Self) -> Self::Output {
            Self::from_array(const_div_rem(&self.array, &other.array).1)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Rem<&FixedUInt<T, N, Nct>> for FixedUInt<T, N, Nct> {
        type Output = Self;
        fn rem(self, other: &FixedUInt<T, N, Nct>) -> Self::Output {
            Self::from_array(const_div_rem(&self.array, &other.array).1)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Rem<FixedUInt<T, N, Nct>> for &FixedUInt<T, N, Nct> {
        type Output = FixedUInt<T, N, Nct>;
        fn rem(self, other: FixedUInt<T, N, Nct>) -> Self::Output {
            Self::Output::from_array(const_div_rem(&self.array, &other.array).1)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::Rem<&FixedUInt<T, N, Nct>> for &FixedUInt<T, N, Nct> {
        type Output = FixedUInt<T, N, Nct>;
        fn rem(self, other: &FixedUInt<T, N, Nct>) -> Self::Output {
            Self::Output::from_array(const_div_rem(&self.array, &other.array).1)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::RemAssign for FixedUInt<T, N, Nct> {
        fn rem_assign(&mut self, other: Self) {
            self.array = const_div_rem(&self.array, &other.array).1;
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::ops::RemAssign<&FixedUInt<T, N, Nct>> for FixedUInt<T, N, Nct> {
        fn rem_assign(&mut self, other: &FixedUInt<T, N, Nct>) {
            self.array = const_div_rem(&self.array, &other.array).1;
        }
    }
}

c0nst::c0nst! {
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstCheckedRem for FixedUInt<T, N, Nct> {
        fn checked_rem(&self, other: &Self) -> Option<Self> {
            if <Self as ConstZero>::is_zero(other) {
                None
            } else {
                Some(*self % *other)
            }
        }
    }
}

impl<T: MachineWord, const N: usize> num_traits::CheckedRem for FixedUInt<T, N, Nct> {
    fn checked_rem(&self, other: &Self) -> Option<Self> {
        <Self as ConstCheckedRem>::checked_rem(self, other)
    }
}

// Test wrappers for const mul traits
#[cfg(test)]
c0nst::c0nst! {
    pub c0nst fn const_wrapping_mul<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(
        a: &FixedUInt<T, N, P>,
        b: &FixedUInt<T, N, P>
    ) -> FixedUInt<T, N, P> {
        <FixedUInt<T, N, P> as ConstWrappingMul>::wrapping_mul(a, b)
    }

    pub c0nst fn const_checked_mul<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(
        a: &FixedUInt<T, N, P>,
        b: &FixedUInt<T, N, P>
    ) -> Option<FixedUInt<T, N, P>> {
        <FixedUInt<T, N, P> as ConstCheckedMul>::checked_mul(a, b)
    }

    pub c0nst fn const_saturating_mul<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(
        a: &FixedUInt<T, N, P>,
        b: &FixedUInt<T, N, P>
    ) -> FixedUInt<T, N, P> {
        <FixedUInt<T, N, P> as ConstSaturatingMul>::saturating_mul(a, b)
    }

    pub c0nst fn const_overflowing_mul<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(
        a: &FixedUInt<T, N, P>,
        b: &FixedUInt<T, N, P>
    ) -> (FixedUInt<T, N, P>, bool) {
        <FixedUInt<T, N, P> as ConstOverflowingMul>::overflowing_mul(a, b)
    }

    pub c0nst fn const_checked_div<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
        a: &FixedUInt<T, N, Nct>,
        b: &FixedUInt<T, N, Nct>
    ) -> Option<FixedUInt<T, N, Nct>> {
        <FixedUInt<T, N, Nct> as ConstCheckedDiv>::checked_div(a, b)
    }

    pub c0nst fn const_checked_rem<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
        a: &FixedUInt<T, N, Nct>,
        b: &FixedUInt<T, N, Nct>
    ) -> Option<FixedUInt<T, N, Nct>> {
        <FixedUInt<T, N, Nct> as ConstCheckedRem>::checked_rem(a, b)
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
            const A: FixedUInt<u8, 2> = FixedUInt::from_array([12, 0]);
            const B: FixedUInt<u8, 2> = FixedUInt::from_array([3, 0]);

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

    #[test]
    fn test_const_checked_div_rem() {
        let a = FixedUInt::<u8, 2>::from(36u8);
        let b = FixedUInt::<u8, 2>::from(5u8);
        let zero = FixedUInt::<u8, 2>::from(0u8);

        // ConstCheckedDiv - valid division
        assert_eq!(
            const_checked_div(&a, &b),
            Some(FixedUInt::<u8, 2>::from(7u8))
        ); // 36 / 5 = 7

        // ConstCheckedDiv - divide by zero
        assert_eq!(const_checked_div(&a, &zero), None);

        // ConstCheckedRem - valid remainder
        assert_eq!(
            const_checked_rem(&a, &b),
            Some(FixedUInt::<u8, 2>::from(1u8))
        ); // 36 % 5 = 1

        // ConstCheckedRem - remainder by zero
        assert_eq!(const_checked_rem(&a, &zero), None);

        #[cfg(feature = "nightly")]
        {
            const A: FixedUInt<u8, 2> = FixedUInt::from_array([36, 0]);
            const B: FixedUInt<u8, 2> = FixedUInt::from_array([5, 0]);
            const ZERO: FixedUInt<u8, 2> = FixedUInt::from_array([0, 0]);

            const CHECKED_DIV_OK: Option<FixedUInt<u8, 2>> = const_checked_div(&A, &B);
            const CHECKED_DIV_ZERO: Option<FixedUInt<u8, 2>> = const_checked_div(&A, &ZERO);
            const CHECKED_REM_OK: Option<FixedUInt<u8, 2>> = const_checked_rem(&A, &B);
            const CHECKED_REM_ZERO: Option<FixedUInt<u8, 2>> = const_checked_rem(&A, &ZERO);

            assert_eq!(CHECKED_DIV_OK, Some(FixedUInt::from_array([7, 0])));
            assert_eq!(CHECKED_DIV_ZERO, None);
            assert_eq!(CHECKED_REM_OK, Some(FixedUInt::from_array([1, 0])));
            assert_eq!(CHECKED_REM_ZERO, None);
        }
    }
}
