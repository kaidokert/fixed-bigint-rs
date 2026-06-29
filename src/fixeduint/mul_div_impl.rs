use super::{
    FixedUInt, MachineWord, PanicReason, const_ct_select, const_div_rem, const_mul, maybe_panic_if,
};
use crate::const_numtraits::{
    Bounded, CheckedDiv, CheckedMul, CheckedRem, ConstZero, One, OverflowingMul, SaturatingMul,
    WrappingMul, Zero,
};
use crate::machineword::ConstMachineWord;
use const_num_traits::{Nct, Personality, PersonalityTag};

#[cfg(feature = "num-traits")]
impl<T: MachineWord, const N: usize, P: Personality> num_traits::ops::overflowing::OverflowingMul
    for FixedUInt<T, N, P>
{
    fn overflowing_mul(&self, other: &Self) -> (Self, bool) {
        <Self as OverflowingMul>::overflowing_mul(*self, *other)
    }
}

c0nst::c0nst! {
    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> OverflowingMul for FixedUInt<T, N, P> {
        fn overflowing_mul(self, other: Self) -> (Self, bool) {
            let (array, overflow) = const_mul::<T, N, true, P>(&self.array, &other.array, Self::WORD_BITS);
            (Self::from_array(array), overflow)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> WrappingMul for FixedUInt<T, N, P> {
        fn wrapping_mul(self, other: Self) -> Self {
            let (array, _) = const_mul::<T, N, false, P>(&self.array, &other.array, Self::WORD_BITS);
            Self::from_array(array)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> CheckedMul for FixedUInt<T, N, P> {
        fn checked_mul(self, other: Self) -> Option<Self> {
            let (res, overflow) = <Self as OverflowingMul>::overflowing_mul(self, other);
            if overflow { None } else { Some(res) }
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> SaturatingMul for FixedUInt<T, N, P> {
        fn saturating_mul(self, other: Self) -> Self {
            let (res, overflow) = <Self as OverflowingMul>::overflowing_mul(self, other);
            match P::TAG {
                PersonalityTag::Nct => if overflow { <Self as Bounded>::max_value() } else { res },
                PersonalityTag::Ct => const_ct_select(res, <Self as Bounded>::max_value(), overflow as u8),
            }
        }
    }

    // --- Reference-receiver mul impls (see add_sub_impl.rs for rationale) ---

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> OverflowingMul for &FixedUInt<T, N, P> {
        fn overflowing_mul(self, other: Self) -> (FixedUInt<T, N, P>, bool) {
            <FixedUInt<T, N, P> as OverflowingMul>::overflowing_mul(*self, *other)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> WrappingMul for &FixedUInt<T, N, P> {
        fn wrapping_mul(self, other: Self) -> FixedUInt<T, N, P> {
            <FixedUInt<T, N, P> as WrappingMul>::wrapping_mul(*self, *other)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> CheckedMul for &FixedUInt<T, N, P> {
        fn checked_mul(self, other: Self) -> Option<FixedUInt<T, N, P>> {
            <FixedUInt<T, N, P> as CheckedMul>::checked_mul(*self, *other)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> SaturatingMul for &FixedUInt<T, N, P> {
        fn saturating_mul(self, other: Self) -> FixedUInt<T, N, P> {
            <FixedUInt<T, N, P> as SaturatingMul>::saturating_mul(*self, *other)
        }
    }
}

c0nst::c0nst! {
    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::Mul for FixedUInt<T, N, P> {
        type Output = Self;
        fn mul(self, other: Self) -> Self::Output {
            let (array, overflow) = const_mul::<T, N, true, P>(&self.array, &other.array, Self::WORD_BITS);
            maybe_panic_if::<P>(overflow, PanicReason::Mul);
            Self::from_array(array)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::Mul<&FixedUInt<T, N, P>> for FixedUInt<T, N, P> {
        type Output = Self;
        fn mul(self, other: &FixedUInt<T, N, P>) -> Self::Output {
            let (array, overflow) = const_mul::<T, N, true, P>(&self.array, &other.array, Self::WORD_BITS);
            maybe_panic_if::<P>(overflow, PanicReason::Mul);
            Self::from_array(array)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::Mul<FixedUInt<T, N, P>> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn mul(self, other: FixedUInt<T, N, P>) -> Self::Output {
            let (array, overflow) = const_mul::<T, N, true, P>(&self.array, &other.array, Self::Output::WORD_BITS);
            maybe_panic_if::<P>(overflow, PanicReason::Mul);
            FixedUInt::from_array(array)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::Mul<&FixedUInt<T, N, P>> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn mul(self, other: &FixedUInt<T, N, P>) -> Self::Output {
            let (array, overflow) = const_mul::<T, N, true, P>(&self.array, &other.array, Self::Output::WORD_BITS);
            maybe_panic_if::<P>(overflow, PanicReason::Mul);
            FixedUInt::from_array(array)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::Mul<&&FixedUInt<T, N, P>> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn mul(self, other: &&FixedUInt<T, N, P>) -> Self::Output {
            let (array, overflow) = const_mul::<T, N, true, P>(&self.array, &other.array, Self::Output::WORD_BITS);
            maybe_panic_if::<P>(overflow, PanicReason::Mul);
            FixedUInt::from_array(array)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::MulAssign for FixedUInt<T, N, P> {
        fn mul_assign(&mut self, other: Self) {
            let (array, overflow) = const_mul::<T, N, true, P>(&self.array, &other.array, Self::WORD_BITS);
            maybe_panic_if::<P>(overflow, PanicReason::Mul);
            *self = Self::from_array(array);
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::MulAssign<&FixedUInt<T, N, P>> for FixedUInt<T, N, P> {
        fn mul_assign(&mut self, other: &FixedUInt<T, N, P>) {
            let (array, overflow) = const_mul::<T, N, true, P>(&self.array, &other.array, Self::WORD_BITS);
            maybe_panic_if::<P>(overflow, PanicReason::Mul);
            *self = Self::from_array(array);
        }
    }
}

// num_traits wrappers - delegate to const versions
#[cfg(feature = "num-traits")]
impl<T: MachineWord, const N: usize, P: Personality> num_traits::WrappingMul
    for FixedUInt<T, N, P>
{
    fn wrapping_mul(&self, other: &Self) -> Self {
        <Self as WrappingMul>::wrapping_mul(*self, *other)
    }
}

#[cfg(feature = "num-traits")]
impl<T: MachineWord, const N: usize, P: Personality> num_traits::CheckedMul for FixedUInt<T, N, P> {
    fn checked_mul(&self, other: &Self) -> Option<Self> {
        <Self as CheckedMul>::checked_mul(*self, *other)
    }
}

#[cfg(feature = "num-traits")]
impl<T: MachineWord, const N: usize, P: Personality> num_traits::ops::saturating::SaturatingMul
    for FixedUInt<T, N, P>
{
    fn saturating_mul(&self, other: &Self) -> Self {
        <Self as SaturatingMul>::saturating_mul(*self, *other)
    }
}

c0nst::c0nst! {
    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> core::ops::Div for FixedUInt<T, N, Nct> {
        type Output = Self;
        fn div(self, other: Self) -> Self::Output {
            Self::from_array(const_div_rem(&self.array, &other.array).0)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> core::ops::Div<&FixedUInt<T, N, Nct>> for FixedUInt<T, N, Nct> {
        type Output = Self;
        fn div(self, other: &FixedUInt<T, N, Nct>) -> Self::Output {
            Self::from_array(const_div_rem(&self.array, &other.array).0)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> core::ops::Div<FixedUInt<T, N, Nct>> for &FixedUInt<T, N, Nct> {
        type Output = FixedUInt<T, N, Nct>;
        fn div(self, other: FixedUInt<T, N, Nct>) -> Self::Output {
            Self::Output::from_array(const_div_rem(&self.array, &other.array).0)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> core::ops::Div<&FixedUInt<T, N, Nct>> for &FixedUInt<T, N, Nct> {
        type Output = FixedUInt<T, N, Nct>;
        fn div(self, other: &FixedUInt<T, N, Nct>) -> Self::Output {
            Self::Output::from_array(const_div_rem(&self.array, &other.array).0)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> core::ops::DivAssign for FixedUInt<T, N, Nct> {
        fn div_assign(&mut self, other: Self) {
            self.array = const_div_rem(&self.array, &other.array).0;
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> core::ops::DivAssign<&FixedUInt<T, N, Nct>> for FixedUInt<T, N, Nct> {
        fn div_assign(&mut self, other: &FixedUInt<T, N, Nct>) {
            self.array = const_div_rem(&self.array, &other.array).0;
        }
    }
}

c0nst::c0nst! {
    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> CheckedDiv for FixedUInt<T, N, Nct> {
        fn checked_div(self, other: Self) -> Option<Self> {
            if <Self as Zero>::is_zero(&other) {
                None
            } else {
                Some(self / other)
            }
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> CheckedDiv for &FixedUInt<T, N, Nct> {
        fn checked_div(self, other: Self) -> Option<FixedUInt<T, N, Nct>> {
            <FixedUInt<T, N, Nct> as CheckedDiv>::checked_div(*self, *other)
        }
    }
}

#[cfg(feature = "num-traits")]
impl<T: MachineWord, const N: usize> num_traits::CheckedDiv for FixedUInt<T, N, Nct> {
    fn checked_div(&self, other: &Self) -> Option<Self> {
        <Self as CheckedDiv>::checked_div(*self, *other)
    }
}

c0nst::c0nst! {
    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> core::ops::Rem for FixedUInt<T, N, Nct> {
        type Output = Self;
        fn rem(self, other: Self) -> Self::Output {
            Self::from_array(const_div_rem(&self.array, &other.array).1)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> core::ops::Rem<&FixedUInt<T, N, Nct>> for FixedUInt<T, N, Nct> {
        type Output = Self;
        fn rem(self, other: &FixedUInt<T, N, Nct>) -> Self::Output {
            Self::from_array(const_div_rem(&self.array, &other.array).1)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> core::ops::Rem<FixedUInt<T, N, Nct>> for &FixedUInt<T, N, Nct> {
        type Output = FixedUInt<T, N, Nct>;
        fn rem(self, other: FixedUInt<T, N, Nct>) -> Self::Output {
            Self::Output::from_array(const_div_rem(&self.array, &other.array).1)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> core::ops::Rem<&FixedUInt<T, N, Nct>> for &FixedUInt<T, N, Nct> {
        type Output = FixedUInt<T, N, Nct>;
        fn rem(self, other: &FixedUInt<T, N, Nct>) -> Self::Output {
            Self::Output::from_array(const_div_rem(&self.array, &other.array).1)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> core::ops::RemAssign for FixedUInt<T, N, Nct> {
        fn rem_assign(&mut self, other: Self) {
            self.array = const_div_rem(&self.array, &other.array).1;
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> core::ops::RemAssign<&FixedUInt<T, N, Nct>> for FixedUInt<T, N, Nct> {
        fn rem_assign(&mut self, other: &FixedUInt<T, N, Nct>) {
            self.array = const_div_rem(&self.array, &other.array).1;
        }
    }
}

c0nst::c0nst! {
    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> CheckedRem for FixedUInt<T, N, Nct> {
        fn checked_rem(self, other: Self) -> Option<Self> {
            if <Self as Zero>::is_zero(&other) {
                None
            } else {
                Some(self % other)
            }
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> CheckedRem for &FixedUInt<T, N, Nct> {
        fn checked_rem(self, other: Self) -> Option<FixedUInt<T, N, Nct>> {
            <FixedUInt<T, N, Nct> as CheckedRem>::checked_rem(*self, *other)
        }
    }
}

#[cfg(feature = "num-traits")]
impl<T: MachineWord, const N: usize> num_traits::CheckedRem for FixedUInt<T, N, Nct> {
    fn checked_rem(&self, other: &Self) -> Option<Self> {
        <Self as CheckedRem>::checked_rem(*self, *other)
    }
}

// Test wrappers for const mul traits
#[cfg(test)]
c0nst::c0nst! {
    pub c0nst fn const_wrapping_mul<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(
        a: &FixedUInt<T, N, P>,
        b: &FixedUInt<T, N, P>
    ) -> FixedUInt<T, N, P> {
        <FixedUInt<T, N, P> as WrappingMul>::wrapping_mul(*a, *b)
    }

    pub c0nst fn const_checked_mul<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(
        a: &FixedUInt<T, N, P>,
        b: &FixedUInt<T, N, P>
    ) -> Option<FixedUInt<T, N, P>> {
        <FixedUInt<T, N, P> as CheckedMul>::checked_mul(*a, *b)
    }

    pub c0nst fn const_saturating_mul<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(
        a: &FixedUInt<T, N, P>,
        b: &FixedUInt<T, N, P>
    ) -> FixedUInt<T, N, P> {
        <FixedUInt<T, N, P> as SaturatingMul>::saturating_mul(*a, *b)
    }

    pub c0nst fn const_overflowing_mul<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(
        a: &FixedUInt<T, N, P>,
        b: &FixedUInt<T, N, P>
    ) -> (FixedUInt<T, N, P>, bool) {
        <FixedUInt<T, N, P> as OverflowingMul>::overflowing_mul(*a, *b)
    }

    pub c0nst fn const_checked_div<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
        a: &FixedUInt<T, N, Nct>,
        b: &FixedUInt<T, N, Nct>
    ) -> Option<FixedUInt<T, N, Nct>> {
        <FixedUInt<T, N, Nct> as CheckedDiv>::checked_div(*a, *b)
    }

    pub c0nst fn const_checked_rem<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
        a: &FixedUInt<T, N, Nct>,
        b: &FixedUInt<T, N, Nct>
    ) -> Option<FixedUInt<T, N, Nct>> {
        <FixedUInt<T, N, Nct> as CheckedRem>::checked_rem(*a, *b)
    }
}

// ── CtCheckedMul (masked-return checked mul) ─────────────────────────
//
// Same shape as CtCheckedAdd/Sub: delegate to `OverflowingMul`, wrap
// the (Self, bool) overflow flag into CtOption via Choice. Uniform
// across both personalities — the underlying `const_mul`'s `true`
// generic arm computes the overflow flag branchlessly.
impl<T, const N: usize, P: Personality> const_num_traits::ops::ct::CtCheckedMul
    for FixedUInt<T, N, P>
where
    T: MachineWord,
{
    fn ct_checked_mul(&self, v: &Self) -> subtle::CtOption<Self> {
        let (val, overflow) = <Self as OverflowingMul>::overflowing_mul(*self, *v);
        subtle::CtOption::new(val, subtle::Choice::from(!overflow as u8))
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

        // WrappingMul
        assert_eq!(const_wrapping_mul(&a, &b), expected);

        // CheckedMul - no overflow
        assert_eq!(const_checked_mul(&a, &b), Some(expected));

        // SaturatingMul - no overflow
        assert_eq!(const_saturating_mul(&a, &b), expected);

        // OverflowingMul - no overflow
        let (result, overflow) = const_overflowing_mul(&a, &b);
        assert_eq!(result, expected);
        assert!(!overflow);

        // Test overflow cases: 256 * 256 = 65536 which overflows 16 bits
        let large = FixedUInt::<u8, 2>::from(256u16); // 0x100

        // CheckedMul - with overflow
        assert_eq!(const_checked_mul(&large, &large), None);

        // SaturatingMul - with overflow saturates to max
        let saturated = const_saturating_mul(&large, &large);
        assert_eq!(saturated, FixedUInt::<u8, 2>::from(0xFFFFu16));

        // OverflowingMul - with overflow
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

        // CheckedDiv - valid division
        assert_eq!(
            const_checked_div(&a, &b),
            Some(FixedUInt::<u8, 2>::from(7u8))
        ); // 36 / 5 = 7

        // CheckedDiv - divide by zero
        assert_eq!(const_checked_div(&a, &zero), None);

        // CheckedRem - valid remainder
        assert_eq!(
            const_checked_rem(&a, &b),
            Some(FixedUInt::<u8, 2>::from(1u8))
        ); // 36 % 5 = 1

        // CheckedRem - remainder by zero
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

    #[test]
    fn ct_checked_mul_masks_overflow() {
        use const_num_traits::ops::ct::CtCheckedMul;
        type U16 = FixedUInt<u8, 2>;
        let ok = U16::from(100u8).ct_checked_mul(&U16::from(50u8));
        assert!(bool::from(ok.is_some()));
        assert_eq!(ok.unwrap(), U16::from(5000u16));
        // Overflow: 1000 * 1000 = 1_000_000 > U16::MAX
        let bad = U16::from(1000u16).ct_checked_mul(&U16::from(1000u16));
        assert!(!bool::from(bad.is_some()));
    }
}
