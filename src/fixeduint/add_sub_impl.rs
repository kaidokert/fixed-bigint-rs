use super::{
    FixedUInt, MachineWord, PanicReason, add_impl, const_ct_select, maybe_panic_if, sub_impl,
};
use crate::const_numtraits::{
    Bounded, CheckedAdd, CheckedSub, ConstZero, OverflowingAdd, OverflowingSub, SaturatingAdd,
    SaturatingSub, WrappingAdd, WrappingSub,
};
use crate::machineword::ConstMachineWord;
use const_num_traits::{Personality, PersonalityTag};

c0nst::c0nst! {
    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> crate::const_numtraits::OverflowingAdd for FixedUInt<T, N, P> {
        fn overflowing_add(self, other: Self) -> (Self, bool) {
            let mut ret = self;
            let overflow = add_impl(&mut ret.array, &other.array);
            (ret, overflow)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> crate::const_numtraits::OverflowingSub for FixedUInt<T, N, P> {
        fn overflowing_sub(self, other: Self) -> (Self, bool) {
            let mut ret = self;
            let overflow = sub_impl(&mut ret.array, &other.array);
            (ret, overflow)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> WrappingAdd for FixedUInt<T, N, P> {
        fn wrapping_add(self, other: Self) -> Self {
            <Self as OverflowingAdd>::overflowing_add(self, other).0
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> WrappingSub for FixedUInt<T, N, P> {
        fn wrapping_sub(self, other: Self) -> Self {
            <Self as OverflowingSub>::overflowing_sub(self, other).0
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> CheckedAdd for FixedUInt<T, N, P> {
        fn checked_add(self, other: Self) -> Option<Self> {
            let (res, overflow) = <Self as OverflowingAdd>::overflowing_add(self, other);
            if overflow { None } else { Some(res) }
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> CheckedSub for FixedUInt<T, N, P> {
        fn checked_sub(self, other: Self) -> Option<Self> {
            let (res, overflow) = <Self as OverflowingSub>::overflowing_sub(self, other);
            if overflow { None } else { Some(res) }
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> SaturatingAdd for FixedUInt<T, N, P> {
        fn saturating_add(self, other: Self) -> Self {
            let (res, overflow) = <Self as OverflowingAdd>::overflowing_add(self, other);
            match P::TAG {
                PersonalityTag::Nct => if overflow { <Self as Bounded>::max_value() } else { res },
                PersonalityTag::Ct => const_ct_select(res, <Self as Bounded>::max_value(), overflow as u8),
            }
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> SaturatingSub for FixedUInt<T, N, P> {
        fn saturating_sub(self, other: Self) -> Self {
            let (res, overflow) = <Self as OverflowingSub>::overflowing_sub(self, other);
            match P::TAG {
                PersonalityTag::Nct => if overflow { <Self as ConstZero>::ZERO } else { res },
                PersonalityTag::Ct => const_ct_select(res, <Self as ConstZero>::ZERO, overflow as u8),
            }
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::Add for FixedUInt<T, N, P> {
        type Output = Self;
        fn add(self, other: Self) -> Self {
            let (res, overflow) = <Self as crate::const_numtraits::OverflowingAdd>::overflowing_add(self, other);
            maybe_panic_if::<P>(overflow, PanicReason::Add);
            res
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::Sub for FixedUInt<T, N, P> {
        type Output = Self;
        fn sub(self, other: Self) -> Self {
            let (res, overflow) = <Self as crate::const_numtraits::OverflowingSub>::overflowing_sub(self, other);
            maybe_panic_if::<P>(overflow, PanicReason::Sub);
            res
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::Add<&'_ Self> for FixedUInt<T, N, P> {
        type Output = Self;
        fn add(self, other: &Self) -> Self {
            let (res, overflow) = <Self as crate::const_numtraits::OverflowingAdd>::overflowing_add(self, *other);
            maybe_panic_if::<P>(overflow, PanicReason::Add);
            res
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::Add<FixedUInt<T, N, P>> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn add(self, other: FixedUInt<T, N, P>) -> Self::Output {
            let (res, overflow) = <FixedUInt<T, N, P> as crate::const_numtraits::OverflowingAdd>::overflowing_add(*self, other);
            maybe_panic_if::<P>(overflow, PanicReason::Add);
            res
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::Add<Self> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn add(self, other: Self) -> Self::Output {
            let (res, overflow) = <FixedUInt<T, N, P> as crate::const_numtraits::OverflowingAdd>::overflowing_add(*self, *other);
            maybe_panic_if::<P>(overflow, PanicReason::Add);
            res
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::Sub<&'_ Self> for FixedUInt<T, N, P> {
        type Output = Self;
        fn sub(self, other: &Self) -> Self {
            let (res, overflow) = <Self as crate::const_numtraits::OverflowingSub>::overflowing_sub(self, *other);
            maybe_panic_if::<P>(overflow, PanicReason::Sub);
            res
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::Sub<FixedUInt<T, N, P>> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn sub(self, other: FixedUInt<T, N, P>) -> Self::Output {
            let (res, overflow) = <FixedUInt<T, N, P> as crate::const_numtraits::OverflowingSub>::overflowing_sub(*self, other);
            maybe_panic_if::<P>(overflow, PanicReason::Sub);
            res
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::Sub<Self> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn sub(self, other: Self) -> Self::Output {
            let (res, overflow) = <FixedUInt<T, N, P> as crate::const_numtraits::OverflowingSub>::overflowing_sub(*self, *other);
            maybe_panic_if::<P>(overflow, PanicReason::Sub);
            res
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::AddAssign<Self> for FixedUInt<T, N, P> {
        fn add_assign(&mut self, other: Self) {
            let mut array = self.array;
            let overflow = add_impl(&mut array, &other.array);
            maybe_panic_if::<P>(overflow, PanicReason::Add);
            self.array = array;
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::AddAssign<&'_ Self> for FixedUInt<T, N, P> {
        fn add_assign(&mut self, other: &Self) {
            let mut array = self.array;
            let overflow = add_impl(&mut array, &other.array);
            maybe_panic_if::<P>(overflow, PanicReason::Add);
            self.array = array;
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::SubAssign<Self> for FixedUInt<T, N, P> {
        fn sub_assign(&mut self, other: Self) {
            let mut array = self.array;
            let overflow = sub_impl(&mut array, &other.array);
            maybe_panic_if::<P>(overflow, PanicReason::Sub);
            self.array = array;
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::SubAssign<&'_ Self> for FixedUInt<T, N, P> {
        fn sub_assign(&mut self, other: &Self) {
            let mut array = self.array;
            let overflow = sub_impl(&mut array, &other.array);
            maybe_panic_if::<P>(overflow, PanicReason::Sub);
            self.array = array;
        }
    }

    // --- Reference-receiver impls ------------------------------------------
    //
    // MIGRATION.md §2.3 introduces the `type Output` associated type so the
    // by-value trait surface can also be implemented for `&Self`. For Copy
    // types like FixedUInt the body just dereferences and delegates to the
    // owned impl above, but the ergonomic payoff is real: call sites can
    // write `(&x).checked_add(&y)` (or call generically through a `T:
    // CheckedAdd` bound where T is `&FixedUInt`) without sprinkling derefs
    // through arithmetic helpers. The `Add<&FixedUInt> for &FixedUInt`
    // impls in this file (lines 96+) supply the `Output = FixedUInt<T,N,P>`
    // that the operator-backed supertrait expects.

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> crate::const_numtraits::OverflowingAdd for &FixedUInt<T, N, P> {
        fn overflowing_add(self, other: Self) -> (FixedUInt<T, N, P>, bool) {
            <FixedUInt<T, N, P> as crate::const_numtraits::OverflowingAdd>::overflowing_add(*self, *other)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> crate::const_numtraits::OverflowingSub for &FixedUInt<T, N, P> {
        fn overflowing_sub(self, other: Self) -> (FixedUInt<T, N, P>, bool) {
            <FixedUInt<T, N, P> as crate::const_numtraits::OverflowingSub>::overflowing_sub(*self, *other)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> WrappingAdd for &FixedUInt<T, N, P> {
        fn wrapping_add(self, other: Self) -> FixedUInt<T, N, P> {
            <FixedUInt<T, N, P> as WrappingAdd>::wrapping_add(*self, *other)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> WrappingSub for &FixedUInt<T, N, P> {
        fn wrapping_sub(self, other: Self) -> FixedUInt<T, N, P> {
            <FixedUInt<T, N, P> as WrappingSub>::wrapping_sub(*self, *other)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> CheckedAdd for &FixedUInt<T, N, P> {
        fn checked_add(self, other: Self) -> Option<FixedUInt<T, N, P>> {
            <FixedUInt<T, N, P> as CheckedAdd>::checked_add(*self, *other)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> CheckedSub for &FixedUInt<T, N, P> {
        fn checked_sub(self, other: Self) -> Option<FixedUInt<T, N, P>> {
            <FixedUInt<T, N, P> as CheckedSub>::checked_sub(*self, *other)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> SaturatingAdd for &FixedUInt<T, N, P> {
        fn saturating_add(self, other: Self) -> FixedUInt<T, N, P> {
            <FixedUInt<T, N, P> as SaturatingAdd>::saturating_add(*self, *other)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> SaturatingSub for &FixedUInt<T, N, P> {
        fn saturating_sub(self, other: Self) -> FixedUInt<T, N, P> {
            <FixedUInt<T, N, P> as SaturatingSub>::saturating_sub(*self, *other)
        }
    }
}

#[cfg(feature = "num-traits")]
impl<T: MachineWord, const N: usize, P: Personality> num_traits::ops::overflowing::OverflowingAdd
    for FixedUInt<T, N, P>
{
    fn overflowing_add(&self, other: &Self) -> (Self, bool) {
        <Self as crate::const_numtraits::OverflowingAdd>::overflowing_add(*self, *other)
    }
}

#[cfg(feature = "num-traits")]
impl<T: MachineWord, const N: usize, P: Personality> num_traits::WrappingAdd
    for FixedUInt<T, N, P>
{
    fn wrapping_add(&self, other: &Self) -> Self {
        <Self as WrappingAdd>::wrapping_add(*self, *other)
    }
}

#[cfg(feature = "num-traits")]
impl<T: MachineWord, const N: usize, P: Personality> num_traits::CheckedAdd for FixedUInt<T, N, P> {
    fn checked_add(&self, other: &Self) -> Option<Self> {
        <Self as CheckedAdd>::checked_add(*self, *other)
    }
}

#[cfg(feature = "num-traits")]
impl<T: MachineWord, const N: usize, P: Personality> num_traits::ops::saturating::SaturatingAdd
    for FixedUInt<T, N, P>
{
    fn saturating_add(&self, other: &Self) -> Self {
        <Self as SaturatingAdd>::saturating_add(*self, *other)
    }
}

#[cfg(feature = "num-traits")]
impl<T: MachineWord, const N: usize, P: Personality> num_traits::ops::overflowing::OverflowingSub
    for FixedUInt<T, N, P>
{
    fn overflowing_sub(&self, other: &Self) -> (Self, bool) {
        <Self as crate::const_numtraits::OverflowingSub>::overflowing_sub(*self, *other)
    }
}

#[cfg(feature = "num-traits")]
impl<T: MachineWord, const N: usize, P: Personality> num_traits::WrappingSub
    for FixedUInt<T, N, P>
{
    fn wrapping_sub(&self, other: &Self) -> Self {
        <Self as WrappingSub>::wrapping_sub(*self, *other)
    }
}

#[cfg(feature = "num-traits")]
impl<T: MachineWord, const N: usize, P: Personality> num_traits::CheckedSub for FixedUInt<T, N, P> {
    fn checked_sub(&self, other: &Self) -> Option<Self> {
        <Self as CheckedSub>::checked_sub(*self, *other)
    }
}

#[cfg(feature = "num-traits")]
impl<T: MachineWord, const N: usize, P: Personality> num_traits::ops::saturating::SaturatingSub
    for FixedUInt<T, N, P>
{
    fn saturating_sub(&self, other: &Self) -> Self {
        <Self as SaturatingSub>::saturating_sub(*self, *other)
    }
}

/// Note: This is marked deprecated, but still used by PrimInt
#[cfg(feature = "num-traits")]
impl<T: MachineWord, const N: usize, P: Personality> num_traits::Saturating for FixedUInt<T, N, P> {
    fn saturating_add(self, other: Self) -> Self {
        <Self as SaturatingAdd>::saturating_add(self, other)
    }

    fn saturating_sub(self, other: Self) -> Self {
        <Self as SaturatingSub>::saturating_sub(self, other)
    }
}

// ── CtCheckedAdd / CtCheckedSub (masked-return checked arithmetic) ───
//
// Delegate to the existing `OverflowingAdd`/`OverflowingSub` impls (which
// already cover both personalities branchlessly via `add_impl`/`sub_impl`),
// then wrap the `(Self, bool)` into a `CtOption<Self>` by converting the
// overflow flag to a `Choice`. Same shape upstream uses for the primitives.
impl<T, const N: usize, P: Personality> const_num_traits::ops::ct::CtCheckedAdd
    for FixedUInt<T, N, P>
where
    T: MachineWord,
{
    fn ct_checked_add(&self, v: &Self) -> subtle::CtOption<Self> {
        let (val, overflow) =
            <Self as crate::const_numtraits::OverflowingAdd>::overflowing_add(*self, *v);
        subtle::CtOption::new(val, subtle::Choice::from(!overflow as u8))
    }
}

impl<T, const N: usize, P: Personality> const_num_traits::ops::ct::CtCheckedSub
    for FixedUInt<T, N, P>
where
    T: MachineWord,
{
    fn ct_checked_sub(&self, v: &Self) -> subtle::CtOption<Self> {
        let (val, overflow) =
            <Self as crate::const_numtraits::OverflowingSub>::overflowing_sub(*self, *v);
        subtle::CtOption::new(val, subtle::Choice::from(!overflow as u8))
    }
}

#[cfg(test)]
// Coverage tests deliberately exercise every ref/value combination of
// `Add`/`Sub` (see `test_add_combinations`, `test_sub_combinations`).
#[allow(clippy::op_ref)]
mod tests {
    use super::*;
    use crate::const_numtraits::Bounded;
    use crate::const_numtraits::{
        CheckedAdd, CheckedSub, OverflowingAdd, OverflowingSub, WrappingAdd, WrappingSub,
    };
    use crate::machineword::ConstMachineWord;

    c0nst::c0nst! {
        /// Test wrapper for OverflowingAdd
        pub c0nst fn const_overflowing_add<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(
            a: &FixedUInt<T, N, P>,
            b: &FixedUInt<T, N, P>
        ) -> (FixedUInt<T, N, P>, bool) {
            <FixedUInt<T, N, P> as OverflowingAdd>::overflowing_add(*a, *b)
        }

        /// Test wrapper for OverflowingSub
        pub c0nst fn const_overflowing_sub<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(
            a: &FixedUInt<T, N, P>,
            b: &FixedUInt<T, N, P>
        ) -> (FixedUInt<T, N, P>, bool) {
            <FixedUInt<T, N, P> as OverflowingSub>::overflowing_sub(*a, *b)
        }

        /// Test wrapper for const Add
        pub c0nst fn const_add<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(
            a: FixedUInt<T, N, P>,
            b: FixedUInt<T, N, P>
        ) -> FixedUInt<T, N, P> {
            a + b
        }

        /// Test wrapper for const Sub
        pub c0nst fn const_sub<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(
            a: FixedUInt<T, N, P>,
            b: FixedUInt<T, N, P>
        ) -> FixedUInt<T, N, P> {
            a - b
        }

        /// Test wrapper for WrappingAdd
        pub c0nst fn const_wrapping_add<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(
            a: &FixedUInt<T, N, P>,
            b: &FixedUInt<T, N, P>
        ) -> FixedUInt<T, N, P> {
            <FixedUInt<T, N, P> as WrappingAdd>::wrapping_add(*a, *b)
        }

        /// Test wrapper for WrappingSub
        pub c0nst fn const_wrapping_sub<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(
            a: &FixedUInt<T, N, P>,
            b: &FixedUInt<T, N, P>
        ) -> FixedUInt<T, N, P> {
            <FixedUInt<T, N, P> as WrappingSub>::wrapping_sub(*a, *b)
        }

        /// Test wrapper for CheckedAdd
        pub c0nst fn const_checked_add<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(
            a: &FixedUInt<T, N, P>,
            b: &FixedUInt<T, N, P>
        ) -> Option<FixedUInt<T, N, P>> {
            <FixedUInt<T, N, P> as CheckedAdd>::checked_add(*a, *b)
        }

        /// Test wrapper for CheckedSub
        pub c0nst fn const_checked_sub<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(
            a: &FixedUInt<T, N, P>,
            b: &FixedUInt<T, N, P>
        ) -> Option<FixedUInt<T, N, P>> {
            <FixedUInt<T, N, P> as CheckedSub>::checked_sub(*a, *b)
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
        let a = <FixedUInt<u8, 2> as Bounded>::max_value();
        let b = <FixedUInt<u8, 2> as Bounded>::max_value();
        let (result, overflow) = const_overflowing_add(&a, &b);
        // 0xFFFF + 0xFFFF = 0x1FFFE, which wraps to 0xFFFE with overflow
        assert_eq!(result, FixedUInt::<u8, 2>::from(u16::MAX - 1));
        assert!(overflow);

        // Max value overflow
        let max = <FixedUInt<u8, 2> as Bounded>::max_value();
        let one = FixedUInt::<u8, 2>::from(1u8);
        let (_, overflow) = const_overflowing_add(&max, &one);
        assert!(overflow);

        #[cfg(feature = "nightly")]
        {
            const A: FixedUInt<u8, 2> = FixedUInt::from_array([12, 0]);
            const B: FixedUInt<u8, 2> = FixedUInt::from_array([3, 0]);
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
            const A: FixedUInt<u8, 2> = FixedUInt::from_array([15, 0]);
            const B: FixedUInt<u8, 2> = FixedUInt::from_array([3, 0]);
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
            const A: FixedUInt<u8, 2> = FixedUInt::from_array([12, 0]);
            const B: FixedUInt<u8, 2> = FixedUInt::from_array([3, 0]);
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
            const A: FixedUInt<u8, 2> = FixedUInt::from_array([15, 0]);
            const B: FixedUInt<u8, 2> = FixedUInt::from_array([3, 0]);
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
        let max = <FixedUInt<u8, 2> as Bounded>::max_value();
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
        assert_eq!(result, <FixedUInt::<u8, 2> as Bounded>::max_value());

        // Test checked_add without overflow
        let a = FixedUInt::<u8, 2>::from(100u8);
        let b = FixedUInt::<u8, 2>::from(50u8);
        let result = const_checked_add(&a, &b);
        assert_eq!(result, Some(FixedUInt::<u8, 2>::from(150u8)));

        // Test checked_add with overflow
        let max = <FixedUInt<u8, 2> as Bounded>::max_value();
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
            const A: FixedUInt<u8, 2> = FixedUInt::from_array([100, 0]);
            const B: FixedUInt<u8, 2> = FixedUInt::from_array([50, 0]);

            const WRAP_ADD: FixedUInt<u8, 2> = const_wrapping_add(&A, &B);
            const WRAP_SUB: FixedUInt<u8, 2> = const_wrapping_sub(&A, &B);
            const CHECK_ADD: Option<FixedUInt<u8, 2>> = const_checked_add(&A, &B);
            const CHECK_SUB: Option<FixedUInt<u8, 2>> = const_checked_sub(&A, &B);

            assert_eq!(WRAP_ADD.array, [150, 0]);
            assert_eq!(WRAP_SUB.array, [50, 0]);
            assert!(CHECK_ADD.is_some());
            assert!(CHECK_SUB.is_some());

            const MAX: FixedUInt<u8, 2> = FixedUInt::from_array([255, 255]);
            const ONE: FixedUInt<u8, 2> = FixedUInt::from_array([1, 0]);
            const CHECK_ADD_OVERFLOW: Option<FixedUInt<u8, 2>> = const_checked_add(&MAX, &ONE);
            assert!(CHECK_ADD_OVERFLOW.is_none());
        }
    }

    #[test]
    fn ct_checked_add_masks_overflow() {
        use const_num_traits::ops::ct::CtCheckedAdd;
        type U16 = FixedUInt<u8, 2>;
        let a = U16::from(100u8);
        let b = U16::from(50u8);
        let ok = a.ct_checked_add(&b);
        assert!(bool::from(ok.is_some()));
        assert_eq!(ok.unwrap(), U16::from(150u8));
        // Overflow case: MAX + 1
        let max = <U16 as crate::const_numtraits::Bounded>::max_value();
        let one = U16::from(1u8);
        let bad = max.ct_checked_add(&one);
        assert!(!bool::from(bad.is_some()));
    }

    #[test]
    fn ct_checked_sub_masks_underflow() {
        use const_num_traits::ops::ct::CtCheckedSub;
        type U16 = FixedUInt<u8, 2>;
        let ok = U16::from(100u8).ct_checked_sub(&U16::from(50u8));
        assert!(bool::from(ok.is_some()));
        assert_eq!(ok.unwrap(), U16::from(50u8));
        // Underflow: 0 - 1
        let bad = U16::from(0u8).ct_checked_sub(&U16::from(1u8));
        assert!(!bool::from(bad.is_some()));
    }
}
