use super::{
    FixedUInt, MachineWord, const_is_one, const_is_one_ct, const_is_zero, const_is_zero_ct,
};
use crate::const_numtraits::{Bounded, ConstOne, ConstZero, One, Zero};
use crate::machineword::ConstMachineWord;
use const_num_traits::{Personality, PersonalityTag};

c0nst::c0nst! {
    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> Zero for FixedUInt<T, N, P> {
        fn zero() -> Self {
            FixedUInt::from_array([<T as Zero>::zero(); N])
        }
        fn is_zero(&self) -> bool {
            match P::TAG {
                PersonalityTag::Nct => const_is_zero(&self.array),
                PersonalityTag::Ct => const_is_zero_ct(&self.array),
            }
        }
        fn set_zero(&mut self) {
            let mut i = 0;
            while i < N {
                <T as Zero>::set_zero(&mut self.array[i]);
                i += 1;
            }
        }
    }


    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> One for FixedUInt<T, N, P> {
        fn one() -> Self {
            let mut ret = <Self as ConstZero>::ZERO;
            if N > 0 {
                ret.array[0] = <T as One>::one();
            }
            ret
        }
        fn is_one(&self) -> bool {
            match P::TAG {
                PersonalityTag::Nct => const_is_one(&self.array),
                PersonalityTag::Ct => const_is_one_ct(&self.array),
            }
        }
        fn set_one(&mut self) {
            <Self as Zero>::set_zero(self);
            if N > 0 {
                <T as One>::set_one(&mut self.array[0]);
            }
        }
    }


    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> Bounded for FixedUInt<T, N, P> {
        fn min_value() -> Self {
            <Self as ConstZero>::ZERO
        }
        fn max_value() -> Self {
            FixedUInt::from_array([<T as Bounded>::max_value(); N])
        }
    }
}

// `ConstZero` and `ConstOne` are NOT `c0nst` traits in the external
// crate (they only declare an associated constant). The c0nst macro
// rejects mixing const-trait impls with non-const-trait impls in the
// same block, so these two impls live outside the c0nst! block above.

impl<T: ConstMachineWord + MachineWord, const N: usize, P: Personality> ConstZero
    for FixedUInt<T, N, P>
{
    const ZERO: Self = FixedUInt::from_array([<T as ConstZero>::ZERO; N]);
}

impl<T: ConstMachineWord + MachineWord, const N: usize, P: Personality> ConstOne
    for FixedUInt<T, N, P>
{
    const ONE: Self = {
        // Construct array with T::ONE in slot 0, T::ZERO elsewhere.
        let mut a = [<T as ConstZero>::ZERO; N];
        if N > 0 {
            a[0] = <T as ConstOne>::ONE;
        }
        FixedUInt::from_array(a)
    };
}

#[cfg(feature = "num-traits")]
impl<T: MachineWord, const N: usize, P: Personality> num_traits::Zero for FixedUInt<T, N, P> {
    fn zero() -> Self {
        <Self as ConstZero>::ZERO
    }
    fn is_zero(&self) -> bool {
        <Self as Zero>::is_zero(self)
    }
}

#[cfg(feature = "num-traits")]
impl<T: MachineWord, const N: usize, P: Personality> num_traits::One for FixedUInt<T, N, P> {
    fn one() -> Self {
        <Self as ConstOne>::ONE
    }
}

#[cfg(feature = "num-traits")]
impl<T: MachineWord, const N: usize, P: Personality> num_traits::Bounded for FixedUInt<T, N, P> {
    fn min_value() -> Self {
        <Self as Bounded>::min_value()
    }
    fn max_value() -> Self {
        <Self as Bounded>::max_value()
    }
}

// ── CtIsZero (masked-return is_zero) ─────────────────────────────────
//
// AND-fold `ct_eq(&ZERO)` across all limbs. Uniform across both
// personalities — the masking is purely about the return shape, the
// `Zero::is_zero` body's `match P::TAG` already covers the
// short-circuit-vs-OR-fold choice for the `bool`-returning version,
// but for the `Choice` return we always do the full AND-fold to avoid
// branching on the limb-by-limb result.
impl<T, const N: usize, P: Personality> const_num_traits::ops::ct::CtIsZero for FixedUInt<T, N, P>
where
    T: MachineWord + subtle::ConstantTimeEq,
{
    fn ct_is_zero(&self) -> subtle::Choice {
        let mut choice = subtle::Choice::from(1u8);
        let mut i = 0;
        while i < N {
            choice &= self.array[i].ct_eq(&<T as ConstZero>::ZERO);
            i += 1;
        }
        choice
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use const_num_traits::Nct;

    c0nst::c0nst! {
        c0nst fn const_zero<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>() -> FixedUInt<T, N, P> {
            <FixedUInt<T, N, P> as ConstZero>::ZERO
        }

        c0nst fn const_one<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>() -> FixedUInt<T, N, P> {
            <FixedUInt<T, N, P> as ConstOne>::ONE
        }

        c0nst fn const_is_zero<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: &FixedUInt<T, N, P>) -> bool {
            <FixedUInt<T, N, P> as Zero>::is_zero(v)
        }

        c0nst fn const_is_one<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: &FixedUInt<T, N, P>) -> bool {
            <FixedUInt<T, N, P> as One>::is_one(v)
        }

        c0nst fn const_min_value<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>() -> FixedUInt<T, N, P> {
            <FixedUInt<T, N, P> as Bounded>::min_value()
        }

        c0nst fn const_max_value<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>() -> FixedUInt<T, N, P> {
            <FixedUInt<T, N, P> as Bounded>::max_value()
        }

        c0nst fn const_set_zero<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: &mut FixedUInt<T, N, P>) {
            <FixedUInt<T, N, P> as Zero>::set_zero(v)
        }

        c0nst fn const_set_one<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: &mut FixedUInt<T, N, P>) {
            <FixedUInt<T, N, P> as One>::set_one(v)
        }
    }

    #[test]
    fn test_const_identity_traits() {
        type TestInt = FixedUInt<u8, 2>;

        // Test zero
        let zero = const_zero::<u8, 2, Nct>();
        assert!(const_is_zero(&zero));
        assert!(!const_is_one(&zero));

        // Test one
        let one = const_one::<u8, 2, Nct>();
        assert!(!const_is_zero(&one));
        assert!(const_is_one(&one));

        // Test min/max
        let min = const_min_value::<u8, 2, Nct>();
        let max = const_max_value::<u8, 2, Nct>();
        assert!(const_is_zero(&min));
        assert_eq!(max.array, [255, 255]);

        // Test set_zero/set_one
        let mut val = TestInt::from(42u8);
        const_set_zero(&mut val);
        assert!(const_is_zero(&val));

        const_set_one(&mut val);
        assert!(const_is_one(&val));

        #[cfg(feature = "nightly")]
        {
            const ZERO: TestInt = const_zero::<u8, 2, Nct>();
            const ONE: TestInt = const_one::<u8, 2, Nct>();
            const IS_ZERO_TRUE: bool = const_is_zero(&ZERO);
            const IS_ZERO_FALSE: bool = const_is_zero(&ONE);
            const IS_ONE_TRUE: bool = const_is_one(&ONE);
            const IS_ONE_FALSE: bool = const_is_one(&ZERO);
            const MIN: TestInt = const_min_value::<u8, 2, Nct>();
            const MAX: TestInt = const_max_value::<u8, 2, Nct>();

            assert_eq!(ZERO.array, [0, 0]);
            assert_eq!(ONE.array, [1, 0]);
            assert!(IS_ZERO_TRUE);
            assert!(!IS_ZERO_FALSE);
            assert!(IS_ONE_TRUE);
            assert!(!IS_ONE_FALSE);
            assert_eq!(MIN.array, [0, 0]);
            assert_eq!(MAX.array, [255, 255]);

            const SET_ZERO_RES: TestInt = {
                let mut v = FixedUInt::from_array([42, 0]);
                const_set_zero(&mut v);
                v
            };
            const SET_ONE_RES: TestInt = {
                let mut v = FixedUInt::from_array([0, 0]);
                const_set_one(&mut v);
                v
            };
            assert_eq!(SET_ZERO_RES.array, [0, 0]);
            assert_eq!(SET_ONE_RES.array, [1, 0]);
        }
    }

    #[test]
    fn ct_is_zero_matches_is_zero() {
        use const_num_traits::Ct;
        use const_num_traits::ops::ct::CtIsZero;
        type U16Nct = FixedUInt<u8, 2>;
        type U16Ct = FixedUInt<u8, 2, Ct>;
        // Nct
        assert!(bool::from(CtIsZero::ct_is_zero(&U16Nct::from(0u8))));
        assert!(!bool::from(CtIsZero::ct_is_zero(&U16Nct::from(1u8))));
        assert!(!bool::from(CtIsZero::ct_is_zero(&U16Nct::from(0xFFFFu16))));
        // Non-zero in the high limb only (catches a per-limb-AND bug)
        assert!(!bool::from(CtIsZero::ct_is_zero(
            &FixedUInt::<u8, 2>::from_array([0, 1])
        )));
        // Ct
        let z_ct: U16Ct = U16Nct::from(0u8).into();
        let nz_ct: U16Ct = U16Nct::from(42u8).into();
        assert!(bool::from(CtIsZero::ct_is_zero(&z_ct)));
        assert!(!bool::from(CtIsZero::ct_is_zero(&nz_ct)));
    }
}
