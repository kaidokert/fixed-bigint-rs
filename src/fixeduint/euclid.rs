use super::{FixedUInt, MachineWord};
use crate::const_numtraits::{CheckedEuclid, ConstZero, Euclid, One, Zero};
use crate::machineword::ConstMachineWord;
use const_num_traits::Nct;

c0nst::c0nst! {
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst Euclid for FixedUInt<T, N, Nct> {
        fn div_euclid(self, v: Self) -> Self {
            // For unsigned integers, Euclidean division is the same as regular division
            self / v
        }

        fn rem_euclid(self, v: Self) -> Self {
            // For unsigned integers, Euclidean remainder is the same as regular remainder
            self % v
        }

        fn div_rem_euclid(self, v: Self) -> (Self, Self) {
            (self / v, self % v)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst CheckedEuclid for FixedUInt<T, N, Nct> {
        fn checked_div_euclid(self, v: Self) -> Option<Self> {
            if <Self as Zero>::is_zero(&v) {
                None
            } else {
                Some(self / v)
            }
        }

        fn checked_rem_euclid(self, v: Self) -> Option<Self> {
            if <Self as Zero>::is_zero(&v) {
                None
            } else {
                Some(self % v)
            }
        }

        fn checked_div_rem_euclid(self, v: Self) -> Option<(Self, Self)> {
            if <Self as Zero>::is_zero(&v) {
                None
            } else {
                Some((self / v, self % v))
            }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst Euclid for &FixedUInt<T, N, Nct> {
        fn div_euclid(self, v: Self) -> FixedUInt<T, N, Nct> {
            <FixedUInt<T, N, Nct> as Euclid>::div_euclid(*self, *v)
        }
        fn rem_euclid(self, v: Self) -> FixedUInt<T, N, Nct> {
            <FixedUInt<T, N, Nct> as Euclid>::rem_euclid(*self, *v)
        }
        fn div_rem_euclid(self, v: Self) -> (FixedUInt<T, N, Nct>, FixedUInt<T, N, Nct>) {
            <FixedUInt<T, N, Nct> as Euclid>::div_rem_euclid(*self, *v)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst CheckedEuclid for &FixedUInt<T, N, Nct> {
        fn checked_div_euclid(self, v: Self) -> Option<FixedUInt<T, N, Nct>> {
            <FixedUInt<T, N, Nct> as CheckedEuclid>::checked_div_euclid(*self, *v)
        }
        fn checked_rem_euclid(self, v: Self) -> Option<FixedUInt<T, N, Nct>> {
            <FixedUInt<T, N, Nct> as CheckedEuclid>::checked_rem_euclid(*self, *v)
        }
        fn checked_div_rem_euclid(self, v: Self) -> Option<(FixedUInt<T, N, Nct>, FixedUInt<T, N, Nct>)> {
            <FixedUInt<T, N, Nct> as CheckedEuclid>::checked_div_rem_euclid(*self, *v)
        }
    }
}

// (legacy num_traits::Euclid / CheckedEuclid shim impls retired — the
// `c0nst Euclid` / `c0nst CheckedEuclid` impls above ARE the impls
// of the external traits now.)

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machineword::ConstMachineWord;

    #[test]
    fn test_div_euclid() {
        use crate::const_numtraits::Euclid;
        let a = FixedUInt::<u8, 2>::from(100u8);
        let b = FixedUInt::<u8, 2>::from(30u8);
        assert_eq!(Euclid::div_euclid(a, b), 3u8.into());
        assert_eq!(Euclid::rem_euclid(a, b), 10u8.into());
    }

    #[test]
    fn test_checked_div_euclid() {
        use crate::const_numtraits::CheckedEuclid;
        let a = FixedUInt::<u8, 2>::from(100u8);
        let b = FixedUInt::<u8, 2>::from(30u8);
        assert_eq!(CheckedEuclid::checked_div_euclid(a, b), Some(3u8.into()));
        assert_eq!(CheckedEuclid::checked_rem_euclid(a, b), Some(10u8.into()));

        // Test division by zero
        let zero = FixedUInt::<u8, 2>::from(0u8);
        assert_eq!(CheckedEuclid::checked_div_euclid(a, zero), None);
        assert_eq!(CheckedEuclid::checked_rem_euclid(a, zero), None);
    }

    c0nst::c0nst! {
        pub c0nst fn const_div_euclid<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            a: &FixedUInt<T, N, Nct>,
            b: &FixedUInt<T, N, Nct>,
        ) -> FixedUInt<T, N, Nct> {
            Euclid::div_euclid(*a, *b)
        }

        pub c0nst fn const_rem_euclid<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            a: &FixedUInt<T, N, Nct>,
            b: &FixedUInt<T, N, Nct>,
        ) -> FixedUInt<T, N, Nct> {
            Euclid::rem_euclid(*a, *b)
        }

        pub c0nst fn const_checked_div_euclid<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            a: &FixedUInt<T, N, Nct>,
            b: &FixedUInt<T, N, Nct>,
        ) -> Option<FixedUInt<T, N, Nct>> {
            CheckedEuclid::checked_div_euclid(*a, *b)
        }

        pub c0nst fn const_checked_rem_euclid<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            a: &FixedUInt<T, N, Nct>,
            b: &FixedUInt<T, N, Nct>,
        ) -> Option<FixedUInt<T, N, Nct>> {
            CheckedEuclid::checked_rem_euclid(*a, *b)
        }
    }

    #[test]
    fn test_const_euclid() {
        let a = FixedUInt::<u8, 2>::from(100u8);
        let b = FixedUInt::<u8, 2>::from(30u8);
        assert_eq!(const_div_euclid(&a, &b), 3u8.into());
        assert_eq!(const_rem_euclid(&a, &b), 10u8.into());
        assert_eq!(const_checked_div_euclid(&a, &b), Some(3u8.into()));
        assert_eq!(const_checked_rem_euclid(&a, &b), Some(10u8.into()));

        #[cfg(feature = "nightly")]
        {
            const A: FixedUInt<u8, 2> = FixedUInt::from_array([100, 0]);
            const B: FixedUInt<u8, 2> = FixedUInt::from_array([30, 0]);
            const DIV_RESULT: FixedUInt<u8, 2> = const_div_euclid(&A, &B);
            const REM_RESULT: FixedUInt<u8, 2> = const_rem_euclid(&A, &B);
            const CHECKED_DIV: Option<FixedUInt<u8, 2>> = const_checked_div_euclid(&A, &B);
            const CHECKED_REM: Option<FixedUInt<u8, 2>> = const_checked_rem_euclid(&A, &B);
            assert_eq!(DIV_RESULT, FixedUInt::from_array([3, 0]));
            assert_eq!(REM_RESULT, FixedUInt::from_array([10, 0]));
            assert_eq!(CHECKED_DIV, Some(FixedUInt::from_array([3, 0])));
            assert_eq!(CHECKED_REM, Some(FixedUInt::from_array([10, 0])));
        }
    }
}
