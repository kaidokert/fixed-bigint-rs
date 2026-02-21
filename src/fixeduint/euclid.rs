use num_traits::{CheckedEuclid, Euclid};

use super::{FixedUInt, MachineWord};
use crate::const_numtraits::{ConstCheckedEuclid, ConstEuclid, ConstZero};
use crate::machineword::ConstMachineWord;

c0nst::c0nst! {
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstEuclid for FixedUInt<T, N> {
        fn div_euclid(&self, v: &Self) -> Self {
            // For unsigned integers, Euclidean division is the same as regular division
            *self / *v
        }

        fn rem_euclid(&self, v: &Self) -> Self {
            // For unsigned integers, Euclidean remainder is the same as regular remainder
            *self % *v
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstCheckedEuclid for FixedUInt<T, N> {
        fn checked_div_euclid(&self, v: &Self) -> Option<Self> {
            if v.is_zero() {
                None
            } else {
                Some(*self / *v)
            }
        }

        fn checked_rem_euclid(&self, v: &Self) -> Option<Self> {
            if v.is_zero() {
                None
            } else {
                Some(*self % *v)
            }
        }
    }
}

// num_traits::Euclid - uses direct operators (no const bounds needed)
impl<T: MachineWord, const N: usize> Euclid for FixedUInt<T, N> {
    fn div_euclid(&self, v: &Self) -> Self {
        self / v
    }

    fn rem_euclid(&self, v: &Self) -> Self {
        self % v
    }
}

// num_traits::CheckedEuclid - uses direct checked calls (no const bounds needed)
impl<T: MachineWord, const N: usize> CheckedEuclid for FixedUInt<T, N> {
    fn checked_div_euclid(&self, v: &Self) -> Option<Self> {
        num_traits::CheckedDiv::checked_div(self, v)
    }

    fn checked_rem_euclid(&self, v: &Self) -> Option<Self> {
        num_traits::CheckedRem::checked_rem(self, v)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machineword::ConstMachineWord;

    #[test]
    fn test_div_euclid() {
        use num_traits::Euclid;
        let a = FixedUInt::<u8, 2>::from(100u8);
        let b = FixedUInt::<u8, 2>::from(30u8);
        assert_eq!(Euclid::div_euclid(&a, &b), 3u8.into());
        assert_eq!(Euclid::rem_euclid(&a, &b), 10u8.into());
    }

    #[test]
    fn test_checked_div_euclid() {
        use num_traits::CheckedEuclid;
        let a = FixedUInt::<u8, 2>::from(100u8);
        let b = FixedUInt::<u8, 2>::from(30u8);
        assert_eq!(CheckedEuclid::checked_div_euclid(&a, &b), Some(3u8.into()));
        assert_eq!(CheckedEuclid::checked_rem_euclid(&a, &b), Some(10u8.into()));

        // Test division by zero
        let zero = FixedUInt::<u8, 2>::from(0u8);
        assert_eq!(CheckedEuclid::checked_div_euclid(&a, &zero), None);
        assert_eq!(CheckedEuclid::checked_rem_euclid(&a, &zero), None);
    }

    c0nst::c0nst! {
        pub c0nst fn const_div_euclid<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            a: &FixedUInt<T, N>,
            b: &FixedUInt<T, N>,
        ) -> FixedUInt<T, N> {
            ConstEuclid::div_euclid(a, b)
        }

        pub c0nst fn const_rem_euclid<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            a: &FixedUInt<T, N>,
            b: &FixedUInt<T, N>,
        ) -> FixedUInt<T, N> {
            ConstEuclid::rem_euclid(a, b)
        }

        pub c0nst fn const_checked_div_euclid<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            a: &FixedUInt<T, N>,
            b: &FixedUInt<T, N>,
        ) -> Option<FixedUInt<T, N>> {
            ConstCheckedEuclid::checked_div_euclid(a, b)
        }

        pub c0nst fn const_checked_rem_euclid<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            a: &FixedUInt<T, N>,
            b: &FixedUInt<T, N>,
        ) -> Option<FixedUInt<T, N>> {
            ConstCheckedEuclid::checked_rem_euclid(a, b)
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
            const A: FixedUInt<u8, 2> = FixedUInt { array: [100, 0] };
            const B: FixedUInt<u8, 2> = FixedUInt { array: [30, 0] };
            const DIV_RESULT: FixedUInt<u8, 2> = const_div_euclid(&A, &B);
            const REM_RESULT: FixedUInt<u8, 2> = const_rem_euclid(&A, &B);
            const CHECKED_DIV: Option<FixedUInt<u8, 2>> = const_checked_div_euclid(&A, &B);
            const CHECKED_REM: Option<FixedUInt<u8, 2>> = const_checked_rem_euclid(&A, &B);
            assert_eq!(DIV_RESULT, FixedUInt { array: [3, 0] });
            assert_eq!(REM_RESULT, FixedUInt { array: [10, 0] });
            assert_eq!(CHECKED_DIV, Some(FixedUInt { array: [3, 0] }));
            assert_eq!(CHECKED_REM, Some(FixedUInt { array: [10, 0] }));
        }
    }
}
