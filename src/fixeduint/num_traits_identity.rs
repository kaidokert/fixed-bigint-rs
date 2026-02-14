use super::{const_array_is_zero, FixedUInt, MachineWord};
use crate::const_numtrait::{ConstBounded, ConstOne, ConstZero};
use crate::machineword::ConstMachineWord;

c0nst::c0nst! {
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstZero for FixedUInt<T, N> {
        fn zero() -> Self {
            FixedUInt {
                array: [T::zero(); N],
            }
        }
        fn is_zero(&self) -> bool {
            const_array_is_zero(&self.array)
        }
        fn set_zero(&mut self) {
            let mut i = 0;
            while i < N {
                self.array[i].set_zero();
                i += 1;
            }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstOne for FixedUInt<T, N> {
        fn one() -> Self {
            let mut ret = <Self as ConstZero>::zero();
            if N > 0 {
                ret.array[0] = T::one();
            }
            ret
        }
        fn is_one(&self) -> bool {
            if N == 0 || !self.array[0].is_one() {
                return false;
            }
            let mut i = 1;
            while i < N {
                if !self.array[i].is_zero() {
                    return false;
                }
                i += 1;
            }
            true
        }
        fn set_one(&mut self) {
            <Self as ConstZero>::set_zero(self);
            if N > 0 {
                self.array[0].set_one();
            }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstBounded for FixedUInt<T, N> {
        fn min_value() -> Self {
            <Self as ConstZero>::zero()
        }
        fn max_value() -> Self {
            FixedUInt {
                array: [T::max_value(); N],
            }
        }
    }
}

impl<T: MachineWord, const N: usize> num_traits::Zero for FixedUInt<T, N> {
    fn zero() -> Self {
        <Self as ConstZero>::zero()
    }
    fn is_zero(&self) -> bool {
        <Self as ConstZero>::is_zero(self)
    }
}

impl<T: MachineWord, const N: usize> num_traits::One for FixedUInt<T, N> {
    fn one() -> Self {
        <Self as ConstOne>::one()
    }
}

impl<T: MachineWord, const N: usize> num_traits::Bounded for FixedUInt<T, N> {
    fn min_value() -> Self {
        <Self as ConstBounded>::min_value()
    }
    fn max_value() -> Self {
        <Self as ConstBounded>::max_value()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    c0nst::c0nst! {
        c0nst fn const_zero<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>() -> FixedUInt<T, N> {
            <FixedUInt<T, N> as ConstZero>::zero()
        }

        c0nst fn const_one<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>() -> FixedUInt<T, N> {
            <FixedUInt<T, N> as ConstOne>::one()
        }

        c0nst fn const_is_zero<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(v: &FixedUInt<T, N>) -> bool {
            <FixedUInt<T, N> as ConstZero>::is_zero(v)
        }

        c0nst fn const_is_one<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(v: &FixedUInt<T, N>) -> bool {
            <FixedUInt<T, N> as ConstOne>::is_one(v)
        }

        c0nst fn const_min_value<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>() -> FixedUInt<T, N> {
            <FixedUInt<T, N> as ConstBounded>::min_value()
        }

        c0nst fn const_max_value<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>() -> FixedUInt<T, N> {
            <FixedUInt<T, N> as ConstBounded>::max_value()
        }

        c0nst fn const_set_zero<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(v: &mut FixedUInt<T, N>) {
            <FixedUInt<T, N> as ConstZero>::set_zero(v)
        }

        c0nst fn const_set_one<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(v: &mut FixedUInt<T, N>) {
            <FixedUInt<T, N> as ConstOne>::set_one(v)
        }
    }

    #[test]
    fn test_const_identity_traits() {
        type TestInt = FixedUInt<u8, 2>;

        // Test zero
        let zero = const_zero::<u8, 2>();
        assert!(const_is_zero(&zero));
        assert!(!const_is_one(&zero));

        // Test one
        let one = const_one::<u8, 2>();
        assert!(!const_is_zero(&one));
        assert!(const_is_one(&one));

        // Test min/max
        let min = const_min_value::<u8, 2>();
        let max = const_max_value::<u8, 2>();
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
            const ZERO: TestInt = const_zero::<u8, 2>();
            const ONE: TestInt = const_one::<u8, 2>();
            const IS_ZERO_TRUE: bool = const_is_zero(&ZERO);
            const IS_ZERO_FALSE: bool = const_is_zero(&ONE);
            const IS_ONE_TRUE: bool = const_is_one(&ONE);
            const IS_ONE_FALSE: bool = const_is_one(&ZERO);
            const MIN: TestInt = const_min_value::<u8, 2>();
            const MAX: TestInt = const_max_value::<u8, 2>();

            assert_eq!(ZERO.array, [0, 0]);
            assert_eq!(ONE.array, [1, 0]);
            assert!(IS_ZERO_TRUE);
            assert!(!IS_ZERO_FALSE);
            assert!(IS_ONE_TRUE);
            assert!(!IS_ONE_FALSE);
            assert_eq!(MIN.array, [0, 0]);
            assert_eq!(MAX.array, [255, 255]);

            const SET_ZERO_RES: TestInt = {
                let mut v = FixedUInt { array: [42, 0] };
                const_set_zero(&mut v);
                v
            };
            const SET_ONE_RES: TestInt = {
                let mut v = FixedUInt { array: [0, 0] };
                const_set_one(&mut v);
                v
            };
            assert_eq!(SET_ZERO_RES.array, [0, 0]);
            assert_eq!(SET_ONE_RES.array, [1, 0]);
        }
    }
}
