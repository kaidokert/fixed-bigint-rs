// Copyright 2021 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

c0nst::c0nst! {
    // TODO: num_traits already has ConstZero and ConstOne,
    // Consider if we should use those as a base here
    pub c0nst trait ConstZero {
        fn zero() -> Self;
        fn is_zero(&self) -> bool;
        fn set_zero(&mut self);
    }
    pub c0nst trait ConstOne {
        fn one() -> Self;
        fn is_one(&self) -> bool;
        fn set_one(&mut self);
    }
    pub c0nst trait ConstBounded {
        fn min_value() -> Self;
        fn max_value() -> Self;
    }

    pub c0nst trait ConstOverflowingAdd: Sized + [c0nst] core::ops::Add<Output = Self> {
        /// Returns a tuple of the sum along with a boolean indicating whether an arithmetic overflow would occur.
        /// If an overflow would have occurred then the wrapped value is returned.
        fn overflowing_add(&self, v: &Self) -> (Self, bool);
    }

    pub c0nst trait ConstOverflowingSub: Sized + [c0nst] core::ops::Sub<Output = Self> {
        /// Returns a tuple of the difference along with a boolean indicating whether an arithmetic overflow would occur.
        /// If an overflow would have occurred then the wrapped value is returned.
        fn overflowing_sub(&self, v: &Self) -> (Self, bool);
    }

    pub c0nst trait ConstWrappingAdd: Sized + [c0nst] ConstOverflowingAdd {
        /// Wrapping (modular) addition. Computes `self + other`, wrapping around at the boundary of the type.
        fn wrapping_add(&self, v: &Self) -> Self;
    }

    pub c0nst trait ConstWrappingSub: Sized + [c0nst] ConstOverflowingSub {
        /// Wrapping (modular) subtraction. Computes `self - other`, wrapping around at the boundary of the type.
        fn wrapping_sub(&self, v: &Self) -> Self;
    }

    pub c0nst trait ConstCheckedAdd: Sized + [c0nst] ConstOverflowingAdd {
        /// Checked addition. Returns `None` if overflow occurred.
        fn checked_add(&self, v: &Self) -> Option<Self>;
    }

    pub c0nst trait ConstCheckedSub: Sized + [c0nst] ConstOverflowingSub {
        /// Checked subtraction. Returns `None` if overflow occurred.
        fn checked_sub(&self, v: &Self) -> Option<Self>;
    }

    pub c0nst trait ConstToBytes {
        type Bytes: Copy + AsRef<[u8]> + AsMut<[u8]>;
        fn to_le_bytes(&self) -> Self::Bytes;
        fn to_be_bytes(&self) -> Self::Bytes;
    }

    /// Base arithmetic traits for constant primitive integers
    pub c0nst trait ConstPrimInt:
        [c0nst] core::ops::Add<Output = Self> +
        [c0nst] core::ops::Sub<Output = Self> +
        [c0nst] core::ops::Mul<Output = Self> +
        [c0nst] core::ops::Div<Output = Self> +
        [c0nst] core::ops::BitAnd<Output = Self> +
        [c0nst] core::ops::BitOr<Output = Self> +
        [c0nst] core::ops::BitXor<Output = Self> +
        [c0nst] core::ops::Not<Output = Self> +
        [c0nst] core::ops::Shl<usize, Output = Self> +
        [c0nst] core::ops::Shr<usize, Output = Self> +
        [c0nst] core::ops::AddAssign +
        [c0nst] core::ops::SubAssign +
        [c0nst] core::ops::BitAndAssign +
        [c0nst] core::ops::BitOrAssign +
        [c0nst] core::ops::BitXorAssign +
        [c0nst] core::ops::ShlAssign<usize> +
        [c0nst] core::ops::ShrAssign<usize> +
        [c0nst] core::cmp::PartialEq +
        [c0nst] core::cmp::Eq +
        [c0nst] core::cmp::PartialOrd +
        [c0nst] core::cmp::Ord +
        [c0nst] core::convert::From<u8> +
        [c0nst] core::default::Default +
        [c0nst] ConstOne +
        [c0nst] ConstZero +
        [c0nst] ConstBounded +
        Sized + Copy {

            fn swap_bytes(self) -> Self;
            fn leading_zeros(self) -> u32;
            fn trailing_zeros(self) -> u32;
            fn count_zeros(self) -> u32;
            fn count_ones(self) -> u32;
    }
}

macro_rules! const_zero_impl {
    ($t:ty, $v:expr) => {
        c0nst::c0nst! {
            impl c0nst ConstZero for $t {
                fn zero() -> Self { $v }
                fn is_zero(&self) -> bool { *self == $v }
                fn set_zero(&mut self) { *self = $v }
            }
        }
    };
}

macro_rules! const_one_impl {
    ($t:ty, $v:expr) => {
        c0nst::c0nst! {
            impl c0nst ConstOne for $t {
                fn one() -> Self { $v }
                fn is_one(&self) -> bool { *self == $v }
                fn set_one(&mut self) { *self = $v }
            }
        }
    };
}

macro_rules! const_bounded_impl {
    ($t:ty, $min:expr, $max:expr) => {
        c0nst::c0nst! {
            impl c0nst ConstBounded for $t {
                fn min_value() -> Self { $min }
                fn max_value() -> Self { $max }
            }
        }
    };
}

macro_rules! const_prim_int_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstPrimInt for $t {
                fn leading_zeros(self) -> u32 { self.leading_zeros() }
                fn trailing_zeros(self) -> u32 { self.trailing_zeros() }
                fn count_zeros(self) -> u32 { self.count_zeros() }
                fn count_ones(self) -> u32 { self.count_ones() }
                fn swap_bytes(self) -> Self { self.swap_bytes() }
            }
        }
    };
}

macro_rules! const_overflowing_add_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstOverflowingAdd for $t {
                fn overflowing_add(&self, v: &Self) -> (Self, bool) {
                    (*self).overflowing_add(*v)
                }
            }
        }
    };
}

macro_rules! const_overflowing_sub_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstOverflowingSub for $t {
                fn overflowing_sub(&self, v: &Self) -> (Self, bool) {
                    (*self).overflowing_sub(*v)
                }
            }
        }
    };
}

const_zero_impl!(u8, 0);
const_zero_impl!(u16, 0);
const_zero_impl!(u32, 0);
const_zero_impl!(u64, 0);
const_zero_impl!(u128, 0);

const_one_impl!(u8, 1);
const_one_impl!(u16, 1);
const_one_impl!(u32, 1);
const_one_impl!(u64, 1);
const_one_impl!(u128, 1);

const_bounded_impl!(u8, u8::MIN, u8::MAX);
const_bounded_impl!(u16, u16::MIN, u16::MAX);
const_bounded_impl!(u32, u32::MIN, u32::MAX);
const_bounded_impl!(u64, u64::MIN, u64::MAX);
const_bounded_impl!(u128, u128::MIN, u128::MAX);

const_overflowing_add_impl!(u8);
const_overflowing_add_impl!(u16);
const_overflowing_add_impl!(u32);
const_overflowing_add_impl!(u64);
const_overflowing_add_impl!(u128);

const_overflowing_sub_impl!(u8);
const_overflowing_sub_impl!(u16);
const_overflowing_sub_impl!(u32);
const_overflowing_sub_impl!(u64);
const_overflowing_sub_impl!(u128);

macro_rules! const_wrapping_add_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstWrappingAdd for $t {
                fn wrapping_add(&self, v: &Self) -> Self {
                    self.overflowing_add(v).0
                }
            }
        }
    };
}

macro_rules! const_wrapping_sub_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstWrappingSub for $t {
                fn wrapping_sub(&self, v: &Self) -> Self {
                    self.overflowing_sub(v).0
                }
            }
        }
    };
}

macro_rules! const_checked_add_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstCheckedAdd for $t {
                fn checked_add(&self, v: &Self) -> Option<Self> {
                    let (res, overflow) = self.overflowing_add(v);
                    if overflow { None } else { Some(res) }
                }
            }
        }
    };
}

macro_rules! const_checked_sub_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstCheckedSub for $t {
                fn checked_sub(&self, v: &Self) -> Option<Self> {
                    let (res, overflow) = self.overflowing_sub(v);
                    if overflow { None } else { Some(res) }
                }
            }
        }
    };
}

const_wrapping_add_impl!(u8);
const_wrapping_add_impl!(u16);
const_wrapping_add_impl!(u32);
const_wrapping_add_impl!(u64);
const_wrapping_add_impl!(u128);

const_wrapping_sub_impl!(u8);
const_wrapping_sub_impl!(u16);
const_wrapping_sub_impl!(u32);
const_wrapping_sub_impl!(u64);
const_wrapping_sub_impl!(u128);

const_checked_add_impl!(u8);
const_checked_add_impl!(u16);
const_checked_add_impl!(u32);
const_checked_add_impl!(u64);
const_checked_add_impl!(u128);

const_checked_sub_impl!(u8);
const_checked_sub_impl!(u16);
const_checked_sub_impl!(u32);
const_checked_sub_impl!(u64);
const_checked_sub_impl!(u128);

macro_rules! const_to_bytes_impl {
    ($t:ty, $n:expr) => {
        c0nst::c0nst! {
            impl c0nst ConstToBytes for $t {
                type Bytes = [u8; $n];
                fn to_le_bytes(&self) -> [u8; $n] { (*self).to_le_bytes() }
                fn to_be_bytes(&self) -> [u8; $n] { (*self).to_be_bytes() }
            }
        }
    };
}

const_to_bytes_impl!(u8, 1);
const_to_bytes_impl!(u16, 2);
const_to_bytes_impl!(u32, 4);
const_to_bytes_impl!(u64, 8);
const_to_bytes_impl!(u128, 16);

const_prim_int_impl!(u8);
const_prim_int_impl!(u16);
const_prim_int_impl!(u32);
const_prim_int_impl!(u64);
const_prim_int_impl!(u128);

#[cfg(test)]
mod tests {
    use super::*;

    c0nst::c0nst! {
        pub c0nst fn add_words<T: [c0nst] ConstPrimInt>(a: T, b: T) -> T {
            a + b
        }

        pub c0nst fn assign_add<T: [c0nst] ConstPrimInt>(a: &mut T, b: T) {
            *a += b;
        }

        pub c0nst fn default_word<T: [c0nst] ConstPrimInt>() -> T {
            T::default()
        }

        pub c0nst fn zero_word<T: [c0nst] ConstZero>() -> T {
            T::zero()
        }

        pub c0nst fn one_word<T: [c0nst] ConstOne>() -> T {
            T::one()
        }

        pub c0nst fn min_word<T: [c0nst] ConstBounded>() -> T {
            T::min_value()
        }

        pub c0nst fn max_word<T: [c0nst] ConstBounded>() -> T {
            T::max_value()
        }

        pub c0nst fn is_zero_word<T: [c0nst] ConstZero>(v: &T) -> bool {
            v.is_zero()
        }

        pub c0nst fn set_zero_word<T: [c0nst] ConstZero>(v: &mut T) {
            v.set_zero();
        }

        pub c0nst fn is_one_word<T: [c0nst] ConstOne>(v: &T) -> bool {
            v.is_one()
        }

        pub c0nst fn set_one_word<T: [c0nst] ConstOne>(v: &mut T) {
            v.set_one();
        }

        pub c0nst fn overflowing_add_word<T: [c0nst] ConstOverflowingAdd>(a: &T, b: &T) -> (T, bool) {
            a.overflowing_add(b)
        }

        pub c0nst fn overflowing_sub_word<T: [c0nst] ConstOverflowingSub>(a: &T, b: &T) -> (T, bool) {
            a.overflowing_sub(b)
        }

        pub c0nst fn to_le_bytes_word<T: [c0nst] ConstToBytes>(v: &T) -> T::Bytes {
            v.to_le_bytes()
        }

        pub c0nst fn to_be_bytes_word<T: [c0nst] ConstToBytes>(v: &T) -> T::Bytes {
            v.to_be_bytes()
        }

        pub c0nst fn wrapping_add_word<T: [c0nst] ConstWrappingAdd>(a: &T, b: &T) -> T {
            a.wrapping_add(b)
        }

        pub c0nst fn wrapping_sub_word<T: [c0nst] ConstWrappingSub>(a: &T, b: &T) -> T {
            a.wrapping_sub(b)
        }

        pub c0nst fn checked_add_word<T: [c0nst] ConstCheckedAdd>(a: &T, b: &T) -> Option<T> {
            a.checked_add(b)
        }

        pub c0nst fn checked_sub_word<T: [c0nst] ConstCheckedSub>(a: &T, b: &T) -> Option<T> {
            a.checked_sub(b)
        }
    }

    #[test]
    fn test_constprimint_ops() {
        assert_eq!(add_words(2u8, 3u8), 5u8);
        assert_eq!(default_word::<u32>(), 0u32);
        assert_eq!(zero_word::<u64>(), 0u64);
        assert_eq!(one_word::<u128>(), 1u128);
        assert_eq!(min_word::<u8>(), 0u8);
        assert_eq!(max_word::<u8>(), 255u8);

        let mut val = 10u8;
        assign_add(&mut val, 5u8);
        assert_eq!(val, 15u8);

        #[cfg(feature = "nightly")]
        {
            const ADD_RES: u8 = add_words(2u8, 3u8);
            const DEFAULT_RES: u32 = default_word::<u32>();
            const ZERO_RES: u64 = zero_word::<u64>();
            const ONE_RES: u128 = one_word::<u128>();
            const MIN_RES: u8 = min_word::<u8>();
            const MAX_RES: u8 = max_word::<u8>();
            const ASSIGN_RES: u8 = {
                let mut v = 10u8;
                assign_add(&mut v, 5u8);
                v
            };
            assert_eq!(ADD_RES, 5u8);
            assert_eq!(DEFAULT_RES, 0u32);
            assert_eq!(ZERO_RES, 0u64);
            assert_eq!(ONE_RES, 1u128);
            assert_eq!(MIN_RES, 0u8);
            assert_eq!(MAX_RES, 255u8);
            assert_eq!(ASSIGN_RES, 15u8);
        }
    }

    #[test]
    fn test_const_zero_one_methods() {
        // Test is_zero
        assert!(is_zero_word(&0u8));
        assert!(!is_zero_word(&1u8));
        assert!(is_zero_word(&0u64));
        assert!(!is_zero_word(&42u64));

        // Test set_zero
        let mut val = 42u32;
        set_zero_word(&mut val);
        assert_eq!(val, 0u32);

        // Test is_one
        assert!(is_one_word(&1u8));
        assert!(!is_one_word(&0u8));
        assert!(!is_one_word(&2u8));
        assert!(is_one_word(&1u128));

        // Test set_one
        let mut val = 0u16;
        set_one_word(&mut val);
        assert_eq!(val, 1u16);

        #[cfg(feature = "nightly")]
        {
            const IS_ZERO_TRUE: bool = is_zero_word(&0u8);
            const IS_ZERO_FALSE: bool = is_zero_word(&1u8);
            const SET_ZERO_RES: u32 = {
                let mut v = 42u32;
                set_zero_word(&mut v);
                v
            };
            const IS_ONE_TRUE: bool = is_one_word(&1u64);
            const IS_ONE_FALSE: bool = is_one_word(&0u64);
            const SET_ONE_RES: u16 = {
                let mut v = 0u16;
                set_one_word(&mut v);
                v
            };
            assert!(IS_ZERO_TRUE);
            assert!(!IS_ZERO_FALSE);
            assert_eq!(SET_ZERO_RES, 0u32);
            assert!(IS_ONE_TRUE);
            assert!(!IS_ONE_FALSE);
            assert_eq!(SET_ONE_RES, 1u16);
        }
    }

    #[test]
    fn test_const_overflowing_ops() {
        // Test overflowing_add without overflow
        let (sum, overflow) = overflowing_add_word(&100u8, &50u8);
        assert_eq!(sum, 150u8);
        assert!(!overflow);

        // Test overflowing_add with overflow
        let (sum, overflow) = overflowing_add_word(&200u8, &100u8);
        assert_eq!(sum, 44u8); // 300 wraps to 44
        assert!(overflow);

        // Test overflowing_sub without overflow
        let (diff, overflow) = overflowing_sub_word(&100u8, &50u8);
        assert_eq!(diff, 50u8);
        assert!(!overflow);

        // Test overflowing_sub with overflow (underflow)
        let (diff, overflow) = overflowing_sub_word(&50u8, &100u8);
        assert_eq!(diff, 206u8); // wraps around
        assert!(overflow);

        // Test with larger types
        let (sum, overflow) = overflowing_add_word(&u64::MAX, &1u64);
        assert_eq!(sum, 0u64);
        assert!(overflow);

        #[cfg(feature = "nightly")]
        {
            const ADD_NO_OVERFLOW: (u8, bool) = overflowing_add_word(&100u8, &50u8);
            const ADD_OVERFLOW: (u8, bool) = overflowing_add_word(&200u8, &100u8);
            const SUB_NO_OVERFLOW: (u8, bool) = overflowing_sub_word(&100u8, &50u8);
            const SUB_OVERFLOW: (u8, bool) = overflowing_sub_word(&50u8, &100u8);

            assert_eq!(ADD_NO_OVERFLOW, (150u8, false));
            assert_eq!(ADD_OVERFLOW, (44u8, true));
            assert_eq!(SUB_NO_OVERFLOW, (50u8, false));
            assert_eq!(SUB_OVERFLOW, (206u8, true));
        }
    }

    #[test]
    fn test_const_to_bytes() {
        // Test to_le_bytes
        let bytes = to_le_bytes_word(&0x12345678u32);
        assert_eq!(bytes.as_ref(), &[0x78, 0x56, 0x34, 0x12]);

        // Test to_be_bytes
        let bytes = to_be_bytes_word(&0x12345678u32);
        assert_eq!(bytes.as_ref(), &[0x12, 0x34, 0x56, 0x78]);

        // Test with u8
        let bytes = to_le_bytes_word(&0xABu8);
        assert_eq!(bytes.as_ref(), &[0xAB]);

        // Test with u64
        let bytes = to_le_bytes_word(&0x0102030405060708u64);
        assert_eq!(
            bytes.as_ref(),
            &[0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01]
        );

        #[cfg(feature = "nightly")]
        {
            const LE_BYTES: [u8; 4] = to_le_bytes_word(&0x12345678u32);
            const BE_BYTES: [u8; 4] = to_be_bytes_word(&0x12345678u32);
            assert_eq!(LE_BYTES, [0x78, 0x56, 0x34, 0x12]);
            assert_eq!(BE_BYTES, [0x12, 0x34, 0x56, 0x78]);
        }
    }

    #[test]
    fn test_const_wrapping_checked_ops() {
        // Test wrapping_add without overflow
        assert_eq!(wrapping_add_word(&100u8, &50u8), 150u8);
        // Test wrapping_add with overflow
        assert_eq!(wrapping_add_word(&200u8, &100u8), 44u8);

        // Test wrapping_sub without overflow
        assert_eq!(wrapping_sub_word(&100u8, &50u8), 50u8);
        // Test wrapping_sub with overflow (underflow)
        assert_eq!(wrapping_sub_word(&50u8, &100u8), 206u8);

        // Test checked_add without overflow
        assert_eq!(checked_add_word(&100u8, &50u8), Some(150u8));
        // Test checked_add with overflow
        assert_eq!(checked_add_word(&200u8, &100u8), None);

        // Test checked_sub without overflow
        assert_eq!(checked_sub_word(&100u8, &50u8), Some(50u8));
        // Test checked_sub with overflow (underflow)
        assert_eq!(checked_sub_word(&50u8, &100u8), None);

        // Test with larger types
        assert_eq!(wrapping_add_word(&u64::MAX, &1u64), 0u64);
        assert_eq!(checked_add_word(&u64::MAX, &1u64), None);

        #[cfg(feature = "nightly")]
        {
            const WRAP_ADD_NO_OVERFLOW: u8 = wrapping_add_word(&100u8, &50u8);
            const WRAP_ADD_OVERFLOW: u8 = wrapping_add_word(&200u8, &100u8);
            const WRAP_SUB_NO_OVERFLOW: u8 = wrapping_sub_word(&100u8, &50u8);
            const WRAP_SUB_OVERFLOW: u8 = wrapping_sub_word(&50u8, &100u8);

            const CHECK_ADD_OK: Option<u8> = checked_add_word(&100u8, &50u8);
            const CHECK_ADD_OVERFLOW: Option<u8> = checked_add_word(&200u8, &100u8);
            const CHECK_SUB_OK: Option<u8> = checked_sub_word(&100u8, &50u8);
            const CHECK_SUB_OVERFLOW: Option<u8> = checked_sub_word(&50u8, &100u8);

            assert_eq!(WRAP_ADD_NO_OVERFLOW, 150u8);
            assert_eq!(WRAP_ADD_OVERFLOW, 44u8);
            assert_eq!(WRAP_SUB_NO_OVERFLOW, 50u8);
            assert_eq!(WRAP_SUB_OVERFLOW, 206u8);

            assert_eq!(CHECK_ADD_OK, Some(150u8));
            assert_eq!(CHECK_ADD_OVERFLOW, None);
            assert_eq!(CHECK_SUB_OK, Some(50u8));
            assert_eq!(CHECK_SUB_OVERFLOW, None);
        }
    }
}
