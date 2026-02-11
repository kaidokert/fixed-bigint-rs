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
}
