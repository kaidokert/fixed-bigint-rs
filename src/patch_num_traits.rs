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

// These should be in num_traits
pub trait OverflowingShl: Sized {
    fn overflowing_shl(self, rhs: u32) -> (Self, bool);
}
pub trait OverflowingShr: Sized {
    fn overflowing_shr(self, rhs: u32) -> (Self, bool);
}

macro_rules! overflowing_shift_impl {
    ($trait_name:ident, $method:ident, $t:ty) => {
        impl $trait_name for $t {
            #[inline]
            fn $method(self, rhs: u32) -> ($t, bool) {
                <$t>::$method(self, rhs)
            }
        }
    };
}

overflowing_shift_impl!(OverflowingShl, overflowing_shl, u8);
overflowing_shift_impl!(OverflowingShl, overflowing_shl, u16);
overflowing_shift_impl!(OverflowingShl, overflowing_shl, u32);
overflowing_shift_impl!(OverflowingShl, overflowing_shl, u64);

overflowing_shift_impl!(OverflowingShr, overflowing_shr, u8);
overflowing_shift_impl!(OverflowingShr, overflowing_shr, u16);
overflowing_shift_impl!(OverflowingShr, overflowing_shr, u32);
overflowing_shift_impl!(OverflowingShr, overflowing_shr, u64);

/// Widening multiplication for extended precision arithmetic.
///
/// Multiplies two values and returns the full double-width result as (low, high).
/// This is the non-const version that delegates to [`ConstWideningMul`] implementations.
///
/// [`ConstWideningMul`]: crate::const_numtraits::ConstWideningMul
pub trait WideningMul: Sized {
    type Output;
    /// Calculates the complete product `self * rhs` without overflow.
    ///
    /// Returns `(low, high)` where the full result is `high * 2^BITS + low`.
    fn widening_mul(self, rhs: Self) -> (Self::Output, Self::Output);
}

macro_rules! widening_mul_impl {
    ($t:ty, $double:ty, $bits:expr) => {
        impl WideningMul for $t {
            type Output = Self;
            fn widening_mul(self, rhs: Self) -> (Self, Self) {
                let product = (self as $double) * (rhs as $double);
                (product as $t, (product >> $bits) as $t)
            }
        }
        impl WideningMul for &$t {
            type Output = $t;
            fn widening_mul(self, rhs: Self) -> ($t, $t) {
                <$t as WideningMul>::widening_mul(*self, *rhs)
            }
        }
    };
}

widening_mul_impl!(u8, u16, 8);
widening_mul_impl!(u16, u32, 16);
widening_mul_impl!(u32, u64, 32);
widening_mul_impl!(u64, u128, 64);

/// Carrying multiplication for extended precision arithmetic.
///
/// Provides multiply-accumulate operations returning double-width results.
/// This is the non-const version that delegates to [`ConstCarryingMul`] implementations.
///
/// [`ConstCarryingMul`]: crate::const_numtraits::ConstCarryingMul
pub trait CarryingMul: Sized {
    type Output;
    /// Calculates `self * rhs + carry`, returning `(low, high)`.
    ///
    /// The result fits in double-width (2 * BITS) since
    /// `MAX * MAX + MAX < (MAX+1)^2 = 2^(2*BITS)`.
    fn carrying_mul(self, rhs: Self, carry: Self) -> (Self::Output, Self::Output);

    /// Calculates `self * rhs + addend + carry`, returning `(low, high)`.
    ///
    /// The result fits in double-width (2 * BITS) since
    /// `MAX * MAX + MAX + MAX < (MAX+1)^2 = 2^(2*BITS)`.
    fn carrying_mul_add(self, rhs: Self, addend: Self, carry: Self)
        -> (Self::Output, Self::Output);
}

macro_rules! carrying_mul_impl {
    ($t:ty, $double:ty, $bits:expr) => {
        impl CarryingMul for $t {
            type Output = Self;
            fn carrying_mul(self, rhs: Self, carry: Self) -> (Self, Self) {
                let product = (self as $double) * (rhs as $double) + (carry as $double);
                (product as $t, (product >> $bits) as $t)
            }

            fn carrying_mul_add(self, rhs: Self, addend: Self, carry: Self) -> (Self, Self) {
                let product =
                    (self as $double) * (rhs as $double) + (addend as $double) + (carry as $double);
                (product as $t, (product >> $bits) as $t)
            }
        }
        impl CarryingMul for &$t {
            type Output = $t;
            fn carrying_mul(self, rhs: Self, carry: Self) -> ($t, $t) {
                <$t as CarryingMul>::carrying_mul(*self, *rhs, *carry)
            }
            fn carrying_mul_add(self, rhs: Self, addend: Self, carry: Self) -> ($t, $t) {
                <$t as CarryingMul>::carrying_mul_add(*self, *rhs, *addend, *carry)
            }
        }
    };
}

carrying_mul_impl!(u8, u16, 8);
carrying_mul_impl!(u16, u32, 16);
carrying_mul_impl!(u32, u64, 32);
carrying_mul_impl!(u64, u128, 64);
