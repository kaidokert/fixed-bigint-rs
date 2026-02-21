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

    pub c0nst trait ConstSaturatingAdd: Sized + [c0nst] ConstOverflowingAdd + [c0nst] ConstBounded {
        /// Saturating addition. Computes `self + other`, saturating at max_value().
        fn saturating_add(&self, v: &Self) -> Self;
    }

    pub c0nst trait ConstSaturatingSub: Sized + [c0nst] ConstOverflowingSub + [c0nst] ConstZero {
        /// Saturating subtraction. Computes `self - other`, saturating at zero.
        fn saturating_sub(&self, v: &Self) -> Self;
    }

    pub c0nst trait ConstOverflowingMul: Sized + [c0nst] core::ops::Mul<Output = Self> {
        /// Returns a tuple of the product along with a boolean indicating whether an arithmetic overflow would occur.
        /// If an overflow would have occurred then the wrapped value is returned.
        fn overflowing_mul(&self, v: &Self) -> (Self, bool);
    }

    pub c0nst trait ConstWrappingMul: Sized + [c0nst] ConstOverflowingMul {
        /// Wrapping (modular) multiplication. Computes `self * other`, wrapping around at the boundary of the type.
        fn wrapping_mul(&self, v: &Self) -> Self;
    }

    pub c0nst trait ConstCheckedMul: Sized + [c0nst] ConstOverflowingMul {
        /// Checked multiplication. Returns `None` if overflow occurred.
        fn checked_mul(&self, v: &Self) -> Option<Self>;
    }

    pub c0nst trait ConstSaturatingMul: Sized + [c0nst] ConstOverflowingMul + [c0nst] ConstBounded {
        /// Saturating multiplication. Computes `self * other`, saturating at max_value().
        fn saturating_mul(&self, v: &Self) -> Self;
    }

    pub c0nst trait ConstCheckedDiv: Sized + [c0nst] core::ops::Div<Output = Self> + [c0nst] ConstZero {
        /// Checked division. Returns `None` if the divisor is zero.
        fn checked_div(&self, v: &Self) -> Option<Self>;
    }

    pub c0nst trait ConstCheckedRem: Sized + [c0nst] core::ops::Rem<Output = Self> + [c0nst] ConstZero {
        /// Checked remainder. Returns `None` if the divisor is zero.
        fn checked_rem(&self, v: &Self) -> Option<Self>;
    }

    pub c0nst trait ConstEuclid: Sized + [c0nst] core::ops::Div<Output = Self> + [c0nst] core::ops::Rem<Output = Self> {
        /// Euclidean division. For unsigned integers, same as regular division.
        fn div_euclid(&self, v: &Self) -> Self;
        /// Euclidean remainder. For unsigned integers, same as regular remainder.
        fn rem_euclid(&self, v: &Self) -> Self;
    }

    pub c0nst trait ConstCheckedEuclid: Sized + [c0nst] ConstEuclid + [c0nst] ConstZero {
        /// Checked Euclidean division. Returns `None` if the divisor is zero.
        fn checked_div_euclid(&self, v: &Self) -> Option<Self>;
        /// Checked Euclidean remainder. Returns `None` if the divisor is zero.
        fn checked_rem_euclid(&self, v: &Self) -> Option<Self>;
    }

    pub c0nst trait ConstOverflowingShl: Sized + [c0nst] core::ops::Shl<u32, Output = Self> {
        /// Shift left with overflow detection.
        /// Returns the shifted value and whether the shift amount exceeded the bit width.
        fn overflowing_shl(&self, rhs: u32) -> (Self, bool);
    }

    pub c0nst trait ConstOverflowingShr: Sized + [c0nst] core::ops::Shr<u32, Output = Self> {
        /// Shift right with overflow detection.
        /// Returns the shifted value and whether the shift amount exceeded the bit width.
        fn overflowing_shr(&self, rhs: u32) -> (Self, bool);
    }

    pub c0nst trait ConstWrappingShl: Sized + [c0nst] ConstOverflowingShl {
        /// Wrapping shift left. Shifts, masking the shift amount to the bit width.
        fn wrapping_shl(&self, rhs: u32) -> Self;
    }

    pub c0nst trait ConstWrappingShr: Sized + [c0nst] ConstOverflowingShr {
        /// Wrapping shift right. Shifts, masking the shift amount to the bit width.
        fn wrapping_shr(&self, rhs: u32) -> Self;
    }

    pub c0nst trait ConstCheckedShl: Sized + [c0nst] ConstOverflowingShl {
        /// Checked shift left. Returns `None` if the shift amount exceeds bit width.
        fn checked_shl(&self, rhs: u32) -> Option<Self>;
    }

    pub c0nst trait ConstCheckedShr: Sized + [c0nst] ConstOverflowingShr {
        /// Checked shift right. Returns `None` if the shift amount exceeds bit width.
        fn checked_shr(&self, rhs: u32) -> Option<Self>;
    }

    pub c0nst trait ConstToBytes {
        type Bytes: Copy + [c0nst] AsRef<[u8]> + [c0nst] AsMut<[u8]>;
        fn to_le_bytes(&self) -> Self::Bytes;
        fn to_be_bytes(&self) -> Self::Bytes;
    }

    /// Const-compatible power-of-two operations.
    ///
    /// These methods mirror the inherent methods on primitive integers
    /// but are not part of num_traits.
    ///
    /// # Unsigned types only
    ///
    /// This trait is designed for unsigned integer types. Implementing it for
    /// signed types may produce unexpected results (e.g., negative values are
    /// never powers of two, and `next_power_of_two` behavior is undefined for
    /// negative inputs).
    pub c0nst trait ConstPowerOfTwo: Sized + [c0nst] ConstZero + [c0nst] ConstOne {
        /// Returns `true` if `self` is a power of two.
        ///
        /// Zero is not a power of two.
        fn is_power_of_two(&self) -> bool;

        /// Returns the smallest power of two greater than or equal to `self`.
        ///
        /// # Panics
        ///
        /// Panics if the result overflows (i.e., `self > (1 << (bits-1))`).
        fn next_power_of_two(self) -> Self;

        /// Returns the smallest power of two greater than or equal to `self`.
        ///
        /// Returns `None` if the result would overflow.
        fn checked_next_power_of_two(self) -> Option<Self>;
    }

    /// Const-compatible absolute difference.
    ///
    /// Computes the absolute difference between two values. For unsigned types,
    /// this is `max(a, b) - min(a, b)`.
    ///
    /// # Unsigned types only
    ///
    /// This trait is designed for unsigned integer types where `abs_diff` cannot
    /// overflow. Implementors for signed types must ensure overflow is handled
    /// correctly (e.g., by returning an unsigned result type or using checked
    /// arithmetic), as the trait bounds do not enforce this.
    pub c0nst trait ConstAbsDiff: Sized + [c0nst] core::cmp::Ord + [c0nst] core::ops::Sub<Output = Self> {
        /// Computes the absolute difference between `self` and `other`.
        fn abs_diff(self, other: Self) -> Self;
    }

    /// Const-compatible checked exponentiation.
    ///
    /// Returns `None` if the result would overflow.
    pub c0nst trait ConstCheckedPow: Sized + [c0nst] ConstOne + [c0nst] ConstCheckedMul {
        /// Checked exponentiation. Computes `self.pow(exp)`, returning `None`
        /// if overflow occurred.
        fn checked_pow(self, exp: u32) -> Option<Self>;
    }

    /// Const-compatible integer logarithm operations.
    ///
    /// # Unsigned types only
    ///
    /// This trait is designed for unsigned integer types. The logarithm of zero
    /// is undefined and will panic (or return `None` for checked variants).
    pub c0nst trait ConstIlog: Sized + [c0nst] ConstZero + [c0nst] ConstOne + [c0nst] core::cmp::Ord + [c0nst] core::ops::Div<Output = Self> {
        /// Returns the base 2 logarithm of the number, rounded down.
        ///
        /// # Panics
        ///
        /// Panics if `self` is zero.
        fn ilog2(self) -> u32;

        /// Returns the base 10 logarithm of the number, rounded down.
        ///
        /// # Panics
        ///
        /// Panics if `self` is zero.
        fn ilog10(self) -> u32;

        /// Returns the logarithm of the number with respect to an arbitrary base,
        /// rounded down.
        ///
        /// # Panics
        ///
        /// Panics if `self` is zero, or if `base` is less than 2.
        fn ilog(self, base: Self) -> u32;

        /// Returns the base 2 logarithm of the number, rounded down.
        ///
        /// Returns `None` if `self` is zero.
        fn checked_ilog2(self) -> Option<u32>;

        /// Returns the base 10 logarithm of the number, rounded down.
        ///
        /// Returns `None` if `self` is zero.
        fn checked_ilog10(self) -> Option<u32>;

        /// Returns the logarithm of the number with respect to an arbitrary base,
        /// rounded down.
        ///
        /// Returns `None` if `self` is zero, or if `base` is less than 2.
        fn checked_ilog(self, base: Self) -> Option<u32>;
    }

    /// Const-compatible multiple-of operations.
    ///
    /// # Unsigned types only
    ///
    /// This trait is designed for unsigned integer types.
    pub c0nst trait ConstMultiple: Sized + [c0nst] ConstZero + [c0nst] core::ops::Rem<Output = Self> + [c0nst] core::ops::Add<Output = Self> + [c0nst] core::ops::Sub<Output = Self> + [c0nst] core::cmp::Eq {
        /// Returns `true` if `self` is a multiple of `rhs`.
        ///
        /// Returns `false` if `rhs` is zero.
        fn is_multiple_of(&self, rhs: &Self) -> bool;

        /// Returns the smallest value greater than or equal to `self` that
        /// is a multiple of `rhs`.
        ///
        /// # Panics
        ///
        /// Panics if `rhs` is zero, or if the result would overflow.
        fn next_multiple_of(self, rhs: Self) -> Self;

        /// Returns the smallest value greater than or equal to `self` that
        /// is a multiple of `rhs`.
        ///
        /// Returns `None` if `rhs` is zero, or if the result would overflow.
        fn checked_next_multiple_of(self, rhs: Self) -> Option<Self>;
    }

    /// Const-compatible ceiling division.
    ///
    /// Returns the smallest integer greater than or equal to the exact quotient.
    pub c0nst trait ConstDivCeil: Sized + [c0nst] ConstZero + [c0nst] ConstOne + [c0nst] ConstCheckedAdd {
        /// Calculates the quotient of `self` and `rhs`, rounding up.
        ///
        /// # Panics
        ///
        /// Panics if `rhs` is zero.
        fn div_ceil(self, rhs: Self) -> Self;

        /// Calculates the quotient of `self` and `rhs`, rounding up.
        ///
        /// Returns `None` if `rhs` is zero.
        fn checked_div_ceil(self, rhs: Self) -> Option<Self>;
    }

    /// Const-compatible integer square root for unsigned integers.
    ///
    /// Returns the largest integer `r` such that `r * r <= self`.
    pub c0nst trait ConstIsqrt: Sized + [c0nst] ConstZero {
        /// Returns the integer square root of `self`.
        fn isqrt(self) -> Self;

        /// Returns the integer square root of `self`.
        ///
        /// For unsigned types, this always returns `Some`. The checked variant
        /// exists for API consistency with signed types where negative values
        /// would return `None`.
        fn checked_isqrt(self) -> Option<Self>;
    }

    /// Const-compatible addition with carry for extended precision arithmetic.
    ///
    /// Performs `self + rhs + carry`, returning the sum and output carry.
    /// This is a full adder operation useful for multi-word addition.
    pub c0nst trait ConstCarryingAdd: Sized {
        /// Calculates `self + rhs + carry`, returning `(sum, carry_out)`.
        ///
        /// The `carry` input should be `false` for normal addition or `true`
        /// to add an additional 1 (carry from a previous addition).
        fn carrying_add(self, rhs: Self, carry: bool) -> (Self, bool);
    }

    /// Const-compatible subtraction with borrow for extended precision arithmetic.
    ///
    /// Performs `self - rhs - borrow`, returning the difference and output borrow.
    /// This is a full subtractor operation useful for multi-word subtraction.
    pub c0nst trait ConstBorrowingSub: Sized {
        /// Calculates `self - rhs - borrow`, returning `(difference, borrow_out)`.
        ///
        /// The `borrow` input should be `false` for normal subtraction or `true`
        /// to subtract an additional 1 (borrow from a previous subtraction).
        fn borrowing_sub(self, rhs: Self, borrow: bool) -> (Self, bool);
    }

    /// Const-compatible widening multiplication for extended precision arithmetic.
    ///
    /// Multiplies two values and returns the full double-width result as (low, high).
    pub c0nst trait ConstWideningMul: Sized {
        /// Calculates the complete product `self * rhs` without overflow.
        ///
        /// Returns `(low, high)` where the full result is `high * 2^BITS + low`.
        fn widening_mul(self, rhs: Self) -> (Self, Self);
    }

    /// Const-compatible carrying multiplication for extended precision arithmetic.
    ///
    /// Provides multiply-accumulate operations returning double-width results.
    pub c0nst trait ConstCarryingMul: Sized {
        /// Calculates `self * rhs + carry`, returning `(low, high)`.
        ///
        /// The result fits in double-width (2 * BITS) since
        /// `MAX * MAX + MAX < (MAX+1)^2 = 2^(2*BITS)`.
        fn carrying_mul(self, rhs: Self, carry: Self) -> (Self, Self);

        /// Calculates `self * rhs + addend + carry`, returning `(low, high)`.
        ///
        /// The result fits in double-width (2 * BITS) since
        /// `MAX * MAX + MAX + MAX < (MAX+1)^2 = 2^(2*BITS)`.
        fn carrying_mul_add(self, rhs: Self, addend: Self, carry: Self) -> (Self, Self);
    }

    /// Const-compatible midpoint calculation.
    ///
    /// Computes the average of two values, rounded down, without overflow.
    /// Stable since Rust 1.85.0.
    pub c0nst trait ConstMidpoint: Sized {
        /// Calculates the midpoint (average) of `self` and `rhs`, rounded down.
        ///
        /// This never overflows, even for values close to the maximum.
        fn midpoint(self, rhs: Self) -> Self;
    }

    /// Const-compatible unbounded shift operations.
    ///
    /// Unlike regular shifts, unbounded shifts don't panic when the shift
    /// amount exceeds the bit width. Instead:
    /// - `unbounded_shl(n)` returns 0 when n >= BITS (all bits shifted out)
    /// - `unbounded_shr(n)` returns 0 when n >= BITS (all bits shifted out)
    pub c0nst trait ConstUnboundedShift: Sized {
        /// Unbounded shift left. Returns 0 if `rhs` is greater than or equal to the bit width of the type.
        fn unbounded_shl(self, rhs: u32) -> Self;

        /// Unbounded shift right. Returns 0 if `rhs` is greater than or equal to the bit width of the type.
        fn unbounded_shr(self, rhs: u32) -> Self;
    }

    /// Base arithmetic traits for constant primitive integers.
    ///
    /// # Implementor requirements for default methods
    ///
    /// The default implementations of `leading_ones` and `trailing_ones` rely on
    /// `!self` (bitwise NOT) producing a value with the same fixed bit-width, and
    /// `leading_zeros`/`trailing_zeros` counting from the MSB/LSB of that full
    /// representation. This is correct for all fixed-width unsigned integers
    /// (primitives and `FixedUInt`), but implementors of custom types should
    /// verify these assumptions hold or override the defaults.
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

            // PR 1: Shifts, rotations, and trivial derivations
            fn leading_ones(self) -> u32 {
                (!self).leading_zeros()
            }
            fn trailing_ones(self) -> u32 {
                (!self).trailing_zeros()
            }
            fn rotate_left(self, n: u32) -> Self;
            fn rotate_right(self, n: u32) -> Self;
            fn unsigned_shl(self, n: u32) -> Self;
            fn unsigned_shr(self, n: u32) -> Self;
            fn signed_shl(self, n: u32) -> Self {
                self.unsigned_shl(n)
            }
            fn signed_shr(self, n: u32) -> Self {
                self.unsigned_shr(n)
            }

            // PR 2: Endianness conversions, reverse_bits, pow
            fn reverse_bits(self) -> Self;
            fn from_be(x: Self) -> Self;
            fn from_le(x: Self) -> Self;
            fn to_be(self) -> Self;
            fn to_le(self) -> Self;
            fn pow(self, exp: u32) -> Self;
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
                fn rotate_left(self, n: u32) -> Self { self.rotate_left(n) }
                fn rotate_right(self, n: u32) -> Self { self.rotate_right(n) }
                fn unsigned_shl(self, n: u32) -> Self { self << n }
                fn unsigned_shr(self, n: u32) -> Self { self >> n }
                fn reverse_bits(self) -> Self { self.reverse_bits() }
                fn from_be(x: Self) -> Self { <$t>::from_be(x) }
                fn from_le(x: Self) -> Self { <$t>::from_le(x) }
                fn to_be(self) -> Self { self.to_be() }
                fn to_le(self) -> Self { self.to_le() }
                fn pow(self, exp: u32) -> Self { self.pow(exp) }
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

macro_rules! const_saturating_add_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstSaturatingAdd for $t {
                fn saturating_add(&self, v: &Self) -> Self {
                    let (res, overflow) = self.overflowing_add(v);
                    if overflow { Self::max_value() } else { res }
                }
            }
        }
    };
}

macro_rules! const_saturating_sub_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstSaturatingSub for $t {
                fn saturating_sub(&self, v: &Self) -> Self {
                    let (res, overflow) = self.overflowing_sub(v);
                    if overflow { Self::zero() } else { res }
                }
            }
        }
    };
}

const_saturating_add_impl!(u8);
const_saturating_add_impl!(u16);
const_saturating_add_impl!(u32);
const_saturating_add_impl!(u64);
const_saturating_add_impl!(u128);

const_saturating_sub_impl!(u8);
const_saturating_sub_impl!(u16);
const_saturating_sub_impl!(u32);
const_saturating_sub_impl!(u64);
const_saturating_sub_impl!(u128);

macro_rules! const_overflowing_mul_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstOverflowingMul for $t {
                fn overflowing_mul(&self, v: &Self) -> (Self, bool) {
                    (*self).overflowing_mul(*v)
                }
            }
        }
    };
}

macro_rules! const_wrapping_mul_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstWrappingMul for $t {
                fn wrapping_mul(&self, v: &Self) -> Self {
                    self.overflowing_mul(v).0
                }
            }
        }
    };
}

macro_rules! const_checked_mul_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstCheckedMul for $t {
                fn checked_mul(&self, v: &Self) -> Option<Self> {
                    let (res, overflow) = self.overflowing_mul(v);
                    if overflow { None } else { Some(res) }
                }
            }
        }
    };
}

macro_rules! const_saturating_mul_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstSaturatingMul for $t {
                fn saturating_mul(&self, v: &Self) -> Self {
                    let (res, overflow) = self.overflowing_mul(v);
                    if overflow { Self::max_value() } else { res }
                }
            }
        }
    };
}

const_overflowing_mul_impl!(u8);
const_overflowing_mul_impl!(u16);
const_overflowing_mul_impl!(u32);
const_overflowing_mul_impl!(u64);
const_overflowing_mul_impl!(u128);

const_wrapping_mul_impl!(u8);
const_wrapping_mul_impl!(u16);
const_wrapping_mul_impl!(u32);
const_wrapping_mul_impl!(u64);
const_wrapping_mul_impl!(u128);

const_checked_mul_impl!(u8);
const_checked_mul_impl!(u16);
const_checked_mul_impl!(u32);
const_checked_mul_impl!(u64);
const_checked_mul_impl!(u128);

const_saturating_mul_impl!(u8);
const_saturating_mul_impl!(u16);
const_saturating_mul_impl!(u32);
const_saturating_mul_impl!(u64);
const_saturating_mul_impl!(u128);

macro_rules! const_checked_div_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstCheckedDiv for $t {
                fn checked_div(&self, v: &Self) -> Option<Self> {
                    if v.is_zero() { None } else { Some(*self / *v) }
                }
            }
        }
    };
}

macro_rules! const_checked_rem_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstCheckedRem for $t {
                fn checked_rem(&self, v: &Self) -> Option<Self> {
                    if v.is_zero() { None } else { Some(*self % *v) }
                }
            }
        }
    };
}

const_checked_div_impl!(u8);
const_checked_div_impl!(u16);
const_checked_div_impl!(u32);
const_checked_div_impl!(u64);
const_checked_div_impl!(u128);

const_checked_rem_impl!(u8);
const_checked_rem_impl!(u16);
const_checked_rem_impl!(u32);
const_checked_rem_impl!(u64);
const_checked_rem_impl!(u128);

macro_rules! const_euclid_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstEuclid for $t {
                fn div_euclid(&self, v: &Self) -> Self {
                    // For unsigned integers, Euclidean division is the same as regular division
                    *self / *v
                }
                fn rem_euclid(&self, v: &Self) -> Self {
                    // For unsigned integers, Euclidean remainder is the same as regular remainder
                    *self % *v
                }
            }
        }
    };
}

macro_rules! const_checked_euclid_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstCheckedEuclid for $t {
                fn checked_div_euclid(&self, v: &Self) -> Option<Self> {
                    if v.is_zero() { None } else { Some(*self / *v) }
                }
                fn checked_rem_euclid(&self, v: &Self) -> Option<Self> {
                    if v.is_zero() { None } else { Some(*self % *v) }
                }
            }
        }
    };
}

const_euclid_impl!(u8);
const_euclid_impl!(u16);
const_euclid_impl!(u32);
const_euclid_impl!(u64);
const_euclid_impl!(u128);

const_checked_euclid_impl!(u8);
const_checked_euclid_impl!(u16);
const_checked_euclid_impl!(u32);
const_checked_euclid_impl!(u64);
const_checked_euclid_impl!(u128);

macro_rules! const_overflowing_shl_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstOverflowingShl for $t {
                fn overflowing_shl(&self, rhs: u32) -> (Self, bool) {
                    (*self).overflowing_shl(rhs)
                }
            }
        }
    };
}

macro_rules! const_overflowing_shr_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstOverflowingShr for $t {
                fn overflowing_shr(&self, rhs: u32) -> (Self, bool) {
                    (*self).overflowing_shr(rhs)
                }
            }
        }
    };
}

macro_rules! const_wrapping_shl_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstWrappingShl for $t {
                fn wrapping_shl(&self, rhs: u32) -> Self {
                    ConstOverflowingShl::overflowing_shl(self, rhs).0
                }
            }
        }
    };
}

macro_rules! const_wrapping_shr_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstWrappingShr for $t {
                fn wrapping_shr(&self, rhs: u32) -> Self {
                    ConstOverflowingShr::overflowing_shr(self, rhs).0
                }
            }
        }
    };
}

macro_rules! const_checked_shl_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstCheckedShl for $t {
                fn checked_shl(&self, rhs: u32) -> Option<Self> {
                    let (res, overflow) = ConstOverflowingShl::overflowing_shl(self, rhs);
                    if overflow { None } else { Some(res) }
                }
            }
        }
    };
}

macro_rules! const_checked_shr_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstCheckedShr for $t {
                fn checked_shr(&self, rhs: u32) -> Option<Self> {
                    let (res, overflow) = ConstOverflowingShr::overflowing_shr(self, rhs);
                    if overflow { None } else { Some(res) }
                }
            }
        }
    };
}

const_overflowing_shl_impl!(u8);
const_overflowing_shl_impl!(u16);
const_overflowing_shl_impl!(u32);
const_overflowing_shl_impl!(u64);
const_overflowing_shl_impl!(u128);

const_overflowing_shr_impl!(u8);
const_overflowing_shr_impl!(u16);
const_overflowing_shr_impl!(u32);
const_overflowing_shr_impl!(u64);
const_overflowing_shr_impl!(u128);

const_wrapping_shl_impl!(u8);
const_wrapping_shl_impl!(u16);
const_wrapping_shl_impl!(u32);
const_wrapping_shl_impl!(u64);
const_wrapping_shl_impl!(u128);

const_wrapping_shr_impl!(u8);
const_wrapping_shr_impl!(u16);
const_wrapping_shr_impl!(u32);
const_wrapping_shr_impl!(u64);
const_wrapping_shr_impl!(u128);

const_checked_shl_impl!(u8);
const_checked_shl_impl!(u16);
const_checked_shl_impl!(u32);
const_checked_shl_impl!(u64);
const_checked_shl_impl!(u128);

const_checked_shr_impl!(u8);
const_checked_shr_impl!(u16);
const_checked_shr_impl!(u32);
const_checked_shr_impl!(u64);
const_checked_shr_impl!(u128);

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

macro_rules! const_power_of_two_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstPowerOfTwo for $t {
                fn is_power_of_two(&self) -> bool {
                    (*self).is_power_of_two()
                }
                fn next_power_of_two(self) -> Self {
                    self.next_power_of_two()
                }
                fn checked_next_power_of_two(self) -> Option<Self> {
                    self.checked_next_power_of_two()
                }
            }
        }
    };
}

const_power_of_two_impl!(u8);
const_power_of_two_impl!(u16);
const_power_of_two_impl!(u32);
const_power_of_two_impl!(u64);
const_power_of_two_impl!(u128);

macro_rules! const_abs_diff_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstAbsDiff for $t {
                fn abs_diff(self, other: Self) -> Self {
                    <$t>::abs_diff(self, other)
                }
            }
        }
    };
}

const_abs_diff_impl!(u8);
const_abs_diff_impl!(u16);
const_abs_diff_impl!(u32);
const_abs_diff_impl!(u64);
const_abs_diff_impl!(u128);

macro_rules! const_checked_pow_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstCheckedPow for $t {
                fn checked_pow(self, exp: u32) -> Option<Self> {
                    self.checked_pow(exp)
                }
            }
        }
    };
}

const_checked_pow_impl!(u8);
const_checked_pow_impl!(u16);
const_checked_pow_impl!(u32);
const_checked_pow_impl!(u64);
const_checked_pow_impl!(u128);

macro_rules! const_ilog_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstIlog for $t {
                fn ilog2(self) -> u32 {
                    self.ilog2()
                }
                fn ilog10(self) -> u32 {
                    self.ilog10()
                }
                fn ilog(self, base: Self) -> u32 {
                    self.ilog(base)
                }
                fn checked_ilog2(self) -> Option<u32> {
                    self.checked_ilog2()
                }
                fn checked_ilog10(self) -> Option<u32> {
                    self.checked_ilog10()
                }
                fn checked_ilog(self, base: Self) -> Option<u32> {
                    self.checked_ilog(base)
                }
            }
        }
    };
}

const_ilog_impl!(u8);
const_ilog_impl!(u16);
const_ilog_impl!(u32);
const_ilog_impl!(u64);
const_ilog_impl!(u128);

// Native is_multiple_of() requires Rust 1.87+, gate behind 1_87 feature
#[cfg(not(feature = "1_87"))]
macro_rules! const_multiple_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstMultiple for $t {
                fn is_multiple_of(&self, rhs: &Self) -> bool {
                    if rhs.is_zero() {
                        false
                    } else {
                        *self % *rhs == 0
                    }
                }
                fn next_multiple_of(self, rhs: Self) -> Self {
                    self.next_multiple_of(rhs)
                }
                fn checked_next_multiple_of(self, rhs: Self) -> Option<Self> {
                    self.checked_next_multiple_of(rhs)
                }
            }
        }
    };
}

#[cfg(feature = "1_87")]
macro_rules! const_multiple_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstMultiple for $t {
                fn is_multiple_of(&self, rhs: &Self) -> bool {
                    <$t>::is_multiple_of(*self, *rhs)
                }
                fn next_multiple_of(self, rhs: Self) -> Self {
                    self.next_multiple_of(rhs)
                }
                fn checked_next_multiple_of(self, rhs: Self) -> Option<Self> {
                    self.checked_next_multiple_of(rhs)
                }
            }
        }
    };
}

const_multiple_impl!(u8);
const_multiple_impl!(u16);
const_multiple_impl!(u32);
const_multiple_impl!(u64);
const_multiple_impl!(u128);

macro_rules! const_div_ceil_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstDivCeil for $t {
                fn div_ceil(self, rhs: Self) -> Self {
                    <$t>::div_ceil(self, rhs)
                }
                fn checked_div_ceil(self, rhs: Self) -> Option<Self> {
                    if rhs.is_zero() {
                        None
                    } else {
                        Some(<$t>::div_ceil(self, rhs))
                    }
                }
            }
        }
    };
}

const_div_ceil_impl!(u8);
const_div_ceil_impl!(u16);
const_div_ceil_impl!(u32);
const_div_ceil_impl!(u64);
const_div_ceil_impl!(u128);

// Primitive isqrt requires Rust 1.84+, gate behind nightly
#[cfg(feature = "nightly")]
macro_rules! const_isqrt_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstIsqrt for $t {
                fn isqrt(self) -> Self {
                    <$t>::isqrt(self)
                }
                fn checked_isqrt(self) -> Option<Self> {
                    // For unsigned types, isqrt always succeeds
                    Some(<$t>::isqrt(self))
                }
            }
        }
    };
}

#[cfg(feature = "nightly")]
const_isqrt_impl!(u8);
#[cfg(feature = "nightly")]
const_isqrt_impl!(u16);
#[cfg(feature = "nightly")]
const_isqrt_impl!(u32);
#[cfg(feature = "nightly")]
const_isqrt_impl!(u64);
#[cfg(feature = "nightly")]
const_isqrt_impl!(u128);

// Extended precision primitive implementations
// Native bigint_helper_methods stable since Rust 1.91.0
#[cfg(not(feature = "nightly"))]
macro_rules! const_carrying_add_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstCarryingAdd for $t {
                fn carrying_add(self, rhs: Self, carry: bool) -> (Self, bool) {
                    let (sum1, c1) = self.overflowing_add(rhs);
                    let (sum2, c2) = sum1.overflowing_add(carry as $t);
                    (sum2, c1 || c2)
                }
            }
        }
    };
}

#[cfg(feature = "nightly")]
macro_rules! const_carrying_add_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstCarryingAdd for $t {
                fn carrying_add(self, rhs: Self, carry: bool) -> (Self, bool) {
                    <$t>::carrying_add(self, rhs, carry)
                }
            }
        }
    };
}

#[cfg(not(feature = "nightly"))]
macro_rules! const_borrowing_sub_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstBorrowingSub for $t {
                fn borrowing_sub(self, rhs: Self, borrow: bool) -> (Self, bool) {
                    let (diff1, b1) = self.overflowing_sub(rhs);
                    let (diff2, b2) = diff1.overflowing_sub(borrow as $t);
                    (diff2, b1 || b2)
                }
            }
        }
    };
}

#[cfg(feature = "nightly")]
macro_rules! const_borrowing_sub_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstBorrowingSub for $t {
                fn borrowing_sub(self, rhs: Self, borrow: bool) -> (Self, bool) {
                    <$t>::borrowing_sub(self, rhs, borrow)
                }
            }
        }
    };
}

#[cfg(not(feature = "nightly"))]
macro_rules! const_widening_mul_impl {
    ($t:ty, $double:ty, $bits:expr) => {
        c0nst::c0nst! {
            impl c0nst ConstWideningMul for $t {
                fn widening_mul(self, rhs: Self) -> (Self, Self) {
                    let product = (self as $double) * (rhs as $double);
                    (product as $t, (product >> $bits) as $t)
                }
            }
        }
    };
}

#[cfg(feature = "nightly")]
macro_rules! const_widening_mul_impl {
    ($t:ty, $double:ty, $bits:expr) => {
        c0nst::c0nst! {
            impl c0nst ConstWideningMul for $t {
                fn widening_mul(self, rhs: Self) -> (Self, Self) {
                    <$t>::widening_mul(self, rhs)
                }
            }
        }
    };
}

#[cfg(not(feature = "nightly"))]
macro_rules! const_carrying_mul_impl {
    ($t:ty, $double:ty, $bits:expr) => {
        c0nst::c0nst! {
            impl c0nst ConstCarryingMul for $t {
                fn carrying_mul(self, rhs: Self, carry: Self) -> (Self, Self) {
                    let product = (self as $double) * (rhs as $double) + (carry as $double);
                    (product as $t, (product >> $bits) as $t)
                }
                fn carrying_mul_add(self, rhs: Self, addend: Self, carry: Self) -> (Self, Self) {
                    let product = (self as $double) * (rhs as $double)
                        + (addend as $double)
                        + (carry as $double);
                    (product as $t, (product >> $bits) as $t)
                }
            }
        }
    };
}

#[cfg(feature = "nightly")]
macro_rules! const_carrying_mul_impl {
    ($t:ty, $double:ty, $bits:expr) => {
        c0nst::c0nst! {
            impl c0nst ConstCarryingMul for $t {
                fn carrying_mul(self, rhs: Self, carry: Self) -> (Self, Self) {
                    <$t>::carrying_mul(self, rhs, carry)
                }
                fn carrying_mul_add(self, rhs: Self, addend: Self, carry: Self) -> (Self, Self) {
                    // No native carrying_mul_add, use carrying_mul + overflowing_add
                    let (lo, hi) = <$t>::carrying_mul(self, rhs, carry);
                    let (lo2, c) = lo.overflowing_add(addend);
                    (lo2, hi.wrapping_add(c as $t))
                }
            }
        }
    };
}

const_carrying_add_impl!(u8);
const_carrying_add_impl!(u16);
const_carrying_add_impl!(u32);
const_carrying_add_impl!(u64);
const_carrying_add_impl!(u128);

const_borrowing_sub_impl!(u8);
const_borrowing_sub_impl!(u16);
const_borrowing_sub_impl!(u32);
const_borrowing_sub_impl!(u64);
const_borrowing_sub_impl!(u128);

const_widening_mul_impl!(u8, u16, 8);
const_widening_mul_impl!(u16, u32, 16);
const_widening_mul_impl!(u32, u64, 32);
const_widening_mul_impl!(u64, u128, 64);
// TODO: u128 widening_mul requires u256 type (not available in Rust)

const_carrying_mul_impl!(u8, u16, 8);
const_carrying_mul_impl!(u16, u32, 16);
const_carrying_mul_impl!(u32, u64, 32);
const_carrying_mul_impl!(u64, u128, 64);
// TODO: u128 carrying_mul requires u256 type (not available in Rust)

// Native midpoint() requires Rust 1.85+, gate behind 1_87 feature
#[cfg(not(feature = "1_87"))]
macro_rules! const_midpoint_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstMidpoint for $t {
                fn midpoint(self, rhs: Self) -> Self {
                    // (a & b) + ((a ^ b) >> 1) avoids overflow
                    (self & rhs) + ((self ^ rhs) >> 1)
                }
            }
        }
    };
}

#[cfg(feature = "1_87")]
macro_rules! const_midpoint_impl {
    ($t:ty) => {
        c0nst::c0nst! {
            impl c0nst ConstMidpoint for $t {
                fn midpoint(self, rhs: Self) -> Self {
                    <$t>::midpoint(self, rhs)
                }
            }
        }
    };
}

const_midpoint_impl!(u8);
const_midpoint_impl!(u16);
const_midpoint_impl!(u32);
const_midpoint_impl!(u64);
const_midpoint_impl!(u128);

// Native unbounded_shl/shr() requires Rust 1.85+, gate behind 1_87 feature
#[cfg(not(feature = "1_87"))]
macro_rules! const_unbounded_shift_impl {
    ($t:ty, $bits:expr) => {
        c0nst::c0nst! {
            impl c0nst ConstUnboundedShift for $t {
                fn unbounded_shl(self, rhs: u32) -> Self {
                    if rhs >= $bits { 0 } else { self << rhs }
                }
                fn unbounded_shr(self, rhs: u32) -> Self {
                    if rhs >= $bits { 0 } else { self >> rhs }
                }
            }
        }
    };
}

#[cfg(feature = "1_87")]
macro_rules! const_unbounded_shift_impl {
    ($t:ty, $bits:expr) => {
        c0nst::c0nst! {
            impl c0nst ConstUnboundedShift for $t {
                fn unbounded_shl(self, rhs: u32) -> Self {
                    <$t>::unbounded_shl(self, rhs)
                }
                fn unbounded_shr(self, rhs: u32) -> Self {
                    <$t>::unbounded_shr(self, rhs)
                }
            }
        }
    };
}

const_unbounded_shift_impl!(u8, 8);
const_unbounded_shift_impl!(u16, 16);
const_unbounded_shift_impl!(u32, 32);
const_unbounded_shift_impl!(u64, 64);
const_unbounded_shift_impl!(u128, 128);

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

        pub c0nst fn saturating_add_word<T: [c0nst] ConstSaturatingAdd>(a: &T, b: &T) -> T {
            a.saturating_add(b)
        }

        pub c0nst fn saturating_sub_word<T: [c0nst] ConstSaturatingSub>(a: &T, b: &T) -> T {
            a.saturating_sub(b)
        }

        pub c0nst fn carrying_add_word<T: [c0nst] ConstCarryingAdd>(a: T, b: T, carry: bool) -> (T, bool) {
            a.carrying_add(b, carry)
        }

        pub c0nst fn borrowing_sub_word<T: [c0nst] ConstBorrowingSub>(a: T, b: T, borrow: bool) -> (T, bool) {
            a.borrowing_sub(b, borrow)
        }

        pub c0nst fn widening_mul_word<T: [c0nst] ConstWideningMul>(a: T, b: T) -> (T, T) {
            a.widening_mul(b)
        }

        pub c0nst fn carrying_mul_word<T: [c0nst] ConstCarryingMul>(a: T, b: T, carry: T) -> (T, T) {
            a.carrying_mul(b, carry)
        }

        pub c0nst fn carrying_mul_add_word<T: [c0nst] ConstCarryingMul>(a: T, b: T, addend: T, carry: T) -> (T, T) {
            a.carrying_mul_add(b, addend, carry)
        }

        pub c0nst fn midpoint_word<T: [c0nst] ConstMidpoint>(a: T, b: T) -> T {
            a.midpoint(b)
        }

        pub c0nst fn unbounded_shl_word<T: [c0nst] ConstUnboundedShift>(a: T, n: u32) -> T {
            a.unbounded_shl(n)
        }

        pub c0nst fn unbounded_shr_word<T: [c0nst] ConstUnboundedShift>(a: T, n: u32) -> T {
            a.unbounded_shr(n)
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

    #[test]
    fn test_const_saturating_ops() {
        // Test saturating_add without overflow
        assert_eq!(saturating_add_word(&100u8, &50u8), 150u8);
        // Test saturating_add with overflow (saturates at max)
        assert_eq!(saturating_add_word(&200u8, &100u8), 255u8);

        // Test saturating_sub without overflow
        assert_eq!(saturating_sub_word(&100u8, &50u8), 50u8);
        // Test saturating_sub with underflow (saturates at zero)
        assert_eq!(saturating_sub_word(&50u8, &100u8), 0u8);

        // Test with larger types
        assert_eq!(saturating_add_word(&u64::MAX, &1u64), u64::MAX);
        assert_eq!(saturating_sub_word(&0u64, &1u64), 0u64);

        #[cfg(feature = "nightly")]
        {
            const SAT_ADD_NO_OVERFLOW: u8 = saturating_add_word(&100u8, &50u8);
            const SAT_ADD_OVERFLOW: u8 = saturating_add_word(&200u8, &100u8);
            const SAT_SUB_NO_OVERFLOW: u8 = saturating_sub_word(&100u8, &50u8);
            const SAT_SUB_OVERFLOW: u8 = saturating_sub_word(&50u8, &100u8);

            assert_eq!(SAT_ADD_NO_OVERFLOW, 150u8);
            assert_eq!(SAT_ADD_OVERFLOW, 255u8);
            assert_eq!(SAT_SUB_NO_OVERFLOW, 50u8);
            assert_eq!(SAT_SUB_OVERFLOW, 0u8);
        }
    }

    #[test]
    fn test_const_carrying_add() {
        // No carry in, no carry out
        let (sum, carry) = carrying_add_word(100u8, 50u8, false);
        assert_eq!(sum, 150u8);
        assert!(!carry);

        // No carry in, carry out
        let (sum, carry) = carrying_add_word(200u8, 100u8, false);
        assert_eq!(sum, 44u8); // 300 wraps to 44
        assert!(carry);

        // Carry in, no carry out
        let (sum, carry) = carrying_add_word(100u8, 50u8, true);
        assert_eq!(sum, 151u8);
        assert!(!carry);

        // Carry in, carry out
        let (sum, carry) = carrying_add_word(200u8, 55u8, true);
        assert_eq!(sum, 0u8); // 256 wraps to 0
        assert!(carry);

        // Edge case: max + 0 + 1 = carry
        let (sum, carry) = carrying_add_word(u8::MAX, 0u8, true);
        assert_eq!(sum, 0u8);
        assert!(carry);

        // Test with larger types
        let (sum, carry) = carrying_add_word(u64::MAX, 0u64, true);
        assert_eq!(sum, 0u64);
        assert!(carry);

        #[cfg(feature = "nightly")]
        {
            const CA_NO_CARRY: (u8, bool) = carrying_add_word(100u8, 50u8, false);
            const CA_CARRY_OUT: (u8, bool) = carrying_add_word(200u8, 100u8, false);
            const CA_CARRY_IN: (u8, bool) = carrying_add_word(100u8, 50u8, true);
            const CA_BOTH_CARRY: (u8, bool) = carrying_add_word(200u8, 55u8, true);

            assert_eq!(CA_NO_CARRY, (150u8, false));
            assert_eq!(CA_CARRY_OUT, (44u8, true));
            assert_eq!(CA_CARRY_IN, (151u8, false));
            assert_eq!(CA_BOTH_CARRY, (0u8, true));
        }
    }

    #[test]
    fn test_const_borrowing_sub() {
        // No borrow in, no borrow out
        let (diff, borrow) = borrowing_sub_word(100u8, 50u8, false);
        assert_eq!(diff, 50u8);
        assert!(!borrow);

        // No borrow in, borrow out
        let (diff, borrow) = borrowing_sub_word(50u8, 100u8, false);
        assert_eq!(diff, 206u8); // wraps around
        assert!(borrow);

        // Borrow in, no borrow out
        let (diff, borrow) = borrowing_sub_word(100u8, 50u8, true);
        assert_eq!(diff, 49u8);
        assert!(!borrow);

        // Borrow in, borrow out
        let (diff, borrow) = borrowing_sub_word(50u8, 50u8, true);
        assert_eq!(diff, 255u8); // 0 - 1 wraps to 255
        assert!(borrow);

        // Edge case: 0 - 0 - 1 = borrow
        let (diff, borrow) = borrowing_sub_word(0u8, 0u8, true);
        assert_eq!(diff, 255u8);
        assert!(borrow);

        // Test with larger types
        let (diff, borrow) = borrowing_sub_word(0u64, 0u64, true);
        assert_eq!(diff, u64::MAX);
        assert!(borrow);

        #[cfg(feature = "nightly")]
        {
            const BS_NO_BORROW: (u8, bool) = borrowing_sub_word(100u8, 50u8, false);
            const BS_BORROW_OUT: (u8, bool) = borrowing_sub_word(50u8, 100u8, false);
            const BS_BORROW_IN: (u8, bool) = borrowing_sub_word(100u8, 50u8, true);
            const BS_BOTH_BORROW: (u8, bool) = borrowing_sub_word(50u8, 50u8, true);

            assert_eq!(BS_NO_BORROW, (50u8, false));
            assert_eq!(BS_BORROW_OUT, (206u8, true));
            assert_eq!(BS_BORROW_IN, (49u8, false));
            assert_eq!(BS_BOTH_BORROW, (255u8, true));
        }
    }

    #[test]
    fn test_const_widening_mul() {
        // Simple multiplication, no high part
        let (lo, hi) = widening_mul_word(10u8, 5u8);
        assert_eq!(lo, 50u8);
        assert_eq!(hi, 0u8);

        // Multiplication with high part
        let (lo, hi) = widening_mul_word(200u8, 3u8);
        assert_eq!(lo, 88u8); // 600 & 0xFF = 88
        assert_eq!(hi, 2u8); // 600 >> 8 = 2

        // Max * max
        let (lo, hi) = widening_mul_word(u8::MAX, u8::MAX);
        // 255 * 255 = 65025 = 0xFE01
        assert_eq!(lo, 0x01u8);
        assert_eq!(hi, 0xFEu8);

        // Test with u16
        let (lo, hi) = widening_mul_word(1000u16, 1000u16);
        // 1000 * 1000 = 1000000 = 0x000F4240
        assert_eq!(lo, 0x4240u16);
        assert_eq!(hi, 0x000Fu16);

        // Test with u64
        let (lo, hi) = widening_mul_word(u64::MAX, 2u64);
        // MAX * 2 = 2 * (2^64 - 1) = 2^65 - 2 = (1, MAX-1)
        assert_eq!(lo, u64::MAX - 1);
        assert_eq!(hi, 1u64);

        #[cfg(feature = "nightly")]
        {
            const WM_SIMPLE: (u8, u8) = widening_mul_word(10u8, 5u8);
            const WM_HIGH: (u8, u8) = widening_mul_word(200u8, 3u8);
            const WM_MAX: (u8, u8) = widening_mul_word(u8::MAX, u8::MAX);

            assert_eq!(WM_SIMPLE, (50u8, 0u8));
            assert_eq!(WM_HIGH, (88u8, 2u8));
            assert_eq!(WM_MAX, (0x01u8, 0xFEu8));
        }
    }

    #[test]
    fn test_const_carrying_mul() {
        // Simple multiplication with no carry
        let (lo, hi) = carrying_mul_word(10u8, 5u8, 0u8);
        assert_eq!(lo, 50u8);
        assert_eq!(hi, 0u8);

        // Multiplication with carry added
        let (lo, hi) = carrying_mul_word(10u8, 5u8, 10u8);
        // 10 * 5 + 10 = 60
        assert_eq!(lo, 60u8);
        assert_eq!(hi, 0u8);

        // Multiplication with high part
        let (lo, hi) = carrying_mul_word(200u8, 3u8, 0u8);
        assert_eq!(lo, 88u8); // 600 & 0xFF
        assert_eq!(hi, 2u8); // 600 >> 8

        // Multiplication with carry causing high part
        let (lo, hi) = carrying_mul_word(200u8, 3u8, 200u8);
        // 200 * 3 + 200 = 800 = 0x0320
        assert_eq!(lo, 0x20u8);
        assert_eq!(hi, 3u8);

        // Max values
        let (lo, hi) = carrying_mul_word(u8::MAX, u8::MAX, u8::MAX);
        // 255 * 255 + 255 = 65280 = 0xFF00
        assert_eq!(lo, 0x00u8);
        assert_eq!(hi, 0xFFu8);

        // Test with u16
        let (lo, hi) = carrying_mul_word(1000u16, 1000u16, 1000u16);
        // 1000 * 1000 + 1000 = 1001000 = 0x000F4628
        assert_eq!(lo, 0x4628u16);
        assert_eq!(hi, 0x000Fu16);

        #[cfg(feature = "nightly")]
        {
            const CM_SIMPLE: (u8, u8) = carrying_mul_word(10u8, 5u8, 0u8);
            const CM_WITH_CARRY: (u8, u8) = carrying_mul_word(10u8, 5u8, 10u8);
            const CM_MAX: (u8, u8) = carrying_mul_word(u8::MAX, u8::MAX, u8::MAX);

            assert_eq!(CM_SIMPLE, (50u8, 0u8));
            assert_eq!(CM_WITH_CARRY, (60u8, 0u8));
            assert_eq!(CM_MAX, (0x00u8, 0xFFu8));
        }
    }

    #[test]
    fn test_const_carrying_mul_add() {
        // Simple: 10 * 5 + 7 + 0 = 57
        let (lo, hi) = carrying_mul_add_word(10u8, 5u8, 7u8, 0u8);
        assert_eq!(lo, 57u8);
        assert_eq!(hi, 0u8);

        // With all params: 10 * 5 + 10 + 10 = 70
        let (lo, hi) = carrying_mul_add_word(10u8, 5u8, 10u8, 10u8);
        assert_eq!(lo, 70u8);
        assert_eq!(hi, 0u8);

        // Addend causes lo overflow: 200 * 3 + 200 + 0 = 800 = 0x0320
        // Then we add extra addend to test lo overflow path
        // 16 * 16 + 0 + 0 = 256 = 0x0100
        let (lo, hi) = carrying_mul_add_word(16u8, 16u8, 0u8, 0u8);
        assert_eq!(lo, 0x00u8);
        assert_eq!(hi, 1u8);

        // Max case: 255 * 255 + 255 + 255 = 65535 = 0xFFFF
        // This exercises hi = 0xFF with addend causing no overflow
        // (since carrying_mul gives lo=0 when hi=0xFF)
        let (lo, hi) = carrying_mul_add_word(u8::MAX, u8::MAX, u8::MAX, u8::MAX);
        // 255 * 255 + 255 = 65280 = 0xFF00, then + 255 = 65535 = 0xFFFF
        assert_eq!(lo, 0xFFu8);
        assert_eq!(hi, 0xFFu8);

        // Test case that would trigger wrapping_add:
        // We need hi to be MAX and carry from lo addition
        // For u8: 255 * 255 + 255 gives (0, 255), then adding 255 gives (255, 255)
        // Since lo=0, adding any addend won't overflow, so hi stays 255
        // The wrapping_add is for safety even though u8 can't trigger it

        #[cfg(feature = "nightly")]
        {
            const CMA_SIMPLE: (u8, u8) = carrying_mul_add_word(10u8, 5u8, 7u8, 0u8);
            const CMA_MAX: (u8, u8) = carrying_mul_add_word(u8::MAX, u8::MAX, u8::MAX, u8::MAX);

            assert_eq!(CMA_SIMPLE, (57u8, 0u8));
            assert_eq!(CMA_MAX, (0xFFu8, 0xFFu8));
        }
    }

    #[test]
    fn test_const_midpoint() {
        // Simple midpoint
        assert_eq!(midpoint_word(0u8, 10u8), 5u8);
        assert_eq!(midpoint_word(10u8, 0u8), 5u8); // order doesn't matter

        // Midpoint rounds down
        assert_eq!(midpoint_word(0u8, 9u8), 4u8); // (0+9)/2 = 4.5 -> 4
        assert_eq!(midpoint_word(1u8, 10u8), 5u8); // (1+10)/2 = 5.5 -> 5

        // Same values
        assert_eq!(midpoint_word(42u8, 42u8), 42u8);

        // Edge cases with max values (no overflow!)
        assert_eq!(midpoint_word(u8::MAX, u8::MAX), u8::MAX);
        assert_eq!(midpoint_word(u8::MAX, u8::MAX - 1), u8::MAX - 1); // rounds down
        assert_eq!(midpoint_word(0u8, u8::MAX), 127u8); // (0+255)/2 = 127.5 -> 127

        // Test with larger types
        assert_eq!(midpoint_word(0u64, 100u64), 50u64);
        assert_eq!(midpoint_word(u64::MAX, u64::MAX), u64::MAX);
        assert_eq!(midpoint_word(u64::MAX - 1, u64::MAX), u64::MAX - 1); // rounds down

        // u128
        assert_eq!(midpoint_word(0u128, u128::MAX), u128::MAX / 2);

        #[cfg(feature = "nightly")]
        {
            const MID_SIMPLE: u8 = midpoint_word(0u8, 10u8);
            const MID_ROUND: u8 = midpoint_word(0u8, 9u8);
            const MID_MAX: u8 = midpoint_word(u8::MAX, u8::MAX);
            const MID_EDGE: u8 = midpoint_word(0u8, u8::MAX);

            assert_eq!(MID_SIMPLE, 5u8);
            assert_eq!(MID_ROUND, 4u8);
            assert_eq!(MID_MAX, u8::MAX);
            assert_eq!(MID_EDGE, 127u8);
        }
    }

    #[test]
    fn test_const_unbounded_shift() {
        // Normal shifts (within bounds)
        assert_eq!(unbounded_shl_word(1u8, 0), 1u8);
        assert_eq!(unbounded_shl_word(1u8, 1), 2u8);
        assert_eq!(unbounded_shl_word(1u8, 7), 128u8);
        assert_eq!(unbounded_shr_word(128u8, 7), 1u8);
        assert_eq!(unbounded_shr_word(255u8, 4), 15u8);

        // At boundary (shift by bit width)
        assert_eq!(unbounded_shl_word(1u8, 8), 0u8);
        assert_eq!(unbounded_shr_word(255u8, 8), 0u8);

        // Beyond boundary
        assert_eq!(unbounded_shl_word(255u8, 9), 0u8);
        assert_eq!(unbounded_shl_word(255u8, 100), 0u8);
        assert_eq!(unbounded_shr_word(255u8, 9), 0u8);
        assert_eq!(unbounded_shr_word(255u8, 100), 0u8);

        // Test with larger types
        assert_eq!(unbounded_shl_word(1u64, 63), 1u64 << 63);
        assert_eq!(unbounded_shl_word(1u64, 64), 0u64);
        assert_eq!(unbounded_shr_word(u64::MAX, 64), 0u64);

        // u128
        assert_eq!(unbounded_shl_word(1u128, 127), 1u128 << 127);
        assert_eq!(unbounded_shl_word(1u128, 128), 0u128);
        assert_eq!(unbounded_shr_word(u128::MAX, 128), 0u128);

        #[cfg(feature = "nightly")]
        {
            const SHL_NORMAL: u8 = unbounded_shl_word(1u8, 4);
            const SHL_BOUNDARY: u8 = unbounded_shl_word(1u8, 8);
            const SHL_BEYOND: u8 = unbounded_shl_word(1u8, 100);
            const SHR_NORMAL: u8 = unbounded_shr_word(128u8, 4);
            const SHR_BOUNDARY: u8 = unbounded_shr_word(255u8, 8);
            const SHR_BEYOND: u8 = unbounded_shr_word(255u8, 100);

            assert_eq!(SHL_NORMAL, 16u8);
            assert_eq!(SHL_BOUNDARY, 0u8);
            assert_eq!(SHL_BEYOND, 0u8);
            assert_eq!(SHR_NORMAL, 8u8);
            assert_eq!(SHR_BOUNDARY, 0u8);
            assert_eq!(SHR_BEYOND, 0u8);
        }
    }
}
