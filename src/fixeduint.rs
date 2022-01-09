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

use num_traits::ops::overflowing::{OverflowingAdd, OverflowingMul, OverflowingSub};
use num_traits::{Bounded, One, PrimInt, ToPrimitive, Zero};

use num_integer;

use core::convert::TryFrom;
use core::fmt::Write;

use crate::machineword::MachineWord;
use crate::patch_num_traits::{OverflowingShl, OverflowingShr};

#[allow(unused_imports)]
use num_traits::{FromPrimitive, Num};

/// Fixed-size unsigned integer, represented by array of N words of builtin unsigned type T
#[derive(Debug, Clone, Copy, core::cmp::PartialEq, core::cmp::Eq)]
pub struct FixedUInt<T, const N: usize>
where
    T: MachineWord,
{
    /// Little-endian word array
    array: [T; N],
}

const LONGEST_WORD_IN_BITS: usize = 128;

impl<T: MachineWord, const N: usize> FixedUInt<T, N> {
    const WORD_SIZE: usize = core::mem::size_of::<T>();
    const WORD_BITS: usize = Self::WORD_SIZE * 8;
    const BYTE_SIZE: usize = Self::WORD_SIZE * N;
    const BIT_SIZE: usize = Self::BYTE_SIZE * 8;

    /// Creates and zero-initializes a FixedUInt.
    pub fn new() -> FixedUInt<T, N> {
        FixedUInt {
            array: [T::zero(); N],
        }
    }

    /// Returns number of used bits.
    pub fn bit_length(&self) -> u32 {
        Self::BIT_SIZE as u32 - self.leading_zeros()
    }

    /// Performs a division, returning both the quotient and reminder in a tuple.
    pub fn div_rem(&self, divisor: &Self) -> (Self, Self) {
        let quot = *self / *divisor;
        let tmp = quot * *divisor;
        let rem = *self - tmp;
        (quot, rem)
    }

    /// Create a little-endian integer value from its representation as a byte array in little endian.
    pub fn from_le_bytes(bytes: &[u8]) -> Self {
        let iter: usize = core::cmp::min(bytes.len() / Self::WORD_SIZE, N);
        let mut ret = Self::new(); // FixedUInt::<T, N>::new();
        for word in 0..iter {
            let mut v = T::zero();
            let mut next = T::zero();
            for i in 0..Self::WORD_SIZE {
                let byte = bytes[word * Self::WORD_SIZE + (Self::WORD_SIZE - 1 - i)];
                v = next | byte.into();
                next = if Self::WORD_BITS == 8 { v } else { v.shl(8) };
            }
            ret.array[word] = v;
        }
        ret
    }

    /// Converts to hex string, given a buffer. CAVEAT: This method removes any leading zero
    pub fn to_hex_str<'a>(&self, result: &'a mut [u8]) -> Result<&'a str, core::fmt::Error> {
        type Error = core::fmt::Error;

        let word_size = Self::WORD_SIZE;
        // need length minus leading zeros
        let need_bits = self.bit_length() as usize;
        // number of needed characters (bits/4 = bytes * 2)
        let need_chars = if need_bits > 0 { need_bits / 4 } else { 0 };

        if result.len() < need_chars {
            // not enough space in result...
            return Err(Error {});
        }
        let offset = result.len() - need_chars;
        for i in result.iter_mut() {
            *i = b'0';
        }

        for iter_words in 0..self.array.len() {
            let word = self.array[iter_words];
            let mut encoded = [0u8; LONGEST_WORD_IN_BITS / 4];
            let encode_slice = &mut encoded[0..word_size * 2];
            let mut wordbytes = word.to_ne_bytes();
            let wordslice = &mut wordbytes[0..word_size];
            wordslice.reverse();
            to_slice_hex(wordslice, encode_slice).map_err(|_| Error {})?;
            for iter_chars in 0..encode_slice.len() {
                let getme = encode_slice[(encode_slice.len() - 1) - iter_chars];
                let copy_char_to = (iter_words * word_size * 2) + iter_chars;
                // removes leading zero?
                if copy_char_to <= need_chars {
                    let reverse_index = offset + (need_chars - copy_char_to);
                    if reverse_index <= result.len() && reverse_index > 0 {
                        result[reverse_index - 1] = getme;
                    }
                }
            }
        }

        let convert = core::str::from_utf8(result).map_err(|_| Error {})?;
        let pos = convert.find(|c: char| c != '0');
        match pos {
            Some(x) => Ok(&convert[x..convert.len()]),
            None => {
                if convert.starts_with('0') {
                    Ok("0")
                } else {
                    Ok(convert)
                }
            }
        }
    }

    fn hex_fmt(
        &self,
        formatter: &mut core::fmt::Formatter<'_>,
        uppercase: bool,
    ) -> Result<(), core::fmt::Error>
    where
        u8: core::convert::TryFrom<T>,
    {
        type Err = core::fmt::Error;

        fn to_casedigit(byte: u8, uppercase: bool) -> Result<char, core::fmt::Error> {
            let digit = core::char::from_digit(byte as u32, 16).ok_or(Err {})?;
            if uppercase {
                digit.to_uppercase().next().ok_or(Err {})
            } else {
                digit.to_lowercase().next().ok_or(Err {})
            }
        }

        let mut leading_zero: bool = true;

        let mut maybe_write = |nibble: char| -> Result<(), core::fmt::Error> {
            leading_zero &= nibble == '0';
            if !leading_zero {
                formatter.write_char(nibble)?;
            }
            Ok(())
        };

        for index in (0..N).rev() {
            let val = self.array[index];
            let mask: T = 0xff.into();
            for j in (0..Self::WORD_SIZE as u32).rev() {
                let masked = val & mask.shl((j * 8) as usize);

                let byte = u8::try_from(masked.shr((j * 8) as usize)).map_err(|_| Err {})?;

                maybe_write(to_casedigit((byte & 0xf0) >> 4, uppercase)?)?;
                maybe_write(to_casedigit(byte & 0x0f, uppercase)?)?;
            }
        }
        Ok(())
    }
    // Add other to target, return overflow status
    // Note: in-place, no extra storage is used
    fn add_impl(target: &mut Self, other: &Self) -> bool {
        let mut carry = T::zero();
        for i in 0..N {
            let (res, carry1) = target.array[i].overflowing_add(&other.array[i]);
            let (res, carry2) = res.overflowing_add(&carry);
            carry = if carry1 || carry2 {
                T::one()
            } else {
                T::zero()
            };
            target.array[i] = res
        }
        !carry.is_zero()
    }

    // Here to avoid duplicating this in two traits
    fn saturating_add_impl(self, other: &Self) -> Self {
        let res = self.overflowing_add(other);
        if res.1 {
            Self::max_value()
        } else {
            res.0
        }
    }

    // Subtract other from target, return overflow status
    // Note: in-place, no extra storage is used
    fn sub_impl(target: &mut Self, other: &Self) -> bool {
        let mut borrow = T::zero();
        for i in 0..N {
            let (res, borrow1) = target.array[i].overflowing_sub(&other.array[i]);
            let (res, borrow2) = res.overflowing_sub(&borrow);
            borrow = if borrow1 || borrow2 {
                T::one()
            } else {
                T::zero()
            };
            target.array[i] = res;
        }
        !borrow.is_zero()
    }

    fn saturating_sub_impl(self, other: &Self) -> Self {
        let res = self.overflowing_sub(other);
        if res.1 {
            Self::zero()
        } else {
            res.0
        }
    }

    // Multiply op1 with op2, return overflow status
    // Note: uses extra `result` variable, not sure if in-place multiply is possible at all.
    fn mul_impl<const CHECK_OVERFLOW: bool>(op1: &Self, op2: &Self) -> (Self, bool) {
        let mut result = Self::zero();
        let mut overflowed = false;
        // Calculate N+1 rounds, to check for overflow
        let max_rounds = if CHECK_OVERFLOW { N + 1 } else { N };
        let t_max = T::max_value().to_double();
        for i in 0..N {
            let mut carry = T::DoubleWord::zero();
            for j in 0..N {
                let round = i + j;
                if round < max_rounds {
                    let mul_res = op1.array[i].to_double() * op2.array[j].to_double();
                    let mut accumulator = T::DoubleWord::zero();
                    if round < N {
                        accumulator = result.array[round].to_double();
                    }
                    accumulator = accumulator + mul_res + carry;

                    if accumulator > t_max {
                        carry = accumulator >> Self::WORD_BITS;
                        accumulator = accumulator & t_max;
                    } else {
                        carry = T::DoubleWord::zero();
                    }
                    if round < N {
                        result.array[round] = T::from_double(accumulator);
                    } else if CHECK_OVERFLOW {
                        overflowed = overflowed || !accumulator.is_zero();
                    }
                }
            }
            if !carry.is_zero() && CHECK_OVERFLOW {
                overflowed = true;
            }
        }
        (result, overflowed)
    }

    // Divide dividend with divisor, return result
    // Note: uses 2x extra storage in `result` and `current`
    fn div_impl(dividend: &Self, divisor: &Self) -> Self {
        let mut result = Self::zero();
        let mut current = Self::one();
        let mut tmp = *dividend;
        let mut denom = *divisor;

        let half_max: T::DoubleWord =
            T::one().to_double() + (T::max_value().to_double() / (T::one() + T::one()).to_double());
        let mut overflow = false;
        while denom <= *dividend {
            if denom.array[N - 1].to_double() >= half_max {
                overflow = true;
                break;
            }
            current <<= 1;
            denom <<= 1;
        }
        if !overflow {
            current >>= 1;
            denom >>= 1;
        }
        while !current.is_zero() {
            if tmp >= denom {
                tmp -= denom;
                result |= current;
            }
            current >>= 1;
            denom >>= 1;
        }
        result
    }

    // Shifts left by bits, in-place
    fn shl_impl(target: &mut Self, bits: usize) {
        let nwords = bits / Self::WORD_BITS;
        let nbits = bits - nwords * Self::WORD_BITS;

        // Move words
        for i in (nwords..N).rev() {
            target.array[i] = target.array[i - nwords];
        }
        // Zero out the remainder
        for i in 0..nwords {
            target.array[i] = T::zero();
        }

        if nbits != 0 {
            // Shift remaining bits
            for i in (1..N).rev() {
                let right = target.array[i].shl(nbits);
                let left = target.array[i - 1].shr(Self::WORD_BITS - nbits);
                target.array[i] = right | left;
            }
            target.array[0] = target.array[0].shl(nbits);
        }
    }

    // Shifts right by bits, in-place
    fn shr_impl(target: &mut Self, bits: usize) {
        let nwords = bits / Self::WORD_BITS;
        let nbits = bits - nwords * Self::WORD_BITS;

        let last_index = N - 1;
        let last_word = N - nwords;

        // Move words
        for i in 0..last_word {
            target.array[i] = target.array[i + nwords];
        }

        // Zero out the remainder
        for i in last_word..N {
            target.array[i] = T::zero();
        }

        if nbits != 0 {
            // Shift remaining bits
            for i in 0..last_index {
                let left = target.array[i].shr(nbits);
                let right = target.array[i + 1].shl(Self::WORD_BITS - nbits);
                target.array[i] = left | right;
            }
            target.array[last_index] = target.array[last_index].shr(nbits);
        }
    }
}

impl<T: MachineWord, const N: usize> Default for FixedUInt<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: MachineWord, const N: usize> num_traits::Unsigned for FixedUInt<T, N> {}

// #region Ordering

impl<T: MachineWord, const N: usize> core::cmp::Ord for FixedUInt<T, N> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        for i in (0..N).rev() {
            if self.array[i] > other.array[i] {
                return core::cmp::Ordering::Greater;
            }
            if self.array[i] < other.array[i] {
                return core::cmp::Ordering::Less;
            }
        }
        core::cmp::Ordering::Equal
    }
}

impl<T: MachineWord, const N: usize> core::cmp::PartialOrd for FixedUInt<T, N> {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

// #endregion Ordering

// #region core::convert::From<primitive>

impl<T: MachineWord, const N: usize> core::convert::From<u8> for FixedUInt<T, N> {
    fn from(x: u8) -> Self {
        let mut ret = Self::new();
        ret.array[0] = x.into();
        ret
    }
}

impl<T: MachineWord, const N: usize> core::convert::From<u16> for FixedUInt<T, N> {
    fn from(x: u16) -> Self {
        Self::from_le_bytes(&x.to_le_bytes())
    }
}

impl<T: MachineWord, const N: usize> core::convert::From<u32> for FixedUInt<T, N> {
    fn from(x: u32) -> Self {
        Self::from_le_bytes(&x.to_le_bytes())
    }
}

impl<T: MachineWord, const N: usize> core::convert::From<u64> for FixedUInt<T, N> {
    fn from(x: u64) -> Self {
        Self::from_le_bytes(&x.to_le_bytes())
    }
}

// #endregion core::convert::From<primitive>

// #region Add/Subtract

impl<T: MachineWord, const N: usize> num_traits::ops::overflowing::OverflowingAdd
    for FixedUInt<T, N>
{
    fn overflowing_add(&self, other: &Self) -> (Self, bool) {
        let mut ret = *self;
        let overflow = Self::add_impl(&mut ret, other);
        (ret, overflow)
    }
}

impl<T: MachineWord, const N: usize> core::ops::Add for FixedUInt<T, N> {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        let (res, overflow) = self.overflowing_add(&other);
        if overflow {
            maybe_panic(PanicReason::Add);
        }
        res
    }
}

impl<T: MachineWord, const N: usize> core::ops::Add<&'_ Self> for FixedUInt<T, N> {
    type Output = Self;
    fn add(self, other: &Self) -> Self {
        let (res, overflow) = self.overflowing_add(other);
        if overflow {
            maybe_panic(PanicReason::Add);
        }
        res
    }
}

impl<T: MachineWord, const N: usize> num_traits::WrappingAdd for FixedUInt<T, N> {
    fn wrapping_add(&self, other: &Self) -> Self {
        self.overflowing_add(other).0
    }
}

impl<T: MachineWord, const N: usize> num_traits::CheckedAdd for FixedUInt<T, N> {
    fn checked_add(&self, other: &Self) -> Option<Self> {
        let res = self.overflowing_add(other);
        if res.1 {
            None
        } else {
            Some(res.0)
        }
    }
}

impl<T: MachineWord, const N: usize> num_traits::ops::saturating::SaturatingAdd
    for FixedUInt<T, N>
{
    /// Saturating addition operator. Returns a+b, saturating at the numeric bounds instead of overflowing.
    fn saturating_add(&self, other: &Self) -> Self {
        self.saturating_add_impl(other)
    }
}

impl<T: MachineWord, const N: usize> core::ops::AddAssign<Self> for FixedUInt<T, N> {
    fn add_assign(&mut self, other: Self) {
        if Self::add_impl(self, &other) {
            maybe_panic(PanicReason::Add);
        }
    }
}

impl<T: MachineWord, const N: usize> core::ops::AddAssign<&'_ Self> for FixedUInt<T, N> {
    fn add_assign(&mut self, other: &Self) {
        if Self::add_impl(self, other) {
            maybe_panic(PanicReason::Add);
        }
    }
}

impl<T: MachineWord, const N: usize> num_traits::ops::overflowing::OverflowingSub
    for FixedUInt<T, N>
{
    fn overflowing_sub(&self, other: &Self) -> (Self, bool) {
        let mut ret = *self;
        let overflow = Self::sub_impl(&mut ret, other);
        (ret, overflow)
    }
}

impl<T: MachineWord, const N: usize> core::ops::Sub for FixedUInt<T, N> {
    type Output = Self;
    fn sub(self, other: Self) -> <Self as core::ops::Sub<Self>>::Output {
        let (res, overflow) = self.overflowing_sub(&other);
        if overflow {
            maybe_panic(PanicReason::Sub);
        }
        res
    }
}

impl<T: MachineWord, const N: usize> core::ops::Sub<&'_ Self> for FixedUInt<T, N> {
    type Output = Self;
    fn sub(self, other: &Self) -> Self {
        let (res, overflow) = self.overflowing_sub(other);
        if overflow {
            maybe_panic(PanicReason::Sub);
        }
        res
    }
}

impl<T: MachineWord, const N: usize> num_traits::WrappingSub for FixedUInt<T, N> {
    fn wrapping_sub(&self, other: &Self) -> Self {
        self.overflowing_sub(other).0
    }
}

impl<T: MachineWord, const N: usize> num_traits::CheckedSub for FixedUInt<T, N> {
    fn checked_sub(&self, other: &Self) -> Option<Self> {
        let res = self.overflowing_sub(other);
        if res.1 {
            None
        } else {
            Some(res.0)
        }
    }
}

impl<T: MachineWord, const N: usize> num_traits::ops::saturating::SaturatingSub
    for FixedUInt<T, N>
{
    /// Saturating subtraction operator. Returns a-b, saturating at the numeric bounds instead of overflowing.
    fn saturating_sub(&self, other: &Self) -> Self {
        self.saturating_sub_impl(other)
    }
}

impl<T: MachineWord, const N: usize> core::ops::SubAssign<Self> for FixedUInt<T, N> {
    fn sub_assign(&mut self, other: Self) {
        if Self::sub_impl(self, &other) {
            maybe_panic(PanicReason::Sub);
        }
    }
}

impl<T: MachineWord, const N: usize> core::ops::SubAssign<&'_ Self> for FixedUInt<T, N> {
    fn sub_assign(&mut self, other: &Self) {
        if Self::sub_impl(self, other) {
            maybe_panic(PanicReason::Sub);
        }
    }
}

/// Note: This is marked deprecated, but still used by PrimInt
impl<T: MachineWord, const N: usize> num_traits::Saturating for FixedUInt<T, N> {
    /// Saturating addition operator. Returns a+b, saturating at the numeric bounds instead of overflowing.
    fn saturating_add(self, other: Self) -> Self {
        self.saturating_add_impl(&other)
    }

    /// Saturating subtraction operator. Returns a-b, saturating at the numeric bounds instead of overflowing.
    fn saturating_sub(self, other: Self) -> Self {
        self.saturating_sub_impl(&other)
    }
}

// #endregion Add/Subtract

// #region Multiply/Divide

impl<T: MachineWord, const N: usize> num_traits::ops::overflowing::OverflowingMul
    for FixedUInt<T, N>
{
    fn overflowing_mul(&self, other: &Self) -> (Self, bool) {
        Self::mul_impl::<true>(self, other)
    }
}

impl<T: MachineWord, const N: usize> core::ops::Mul for FixedUInt<T, N> {
    type Output = Self;
    fn mul(self, other: Self) -> <Self as core::ops::Mul<Self>>::Output {
        let res = self.overflowing_mul(&other);
        if res.1 {
            maybe_panic(PanicReason::Mul);
        }
        res.0
    }
}

impl<T: MachineWord, const N: usize> core::ops::Mul<&'_ Self> for FixedUInt<T, N> {
    type Output = Self;
    fn mul(self, other: &Self) -> <Self as core::ops::Mul<Self>>::Output {
        let res = self.overflowing_mul(other);
        if res.1 {
            maybe_panic(PanicReason::Mul);
        }
        res.0
    }
}

impl<T: MachineWord, const N: usize> num_traits::WrappingMul for FixedUInt<T, N> {
    fn wrapping_mul(&self, other: &Self) -> Self {
        Self::mul_impl::<false>(self, other).0
    }
}

impl<T: MachineWord, const N: usize> num_traits::CheckedMul for FixedUInt<T, N> {
    fn checked_mul(&self, other: &Self) -> Option<Self> {
        let res = self.overflowing_mul(other);
        if res.1 {
            None
        } else {
            Some(res.0)
        }
    }
}

impl<T: MachineWord, const N: usize> num_traits::ops::saturating::SaturatingMul
    for FixedUInt<T, N>
{
    fn saturating_mul(&self, other: &Self) -> Self {
        let res = self.overflowing_mul(other);
        if res.1 {
            Self::max_value()
        } else {
            res.0
        }
    }
}

impl<T: MachineWord, const N: usize> core::ops::MulAssign<Self> for FixedUInt<T, N> {
    fn mul_assign(&mut self, other: Self) {
        let res = self.overflowing_mul(&other);
        *self = res.0;
        if res.1 {
            maybe_panic(PanicReason::Mul);
        }
    }
}

impl<T: MachineWord, const N: usize> core::ops::MulAssign<&'_ Self> for FixedUInt<T, N> {
    fn mul_assign(&mut self, other: &Self) {
        let res = self.overflowing_mul(other);
        *self = res.0;
        if res.1 {
            maybe_panic(PanicReason::Mul);
        }
    }
}

impl<T: MachineWord, const N: usize> core::ops::Div for FixedUInt<T, N> {
    type Output = Self;
    fn div(self, other: Self) -> <Self as core::ops::Div<Self>>::Output {
        if other.is_zero() {
            maybe_panic(PanicReason::DivByZero)
        }
        Self::div_impl(&self, &other)
    }
}

impl<T: MachineWord, const N: usize> core::ops::Div<&'_ Self> for FixedUInt<T, N> {
    type Output = Self;
    fn div(self, other: &Self) -> <Self as core::ops::Div<Self>>::Output {
        if other.is_zero() {
            maybe_panic(PanicReason::DivByZero)
        }
        Self::div_impl(&self, other)
    }
}

impl<T: MachineWord, const N: usize> num_traits::CheckedDiv for FixedUInt<T, N> {
    fn checked_div(&self, other: &Self) -> Option<Self> {
        if other.is_zero() {
            None
        } else {
            Some(core::ops::Div::<Self>::div(*self, *other))
        }
    }
}

impl<T: MachineWord, const N: usize> core::ops::DivAssign<Self> for FixedUInt<T, N> {
    fn div_assign(&mut self, other: Self) {
        if other.is_zero() {
            maybe_panic(PanicReason::DivByZero)
        }
        *self = Self::div_impl(self, &other);
    }
}

impl<T: MachineWord, const N: usize> core::ops::DivAssign<&'_ Self> for FixedUInt<T, N> {
    fn div_assign(&mut self, other: &Self) {
        if other.is_zero() {
            maybe_panic(PanicReason::DivByZero)
        }
        *self = Self::div_impl(self, other);
    }
}

impl<T: MachineWord, const N: usize> core::ops::Rem for FixedUInt<T, N> {
    type Output = Self;
    fn rem(self, other: Self) -> Self {
        if other.is_zero() {
            maybe_panic(PanicReason::RemByZero)
        }
        self.div_rem(&other).1
    }
}

impl<T: MachineWord, const N: usize> core::ops::Rem<&'_ Self> for FixedUInt<T, N> {
    type Output = Self;
    fn rem(self, other: &Self) -> Self {
        if other.is_zero() {
            maybe_panic(PanicReason::RemByZero)
        }
        self.div_rem(other).1
    }
}

impl<T: MachineWord, const N: usize> num_traits::CheckedRem for FixedUInt<T, N> {
    fn checked_rem(&self, other: &Self) -> Option<Self> {
        if other.is_zero() {
            None
        } else {
            Some(core::ops::Rem::<Self>::rem(*self, *other))
        }
    }
}

impl<T: MachineWord, const N: usize> core::ops::RemAssign<Self> for FixedUInt<T, N> {
    fn rem_assign(&mut self, other: Self) {
        if other.is_zero() {
            maybe_panic(PanicReason::RemByZero)
        }
        *self = self.div_rem(&other).1;
    }
}

impl<T: MachineWord, const N: usize> core::ops::RemAssign<&'_ Self> for FixedUInt<T, N> {
    fn rem_assign(&mut self, other: &Self) {
        if other.is_zero() {
            maybe_panic(PanicReason::RemByZero)
        }
        *self = self.div_rem(other).1;
    }
}

// #endregion Multiply/Divide

// #region Bitops

impl<T: MachineWord, const N: usize> core::ops::Not for FixedUInt<T, N> {
    type Output = Self;
    fn not(self) -> <Self as core::ops::Not>::Output {
        let mut ret = Self::zero();
        for i in 0..N {
            ret.array[i] = !self.array[i]
        }
        ret
    }
}

impl<T: MachineWord, const N: usize> core::ops::BitAnd for FixedUInt<T, N> {
    type Output = Self;
    fn bitand(self, other: Self) -> <Self as core::ops::BitAnd<Self>>::Output {
        let mut ret = Self::zero();
        for i in 0..N {
            ret.array[i] = self.array[i] & other.array[i]
        }
        ret
    }
}

impl<T: MachineWord, const N: usize> core::ops::BitAndAssign for FixedUInt<T, N> {
    fn bitand_assign(&mut self, other: Self) {
        for i in 0..N {
            self.array[i] &= other.array[i]
        }
    }
}

impl<T: MachineWord, const N: usize> core::ops::BitOr for FixedUInt<T, N> {
    type Output = Self;
    fn bitor(self, other: Self) -> <Self as core::ops::BitOr<Self>>::Output {
        let mut ret = Self::zero();
        for i in 0..N {
            ret.array[i] = self.array[i] | other.array[i]
        }
        ret
    }
}

impl<T: MachineWord, const N: usize> core::ops::BitOrAssign for FixedUInt<T, N> {
    fn bitor_assign(&mut self, other: Self) {
        for i in 0..N {
            self.array[i] |= other.array[i]
        }
    }
}

impl<T: MachineWord, const N: usize> core::ops::BitXor for FixedUInt<T, N> {
    type Output = Self;
    fn bitxor(self, other: Self) -> <Self as core::ops::BitXor<Self>>::Output {
        let mut ret = Self::zero();
        for i in 0..N {
            ret.array[i] = self.array[i] ^ other.array[i]
        }
        ret
    }
}

impl<T: MachineWord, const N: usize> core::ops::BitXorAssign for FixedUInt<T, N> {
    fn bitxor_assign(&mut self, other: Self) {
        for i in 0..N {
            self.array[i] ^= other.array[i]
        }
    }
}

impl<T: MachineWord, const N: usize> OverflowingShl for FixedUInt<T, N> {
    fn overflowing_shl(self, bits: u32) -> (Self, bool) {
        let bitsu = bits as usize;
        let (shift, overflow) = if bitsu >= Self::BIT_SIZE {
            (bitsu & (Self::BIT_SIZE - 1), true)
        } else {
            (bitsu, false)
        };
        let res = core::ops::Shl::<usize>::shl(self, shift);
        (res, overflow)
    }
}

impl<T: MachineWord, const N: usize> core::ops::Shl<u32> for FixedUInt<T, N> {
    type Output = Self;
    fn shl(self, bits: u32) -> <Self as core::ops::Shl<u32>>::Output {
        core::ops::Shl::<usize>::shl(self, bits as usize)
    }
}

impl<T: MachineWord, const N: usize> core::ops::Shl<usize> for FixedUInt<T, N> {
    type Output = Self;
    fn shl(self, bits: usize) -> <Self as core::ops::Shl<usize>>::Output {
        // This copy can be avoided
        let mut result = self;
        Self::shl_impl(&mut result, bits);
        result
    }
}

impl<T: MachineWord, const N: usize> core::ops::Shl<&'_ usize> for FixedUInt<T, N> {
    type Output = Self;
    fn shl(self, bits: &usize) -> <Self as core::ops::Shl<usize>>::Output {
        let mut result = self;
        Self::shl_impl(&mut result, *bits);
        result
    }
}

impl<T: MachineWord, const N: usize> num_traits::WrappingShl for FixedUInt<T, N> {
    fn wrapping_shl(&self, bits: u32) -> Self {
        self.overflowing_shl(bits).0
    }
}

impl<T: MachineWord, const N: usize> num_traits::CheckedShl for FixedUInt<T, N> {
    fn checked_shl(&self, bits: u32) -> Option<Self> {
        let res = self.overflowing_shl(bits);
        if res.1 {
            None
        } else {
            Some(res.0)
        }
    }
}

// SaturatingShl doesn't exist

impl<T: MachineWord, const N: usize> core::ops::ShlAssign<usize> for FixedUInt<T, N> {
    fn shl_assign(&mut self, bits: usize) {
        Self::shl_impl(self, bits);
    }
}

impl<T: MachineWord, const N: usize> core::ops::ShlAssign<&'_ usize> for FixedUInt<T, N> {
    fn shl_assign(&mut self, bits: &usize) {
        Self::shl_impl(self, *bits);
    }
}

impl<T: MachineWord, const N: usize> OverflowingShr for FixedUInt<T, N> {
    fn overflowing_shr(self, bits: u32) -> (Self, bool) {
        let bitsu = bits as usize;
        let (shift, overflow) = if bitsu >= Self::BIT_SIZE {
            (bitsu & (Self::BIT_SIZE - 1), true)
        } else {
            (bitsu, false)
        };
        let res = core::ops::Shr::<usize>::shr(self, shift);
        (res, overflow)
    }
}

impl<T: MachineWord, const N: usize> core::ops::Shr<u32> for FixedUInt<T, N> {
    type Output = Self;
    fn shr(self, bits: u32) -> <Self as core::ops::Shr<u32>>::Output {
        core::ops::Shr::<usize>::shr(self, bits as usize)
    }
}

impl<T: MachineWord, const N: usize> core::ops::Shr<usize> for FixedUInt<T, N> {
    type Output = Self;
    fn shr(self, bits: usize) -> <Self as core::ops::Shr<usize>>::Output {
        // Technically, this copy can be avoided
        let mut result = self;
        Self::shr_impl(&mut result, bits);
        result
    }
}

impl<T: MachineWord, const N: usize> core::ops::Shr<&'_ usize> for FixedUInt<T, N> {
    type Output = Self;
    fn shr(self, bits: &usize) -> <Self as core::ops::Shr<usize>>::Output {
        let mut result = self;
        Self::shr_impl(&mut result, *bits);
        result
    }
}

impl<T: MachineWord, const N: usize> num_traits::WrappingShr for FixedUInt<T, N> {
    fn wrapping_shr(&self, bits: u32) -> Self {
        self.overflowing_shr(bits).0
    }
}

impl<T: MachineWord, const N: usize> num_traits::CheckedShr for FixedUInt<T, N> {
    fn checked_shr(&self, bits: u32) -> Option<Self> {
        let res = self.overflowing_shr(bits);
        if res.1 {
            None
        } else {
            Some(res.0)
        }
    }
}

// SaturatingShr doesn't exist

impl<T: MachineWord, const N: usize> core::ops::ShrAssign<usize> for FixedUInt<T, N> {
    fn shr_assign(&mut self, bits: usize) {
        Self::shr_impl(self, bits);
    }
}

impl<T: MachineWord, const N: usize> core::ops::ShrAssign<&'_ usize> for FixedUInt<T, N> {
    fn shr_assign(&mut self, bits: &usize) {
        Self::shr_impl(self, *bits);
    }
}

// #endregion Bitops

// #region num_traits Identity

impl<T: MachineWord, const N: usize> num_traits::Zero for FixedUInt<T, N> {
    fn zero() -> Self {
        Self::new()
    }
    fn is_zero(&self) -> bool {
        !self.array.iter().any(|v| !v.is_zero())
    }
}

impl<T: MachineWord, const N: usize> num_traits::One for FixedUInt<T, N> {
    fn one() -> Self {
        let mut ret = Self::zero();
        ret.array[0] = T::one();
        ret
    }
}

impl<T: MachineWord, const N: usize> num_traits::Bounded for FixedUInt<T, N> {
    fn min_value() -> Self {
        Self::zero()
    }
    fn max_value() -> Self {
        FixedUInt {
            array: [T::max_value(); N],
        }
    }
}

// #endregion num_traits Identity

// #region num_traits casting

impl<T: MachineWord, const N: usize> num_traits::NumCast for FixedUInt<T, N> {
    fn from<X>(_: X) -> Option<Self>
    where
        T: ToPrimitive,
    {
        todo!()
    }
}

impl<T: MachineWord, const N: usize> num_traits::ToPrimitive for FixedUInt<T, N> {
    fn to_i64(&self) -> Option<i64> {
        None
    }
    fn to_u64(&self) -> Option<u64> {
        let mut ret: u64 = 0;
        let iter: usize = core::cmp::min(8 / Self::WORD_SIZE, N);
        for (word, bits) in (0..iter).map(|x| (x, x as u64 * Self::WORD_SIZE as u64 * 8)) {
            ret += T::to_u64(&self.array[word])? << bits;
        }
        Some(ret)
    }
}

impl<T: MachineWord, const N: usize> num_traits::FromPrimitive for FixedUInt<T, N> {
    fn from_i64(_: i64) -> Option<Self> {
        None
    }
    fn from_u64(input: u64) -> Option<Self> {
        Some(Self::from_le_bytes(&input.to_le_bytes()))
    }
}

// #endregion num_traits casting

// #region helpers

// This is slightly less than ideal, but PIE isn't directly constructible
// due to unstable members.
fn make_parse_int_err() -> core::num::ParseIntError {
    <u8>::from_str_radix("-", 2).err().unwrap()
}
fn make_overflow_err() -> core::num::ParseIntError {
    <u8>::from_str_radix("101", 16).err().unwrap()
}
fn make_empty_error() -> core::num::ParseIntError {
    <u8>::from_str_radix("", 8).err().unwrap()
}
fn make_neg_overflow_err() -> core::num::ParseIntError {
    <u8>::from_str_radix("-ff", 16).err().unwrap()
}

fn to_slice_hex<T: AsRef<[u8]>>(
    input: T,
    output: &mut [u8],
) -> Result<(), core::num::ParseIntError> {
    fn from_digit(byte: u8) -> Option<char> {
        core::char::from_digit(byte as u32, 16)
    }
    let r = input.as_ref();
    if r.len() * 2 != output.len() {
        return Err(make_parse_int_err());
    }
    for i in 0..r.len() {
        let byte = r[i];
        output[i * 2] = from_digit((byte & 0xf0) >> 4).ok_or_else(make_parse_int_err)? as u8;
        output[i * 2 + 1] = from_digit(byte & 0x0f).ok_or_else(make_parse_int_err)? as u8;
    }

    Ok(())
}

enum PanicReason {
    Add,
    Sub,
    Mul,
    DivByZero,
    RemByZero,
}

fn maybe_panic(r: PanicReason) {
    match r {
        PanicReason::Add => panic!("attempt to add with overflow"),
        PanicReason::Sub => panic!("attempt to subtract with overflow"),
        PanicReason::Mul => panic!("attempt to multiply with overflow"),
        PanicReason::DivByZero => panic!("attempt to divide by zero"),
        PanicReason::RemByZero => {
            panic!("attempt to calculate the remainder with a divisor of zero")
        }
    }
}

// #endregion helpers

// #region strings

impl<T: MachineWord, const N: usize> num_traits::Num for FixedUInt<T, N> {
    type FromStrRadixErr = core::num::ParseIntError;
    fn from_str_radix(
        input: &str,
        radix: u32,
    ) -> Result<Self, <Self as num_traits::Num>::FromStrRadixErr> {
        if input.is_empty() {
            return Err(make_empty_error());
        }
        let mut ret = Self::zero();
        let range = match input.find(|c: char| c != '0') {
            Some(x) => &input[x..],
            _ => input,
        };
        let bits_per_char = match radix {
            2 => 1,
            4 => 2,
            16 => 4,
            _ => return Err(make_neg_overflow_err()),
        };
        let input_chars = range.len();
        let input_bits = input_chars * bits_per_char;
        if input_bits > Self::BIT_SIZE {
            return Err(make_overflow_err());
        }
        let chars_per_word = Self::WORD_BITS / bits_per_char;
        let input_words = ((input_chars - 1) / chars_per_word) + 1;
        for idx in 0..input_words {
            let slice_end = input_chars - idx * chars_per_word;
            let slice_start =
                core::cmp::max(0, slice_end as isize - chars_per_word as isize) as usize;
            let slice = &range[slice_start..slice_end];
            let val = match T::from_str_radix(slice, radix) {
                Ok(x) => x,
                Err(_) => return Err(make_parse_int_err()),
            };
            ret.array[idx] = val;
        }
        Ok(ret)
    }
}

impl<T: MachineWord, const N: usize> core::fmt::UpperHex for FixedUInt<T, N>
where
    u8: core::convert::TryFrom<T>,
{
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        self.hex_fmt(formatter, true)
    }
}

impl<T: MachineWord, const N: usize> core::fmt::LowerHex for FixedUInt<T, N>
where
    u8: core::convert::TryFrom<T>,
{
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        self.hex_fmt(formatter, false)
    }
}

// #endregion strings

// #region unimplemented

impl<T: MachineWord, const N: usize> num_traits::PrimInt for FixedUInt<T, N> {
    fn count_ones(self) -> u32 {
        self.array.iter().map(|&val| val.count_ones()).sum()
    }
    fn count_zeros(self) -> u32 {
        self.array.iter().map(|&val| val.count_zeros()).sum()
    }
    fn leading_zeros(self) -> u32 {
        let mut ret = 0u32;
        for index in (0..N).rev() {
            let v = self.array[index];
            ret += v.leading_zeros();
            if !v.is_zero() {
                break;
            }
        }
        ret
    }
    fn trailing_zeros(self) -> u32 {
        let mut ret = 0u32;
        for index in 0..N {
            let v = self.array[index];
            ret += v.trailing_zeros();
            if !v.is_zero() {
                break;
            }
        }
        ret
    }
    fn rotate_left(self, bits: u32) -> Self {
        let a = self << bits;
        let b = self >> (Self::BIT_SIZE - bits as usize);
        a | b
    }
    fn rotate_right(self, bits: u32) -> Self {
        let a = self >> bits;
        let b = self << (Self::BIT_SIZE - bits as usize);
        a | b
    }
    fn signed_shl(self, _: u32) -> Self {
        todo!()
    }
    fn signed_shr(self, _: u32) -> Self {
        todo!()
    }
    fn unsigned_shl(self, bits: u32) -> Self {
        core::ops::Shl::<u32>::shl(self, bits)
    }
    fn unsigned_shr(self, bits: u32) -> Self {
        core::ops::Shr::<u32>::shr(self, bits)
    }
    fn swap_bytes(self) -> Self {
        let mut ret = Self::new();
        for index in 0..N {
            ret.array[index] = self.array[N - 1 - index].swap_bytes();
        }

        ret
    }
    fn from_be(source: Self) -> Self {
        let mut ret = Self::new();
        for index in 0..N {
            ret.array[index] = source.array[N - 1 - index].swap_bytes();
        }

        ret
    }
    fn from_le(source: Self) -> Self {
        let mut ret = Self::new();
        for index in 0..N {
            ret.array[index] = source.array[index];
        }

        ret
    }
    fn to_be(self) -> Self {
        let mut ret = Self::new();
        for index in 0..N {
            ret.array[index] = self.array[N - 1 - index].swap_bytes();
        }

        ret
    }
    fn to_le(self) -> Self {
        let mut ret = Self::new();
        for index in 0..N {
            ret.array[index] = self.array[index];
        }

        ret
    }
    fn pow(self, _: u32) -> Self {
        todo!()
    }
}

// #endregion unimplemented

// #region num-integer::Integer

// Most code here from num_integer crate, unsigned implementation

impl<T: MachineWord, const N: usize> num_integer::Integer for FixedUInt<T, N> {
    fn div_floor(&self, other: &Self) -> Self {
        *self / *other
    }
    fn mod_floor(&self, other: &Self) -> Self {
        *self % *other
    }
    fn gcd(&self, other: &Self) -> Self {
        // Use Stein's algorithm
        let mut m = *self;
        let mut n = *other;
        let zero = Self::zero();
        if m == zero || n == zero {
            return m | n;
        }

        // find common factors of 2
        let shift = (m | n).trailing_zeros();

        // divide n and m by 2 until odd
        m = m >> m.trailing_zeros();
        n = n >> n.trailing_zeros();

        while m != n {
            if m > n {
                m -= n;
                m = m >> m.trailing_zeros();
            } else {
                n -= m;
                n = n >> n.trailing_zeros();
            }
        }
        m << shift
    }
    fn lcm(&self, other: &Self) -> Self {
        if self.is_zero() && other.is_zero() {
            return Self::zero();
        }
        let gcd = self.gcd(other);
        *self * (*other / gcd)
    }
    fn divides(&self, other: &Self) -> bool {
        self.is_multiple_of(other)
    }
    fn is_multiple_of(&self, other: &Self) -> bool {
        (*self) % other == Self::zero()
    }
    fn is_even(&self) -> bool {
        (*self) & Self::one() == Self::zero()
    }
    fn is_odd(&self) -> bool {
        !self.is_even()
    }
    fn div_rem(&self, other: &Self) -> (Self, Self) {
        self.div_rem(other)
    }
}

// #endregion num-integer::Integer

#[cfg(test)]
mod tests {
    use super::FixedUInt as Bn;
    use super::*;

    type Bn8 = Bn<u8, 8>;
    type Bn16 = Bn<u16, 4>;
    type Bn32 = Bn<u32, 2>;

    #[test]
    fn test_core_convert_u8() {
        let f = Bn::<u8, 1>::from(1u8);
        assert_eq!(f.array, [1]);
        let f = Bn::<u8, 2>::from(1u8);
        assert_eq!(f.array, [1, 0]);

        let f = Bn::<u16, 1>::from(1u8);
        assert_eq!(f.array, [1]);
        let f = Bn::<u16, 2>::from(1u8);
        assert_eq!(f.array, [1, 0]);
    }

    #[test]
    fn test_core_convert_u16() {
        let f = Bn::<u8, 1>::from(1u16);
        assert_eq!(f.array, [1]);
        let f = Bn::<u8, 2>::from(1u16);
        assert_eq!(f.array, [1, 0]);

        let f = Bn::<u8, 1>::from(256u16);
        assert_eq!(f.array, [0]);
        let f = Bn::<u8, 2>::from(257u16);
        assert_eq!(f.array, [1, 1]);
        let f = Bn::<u8, 2>::from(65535u16);
        assert_eq!(f.array, [255, 255]);

        let f = Bn::<u16, 1>::from(1u16);
        assert_eq!(f.array, [1]);
        let f = Bn::<u16, 2>::from(1u16);
        assert_eq!(f.array, [1, 0]);

        let f = Bn::<u16, 1>::from(65535u16);
        assert_eq!(f.array, [65535]);
    }

    #[test]
    fn test_core_convert_u32() {
        let f = Bn::<u8, 1>::from(1u32);
        assert_eq!(f.array, [1]);
        let f = Bn::<u8, 1>::from(256u32);
        assert_eq!(f.array, [0]);

        let f = Bn::<u8, 2>::from(1u32);
        assert_eq!(f.array, [1, 0]);
        let f = Bn::<u8, 2>::from(257u32);
        assert_eq!(f.array, [1, 1]);
        let f = Bn::<u8, 2>::from(65535u32);
        assert_eq!(f.array, [255, 255]);

        let f = Bn::<u8, 4>::from(1u32);
        assert_eq!(f.array, [1, 0, 0, 0]);
        let f = Bn::<u8, 4>::from(257u32);
        assert_eq!(f.array, [1, 1, 0, 0]);
        let f = Bn::<u8, 4>::from(u32::max_value());
        assert_eq!(f.array, [255, 255, 255, 255]);

        let f = Bn::<u8, 1>::from(1u32);
        assert_eq!(f.array, [1]);
        let f = Bn::<u8, 1>::from(256u32);
        assert_eq!(f.array, [0]);

        let f = Bn::<u16, 2>::from(65537u32);
        assert_eq!(f.array, [1, 1]);

        let f = Bn::<u32, 1>::from(1u32);
        assert_eq!(f.array, [1]);
        let f = Bn::<u32, 2>::from(1u32);
        assert_eq!(f.array, [1, 0]);

        let f = Bn::<u32, 1>::from(65537u32);
        assert_eq!(f.array, [65537]);

        let f = Bn::<u32, 1>::from(u32::max_value());
        assert_eq!(f.array, [4294967295]);
    }

    #[test]
    fn testsimple() {
        assert_eq!(Bn::<u8, 8>::new(), Bn::<u8, 8>::new());

        assert_eq!(Bn::<u8, 8>::from_u8(3).unwrap().to_u32(), Some(3));
        assert_eq!(Bn::<u16, 4>::from_u8(3).unwrap().to_u32(), Some(3));
        assert_eq!(Bn::<u32, 2>::from_u8(3).unwrap().to_u32(), Some(3));
        assert_eq!(Bn::<u32, 2>::from_u64(3).unwrap().to_u32(), Some(3));
        assert_eq!(Bn::<u8, 8>::from_u64(255).unwrap().to_u32(), Some(255));
        assert_eq!(Bn::<u8, 8>::from_u64(256).unwrap().to_u32(), Some(256));
        assert_eq!(Bn::<u8, 8>::from_u64(65536).unwrap().to_u32(), Some(65536));
    }
    #[test]
    fn testfrom() {
        let mut n1 = Bn::<u8, 8>::new();
        n1.array[0] = 1;
        assert_eq!(Some(1), n1.to_u32());
        n1.array[1] = 1;
        assert_eq!(Some(257), n1.to_u32());

        let mut n2 = Bn::<u16, 8>::new();
        n2.array[0] = 0xffff;
        assert_eq!(Some(65535), n2.to_u32());
        n2.array[0] = 0x0;
        n2.array[2] = 0x1;
        // Overflow
        assert_eq!(None, n2.to_u32());
        assert_eq!(Some(0x100000000), n2.to_u64());
    }

    #[test]
    fn test_from_str_bitlengths() {
        let test_s64 = "81906f5e4d3c2c01";
        let test_u64: u64 = 0x81906f5e4d3c2c01;
        let bb = Bn8::from_str_radix(test_s64, 16).unwrap();
        let cc = Bn8::from_u64(test_u64).unwrap();
        assert_eq!(cc.array, [0x01, 0x2c, 0x3c, 0x4d, 0x5e, 0x6f, 0x90, 0x81]);
        assert_eq!(bb.array, [0x01, 0x2c, 0x3c, 0x4d, 0x5e, 0x6f, 0x90, 0x81]);
        let dd = Bn16::from_u64(test_u64).unwrap();
        let ff = Bn16::from_str_radix(test_s64, 16).unwrap();
        assert_eq!(dd.array, [0x2c01, 0x4d3c, 0x6f5e, 0x8190]);
        assert_eq!(ff.array, [0x2c01, 0x4d3c, 0x6f5e, 0x8190]);
        let ee = Bn32::from_u64(test_u64).unwrap();
        let gg = Bn32::from_str_radix(test_s64, 16).unwrap();
        assert_eq!(ee.array, [0x4d3c2c01, 0x81906f5e]);
        assert_eq!(gg.array, [0x4d3c2c01, 0x81906f5e]);
    }

    #[test]
    fn test_from_str_stringlengths() {
        let ab = Bn::<u8, 9>::from_str_radix("2281906f5e4d3c2c01", 16).unwrap();
        assert_eq!(
            ab.array,
            [0x01, 0x2c, 0x3c, 0x4d, 0x5e, 0x6f, 0x90, 0x81, 0x22]
        );
        assert_eq!(
            [0x2c01, 0x4d3c, 0x6f5e, 0],
            Bn::<u16, 4>::from_str_radix("6f5e4d3c2c01", 16)
                .unwrap()
                .array
        );
        assert_eq!(
            [0x2c01, 0x4d3c, 0x6f5e, 0x190],
            Bn::<u16, 4>::from_str_radix("1906f5e4d3c2c01", 16)
                .unwrap()
                .array
        );
        assert_eq!(
            Err(make_overflow_err()),
            Bn::<u16, 4>::from_str_radix("f81906f5e4d3c2c01", 16)
        );
        assert_eq!(
            Err(make_overflow_err()),
            Bn::<u16, 4>::from_str_radix("af81906f5e4d3c2c01", 16)
        );
        assert_eq!(
            Err(make_overflow_err()),
            Bn::<u16, 4>::from_str_radix("baaf81906f5e4d3c2c01", 16)
        );
        let ac = Bn::<u16, 5>::from_str_radix("baaf81906f5e4d3c2c01", 16).unwrap();
        assert_eq!(ac.array, [0x2c01, 0x4d3c, 0x6f5e, 0x8190, 0xbaaf]);
    }

    #[test]
    fn test_bit_length() {
        assert_eq!(0, Bn8::from_u8(0).unwrap().bit_length());
        assert_eq!(1, Bn8::from_u8(1).unwrap().bit_length());
        assert_eq!(2, Bn8::from_u8(2).unwrap().bit_length());
        assert_eq!(2, Bn8::from_u8(3).unwrap().bit_length());
        assert_eq!(7, Bn8::from_u8(0x70).unwrap().bit_length());
        assert_eq!(8, Bn8::from_u8(0xF0).unwrap().bit_length());
        assert_eq!(9, Bn8::from_u16(0x1F0).unwrap().bit_length());

        assert_eq!(20, Bn8::from_u64(990223).unwrap().bit_length());
        assert_eq!(32, Bn8::from_u64(0xefffffff).unwrap().bit_length());
        assert_eq!(32, Bn8::from_u64(0x8fffffff).unwrap().bit_length());
        assert_eq!(31, Bn8::from_u64(0x7fffffff).unwrap().bit_length());
        assert_eq!(34, Bn8::from_u64(0x3ffffffff).unwrap().bit_length());

        assert_eq!(0, Bn32::from_u8(0).unwrap().bit_length());
        assert_eq!(1, Bn32::from_u8(1).unwrap().bit_length());
        assert_eq!(2, Bn32::from_u8(2).unwrap().bit_length());
        assert_eq!(2, Bn32::from_u8(3).unwrap().bit_length());
        assert_eq!(7, Bn32::from_u8(0x70).unwrap().bit_length());
        assert_eq!(8, Bn32::from_u8(0xF0).unwrap().bit_length());
        assert_eq!(9, Bn32::from_u16(0x1F0).unwrap().bit_length());

        assert_eq!(20, Bn32::from_u64(990223).unwrap().bit_length());
        assert_eq!(32, Bn32::from_u64(0xefffffff).unwrap().bit_length());
        assert_eq!(32, Bn32::from_u64(0x8fffffff).unwrap().bit_length());
        assert_eq!(31, Bn32::from_u64(0x7fffffff).unwrap().bit_length());
        assert_eq!(34, Bn32::from_u64(0x3ffffffff).unwrap().bit_length());
    }
    #[test]
    fn test_cmp() {
        let f0 = Bn8::zero();
        let f1 = Bn8::zero();
        let f2 = Bn8::one();
        assert_eq!(f0, f1);
        assert!(f2 > f0);
        assert!(f0 < f2);
        let f3 = Bn32::from_u64(990223).unwrap();
        assert_eq!(f3, Bn32::from_u64(990223).unwrap());
        let f4 = Bn32::from_u64(990224).unwrap();
        assert!(f4 > Bn32::from_u64(990223).unwrap());

        let f3 = Bn8::from_u64(990223).unwrap();
        assert_eq!(f3, Bn8::from_u64(990223).unwrap());
        let f4 = Bn8::from_u64(990224).unwrap();
        assert!(f4 > Bn8::from_u64(990223).unwrap());
    }
}
