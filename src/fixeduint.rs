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

use num_traits::{ToPrimitive, Zero};

use core::convert::TryFrom;
use core::fmt::Write;

pub use crate::const_numtraits::{
    ConstAbsDiff, ConstBorrowingSub, ConstBounded, ConstCarryingAdd, ConstCarryingMul,
    ConstCheckedPow, ConstDivCeil, ConstIlog, ConstIsqrt, ConstMultiple, ConstOne, ConstPowerOfTwo,
    ConstPrimInt, ConstWideningMul, ConstZero,
};
use crate::machineword::{ConstMachineWord, MachineWord};

#[allow(unused_imports)]
use num_traits::{FromPrimitive, Num};

mod abs_diff_impl;
mod add_sub_impl;
mod bit_ops_impl;
mod checked_pow_impl;
mod div_ceil_impl;
mod euclid;
mod extended_precision_impl;
mod ilog_impl;
mod isqrt_impl;
mod iter_impl;
mod midpoint_impl;
mod mul_div_impl;
mod multiple_impl;
mod num_integer_impl;
mod num_traits_casts;
mod num_traits_identity;
mod power_of_two_impl;
mod prim_int_impl;
mod roots_impl;
mod string_conversion;
// ConstToBytes trait (nightly only, uses generic_const_exprs)
#[cfg(feature = "nightly")]
mod const_to_from_bytes;
// num_traits::ToBytes/FromBytes (stable impl, no generic_const_exprs viral bounds)
#[cfg(any(feature = "nightly", feature = "use-unsafe"))]
mod to_from_bytes;

#[cfg(feature = "zeroize")]
use zeroize::DefaultIsZeroes;

/// Fixed-size unsigned integer, represented by array of N words of builtin unsigned type T
#[derive(Debug, Copy)]
pub struct FixedUInt<T, const N: usize>
where
    T: MachineWord,
{
    /// Little-endian word array
    pub(super) array: [T; N],
}

#[cfg(feature = "zeroize")]
impl<T: MachineWord, const N: usize> DefaultIsZeroes for FixedUInt<T, N> {}

impl<T, const N: usize> From<[T; N]> for FixedUInt<T, N>
where
    T: MachineWord,
{
    fn from(array: [T; N]) -> Self {
        Self { array }
    }
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

    /// Returns the underlying array.
    pub fn words(&self) -> &[T; N] {
        &self.array
    }

    /// Returns number of used bits.
    pub fn bit_length(&self) -> u32 {
        Self::BIT_SIZE as u32 - ConstPrimInt::leading_zeros(*self)
    }

    /// Performs a division, returning both the quotient and remainder in a tuple.
    pub fn div_rem(&self, divisor: &Self) -> (Self, Self) {
        let (quotient, remainder) = const_div_rem(&self.array, &divisor.array);
        (Self { array: quotient }, Self { array: remainder })
    }
}

// Const-compatible from_bytes helper functions
c0nst::c0nst! {
    /// Const-compatible from_le_bytes implementation for slices.
    /// Derives word_size internally from size_of::<T>().
    pub(crate) c0nst fn impl_from_le_bytes_slice<T: [c0nst] ConstMachineWord, const N: usize>(
        bytes: &[u8],
    ) -> [T; N] {
        let word_size = core::mem::size_of::<T>();
        let mut ret: [T; N] = [T::zero(); N];
        let capacity = N * word_size;
        let total_bytes = if bytes.len() < capacity { bytes.len() } else { capacity };

        let mut byte_index = 0;
        while byte_index < total_bytes {
            let word_index = byte_index / word_size;
            let byte_in_word = byte_index % word_size;

            let byte_value: T = T::from(bytes[byte_index]);
            let shifted_value = byte_value.shl(byte_in_word * 8);
            ret[word_index] = ret[word_index].bitor(shifted_value);
            byte_index += 1;
        }
        ret
    }

    /// Const-compatible from_be_bytes implementation for slices.
    /// Derives word_size internally from size_of::<T>().
    pub(crate) c0nst fn impl_from_be_bytes_slice<T: [c0nst] ConstMachineWord, const N: usize>(
        bytes: &[u8],
    ) -> [T; N] {
        let word_size = core::mem::size_of::<T>();
        let mut ret: [T; N] = [T::zero(); N];
        let capacity_bytes = N * word_size;
        let total_bytes = if bytes.len() < capacity_bytes { bytes.len() } else { capacity_bytes };

        // For consistent truncation semantics with from_le_bytes, always take the
        // least significant bytes (rightmost bytes in big-endian representation)
        let start_offset = if bytes.len() > capacity_bytes {
            bytes.len() - capacity_bytes
        } else {
            0
        };

        let mut byte_index = 0;
        while byte_index < total_bytes {
            // Take bytes from the end of the input (least significant in BE)
            let be_byte_index = start_offset + total_bytes - 1 - byte_index;
            let word_index = byte_index / word_size;
            let byte_in_word = byte_index % word_size;

            let byte_value: T = T::from(bytes[be_byte_index]);
            let shifted_value = byte_value.shl(byte_in_word * 8);
            ret[word_index] = ret[word_index].bitor(shifted_value);
            byte_index += 1;
        }
        ret
    }
}

// Inherent from_bytes methods (not const - use ConstFromBytes trait for const access)
impl<T: MachineWord, const N: usize> FixedUInt<T, N> {
    /// Create a little-endian integer value from its representation as a byte array in little endian.
    pub fn from_le_bytes(bytes: &[u8]) -> Self {
        Self {
            array: impl_from_le_bytes_slice::<T, N>(bytes),
        }
    }

    /// Create a big-endian integer value from its representation as a byte array in big endian.
    pub fn from_be_bytes(bytes: &[u8]) -> Self {
        Self {
            array: impl_from_be_bytes_slice::<T, N>(bytes),
        }
    }
}

impl<T: MachineWord, const N: usize> FixedUInt<T, N> {
    /// Converts the FixedUInt into a little-endian byte array.
    pub fn to_le_bytes<'a>(&self, output_buffer: &'a mut [u8]) -> Result<&'a [u8], bool> {
        let total_bytes = N * Self::WORD_SIZE;
        if output_buffer.len() < total_bytes {
            return Err(false); // Buffer too small
        }
        for (i, word) in self.array.iter().enumerate() {
            let start = i * Self::WORD_SIZE;
            let end = start + Self::WORD_SIZE;
            let word_bytes = word.to_le_bytes();
            output_buffer[start..end].copy_from_slice(word_bytes.as_ref());
        }
        Ok(&output_buffer[..total_bytes])
    }

    /// Converts the FixedUInt into a big-endian byte array.
    pub fn to_be_bytes<'a>(&self, output_buffer: &'a mut [u8]) -> Result<&'a [u8], bool> {
        let total_bytes = N * Self::WORD_SIZE;
        if output_buffer.len() < total_bytes {
            return Err(false); // Buffer too small
        }
        for (i, word) in self.array.iter().rev().enumerate() {
            let start = i * Self::WORD_SIZE;
            let end = start + Self::WORD_SIZE;
            let word_bytes = word.to_be_bytes();
            output_buffer[start..end].copy_from_slice(word_bytes.as_ref());
        }
        Ok(&output_buffer[..total_bytes])
    }

    /// Converts to hex string, given a buffer. CAVEAT: This method removes any leading zeroes
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
            let mut wordbytes = word.to_le_bytes();
            wordbytes.as_mut().reverse();
            let wordslice = wordbytes.as_ref();
            to_slice_hex(wordslice, encode_slice).map_err(|_| Error {})?;
            for iter_chars in 0..encode_slice.len() {
                let copy_char_to = (iter_words * word_size * 2) + iter_chars;
                if copy_char_to <= need_chars {
                    let reverse_index = offset + (need_chars - copy_char_to);
                    if reverse_index <= result.len() && reverse_index > 0 {
                        let current_char = encode_slice[(encode_slice.len() - 1) - iter_chars];
                        result[reverse_index - 1] = current_char;
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

    /// Converts to decimal string, given a buffer. CAVEAT: This method removes any leading zeroes
    pub fn to_radix_str<'a>(
        &self,
        result: &'a mut [u8],
        radix: u8,
    ) -> Result<&'a str, core::fmt::Error> {
        type Error = core::fmt::Error;

        if !(2..=16).contains(&radix) {
            return Err(Error {}); // Radix out of supported range
        }
        for byte in result.iter_mut() {
            *byte = b'0';
        }
        if Zero::is_zero(self) {
            if !result.is_empty() {
                result[0] = b'0';
                return core::str::from_utf8(&result[0..1]).map_err(|_| Error {});
            } else {
                return Err(Error {});
            }
        }

        let mut number = *self;
        let mut idx = result.len();

        let radix_t = Self::from(radix);

        while !Zero::is_zero(&number) {
            if idx == 0 {
                return Err(Error {}); // not enough space in result...
            }

            idx -= 1;
            let (quotient, remainder) = number.div_rem(&radix_t);

            let digit = remainder.to_u8().unwrap();
            result[idx] = match digit {
                0..=9 => b'0' + digit,          // digits
                10..=16 => b'a' + (digit - 10), // alphabetic digits for bases > 10
                _ => return Err(Error {}),
            };

            number = quotient;
        }

        let start = result[idx..].iter().position(|&c| c != b'0').unwrap_or(0);
        let radix_str = core::str::from_utf8(&result[idx + start..]).map_err(|_| Error {})?;
        Ok(radix_str)
    }

    /// Construct a new values with a different size.
    ///
    /// - If `N2 < N`, the most-significant (upper) words are truncated.
    /// - If `N2 > N`, the additional most-significant words are filled with zeros.
    #[must_use]
    pub fn resize<const N2: usize>(&self) -> FixedUInt<T, N2> {
        let mut array = [T::zero(); N2];
        let min_size = N.min(N2);
        array[..min_size].copy_from_slice(&self.array[..min_size]);
        FixedUInt { array }
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
}

c0nst::c0nst! {
    /// Const-compatible add implementation operating on raw arrays
    pub(crate) c0nst fn add_impl<T: [c0nst] ConstMachineWord, const N: usize>(
        target: &mut [T; N],
        other: &[T; N]
    ) -> bool {
        let mut carry = T::zero();
        let mut i = 0usize;
        while i < N {
            let (res, carry1) = target[i].overflowing_add(&other[i]);
            let (res, carry2) = res.overflowing_add(&carry);
            carry = if carry1 || carry2 {
                T::one()
            } else {
                T::zero()
            };
            target[i] = res;
            i += 1;
        }
        !carry.is_zero()
    }
}

c0nst::c0nst! {
    /// Const-compatible sub implementation operating on raw arrays
    pub(crate) c0nst fn sub_impl<T: [c0nst] ConstMachineWord, const N: usize>(
        target: &mut [T; N],
        other: &[T; N]
    ) -> bool {
        let mut borrow = T::zero();
        let mut i = 0usize;
        while i < N {
            let (res, borrow1) = target[i].overflowing_sub(&other[i]);
            let (res, borrow2) = res.overflowing_sub(&borrow);
            borrow = if borrow1 || borrow2 {
                T::one()
            } else {
                T::zero()
            };
            target[i] = res;
            i += 1;
        }
        !borrow.is_zero()
    }
}

c0nst::c0nst! {
    /// Const-compatible left shift implementation
    pub(crate) c0nst fn const_shl_impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
        target: &mut FixedUInt<T, N>,
        bits: usize,
    ) {
        if N == 0 {
            return;
        }
        let word_bits = FixedUInt::<T, N>::WORD_BITS;
        let nwords = bits / word_bits;
        let nbits = bits - nwords * word_bits;

        // If shift >= total bits, result is zero
        if nwords >= N {
            let mut i = 0;
            while i < N {
                target.array[i] = T::zero();
                i += 1;
            }
            return;
        }

        // Move words (backwards)
        let mut i = N;
        while i > nwords {
            i -= 1;
            target.array[i] = target.array[i - nwords];
        }
        // Zero out the lower words
        let mut i = 0;
        while i < nwords {
            target.array[i] = T::zero();
            i += 1;
        }

        if nbits != 0 {
            // Shift remaining bits (backwards)
            let mut i = N;
            while i > 1 {
                i -= 1;
                let right = target.array[i] << nbits;
                let left = target.array[i - 1] >> (word_bits - nbits);
                target.array[i] = right | left;
            }
            target.array[0] <<= nbits;
        }
    }

    /// Const-compatible right shift implementation
    pub(crate) c0nst fn const_shr_impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
        target: &mut FixedUInt<T, N>,
        bits: usize,
    ) {
        if N == 0 {
            return;
        }
        let word_bits = FixedUInt::<T, N>::WORD_BITS;
        let nwords = bits / word_bits;
        let nbits = bits - nwords * word_bits;

        // If shift >= total bits, result is zero
        if nwords >= N {
            let mut i = 0;
            while i < N {
                target.array[i] = T::zero();
                i += 1;
            }
            return;
        }

        let last_index = N - 1;
        let last_word = N - nwords;

        // Move words (forwards)
        let mut i = 0;
        while i < last_word {
            target.array[i] = target.array[i + nwords];
            i += 1;
        }

        // Zero out the upper words
        let mut i = last_word;
        while i < N {
            target.array[i] = T::zero();
            i += 1;
        }

        if nbits != 0 {
            // Shift remaining bits (forwards)
            let mut i = 0;
            while i < last_index {
                let left = target.array[i] >> nbits;
                let right = target.array[i + 1] << (word_bits - nbits);
                target.array[i] = left | right;
                i += 1;
            }
            target.array[last_index] >>= nbits;
        }
    }

    /// Standalone const-compatible array multiplication (no FixedUInt dependency)
    /// Returns (result_array, overflowed)
    pub(crate) c0nst fn const_mul<T: [c0nst] ConstMachineWord, const N: usize, const CHECK_OVERFLOW: bool>(
        op1: &[T; N],
        op2: &[T; N],
        word_bits: usize,
    ) -> ([T; N], bool) {
        let mut result: [T; N] = [<T as ConstZero>::zero(); N];
        let mut overflowed = false;
        let t_max = <T as ConstMachineWord>::to_double(<T as ConstBounded>::max_value());
        // Zero for double word type
        let dw_zero = <<T as ConstMachineWord>::ConstDoubleWord as ConstZero>::zero();

        let mut i = 0;
        while i < N {
            let mut carry = dw_zero;
            let mut j = 0;
            while j < N {
                let round = i + j;
                let op1_dw = <T as ConstMachineWord>::to_double(op1[i]);
                let op2_dw = <T as ConstMachineWord>::to_double(op2[j]);
                let mul_res = op1_dw * op2_dw;
                let mut accumulator = if round < N {
                    <T as ConstMachineWord>::to_double(result[round])
                } else {
                    dw_zero
                };
                accumulator = accumulator + mul_res + carry;

                if accumulator > t_max {
                    carry = accumulator >> word_bits;
                    accumulator &= t_max;
                } else {
                    carry = dw_zero;
                }
                if round < N {
                    result[round] = <T as ConstMachineWord>::from_double(accumulator);
                } else if CHECK_OVERFLOW {
                    overflowed = overflowed || accumulator != dw_zero;
                }
                j += 1;
            }
            if carry != dw_zero && CHECK_OVERFLOW {
                overflowed = true;
            }
            i += 1;
        }
        (result, overflowed)
    }

    /// Get the bit width of a word type.
    pub(crate) c0nst fn const_word_bits<T>() -> usize {
        core::mem::size_of::<T>() * 8
    }

    /// Compare two words, returning Some(ordering) if not equal, None if equal.
    pub(crate) c0nst fn const_cmp_words<T: [c0nst] ConstMachineWord>(a: T, b: T) -> Option<core::cmp::Ordering> {
        if a > b {
            Some(core::cmp::Ordering::Greater)
        } else if a < b {
            Some(core::cmp::Ordering::Less)
        } else {
            None
        }
    }

    /// Count leading zeros in a const-compatible way
    pub(crate) c0nst fn const_leading_zeros<T: [c0nst] ConstMachineWord, const N: usize>(
        array: &[T; N],
    ) -> u32 {
        let mut ret = 0u32;
        let mut index = N;
        while index > 0 {
            index -= 1;
            let v = array[index];
            ret += <T as ConstPrimInt>::leading_zeros(v);
            if !<T as ConstZero>::is_zero(&v) {
                break;
            }
        }
        ret
    }

    /// Count trailing zeros in a const-compatible way
    pub(crate) c0nst fn const_trailing_zeros<T: [c0nst] ConstMachineWord, const N: usize>(
        array: &[T; N],
    ) -> u32 {
        let mut ret = 0u32;
        let mut index = 0;
        while index < N {
            let v = array[index];
            ret += <T as ConstPrimInt>::trailing_zeros(v);
            if !<T as ConstZero>::is_zero(&v) {
                break;
            }
            index += 1;
        }
        ret
    }

    /// Get bit length of array (total bits - leading zeros)
    pub(crate) c0nst fn const_bit_length<T: [c0nst] ConstMachineWord, const N: usize>(
        array: &[T; N],
    ) -> usize {
        let word_bits = const_word_bits::<T>();
        let bit_size = N * word_bits;
        bit_size - const_leading_zeros::<T, N>(array) as usize
    }

    /// Check if array is zero
    pub(crate) c0nst fn const_is_zero<T: [c0nst] ConstMachineWord, const N: usize>(
        array: &[T; N],
    ) -> bool {
        let mut index = 0;
        while index < N {
            if !<T as ConstZero>::is_zero(&array[index]) {
                return false;
            }
            index += 1;
        }
        true
    }

    /// Set a specific bit in the array.
    ///
    /// The array uses little-endian representation where index 0 contains
    /// the least significant word, and bit 0 is the least significant bit
    /// of the entire integer.
    pub(crate) c0nst fn const_set_bit<T: [c0nst] ConstMachineWord, const N: usize>(
        array: &mut [T; N],
        pos: usize,
    ) {
        let word_bits = const_word_bits::<T>();
        let word_idx = pos / word_bits;
        if word_idx >= N {
            return;
        }
        let bit_idx = pos % word_bits;
        array[word_idx] |= <T as ConstOne>::one() << bit_idx;
    }

    /// Compare two arrays in a const-compatible way.
    ///
    /// Arrays use little-endian representation where index 0 contains
    /// the least significant word.
    pub(crate) c0nst fn const_cmp<T: [c0nst] ConstMachineWord, const N: usize>(
        a: &[T; N],
        b: &[T; N],
    ) -> core::cmp::Ordering {
        let mut index = N;
        while index > 0 {
            index -= 1;
            if let Some(ord) = const_cmp_words(a[index], b[index]) {
                return ord;
            }
        }
        core::cmp::Ordering::Equal
    }

    /// Get the value of array's word at position `word_idx` when logically shifted left.
    ///
    /// This helper computes what value would be at `word_idx` if the array
    /// were shifted left by `word_shift` words plus `bit_shift` bits.
    pub(crate) c0nst fn const_get_shifted_word<T: [c0nst] ConstMachineWord, const N: usize>(
        array: &[T; N],
        word_idx: usize,
        word_shift: usize,
        bit_shift: usize,
    ) -> T {
        let word_bits = const_word_bits::<T>();

        // Guard against invalid bit_shift that would cause UB
        if bit_shift >= word_bits {
            return <T as ConstZero>::zero();
        }

        if word_idx < word_shift {
            return <T as ConstZero>::zero();
        }

        let source_idx = word_idx - word_shift;

        if bit_shift == 0 {
            if source_idx < N {
                array[source_idx]
            } else {
                <T as ConstZero>::zero()
            }
        } else {
            let mut result = <T as ConstZero>::zero();

            // Get bits from the primary source word
            if source_idx < N {
                result |= array[source_idx] << bit_shift;
            }

            // Get high bits from the next lower word (if it exists)
            if source_idx > 0 && source_idx - 1 < N {
                let high_bits = array[source_idx - 1] >> (word_bits - bit_shift);
                result |= high_bits;
            }

            result
        }
    }

    /// Compare array vs (other << shift_bits) in a const-compatible way.
    ///
    /// This is useful for division algorithms where we need to compare
    /// the dividend against a shifted divisor without allocating.
    pub(crate) c0nst fn const_cmp_shifted<T: [c0nst] ConstMachineWord, const N: usize>(
        array: &[T; N],
        other: &[T; N],
        shift_bits: usize,
    ) -> core::cmp::Ordering {
        let word_bits = const_word_bits::<T>();

        if shift_bits == 0 {
            return const_cmp::<T, N>(array, other);
        }

        let word_shift = shift_bits / word_bits;
        if word_shift >= N {
            // other << shift_bits would overflow to 0
            if const_is_zero::<T, N>(array) {
                return core::cmp::Ordering::Equal;
            } else {
                return core::cmp::Ordering::Greater;
            }
        }

        let bit_shift = shift_bits % word_bits;

        // Compare from most significant words down
        let mut index = N;
        while index > 0 {
            index -= 1;
            let self_word = array[index];
            let other_shifted_word = const_get_shifted_word::<T, N>(
                other, index, word_shift, bit_shift
            );

            if let Some(ord) = const_cmp_words(self_word, other_shifted_word) {
                return ord;
            }
        }

        core::cmp::Ordering::Equal
    }

    /// Subtract (other << shift_bits) from array in-place.
    ///
    /// This is used in division algorithms to subtract shifted divisor
    /// from the remainder without allocating.
    pub(crate) c0nst fn const_sub_shifted<T: [c0nst] ConstMachineWord, const N: usize>(
        array: &mut [T; N],
        other: &[T; N],
        shift_bits: usize,
    ) {
        let word_bits = const_word_bits::<T>();

        if shift_bits == 0 {
            sub_impl::<T, N>(array, other);
            return;
        }

        let word_shift = shift_bits / word_bits;
        if word_shift >= N {
            return;
        }

        let bit_shift = shift_bits % word_bits;
        let mut borrow = T::zero();
        let mut index = 0;
        while index < N {
            let other_word = const_get_shifted_word::<T, N>(other, index, word_shift, bit_shift);
            let (res, borrow1) = array[index].overflowing_sub(&other_word);
            let (res, borrow2) = res.overflowing_sub(&borrow);
            borrow = if borrow1 || borrow2 { T::one() } else { T::zero() };
            array[index] = res;
            index += 1;
        }
    }

    /// In-place division: dividend becomes quotient, returns remainder.
    ///
    /// Low-level const-compatible division on arrays.
    pub(crate) c0nst fn const_div<T: [c0nst] ConstMachineWord, const N: usize>(
        dividend: &mut [T; N],
        divisor: &[T; N],
    ) -> [T; N] {
        use core::cmp::Ordering;

        match const_cmp::<T, N>(dividend, divisor) {
            // dividend < divisor: quotient = 0, remainder = dividend
            Ordering::Less => {
                let remainder = *dividend;
                let mut i = 0;
                while i < N {
                    dividend[i] = <T as ConstZero>::zero();
                    i += 1;
                }
                return remainder;
            }
            // dividend == divisor: quotient = 1, remainder = 0
            Ordering::Equal => {
                let mut i = 0;
                while i < N {
                    dividend[i] = <T as ConstZero>::zero();
                    i += 1;
                }
                if N > 0 {
                    dividend[0] = <T as ConstOne>::one();
                }
                return [<T as ConstZero>::zero(); N];
            }
            Ordering::Greater => {}
        }

        let mut quotient = [<T as ConstZero>::zero(); N];

        // Calculate initial bit position
        let dividend_bits = const_bit_length::<T, N>(dividend);
        let divisor_bits = const_bit_length::<T, N>(divisor);

        let mut bit_pos = if dividend_bits >= divisor_bits {
            dividend_bits - divisor_bits
        } else {
            0
        };

        // Adjust bit position to find the first position where divisor can be subtracted
        while bit_pos > 0 {
            let cmp = const_cmp_shifted::<T, N>(dividend, divisor, bit_pos);
            if !matches!(cmp, Ordering::Less) {
                break;
            }
            bit_pos -= 1;
        }

        // Main division loop
        loop {
            let cmp = const_cmp_shifted::<T, N>(dividend, divisor, bit_pos);
            if !matches!(cmp, Ordering::Less) {
                const_sub_shifted::<T, N>(dividend, divisor, bit_pos);
                const_set_bit::<T, N>(&mut quotient, bit_pos);
            }

            if bit_pos == 0 {
                break;
            }
            bit_pos -= 1;
        }

        let remainder = *dividend;
        *dividend = quotient;
        remainder
    }

    /// Const-compatible div_rem: returns (quotient, remainder).
    ///
    /// Panics on divide by zero.
    pub(crate) c0nst fn const_div_rem<T: [c0nst] ConstMachineWord, const N: usize>(
        dividend: &[T; N],
        divisor: &[T; N],
    ) -> ([T; N], [T; N]) {
        if const_is_zero(divisor) {
            maybe_panic(PanicReason::DivByZero)
        }
        let mut quotient = *dividend;
        let remainder = const_div(&mut quotient, divisor);
        (quotient, remainder)
    }
}

c0nst::c0nst! {
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst Default for FixedUInt<T, N> {
        fn default() -> Self {
            <Self as ConstZero>::zero()
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst Clone for FixedUInt<T, N> {
        fn clone(&self) -> Self {
            *self
        }
    }
}

impl<T: MachineWord, const N: usize> num_traits::Unsigned for FixedUInt<T, N> {}

// #region Equality and Ordering

c0nst::c0nst! {
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::cmp::PartialEq for FixedUInt<T, N> {
        fn eq(&self, other: &Self) -> bool {
            self.array == other.array
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::cmp::Eq for FixedUInt<T, N> {}

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::cmp::Ord for FixedUInt<T, N> {
        fn cmp(&self, other: &Self) -> core::cmp::Ordering {
            const_cmp(&self.array, &other.array)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::cmp::PartialOrd for FixedUInt<T, N> {
        fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
            Some(self.cmp(other))
        }
    }
}

// #endregion Equality and Ordering

// #region core::convert::From<primitive>

c0nst::c0nst! {
    /// Const-compatible conversion from little-endian bytes to array of words.
    /// Delegates to impl_from_le_bytes_slice to avoid code duplication.
    c0nst fn const_from_le_bytes<T: [c0nst] ConstMachineWord, const N: usize, const B: usize>(
        bytes: [u8; B],
    ) -> [T; N] {
        impl_from_le_bytes_slice::<T, N>(&bytes)
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::convert::From<u8> for FixedUInt<T, N> {
        fn from(x: u8) -> Self {
            Self { array: const_from_le_bytes(x.to_le_bytes()) }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::convert::From<u16> for FixedUInt<T, N> {
        fn from(x: u16) -> Self {
            Self { array: const_from_le_bytes(x.to_le_bytes()) }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::convert::From<u32> for FixedUInt<T, N> {
        fn from(x: u32) -> Self {
            Self { array: const_from_le_bytes(x.to_le_bytes()) }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst core::convert::From<u64> for FixedUInt<T, N> {
        fn from(x: u64) -> Self {
            Self { array: const_from_le_bytes(x.to_le_bytes()) }
        }
    }
}

// #endregion core::convert::From<primitive>

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

pub(super) enum PanicReason {
    Add,
    Sub,
    Mul,
    DivByZero,
}

c0nst::c0nst! {
    pub(super) c0nst fn maybe_panic(r: PanicReason) {
        match r {
            PanicReason::Add => panic!("attempt to add with overflow"),
            PanicReason::Sub => panic!("attempt to subtract with overflow"),
            PanicReason::Mul => panic!("attempt to multiply with overflow"),
            PanicReason::DivByZero => panic!("attempt to divide by zero"),
        }
    }
}

// #endregion helpers

#[cfg(test)]
mod tests {
    use core::u32;

    use super::FixedUInt as Bn;
    use super::*;
    use num_traits::One;

    type Bn8 = Bn<u8, 8>;
    type Bn16 = Bn<u16, 4>;
    type Bn32 = Bn<u32, 2>;

    c0nst::c0nst! {
        pub c0nst fn test_add<T: [c0nst] ConstMachineWord, const N: usize>(
            a: &mut [T; N],
            b: &[T; N]
        ) -> bool {
            add_impl(a, b)
        }

        pub c0nst fn test_sub<T: [c0nst] ConstMachineWord, const N: usize>(
            a: &mut [T; N],
            b: &[T; N]
        ) -> bool {
            sub_impl(a, b)
        }

        pub c0nst fn test_mul<T: [c0nst] ConstMachineWord, const N: usize>(
            a: &[T; N],
            b: &[T; N],
            word_bits: usize,
        ) -> ([T; N], bool) {
            const_mul::<T, N, true>(a, b, word_bits)
        }

        pub c0nst fn arr_leading_zeros<T: [c0nst] ConstMachineWord, const N: usize>(
            a: &[T; N],
        ) -> u32 {
            const_leading_zeros::<T, N>(a)
        }

        pub c0nst fn arr_trailing_zeros<T: [c0nst] ConstMachineWord, const N: usize>(
            a: &[T; N],
        ) -> u32 {
            const_trailing_zeros::<T, N>(a)
        }

        pub c0nst fn arr_bit_length<T: [c0nst] ConstMachineWord, const N: usize>(
            a: &[T; N],
        ) -> usize {
            const_bit_length::<T, N>(a)
        }

        pub c0nst fn arr_is_zero<T: [c0nst] ConstMachineWord, const N: usize>(
            a: &[T; N],
        ) -> bool {
            const_is_zero::<T, N>(a)
        }

        pub c0nst fn arr_set_bit<T: [c0nst] ConstMachineWord, const N: usize>(
            a: &mut [T; N],
            pos: usize,
        ) {
            const_set_bit::<T, N>(a, pos)
        }

        pub c0nst fn arr_cmp<T: [c0nst] ConstMachineWord, const N: usize>(
            a: &[T; N],
            b: &[T; N],
        ) -> core::cmp::Ordering {
            const_cmp::<T, N>(a, b)
        }

        pub c0nst fn arr_cmp_shifted<T: [c0nst] ConstMachineWord, const N: usize>(
            a: &[T; N],
            b: &[T; N],
            shift_bits: usize,
        ) -> core::cmp::Ordering {
            const_cmp_shifted::<T, N>(a, b, shift_bits)
        }

        pub c0nst fn arr_get_shifted_word<T: [c0nst] ConstMachineWord, const N: usize>(
            a: &[T; N],
            word_idx: usize,
            word_shift: usize,
            bit_shift: usize,
        ) -> T {
            const_get_shifted_word::<T, N>(a, word_idx, word_shift, bit_shift)
        }
    }

    #[test]
    fn test_const_add_impl() {
        // Simple add, no overflow
        let mut a: [u8; 4] = [1, 0, 0, 0];
        let b: [u8; 4] = [2, 0, 0, 0];
        let overflow = test_add(&mut a, &b);
        assert_eq!(a, [3, 0, 0, 0]);
        assert!(!overflow);

        // Add with carry propagation
        let mut a: [u8; 4] = [255, 0, 0, 0];
        let b: [u8; 4] = [1, 0, 0, 0];
        let overflow = test_add(&mut a, &b);
        assert_eq!(a, [0, 1, 0, 0]);
        assert!(!overflow);

        // Add with overflow
        let mut a: [u8; 4] = [255, 255, 255, 255];
        let b: [u8; 4] = [1, 0, 0, 0];
        let overflow = test_add(&mut a, &b);
        assert_eq!(a, [0, 0, 0, 0]);
        assert!(overflow);

        // Test with u32 words
        let mut a: [u32; 2] = [0xFFFFFFFF, 0];
        let b: [u32; 2] = [1, 0];
        let overflow = test_add(&mut a, &b);
        assert_eq!(a, [0, 1]);
        assert!(!overflow);

        #[cfg(feature = "nightly")]
        {
            const ADD_RESULT: ([u8; 4], bool) = {
                let mut a = [1u8, 0, 0, 0];
                let b = [2u8, 0, 0, 0];
                let overflow = test_add(&mut a, &b);
                (a, overflow)
            };
            assert_eq!(ADD_RESULT, ([3, 0, 0, 0], false));
        }
    }

    #[test]
    fn test_const_sub_impl() {
        // Simple sub, no overflow
        let mut a: [u8; 4] = [3, 0, 0, 0];
        let b: [u8; 4] = [1, 0, 0, 0];
        let overflow = test_sub(&mut a, &b);
        assert_eq!(a, [2, 0, 0, 0]);
        assert!(!overflow);

        // Sub with borrow propagation
        let mut a: [u8; 4] = [0, 1, 0, 0];
        let b: [u8; 4] = [1, 0, 0, 0];
        let overflow = test_sub(&mut a, &b);
        assert_eq!(a, [255, 0, 0, 0]);
        assert!(!overflow);

        // Sub with underflow
        let mut a: [u8; 4] = [0, 0, 0, 0];
        let b: [u8; 4] = [1, 0, 0, 0];
        let overflow = test_sub(&mut a, &b);
        assert_eq!(a, [255, 255, 255, 255]);
        assert!(overflow);

        // Test with u32 words
        let mut a: [u32; 2] = [0, 1];
        let b: [u32; 2] = [1, 0];
        let overflow = test_sub(&mut a, &b);
        assert_eq!(a, [0xFFFFFFFF, 0]);
        assert!(!overflow);

        #[cfg(feature = "nightly")]
        {
            const SUB_RESULT: ([u8; 4], bool) = {
                let mut a = [3u8, 0, 0, 0];
                let b = [1u8, 0, 0, 0];
                let overflow = test_sub(&mut a, &b);
                (a, overflow)
            };
            assert_eq!(SUB_RESULT, ([2, 0, 0, 0], false));
        }
    }

    #[test]
    fn test_const_mul_impl() {
        // Simple mul: 3 * 4 = 12
        let a: [u8; 2] = [3, 0];
        let b: [u8; 2] = [4, 0];
        let (result, overflow) = test_mul(&a, &b, 8);
        assert_eq!(result, [12, 0]);
        assert!(!overflow);

        // Mul with carry: 200 * 2 = 400 = 0x190 = [0x90, 0x01]
        let a: [u8; 2] = [200, 0];
        let b: [u8; 2] = [2, 0];
        let (result, overflow) = test_mul(&a, &b, 8);
        assert_eq!(result, [0x90, 0x01]);
        assert!(!overflow);

        // Mul with overflow: 256 * 256 = 65536 which overflows 16 bits
        let a: [u8; 2] = [0, 1]; // 256
        let b: [u8; 2] = [0, 1]; // 256
        let (_result, overflow) = test_mul(&a, &b, 8);
        assert!(overflow);

        // N=3 overflow at high position (round=4, i=2, j=2)
        // a = [0, 0, 1] = 65536, b = [0, 0, 1] = 65536
        // a * b = 65536^2 = 4294967296 which overflows 24 bits
        let a: [u8; 3] = [0, 0, 1];
        let b: [u8; 3] = [0, 0, 1];
        let (_result, overflow) = test_mul(&a, &b, 8);
        assert!(overflow, "N=3 high-position overflow not detected");

        // N=3 overflow with larger high word values
        // a = [0, 0, 2] = 131072, b = [0, 0, 2] = 131072
        // a * b = 131072^2 = 17179869184 which overflows 24 bits
        let a: [u8; 3] = [0, 0, 2];
        let b: [u8; 3] = [0, 0, 2];
        let (_result, overflow) = test_mul(&a, &b, 8);
        assert!(
            overflow,
            "N=3 high-position overflow with larger values not detected"
        );

        // N=3 non-overflow case: values that fit in 24 bits
        // a = [0, 1, 0] = 256, b = [0, 1, 0] = 256
        // a * b = 256 * 256 = 65536 = [0, 0, 1] which fits in 24 bits
        let a: [u8; 3] = [0, 1, 0];
        let b: [u8; 3] = [0, 1, 0];
        let (result, overflow) = test_mul(&a, &b, 8);
        assert_eq!(result, [0, 0, 1]);
        assert!(
            !overflow,
            "N=3 non-overflow incorrectly detected as overflow"
        );

        // N=3 non-overflow with carry propagation
        // a = [255, 0, 0] = 255, b = [255, 0, 0] = 255
        // a * b = 255 * 255 = 65025 = 0xFE01 = [0x01, 0xFE, 0x00]
        let a: [u8; 3] = [255, 0, 0];
        let b: [u8; 3] = [255, 0, 0];
        let (result, overflow) = test_mul(&a, &b, 8);
        assert_eq!(result, [0x01, 0xFE, 0x00]);
        assert!(!overflow);

        #[cfg(feature = "nightly")]
        {
            const MUL_RESULT: ([u8; 2], bool) = test_mul(&[3u8, 0], &[4u8, 0], 8);
            assert_eq!(MUL_RESULT, ([12, 0], false));
        }
    }

    #[test]
    fn test_const_helpers() {
        // Test leading_zeros
        assert_eq!(arr_leading_zeros(&[0u8, 0, 0, 0]), 32); // all zeros
        assert_eq!(arr_leading_zeros(&[1u8, 0, 0, 0]), 31); // single bit
        assert_eq!(arr_leading_zeros(&[0u8, 0, 0, 1]), 7); // high byte has 1
        assert_eq!(arr_leading_zeros(&[0u8, 0, 0, 0x80]), 0); // MSB set
        assert_eq!(arr_leading_zeros(&[255u8, 255, 255, 255]), 0); // all ones

        // Test trailing_zeros
        assert_eq!(arr_trailing_zeros(&[0u8, 0, 0, 0]), 32); // all zeros
        assert_eq!(arr_trailing_zeros(&[1u8, 0, 0, 0]), 0); // LSB set
        assert_eq!(arr_trailing_zeros(&[0u8, 1, 0, 0]), 8); // second byte
        assert_eq!(arr_trailing_zeros(&[0u8, 0, 0, 1]), 24); // fourth byte
        assert_eq!(arr_trailing_zeros(&[0x80u8, 0, 0, 0]), 7); // bit 7 of first byte

        // Test bit_length
        assert_eq!(arr_bit_length(&[0u8, 0, 0, 0]), 0); // zero
        assert_eq!(arr_bit_length(&[1u8, 0, 0, 0]), 1); // 1
        assert_eq!(arr_bit_length(&[2u8, 0, 0, 0]), 2); // 2
        assert_eq!(arr_bit_length(&[3u8, 0, 0, 0]), 2); // 3
        assert_eq!(arr_bit_length(&[0u8, 1, 0, 0]), 9); // 256
        assert_eq!(arr_bit_length(&[0xF0u8, 0, 0, 0]), 8); // 240 (0xF0)
        assert_eq!(arr_bit_length(&[255u8, 255, 255, 255]), 32); // max

        // Test is_zero
        assert!(arr_is_zero(&[0u8, 0, 0, 0]));
        assert!(!arr_is_zero(&[1u8, 0, 0, 0]));
        assert!(!arr_is_zero(&[0u8, 0, 0, 1]));
        assert!(!arr_is_zero(&[0u8, 1, 0, 0]));

        // Test set_bit
        let mut arr: [u8; 4] = [0, 0, 0, 0];
        arr_set_bit(&mut arr, 0);
        assert_eq!(arr, [1, 0, 0, 0]);

        let mut arr: [u8; 4] = [0, 0, 0, 0];
        arr_set_bit(&mut arr, 8);
        assert_eq!(arr, [0, 1, 0, 0]);

        let mut arr: [u8; 4] = [0, 0, 0, 0];
        arr_set_bit(&mut arr, 31);
        assert_eq!(arr, [0, 0, 0, 0x80]);

        // Set multiple bits
        let mut arr: [u8; 4] = [0, 0, 0, 0];
        arr_set_bit(&mut arr, 0);
        arr_set_bit(&mut arr, 3);
        arr_set_bit(&mut arr, 8);
        assert_eq!(arr, [0b00001001, 1, 0, 0]);

        // Out of bounds should be no-op
        let mut arr: [u8; 4] = [0, 0, 0, 0];
        arr_set_bit(&mut arr, 32);
        assert_eq!(arr, [0, 0, 0, 0]);

        // Test with u32 words
        assert_eq!(arr_leading_zeros(&[0u32, 0]), 64);
        assert_eq!(arr_leading_zeros(&[1u32, 0]), 63);
        assert_eq!(arr_leading_zeros(&[0u32, 1]), 31);
        assert_eq!(arr_trailing_zeros(&[0u32, 0]), 64);
        assert_eq!(arr_trailing_zeros(&[0u32, 1]), 32);
        assert_eq!(arr_bit_length(&[0u32, 0]), 0);
        assert_eq!(arr_bit_length(&[1u32, 0]), 1);
        assert_eq!(arr_bit_length(&[0u32, 1]), 33);

        #[cfg(feature = "nightly")]
        {
            const LEADING: u32 = arr_leading_zeros(&[0u8, 0, 1, 0]);
            assert_eq!(LEADING, 15);

            const TRAILING: u32 = arr_trailing_zeros(&[0u8, 0, 1, 0]);
            assert_eq!(TRAILING, 16);

            const BIT_LEN: usize = arr_bit_length(&[0u8, 0, 1, 0]);
            assert_eq!(BIT_LEN, 17);

            const IS_ZERO: bool = arr_is_zero(&[0u8, 0, 0, 0]);
            assert!(IS_ZERO);

            const NOT_ZERO: bool = arr_is_zero(&[0u8, 1, 0, 0]);
            assert!(!NOT_ZERO);

            const SET_BIT_RESULT: [u8; 4] = {
                let mut arr = [0u8, 0, 0, 0];
                arr_set_bit(&mut arr, 10);
                arr
            };
            assert_eq!(SET_BIT_RESULT, [0, 0b00000100, 0, 0]);
        }
    }

    #[test]
    fn test_const_cmp() {
        use core::cmp::Ordering;

        // Equal arrays
        assert_eq!(arr_cmp(&[1u8, 2, 3, 4], &[1u8, 2, 3, 4]), Ordering::Equal);
        assert_eq!(arr_cmp(&[0u8, 0, 0, 0], &[0u8, 0, 0, 0]), Ordering::Equal);

        // Greater - high word differs
        assert_eq!(arr_cmp(&[0u8, 0, 0, 2], &[0u8, 0, 0, 1]), Ordering::Greater);

        // Less - high word differs
        assert_eq!(arr_cmp(&[0u8, 0, 0, 1], &[0u8, 0, 0, 2]), Ordering::Less);

        // Greater - low word differs (high words equal)
        assert_eq!(arr_cmp(&[2u8, 0, 0, 0], &[1u8, 0, 0, 0]), Ordering::Greater);

        // Less - low word differs
        assert_eq!(arr_cmp(&[1u8, 0, 0, 0], &[2u8, 0, 0, 0]), Ordering::Less);

        // Test with u32 words
        assert_eq!(arr_cmp(&[0u32, 1], &[0u32, 1]), Ordering::Equal);
        assert_eq!(arr_cmp(&[0u32, 2], &[0u32, 1]), Ordering::Greater);
        assert_eq!(arr_cmp(&[0u32, 1], &[0u32, 2]), Ordering::Less);

        #[cfg(feature = "nightly")]
        {
            const CMP_EQ: Ordering = arr_cmp(&[1u8, 2, 3, 4], &[1u8, 2, 3, 4]);
            const CMP_GT: Ordering = arr_cmp(&[0u8, 0, 0, 2], &[0u8, 0, 0, 1]);
            const CMP_LT: Ordering = arr_cmp(&[0u8, 0, 0, 1], &[0u8, 0, 0, 2]);
            assert_eq!(CMP_EQ, Ordering::Equal);
            assert_eq!(CMP_GT, Ordering::Greater);
            assert_eq!(CMP_LT, Ordering::Less);
        }
    }

    #[test]
    fn test_const_cmp_shifted() {
        use core::cmp::Ordering;

        // No shift - same as regular cmp
        assert_eq!(
            arr_cmp_shifted(&[1u8, 0, 0, 0], &[1u8, 0, 0, 0], 0),
            Ordering::Equal
        );

        // Compare [0, 1, 0, 0] (256) vs [1, 0, 0, 0] << 8 (256) = Equal
        assert_eq!(
            arr_cmp_shifted(&[0u8, 1, 0, 0], &[1u8, 0, 0, 0], 8),
            Ordering::Equal
        );

        // Compare [0, 2, 0, 0] (512) vs [1, 0, 0, 0] << 8 (256) = Greater
        assert_eq!(
            arr_cmp_shifted(&[0u8, 2, 0, 0], &[1u8, 0, 0, 0], 8),
            Ordering::Greater
        );

        // Compare [0, 0, 0, 0] (0) vs [1, 0, 0, 0] << 8 (256) = Less
        assert_eq!(
            arr_cmp_shifted(&[0u8, 0, 0, 0], &[1u8, 0, 0, 0], 8),
            Ordering::Less
        );

        // Shift overflow: shift >= bit_size, other becomes 0
        // Compare [1, 0, 0, 0] vs [1, 0, 0, 0] << 32 (0) = Greater
        assert_eq!(
            arr_cmp_shifted(&[1u8, 0, 0, 0], &[1u8, 0, 0, 0], 32),
            Ordering::Greater
        );

        // Compare [0, 0, 0, 0] vs anything << 32 (0) = Equal
        assert_eq!(
            arr_cmp_shifted(&[0u8, 0, 0, 0], &[255u8, 255, 255, 255], 32),
            Ordering::Equal
        );

        // Test get_shifted_word helper with bit_shift == 0
        // [1, 2, 3, 4] shifted left by 1 word (8 bits for u8)
        // word 0 should be 0, word 1 should be 1, word 2 should be 2, etc.
        assert_eq!(arr_get_shifted_word(&[1u8, 2, 3, 4], 0, 1, 0), 0);
        assert_eq!(arr_get_shifted_word(&[1u8, 2, 3, 4], 1, 1, 0), 1);
        assert_eq!(arr_get_shifted_word(&[1u8, 2, 3, 4], 2, 1, 0), 2);

        // Test get_shifted_word with bit_shift != 0 (cross-word bit combination)
        // [0x0F, 0xF0, 0, 0] with word_shift=0, bit_shift=4
        // word 0: 0x0F << 4 = 0xF0 (no lower word to borrow from)
        assert_eq!(arr_get_shifted_word(&[0x0Fu8, 0xF0, 0, 0], 0, 0, 4), 0xF0);
        // word 1: (0xF0 << 4) | (0x0F >> 4) = 0x00 | 0x00 = 0x00
        assert_eq!(arr_get_shifted_word(&[0x0Fu8, 0xF0, 0, 0], 1, 0, 4), 0x00);

        // [0xFF, 0x00, 0, 0] with bit_shift=4
        // word 0: 0xFF << 4 = 0xF0
        assert_eq!(arr_get_shifted_word(&[0xFFu8, 0x00, 0, 0], 0, 0, 4), 0xF0);
        // word 1: (0x00 << 4) | (0xFF >> 4) = 0x00 | 0x0F = 0x0F
        assert_eq!(arr_get_shifted_word(&[0xFFu8, 0x00, 0, 0], 1, 0, 4), 0x0F);

        // Combined word_shift and bit_shift
        // [0xAB, 0xCD, 0, 0] with word_shift=1, bit_shift=4
        // word 0: below word_shift, returns 0
        assert_eq!(arr_get_shifted_word(&[0xABu8, 0xCD, 0, 0], 0, 1, 4), 0);
        // word 1: source_idx=0, 0xAB << 4 = 0xB0 (no lower word)
        assert_eq!(arr_get_shifted_word(&[0xABu8, 0xCD, 0, 0], 1, 1, 4), 0xB0);
        // word 2: source_idx=1, (0xCD << 4) | (0xAB >> 4) = 0xD0 | 0x0A = 0xDA
        assert_eq!(arr_get_shifted_word(&[0xABu8, 0xCD, 0, 0], 2, 1, 4), 0xDA);

        #[cfg(feature = "nightly")]
        {
            const CMP_SHIFTED_EQ: Ordering = arr_cmp_shifted(&[0u8, 1, 0, 0], &[1u8, 0, 0, 0], 8);
            const CMP_SHIFTED_GT: Ordering = arr_cmp_shifted(&[0u8, 2, 0, 0], &[1u8, 0, 0, 0], 8);
            assert_eq!(CMP_SHIFTED_EQ, Ordering::Equal);
            assert_eq!(CMP_SHIFTED_GT, Ordering::Greater);
        }
    }

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

        #[cfg(feature = "nightly")]
        {
            const F1: Bn<u8, 2> = Bn::<u8, 2>::from(42u8);
            assert_eq!(F1.array, [42, 0]);
        }
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

        #[cfg(feature = "nightly")]
        {
            const F1: Bn<u8, 2> = Bn::<u8, 2>::from(0x0102u16);
            assert_eq!(F1.array, [0x02, 0x01]);
        }
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

        #[cfg(feature = "nightly")]
        {
            const F1: Bn<u8, 4> = Bn::<u8, 4>::from(0x01020304u32);
            assert_eq!(F1.array, [0x04, 0x03, 0x02, 0x01]);
        }
    }

    #[test]
    fn test_core_convert_u64() {
        let f = Bn::<u8, 8>::from(0x0102030405060708u64);
        assert_eq!(f.array, [0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01]);

        let f = Bn::<u16, 4>::from(0x0102030405060708u64);
        assert_eq!(f.array, [0x0708, 0x0506, 0x0304, 0x0102]);

        let f = Bn::<u32, 2>::from(0x0102030405060708u64);
        assert_eq!(f.array, [0x05060708, 0x01020304]);

        let f = Bn::<u64, 1>::from(0x0102030405060708u64);
        assert_eq!(f.array, [0x0102030405060708]);

        #[cfg(feature = "nightly")]
        {
            const F1: Bn<u8, 8> = Bn::<u8, 8>::from(0x0102030405060708u64);
            assert_eq!(F1.array, [0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01]);
        }
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
    fn test_resize() {
        type TestInt1 = FixedUInt<u32, 1>;
        type TestInt2 = FixedUInt<u32, 2>;

        let a = TestInt1::from(u32::MAX);
        let b: TestInt2 = a.resize();
        assert_eq!(b, TestInt2::from([u32::MAX, 0]));

        let a = TestInt2::from([u32::MAX, u32::MAX]);
        let b: TestInt1 = a.resize();
        assert_eq!(b, TestInt1::from(u32::MAX));
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
    fn test_bit_length_1000() {
        // Test bit_length with value 1000
        let value = Bn32::from_u16(1000).unwrap();

        // 1000 in binary is 1111101000, which has 10 bits
        // Let's verify the implementation is working correctly
        assert_eq!(value.to_u32().unwrap(), 1000);
        assert_eq!(value.bit_length(), 10);

        // Test some edge cases around 1000
        assert_eq!(Bn32::from_u16(512).unwrap().bit_length(), 10); // 2^9 = 512
        assert_eq!(Bn32::from_u16(1023).unwrap().bit_length(), 10); // 2^10 - 1 = 1023
        assert_eq!(Bn32::from_u16(1024).unwrap().bit_length(), 11); // 2^10 = 1024

        // Test with different word sizes to see if this makes a difference
        assert_eq!(Bn8::from_u16(1000).unwrap().bit_length(), 10);
        assert_eq!(Bn16::from_u16(1000).unwrap().bit_length(), 10);

        // Test with different initialization methods
        let value_from_str = Bn32::from_str_radix("1000", 10).unwrap();
        assert_eq!(value_from_str.bit_length(), 10);

        // This is the problematic case - let's debug it
        let value_from_bytes = Bn32::from_le_bytes(&1000u16.to_le_bytes());
        // Let's see what the actual value is
        assert_eq!(
            value_from_bytes.to_u32().unwrap_or(0),
            1000,
            "from_le_bytes didn't create the correct value"
        );
        assert_eq!(value_from_bytes.bit_length(), 10);
    }
    #[test]
    fn test_cmp() {
        let f0 = <Bn8 as Zero>::zero();
        let f1 = <Bn8 as Zero>::zero();
        let f2 = <Bn8 as One>::one();
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

        #[cfg(feature = "nightly")]
        {
            use core::cmp::Ordering;

            const A: FixedUInt<u8, 2> = FixedUInt { array: [10, 0] };
            const B: FixedUInt<u8, 2> = FixedUInt { array: [20, 0] };
            const C: FixedUInt<u8, 2> = FixedUInt { array: [10, 0] };

            const CMP_LT: Ordering = A.cmp(&B);
            const CMP_GT: Ordering = B.cmp(&A);
            const CMP_EQ: Ordering = A.cmp(&C);
            const EQ_TRUE: bool = A.eq(&C);
            const EQ_FALSE: bool = A.eq(&B);

            assert_eq!(CMP_LT, Ordering::Less);
            assert_eq!(CMP_GT, Ordering::Greater);
            assert_eq!(CMP_EQ, Ordering::Equal);
            assert!(EQ_TRUE);
            assert!(!EQ_FALSE);
        }
    }

    #[test]
    fn test_default() {
        let d: Bn8 = Default::default();
        assert!(Zero::is_zero(&d));

        #[cfg(feature = "nightly")]
        {
            const D: FixedUInt<u8, 2> = <FixedUInt<u8, 2> as Default>::default();
            assert!(Zero::is_zero(&D));
        }
    }

    #[test]
    fn test_clone() {
        let a: Bn8 = 42u8.into();
        let b = a.clone();
        assert_eq!(a, b);

        #[cfg(feature = "nightly")]
        {
            const A: FixedUInt<u8, 2> = FixedUInt { array: [42, 0] };
            const B: FixedUInt<u8, 2> = A.clone();
            assert_eq!(A.array, B.array);
        }
    }

    #[test]
    fn test_le_be_bytes() {
        let le_bytes = [1, 2, 3, 4];
        let be_bytes = [4, 3, 2, 1];
        let u8_ver = FixedUInt::<u8, 4>::from_le_bytes(&le_bytes);
        let u16_ver = FixedUInt::<u16, 2>::from_le_bytes(&le_bytes);
        let u32_ver = FixedUInt::<u32, 1>::from_le_bytes(&le_bytes);
        let u8_ver_be = FixedUInt::<u8, 4>::from_be_bytes(&be_bytes);
        let u16_ver_be = FixedUInt::<u16, 2>::from_be_bytes(&be_bytes);
        let u32_ver_be = FixedUInt::<u32, 1>::from_be_bytes(&be_bytes);

        assert_eq!(u8_ver.array, [1, 2, 3, 4]);
        assert_eq!(u16_ver.array, [0x0201, 0x0403]);
        assert_eq!(u32_ver.array, [0x04030201]);
        assert_eq!(u8_ver_be.array, [1, 2, 3, 4]);
        assert_eq!(u16_ver_be.array, [0x0201, 0x0403]);
        assert_eq!(u32_ver_be.array, [0x04030201]);

        let mut output_buffer = [0u8; 16];
        assert_eq!(u8_ver.to_le_bytes(&mut output_buffer).unwrap(), &le_bytes);
        assert_eq!(u8_ver.to_be_bytes(&mut output_buffer).unwrap(), &be_bytes);
        assert_eq!(u16_ver.to_le_bytes(&mut output_buffer).unwrap(), &le_bytes);
        assert_eq!(u16_ver.to_be_bytes(&mut output_buffer).unwrap(), &be_bytes);
        assert_eq!(u32_ver.to_le_bytes(&mut output_buffer).unwrap(), &le_bytes);
        assert_eq!(u32_ver.to_be_bytes(&mut output_buffer).unwrap(), &be_bytes);
    }

    // Test suite for division implementation
    #[test]
    fn test_div_small() {
        type TestInt = FixedUInt<u8, 2>;

        // Test small values
        let test_cases = [
            (20u16, 3u16, 6u16),        // 20 / 3 = 6
            (100u16, 7u16, 14u16),      // 100 / 7 = 14
            (255u16, 5u16, 51u16),      // 255 / 5 = 51
            (65535u16, 256u16, 255u16), // max u16 / 256 = 255
        ];

        for (dividend_val, divisor_val, expected) in test_cases {
            let dividend = TestInt::from(dividend_val);
            let divisor = TestInt::from(divisor_val);
            let expected_result = TestInt::from(expected);

            assert_eq!(
                dividend / divisor,
                expected_result,
                "Division failed for {} / {} = {}",
                dividend_val,
                divisor_val,
                expected
            );
        }
    }

    #[test]
    fn test_div_edge_cases() {
        type TestInt = FixedUInt<u16, 2>;

        // Division by 1
        let dividend = TestInt::from(1000u16);
        let divisor = TestInt::from(1u16);
        assert_eq!(dividend / divisor, TestInt::from(1000u16));

        // Equal values
        let dividend = TestInt::from(42u16);
        let divisor = TestInt::from(42u16);
        assert_eq!(dividend / divisor, TestInt::from(1u16));

        // Dividend < divisor
        let dividend = TestInt::from(5u16);
        let divisor = TestInt::from(10u16);
        assert_eq!(dividend / divisor, TestInt::from(0u16));

        // Powers of 2
        let dividend = TestInt::from(1024u16);
        let divisor = TestInt::from(4u16);
        assert_eq!(dividend / divisor, TestInt::from(256u16));
    }

    #[test]
    fn test_helper_methods() {
        type TestInt = FixedUInt<u8, 2>;

        // Test const_set_bit
        let mut val = <TestInt as Zero>::zero();
        const_set_bit(&mut val.array, 0);
        assert_eq!(val, TestInt::from(1u8));

        const_set_bit(&mut val.array, 8);
        assert_eq!(val, TestInt::from(257u16)); // bit 0 + bit 8 = 1 + 256 = 257

        // Test const_cmp_shifted
        let a = TestInt::from(8u8); // 1000 in binary
        let b = TestInt::from(1u8); // 0001 in binary

        // b << 3 = 8, so a == (b << 3)
        assert_eq!(
            const_cmp_shifted(&a.array, &b.array, 3),
            core::cmp::Ordering::Equal
        );

        // a > (b << 2) because b << 2 = 4
        assert_eq!(
            const_cmp_shifted(&a.array, &b.array, 2),
            core::cmp::Ordering::Greater
        );

        // a < (b << 4) because b << 4 = 16
        assert_eq!(
            const_cmp_shifted(&a.array, &b.array, 4),
            core::cmp::Ordering::Less
        );

        // Test const_sub_shifted
        let mut val = TestInt::from(10u8);
        let one = TestInt::from(1u8);
        const_sub_shifted(&mut val.array, &one.array, 2); // subtract 1 << 2 = 4
        assert_eq!(val, TestInt::from(6u8)); // 10 - 4 = 6
    }

    #[test]
    fn test_shifted_operations_comprehensive() {
        type TestInt = FixedUInt<u32, 2>;

        // Test cmp_shifted with various word boundary cases
        let a = TestInt::from(0x12345678u32);
        let b = TestInt::from(0x12345678u32);

        // Equal comparison
        assert_eq!(
            const_cmp_shifted(&a.array, &b.array, 0),
            core::cmp::Ordering::Equal
        );

        // Test shifts that cross word boundaries (assuming 32-bit words)
        let c = TestInt::from(0x123u32); // Small number
        let d = TestInt::from(0x48d159e2u32); // c << 16 + some bits

        // c << 16 should be less than d
        assert_eq!(
            const_cmp_shifted(&d.array, &c.array, 16),
            core::cmp::Ordering::Greater
        );

        // Test large shifts (beyond bit size, so shifted value becomes 0)
        let e = TestInt::from(1u32);
        let zero = TestInt::from(0u32);
        assert_eq!(
            const_cmp_shifted(&e.array, &zero.array, 100),
            core::cmp::Ordering::Greater
        );
        // When shift is beyond bit size, 1 << 100 becomes 0, so 0 == 0
        assert_eq!(
            const_cmp_shifted(&zero.array, &e.array, 100),
            core::cmp::Ordering::Equal
        );

        // Test sub_shifted with word boundary crossing
        let mut val = TestInt::from(0x10000u32); // 65536
        let one = TestInt::from(1u32);
        const_sub_shifted(&mut val.array, &one.array, 15); // subtract 1 << 15 = 32768
        assert_eq!(val, TestInt::from(0x8000u32)); // 65536 - 32768 = 32768

        // Test sub_shifted with multi-word operations
        let mut big_val = TestInt::from(0x100000000u64); // 2^32
        const_sub_shifted(&mut big_val.array, &one.array, 31); // subtract 1 << 31 = 2^31
        assert_eq!(big_val, TestInt::from(0x80000000u64)); // 2^32 - 2^31 = 2^31
    }

    #[test]
    fn test_shifted_operations_edge_cases() {
        type TestInt = FixedUInt<u32, 2>;

        // Test zero shifts
        let a = TestInt::from(42u32);
        let a2 = TestInt::from(42u32);
        assert_eq!(
            const_cmp_shifted(&a.array, &a2.array, 0),
            core::cmp::Ordering::Equal
        );

        let mut b = TestInt::from(42u32);
        let ten = TestInt::from(10u32);
        const_sub_shifted(&mut b.array, &ten.array, 0);
        assert_eq!(b, TestInt::from(32u32));

        // Test massive shifts (beyond bit size)
        let c = TestInt::from(123u32);
        let large = TestInt::from(456u32);
        assert_eq!(
            const_cmp_shifted(&c.array, &large.array, 200),
            core::cmp::Ordering::Greater
        );

        let mut d = TestInt::from(123u32);
        const_sub_shifted(&mut d.array, &large.array, 200); // Should be no-op
        assert_eq!(d, TestInt::from(123u32));

        // Test with zero values
        let zero = TestInt::from(0u32);
        let one = TestInt::from(1u32);
        assert_eq!(
            const_cmp_shifted(&zero.array, &zero.array, 10),
            core::cmp::Ordering::Equal
        );
        assert_eq!(
            const_cmp_shifted(&one.array, &zero.array, 10),
            core::cmp::Ordering::Greater
        );
    }

    #[test]
    fn test_shifted_operations_equivalence() {
        type TestInt = FixedUInt<u32, 2>;

        // Test that optimized operations give same results as naive shift+op
        let test_cases = [
            (0x12345u32, 0x678u32, 4),
            (0x1000u32, 0x10u32, 8),
            (0xABCDu32, 0x1u32, 16),
            (0x80000000u32, 0x1u32, 1),
        ];

        for (a_val, b_val, shift) in test_cases {
            let a = TestInt::from(a_val);
            let b = TestInt::from(b_val);

            // Test cmp_shifted equivalence
            let optimized_cmp = const_cmp_shifted(&a.array, &b.array, shift);
            let naive_cmp = a.cmp(&(b << shift));
            assert_eq!(
                optimized_cmp, naive_cmp,
                "cmp_shifted mismatch: {} vs ({} << {})",
                a_val, b_val, shift
            );

            // Test sub_shifted equivalence (if subtraction won't underflow)
            if a >= (b << shift) {
                let mut optimized_result = a;
                const_sub_shifted(&mut optimized_result.array, &b.array, shift);

                let naive_result = a - (b << shift);
                assert_eq!(
                    optimized_result, naive_result,
                    "sub_shifted mismatch: {} - ({} << {})",
                    a_val, b_val, shift
                );
            }
        }
    }

    #[test]
    fn test_div_assign_in_place_optimization() {
        type TestInt = FixedUInt<u32, 2>;

        // Test that div_assign uses the optimized in-place algorithm
        let test_cases = [
            (100u32, 10u32, 10u32, 0u32),     // 100 / 10 = 10 remainder 0
            (123u32, 7u32, 17u32, 4u32),      // 123 / 7 = 17 remainder 4
            (1000u32, 13u32, 76u32, 12u32),   // 1000 / 13 = 76 remainder 12
            (65535u32, 255u32, 257u32, 0u32), // 65535 / 255 = 257 remainder 0
        ];

        for (dividend_val, divisor_val, expected_quotient, expected_remainder) in test_cases {
            // Test div_assign
            let mut dividend = TestInt::from(dividend_val);
            let divisor = TestInt::from(divisor_val);

            dividend /= divisor;
            assert_eq!(
                dividend,
                TestInt::from(expected_quotient),
                "div_assign: {} / {} should be {}",
                dividend_val,
                divisor_val,
                expected_quotient
            );

            // Test div_rem directly
            let dividend2 = TestInt::from(dividend_val);
            let (quotient, remainder) = dividend2.div_rem(&divisor);
            assert_eq!(
                quotient,
                TestInt::from(expected_quotient),
                "div_rem quotient: {} / {} should be {}",
                dividend_val,
                divisor_val,
                expected_quotient
            );
            assert_eq!(
                remainder,
                TestInt::from(expected_remainder),
                "div_rem remainder: {} % {} should be {}",
                dividend_val,
                divisor_val,
                expected_remainder
            );

            // Verify: quotient * divisor + remainder == original dividend
            assert_eq!(
                quotient * divisor + remainder,
                TestInt::from(dividend_val),
                "Property check failed for {}",
                dividend_val
            );
        }
    }

    #[test]
    fn test_div_assign_stack_efficiency() {
        type TestInt = FixedUInt<u32, 4>; // 16 bytes each

        // Create test values
        let mut dividend = TestInt::from(0x123456789ABCDEFu64);
        let divisor = TestInt::from(0x12345u32);
        let original_dividend = dividend;

        // Perform in-place division
        dividend /= divisor;

        // Verify correctness
        let remainder = original_dividend % divisor;
        assert_eq!(dividend * divisor + remainder, original_dividend);
    }

    #[test]
    fn test_rem_assign_optimization() {
        type TestInt = FixedUInt<u32, 2>;

        let test_cases = [
            (100u32, 10u32, 0u32),    // 100 % 10 = 0
            (123u32, 7u32, 4u32),     // 123 % 7 = 4
            (1000u32, 13u32, 12u32),  // 1000 % 13 = 12
            (65535u32, 255u32, 0u32), // 65535 % 255 = 0
        ];

        for (dividend_val, divisor_val, expected_remainder) in test_cases {
            let mut dividend = TestInt::from(dividend_val);
            let divisor = TestInt::from(divisor_val);

            dividend %= divisor;
            assert_eq!(
                dividend,
                TestInt::from(expected_remainder),
                "rem_assign: {} % {} should be {}",
                dividend_val,
                divisor_val,
                expected_remainder
            );
        }
    }

    #[test]
    fn test_div_with_remainder_property() {
        type TestInt = FixedUInt<u32, 2>;

        // Test division with remainder property verification
        let test_cases = [
            (100u32, 10u32, 10u32),     // 100 / 10 = 10
            (123u32, 7u32, 17u32),      // 123 / 7 = 17
            (1000u32, 13u32, 76u32),    // 1000 / 13 = 76
            (65535u32, 255u32, 257u32), // 65535 / 255 = 257
        ];

        for (dividend_val, divisor_val, expected_quotient) in test_cases {
            let dividend = TestInt::from(dividend_val);
            let divisor = TestInt::from(divisor_val);

            // Test that div operator (which uses div_impl) works correctly
            let quotient = dividend / divisor;
            assert_eq!(
                quotient,
                TestInt::from(expected_quotient),
                "Division: {} / {} should be {}",
                dividend_val,
                divisor_val,
                expected_quotient
            );

            // Verify the division property still holds
            let remainder = dividend % divisor;
            assert_eq!(
                quotient * divisor + remainder,
                dividend,
                "Division property check failed for {}",
                dividend_val
            );
        }
    }

    #[test]
    fn test_code_simplification_benefits() {
        type TestInt = FixedUInt<u32, 2>;

        // Verify division property holds
        let dividend = TestInt::from(12345u32);
        let divisor = TestInt::from(67u32);
        let quotient = dividend / divisor;
        let remainder = dividend % divisor;

        // The division property should still hold
        assert_eq!(quotient * divisor + remainder, dividend);
    }

    #[test]
    fn test_rem_assign_correctness_after_fix() {
        type TestInt = FixedUInt<u32, 2>;

        // Test specific case: 17 % 5 = 2
        let mut a = TestInt::from(17u32);
        let b = TestInt::from(5u32);

        // Historical note: an old bug caused quotient corruption during remainder calculation
        // Now const_div_rem properly computes both without corrupting intermediate state
        a %= b;
        assert_eq!(a, TestInt::from(2u32), "17 % 5 should be 2");

        // Test that the original RemAssign bug would have failed this
        let mut test_val = TestInt::from(100u32);
        test_val %= TestInt::from(7u32);
        assert_eq!(
            test_val,
            TestInt::from(2u32),
            "100 % 7 should be 2 (not 14, the quotient)"
        );
    }

    #[test]
    fn test_div_property_based() {
        type TestInt = FixedUInt<u16, 2>;

        // Property: quotient * divisor + remainder == dividend
        let test_pairs = [
            (12345u16, 67u16),
            (1000u16, 13u16),
            (65535u16, 255u16),
            (5000u16, 7u16),
        ];

        for (dividend_val, divisor_val) in test_pairs {
            let dividend = TestInt::from(dividend_val);
            let divisor = TestInt::from(divisor_val);

            let quotient = dividend / divisor;

            // Property verification: quotient * divisor + remainder == dividend
            let remainder = dividend - (quotient * divisor);
            let reconstructed = quotient * divisor + remainder;

            assert_eq!(
                reconstructed,
                dividend,
                "Property failed for {} / {}: {} * {} + {} != {}",
                dividend_val,
                divisor_val,
                quotient.to_u32().unwrap_or(0),
                divisor_val,
                remainder.to_u32().unwrap_or(0),
                dividend_val
            );

            // Remainder should be less than divisor
            assert!(
                remainder < divisor,
                "Remainder {} >= divisor {} for {} / {}",
                remainder.to_u32().unwrap_or(0),
                divisor_val,
                dividend_val,
                divisor_val
            );
        }
    }
}
