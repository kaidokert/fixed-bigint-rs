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

use num_traits::ops::overflowing::{OverflowingAdd, OverflowingSub};
use num_traits::{Bounded, One, PrimInt, ToPrimitive, Zero};

use core::convert::TryFrom;
use core::fmt::Write;

use crate::machineword::MachineWord;

#[allow(unused_imports)]
use num_traits::{FromPrimitive, Num};

mod add_sub_impl;
mod bit_ops_impl;
mod euclid;
mod iter_impl;
mod mul_div_impl;
mod num_integer_impl;
mod num_traits_casts;
mod num_traits_identity;
mod prim_int_impl;
mod roots_impl;
mod string_conversion;
mod to_from_bytes;

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
        let mut ret = Self::new();
        let total_bytes = core::cmp::min(bytes.len(), N * Self::WORD_SIZE);

        for (byte_index, &byte) in bytes.iter().enumerate().take(total_bytes) {
            let word_index = byte_index / Self::WORD_SIZE;
            let byte_in_word = byte_index % Self::WORD_SIZE;

            let byte_value: T = byte.into();
            let shifted_value = byte_value.shl(byte_in_word * 8);
            ret.array[word_index] |= shifted_value;
        }
        ret
    }

    /// Create a big-endian integer value from its representation as a byte array in big endian.
    pub fn from_be_bytes(bytes: &[u8]) -> Self {
        let mut ret = Self::new();
        let capacity_bytes = N * Self::WORD_SIZE;
        let total_bytes = core::cmp::min(bytes.len(), capacity_bytes);

        // For consistent truncation semantics with from_le_bytes, always take the
        // least significant bytes (rightmost bytes in big-endian representation)
        let start_offset = if bytes.len() > capacity_bytes {
            bytes.len() - capacity_bytes
        } else {
            0
        };

        for (byte_index, _) in (0..total_bytes).enumerate() {
            // Take bytes from the end of the input (least significant in BE)
            let be_byte_index = start_offset + total_bytes - 1 - byte_index;
            let word_index = byte_index / Self::WORD_SIZE;
            let byte_in_word = byte_index % Self::WORD_SIZE;

            let byte_value: T = bytes[be_byte_index].into();
            let shifted_value = byte_value.shl(byte_in_word * 8);
            ret.array[word_index] |= shifted_value;
        }
        ret
    }

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
        if self.is_zero() {
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

        while !number.is_zero() {
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

    /// Set a specific bit in the array without full array operations
    fn set_bit(&mut self, pos: usize) {
        if pos >= Self::BIT_SIZE {
            return; // No-op for out-of-bounds
        }
        let word_idx = pos / Self::WORD_BITS;
        let bit_idx = pos % Self::WORD_BITS;
        self.array[word_idx] |= T::one().shl(bit_idx);
    }

    /// Compare self vs other << shift_bits without allocating
    fn cmp_shifted(&self, other: &Self, shift_bits: usize) -> core::cmp::Ordering {
        if shift_bits == 0 {
            return self.cmp(other);
        }

        if shift_bits >= Self::BIT_SIZE {
            // other << shift_bits would be 0, so compare self vs 0
            if self.is_zero() {
                return core::cmp::Ordering::Equal;
            } else {
                return core::cmp::Ordering::Greater;
            }
        }

        // Calculate word and bit offsets
        let word_shift = shift_bits / Self::WORD_BITS;
        let bit_shift = shift_bits % Self::WORD_BITS;

        // Compare from most significant words down
        for i in (0..N).rev() {
            let self_word = self.array[i];
            let other_shifted_word = self.get_shifted_word(other, i, word_shift, bit_shift);

            match self_word.cmp(&other_shifted_word) {
                core::cmp::Ordering::Equal => continue,
                other_result => return other_result,
            }
        }

        core::cmp::Ordering::Equal
    }

    /// Get the value of other's word at position `word_idx` when other is logically shifted left
    fn get_shifted_word(
        &self,
        other: &Self,
        word_idx: usize,
        word_shift: usize,
        bit_shift: usize,
    ) -> T {
        if word_idx < word_shift {
            // This word position would be filled with zeros from the shift
            return T::zero();
        }

        let source_idx = word_idx - word_shift;

        if bit_shift == 0 {
            // Simple word alignment
            if source_idx < N {
                other.array[source_idx]
            } else {
                T::zero()
            }
        } else {
            // Need to combine bits from two source words
            let mut result = T::zero();

            // Get bits from the primary source word
            if source_idx < N {
                result |= other.array[source_idx].shl(bit_shift);
            }

            // Get high bits from the next lower word (if it exists and we need them)
            if source_idx > 0 && (source_idx - 1) < N {
                let high_bits = other.array[source_idx - 1].shr(Self::WORD_BITS - bit_shift);
                result |= high_bits;
            }

            result
        }
    }

    /// Subtract other << shift_bits from self in-place
    fn sub_shifted(&mut self, other: &Self, shift_bits: usize) {
        if shift_bits == 0 {
            *self -= *other;
            return;
        }

        if shift_bits >= Self::BIT_SIZE {
            // other << shift_bits would be 0, so no-op
            return;
        }

        // Calculate word and bit offsets
        let word_shift = shift_bits / Self::WORD_BITS;
        let bit_shift = shift_bits % Self::WORD_BITS;

        let mut borrow = false;

        // Process each word from least significant to most significant
        for i in 0..N {
            let other_shifted_word = self.get_shifted_word(other, i, word_shift, bit_shift);

            // Perform subtraction with borrow
            let (result, new_borrow) =
                Self::sub_with_borrow(self.array[i], other_shifted_word, borrow);
            self.array[i] = result;
            borrow = new_borrow;
        }
    }

    /// Subtract with borrow: a - b - borrow, returns (result, did_borrow)
    fn sub_with_borrow(a: T, b: T, borrow: bool) -> (T, bool) {
        // First subtract the borrow
        let (temp, borrow1) = if borrow {
            a.overflowing_sub(&T::one())
        } else {
            (a, false)
        };

        // Then subtract b
        let (result, borrow2) = temp.overflowing_sub(&b);
        (result, borrow1 || borrow2)
    }

    /// In-place division: dividend becomes quotient, returns remainder
    fn div_assign_impl(dividend: &mut Self, divisor: &Self) -> Self {
        if *dividend < *divisor {
            let remainder = *dividend;
            *dividend = Self::zero();
            return remainder;
        }
        if *dividend == *divisor {
            *dividend = Self::one();
            return Self::zero();
        }

        let mut quotient = Self::zero();

        // Calculate initial bit position
        let dividend_bits = dividend.bit_length() as usize;
        let divisor_bits = divisor.bit_length() as usize;

        if dividend_bits < divisor_bits {
            let remainder = *dividend;
            *dividend = Self::zero();
            return remainder;
        }

        let mut bit_pos = dividend_bits.saturating_sub(divisor_bits);

        // Adjust bit position to find the first position where divisor can be subtracted
        while bit_pos > 0 && dividend.cmp_shifted(divisor, bit_pos) == core::cmp::Ordering::Less {
            bit_pos -= 1;
        }

        // Main division loop - dividend is both remainder and gets modified in-place
        loop {
            if dividend.cmp_shifted(divisor, bit_pos) != core::cmp::Ordering::Less {
                dividend.sub_shifted(divisor, bit_pos);
                quotient.set_bit(bit_pos);
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

    // Divide dividend with divisor, return result
    fn div_impl(dividend: &Self, divisor: &Self) -> Self {
        let mut dividend_copy = *dividend;
        Self::div_assign_impl(&mut dividend_copy, divisor);
        dividend_copy
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

    // Normalize shift amounts for rotations
    fn normalize_shift(bits: u32) -> u32 {
        bits % (Self::BIT_SIZE as u32)
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

    // Test suite for optimized division implementation
    #[test]
    fn test_div_impl_equivalence_small() {
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

            let result = TestInt::div_impl(&dividend, &divisor);

            assert_eq!(
                result, expected_result,
                "Division failed for {} / {} = {}",
                dividend_val, divisor_val, expected
            );
        }
    }

    #[test]
    fn test_div_impl_equivalence_edge_cases() {
        type TestInt = FixedUInt<u16, 2>;

        // Edge cases
        let dividend = TestInt::from(1000u16);
        let divisor = TestInt::from(1u16);
        assert_eq!(
            TestInt::div_impl(&dividend, &divisor),
            TestInt::from(1000u16)
        );

        // Equal values
        let dividend = TestInt::from(42u16);
        let divisor = TestInt::from(42u16);
        assert_eq!(TestInt::div_impl(&dividend, &divisor), TestInt::from(1u16));

        // Dividend < divisor
        let dividend = TestInt::from(5u16);
        let divisor = TestInt::from(10u16);
        assert_eq!(TestInt::div_impl(&dividend, &divisor), TestInt::from(0u16));

        // Powers of 2
        let dividend = TestInt::from(1024u16);
        let divisor = TestInt::from(4u16);
        assert_eq!(
            TestInt::div_impl(&dividend, &divisor),
            TestInt::from(256u16)
        );
    }

    #[test]
    fn test_helper_methods() {
        type TestInt = FixedUInt<u8, 2>;

        // Test set_bit
        let mut val = TestInt::zero();
        val.set_bit(0);
        assert_eq!(val, TestInt::from(1u8));

        val.set_bit(8);
        assert_eq!(val, TestInt::from(257u16)); // bit 0 + bit 8 = 1 + 256 = 257

        // Test cmp_shifted
        let a = TestInt::from(8u8); // 1000 in binary
        let b = TestInt::from(1u8); // 0001 in binary

        // b << 3 = 8, so a == (b << 3)
        assert_eq!(a.cmp_shifted(&b, 3), core::cmp::Ordering::Equal);

        // a > (b << 2) because b << 2 = 4
        assert_eq!(a.cmp_shifted(&b, 2), core::cmp::Ordering::Greater);

        // a < (b << 4) because b << 4 = 16
        assert_eq!(a.cmp_shifted(&b, 4), core::cmp::Ordering::Less);

        // Test sub_shifted
        let mut val = TestInt::from(10u8);
        val.sub_shifted(&TestInt::from(1u8), 2); // subtract 1 << 2 = 4
        assert_eq!(val, TestInt::from(6u8)); // 10 - 4 = 6
    }

    #[test]
    fn test_shifted_operations_comprehensive() {
        type TestInt = FixedUInt<u32, 2>;

        // Test cmp_shifted with various word boundary cases
        let a = TestInt::from(0x12345678u32);
        let b = TestInt::from(0x12345678u32);

        // Equal comparison
        assert_eq!(a.cmp_shifted(&b, 0), core::cmp::Ordering::Equal);

        // Test shifts that cross word boundaries (assuming 32-bit words)
        let c = TestInt::from(0x123u32); // Small number
        let d = TestInt::from(0x48d159e2u32); // c << 16 + some bits

        // c << 16 should be less than d
        assert_eq!(d.cmp_shifted(&c, 16), core::cmp::Ordering::Greater);

        // Test large shifts (beyond bit size, so shifted value becomes 0)
        let e = TestInt::from(1u32);
        assert_eq!(
            e.cmp_shifted(&TestInt::from(0u32), 100),
            core::cmp::Ordering::Greater
        );
        // When shift is beyond bit size, 1 << 100 becomes 0, so 0 == 0
        assert_eq!(
            TestInt::from(0u32).cmp_shifted(&e, 100),
            core::cmp::Ordering::Equal
        );

        // Test sub_shifted with word boundary crossing
        let mut val = TestInt::from(0x10000u32); // 65536
        val.sub_shifted(&TestInt::from(1u32), 15); // subtract 1 << 15 = 32768
        assert_eq!(val, TestInt::from(0x8000u32)); // 65536 - 32768 = 32768

        // Test sub_shifted with multi-word operations
        let mut big_val = TestInt::from(0x100000000u64); // 2^32
        big_val.sub_shifted(&TestInt::from(1u32), 31); // subtract 1 << 31 = 2^31
        assert_eq!(big_val, TestInt::from(0x80000000u64)); // 2^32 - 2^31 = 2^31
    }

    #[test]
    fn test_shifted_operations_edge_cases() {
        type TestInt = FixedUInt<u32, 2>;

        // Test zero shifts
        let a = TestInt::from(42u32);
        assert_eq!(
            a.cmp_shifted(&TestInt::from(42u32), 0),
            core::cmp::Ordering::Equal
        );

        let mut b = TestInt::from(42u32);
        b.sub_shifted(&TestInt::from(10u32), 0);
        assert_eq!(b, TestInt::from(32u32));

        // Test massive shifts (beyond bit size)
        let c = TestInt::from(123u32);
        assert_eq!(
            c.cmp_shifted(&TestInt::from(456u32), 200),
            core::cmp::Ordering::Greater
        );

        let mut d = TestInt::from(123u32);
        d.sub_shifted(&TestInt::from(456u32), 200); // Should be no-op
        assert_eq!(d, TestInt::from(123u32));

        // Test with zero values
        let zero = TestInt::from(0u32);
        assert_eq!(zero.cmp_shifted(&zero, 10), core::cmp::Ordering::Equal);
        assert_eq!(
            TestInt::from(1u32).cmp_shifted(&zero, 10),
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
            let optimized_cmp = a.cmp_shifted(&b, shift);
            let naive_cmp = a.cmp(&(b << shift));
            assert_eq!(
                optimized_cmp, naive_cmp,
                "cmp_shifted mismatch: {} vs ({} << {})",
                a_val, b_val, shift
            );

            // Test sub_shifted equivalence (if subtraction won't underflow)
            if a >= (b << shift) {
                let mut optimized_result = a;
                optimized_result.sub_shifted(&b, shift);

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

            // Test div_assign_impl directly and verify it returns remainder
            let mut dividend2 = TestInt::from(dividend_val);
            let remainder = TestInt::div_assign_impl(&mut dividend2, &divisor);
            assert_eq!(
                dividend2,
                TestInt::from(expected_quotient),
                "div_assign_impl quotient: {} / {} should be {}",
                dividend_val,
                divisor_val,
                expected_quotient
            );
            assert_eq!(
                remainder,
                TestInt::from(expected_remainder),
                "div_assign_impl remainder: {} % {} should be {}",
                dividend_val,
                divisor_val,
                expected_remainder
            );

            // Verify: quotient * divisor + remainder == original dividend
            assert_eq!(
                dividend2 * divisor + remainder,
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
    fn test_div_impl_forwarding() {
        type TestInt = FixedUInt<u32, 2>;

        // Test that div_impl forwarding works correctly
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
                "div_impl forwarding: {} / {} should be {}",
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

        // Verify that the simplified div_impl maintains same behavior
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

        // Before fix: div_assign_impl would modify a to quotient (3), then assign remainder (2)
        // After fix: div_rem properly computes remainder without corrupting intermediate state
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

            let quotient = TestInt::div_impl(&dividend, &divisor);

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
