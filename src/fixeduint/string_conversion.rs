use core::fmt::Write;
use num_traits::{Num, ToPrimitive, Zero};

use super::{make_empty_error, make_overflow_err, make_parse_int_err, FixedUInt, MachineWord};

impl<T: MachineWord, const N: usize> num_traits::Num for FixedUInt<T, N> {
    type FromStrRadixErr = core::num::ParseIntError;
    fn from_str_radix(
        input: &str,
        radix: u32,
    ) -> Result<Self, <Self as num_traits::Num>::FromStrRadixErr> {
        if input.is_empty() {
            return Err(make_empty_error());
        }

        if !(2..=16).contains(&radix) {
            return Err(make_overflow_err()); // Invalid radix
        }

        let mut ret = Self::zero();
        let range = match input.find(|c: char| c != '0') {
            Some(x) => &input[x..],
            _ => input,
        };

        for c in range.chars() {
            let digit = match c.to_digit(radix) {
                Some(d) => d,
                None => return Err(make_parse_int_err()), // Invalid character for the radix
            };

            ret = num_traits::CheckedMul::checked_mul(&ret, &Self::from(radix as u8))
                .ok_or(make_overflow_err())?;
            ret = num_traits::CheckedAdd::checked_add(&ret, &Self::from(digit as u8))
                .ok_or(make_overflow_err())?;
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

impl<T: MachineWord, const N: usize> core::fmt::Display for FixedUInt<T, N> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        const MAX_DIGITS: usize = 20;

        if self.is_zero() {
            return f.write_char('0');
        }

        // 20 is sized for u64
        let mut digit_blocks = [[0u8; MAX_DIGITS]; N];
        let mut digit_count = 0;
        let mut number = *self;
        let ten = Self::from(10u8);

        // Extract digits into our storage
        while !number.is_zero() && digit_count < N * MAX_DIGITS {
            let (quotient, remainder) = number.div_rem(&ten);
            let digit = remainder.to_u8().unwrap();

            let block_idx = digit_count / MAX_DIGITS;
            let digit_idx = digit_count % MAX_DIGITS;
            digit_blocks[block_idx][digit_idx] = b'0' + digit;

            digit_count += 1;
            number = quotient;
        }

        // Write digits in reverse order
        for i in (0..digit_count).rev() {
            let block_idx = i / MAX_DIGITS;
            let digit_idx = i % MAX_DIGITS;
            f.write_char(digit_blocks[block_idx][digit_idx] as char)?;
        }

        Ok(())
    }
}

impl<T: MachineWord, const N: usize> core::str::FromStr for FixedUInt<T, N> {
    type Err = core::num::ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::from_str_radix(s, 10)
    }
}
