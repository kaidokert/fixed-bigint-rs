use num_traits::Zero;

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
