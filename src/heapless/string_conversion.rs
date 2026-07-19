//! `Display`, `LowerHex`/`UpperHex`, `FromStr`, and `num_traits::Num` for
//! `HeaplessBigInt<T, CAP, Nct>`.
//!
//! All Nct-only, mirroring `FixedUInt`: decimal/hex rendering and radix
//! parsing walk limb content, which is not constant-time. `Display` and hex
//! are feature-independent — digit extraction goes through the `MachineWord`
//! `const_num_traits::ToPrimitive` supertrait, not `num_traits` — while
//! `Num`/`FromStr` are gated behind `num-traits`.
//!
//! Rendering is over the value width (`self.len`), never `CAP`, so a value at
//! `len = k` prints exactly what the same-width `FixedUInt<T, k>` prints.

use super::HeaplessBigInt;
use crate::MachineWord;
use const_num_traits::{CarryingMul, Nct, ToPrimitive, Zero};
use core::fmt::Write;

impl<T, const CAP: usize> core::fmt::Display for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        const MAX_DIGITS: usize = 20; // decimal digits per u64-sized block

        if <Self as Zero>::is_zero(self) {
            return f.write_char('0');
        }

        // Worst-case decimal length is bounded by the value width (`len` ≤
        // `CAP`), so `CAP` blocks of `MAX_DIGITS` always suffice.
        let mut digit_blocks = [[0u8; MAX_DIGITS]; CAP];
        let mut digit_count = 0;
        let mut number = *self;
        let ten = Self::from(10u8);

        while !<Self as Zero>::is_zero(&number) && digit_count < CAP * MAX_DIGITS {
            let (quotient, remainder) = number.div_rem(&ten);
            // remainder < 10, held in the low limb (zero-tail gives 0 at len 0).
            let digit = <T as ToPrimitive>::to_u8(&remainder.limbs[0]).unwrap_or(0);
            digit_blocks[digit_count / MAX_DIGITS][digit_count % MAX_DIGITS] = b'0' + digit;
            digit_count += 1;
            number = quotient;
        }

        for i in (0..digit_count).rev() {
            f.write_char(digit_blocks[i / MAX_DIGITS][i % MAX_DIGITS] as char)?;
        }
        Ok(())
    }
}

impl<T, const CAP: usize> HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
    u8: core::convert::TryFrom<T>,
{
    // MSB-to-LSB over the value width, suppressing leading-zero nibbles. Zero
    // renders empty (as `FixedUInt` does); callers that need "0" use `Display`.
    fn hex_fmt(
        &self,
        formatter: &mut core::fmt::Formatter<'_>,
        uppercase: bool,
    ) -> core::fmt::Result {
        fn to_casedigit(byte: u8, uppercase: bool) -> Result<char, core::fmt::Error> {
            let digit = core::char::from_digit(byte as u32, 16).ok_or(core::fmt::Error)?;
            if uppercase {
                digit.to_uppercase().next().ok_or(core::fmt::Error)
            } else {
                digit.to_lowercase().next().ok_or(core::fmt::Error)
            }
        }

        let word_size = core::mem::size_of::<T>();
        let mut leading_zero = true;
        let mut maybe_write = |nibble: char| -> core::fmt::Result {
            leading_zero &= nibble == '0';
            if !leading_zero {
                formatter.write_char(nibble)?;
            }
            Ok(())
        };

        for index in (0..self.len as usize).rev() {
            let val = self.limbs[index];
            let mask: T = 0xff.into();
            for j in (0..word_size as u32).rev() {
                let masked = val & mask.shl((j * 8) as usize);
                let byte =
                    u8::try_from(masked.shr((j * 8) as usize)).map_err(|_| core::fmt::Error)?;
                maybe_write(to_casedigit((byte & 0xf0) >> 4, uppercase)?)?;
                maybe_write(to_casedigit(byte & 0x0f, uppercase)?)?;
            }
        }
        Ok(())
    }
}

impl<T, const CAP: usize> core::fmt::UpperHex for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
    u8: core::convert::TryFrom<T>,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.hex_fmt(f, true)
    }
}

impl<T, const CAP: usize> core::fmt::LowerHex for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
    u8: core::convert::TryFrom<T>,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.hex_fmt(f, false)
    }
}

#[cfg(feature = "num-traits")]
impl<T, const CAP: usize> num_traits::Num for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type FromStrRadixErr = core::num::ParseIntError;

    fn from_str_radix(input: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        use crate::fixeduint::{make_empty_error, make_overflow_err, make_parse_int_err};
        use const_num_traits::{CheckedAdd, CheckedMul};

        if input.is_empty() {
            return Err(make_empty_error());
        }
        if !(2..=16).contains(&radix) {
            return Err(make_overflow_err());
        }

        // Accumulate at the full CAP width, not the minimal width of the
        // intermediate `from(digit)` values — otherwise `ret * radix + digit`
        // would overflow at a single word instead of the carrier's capacity
        // (matching `FixedUInt<T, CAP>`, whose parse width is its `N`).
        let mut ret = <Self as Zero>::zero().widened(CAP as u16);
        let range = match input.find(|c: char| c != '0') {
            Some(x) => &input[x..],
            _ => input,
        };
        for c in range.chars() {
            let digit = c.to_digit(radix).ok_or_else(make_parse_int_err)?;
            ret = CheckedMul::checked_mul(ret, Self::from(radix as u8))
                .ok_or_else(make_overflow_err)?;
            ret = CheckedAdd::checked_add(ret, Self::from(digit as u8))
                .ok_or_else(make_overflow_err)?;
        }
        Ok(ret)
    }
}

#[cfg(feature = "num-traits")]
impl<T, const CAP: usize> core::str::FromStr for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type Err = core::num::ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        <Self as num_traits::Num>::from_str_radix(s, 10)
    }
}
