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

#[cfg(test)]
use fixed_bigint::FixedUInt as Bn;

use fixed_bigint::num_traits::Num;
use fixed_bigint::num_traits::{FromPrimitive, ToPrimitive};
use fixed_bigint::num_traits::{One, Zero};

mod helper;
use helper::WriteWrapper;

use core::fmt::Write;

fn make_invalid_digit_error() -> core::num::ParseIntError {
    <u8>::from_str_radix("-", 2).err().unwrap()
}
fn make_overflow_err() -> core::num::ParseIntError {
    <u8>::from_str_radix("101", 16).err().unwrap()
}
fn make_empty_error() -> core::num::ParseIntError {
    <u8>::from_str_radix("", 2).err().unwrap()
}
/*
fn make_neg_overflow_err() -> core::num::ParseIntError {
    <u8>::from_str_radix("-ff", 16).err().unwrap()
}
*/
#[test]
fn test_from_str_stringlengths_badinput() {
    assert_eq!(
        Err(make_invalid_digit_error()),
        Bn::<u8, 8>::from_str_radix("ax", 16)
    );
}

#[test]
fn test_to_from_str() {
    let mut buf = [0u8; 16];
    let n0 = Bn::<u8, 8>::from_str_radix("01", 16).unwrap();
    assert_eq!(n0.to_u8().unwrap(), 0x1);
    assert_eq!(Ok("1"), n0.to_hex_str(&mut buf));

    let mut buf = [0u8; 4];
    let n0 = Bn::<u8, 8>::from_str_radix("01", 16).unwrap();
    assert_eq!(n0.to_u8().unwrap(), 0x1);
    assert_eq!(Ok("1"), n0.to_hex_str(&mut buf));

    let n0 = Bn::<u8, 8>::from_str_radix("0f", 16).unwrap();
    assert_eq!(n0.to_u8().unwrap(), 0xf);
    assert_eq!(Ok("f"), n0.to_hex_str(&mut buf));

    let n1 = Bn::<u8, 8>::from_str_radix("12", 16).unwrap();
    let n2 = Bn::<u8, 8>::from_str_radix("12", 16).unwrap();
    let n3 = n1 + n2;
    let n = n3.to_u32().unwrap();
    assert_eq!(n, 0x24);
    assert_eq!(n3.to_hex_str(&mut buf), Ok("24"));
    let n4 = Bn::<u8, 8>::from_str_radix("24", 16).unwrap();
    assert_eq!(Ok("24"), n4.to_hex_str(&mut buf));
}

#[test]
fn test_to_hex_str() {
    let mut buf = [0u8; 20];

    let n1 = Bn::<u8, 8>::zero();
    let slice = n1.to_hex_str(&mut buf);
    assert_eq!(Ok("0"), slice);

    let mut buf_small = [0u8; 1];
    let slice = Bn::<u8, 8>::one().to_hex_str(&mut buf_small);
    assert_eq!(Ok("1"), slice);

    let n1 = Bn::<u8, 8>::one();
    assert_eq!(n1.to_u8().unwrap(), 1);
    let slice = n1.to_hex_str(&mut buf);
    assert_eq!(Ok("1"), slice);

    let n1 = Bn::<u32, 2>::from_u64(0x9a802e1c01b2a3f4).unwrap();
    let slice = n1.to_hex_str(&mut buf);
    assert_eq!(Ok("9a802e1c01b2a3f4"), slice);
    let n1 = Bn::<u16, 4>::from_u64(0x01b2a3f4).unwrap();
    let slice = n1.to_hex_str(&mut buf);
    assert_eq!(Ok("1b2a3f4"), slice);

    let n1 = Bn::<u16, 4>::from_u64(0x0102030405).unwrap();
    let slice = n1.to_hex_str(&mut buf);
    assert_eq!(Ok("102030405"), slice);

    let n1 = Bn::<u32, 2>::from_u64(0x010203).unwrap();
    let slice = n1.to_hex_str(&mut buf);
    assert_eq!(Ok("10203"), slice);
    let n1 = Bn::<u32, 2>::from_u64(0x0102030405).unwrap();
    let slice = n1.to_hex_str(&mut buf);
    assert_eq!(Ok("102030405"), slice);

    let mut buf = [0u8; 9];
    let slice = n1.to_hex_str(&mut buf);
    assert_eq!(Ok("102030405"), slice);
}

#[test]
fn from_str_radix() {
    fn test8_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u8>,
    >() {
        assert_eq!(INT::from_str_radix("", 3), Err(make_empty_error()));
        assert_eq!(INT::from_str_radix("08", 16), Ok(8.into()));
        assert_eq!(INT::from_str_radix("008", 16), Ok(8.into()));
        assert_eq!(INT::from_str_radix("108", 16), Err(make_overflow_err()));

        assert_eq!(INT::from_str_radix("3333", 4), Ok(255.into()));
        assert_eq!(INT::from_str_radix("10001000", 2), Ok(0x88.into()));
        assert_eq!(
            INT::from_str_radix("110001000", 2),
            Err(make_overflow_err())
        );
    }

    test8_bit::<u8>();
    test8_bit::<Bn<u8, 1>>();

    fn test16_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u16>,
    >() {
        assert_eq!(INT::from_str_radix("08", 16), Ok(8.into()));
        assert_eq!(INT::from_str_radix("108", 16), Ok(264.into()));
        assert_eq!(INT::from_str_radix("10008", 16), Err(make_overflow_err()));

        assert_eq!(INT::from_str_radix("033333333", 4), Ok(65535.into()));
        assert_eq!(INT::from_str_radix("ffff", 16), Ok(65535.into()));
        assert_eq!(INT::from_str_radix("afaf", 16), Ok(0xafaf.into()));
        assert_eq!(INT::from_str_radix("fabc", 16), Ok(0xfabc.into()));
        assert_eq!(INT::from_str_radix("cbaf", 16), Ok(0xcbaf.into()));

        assert_eq!(
            INT::from_str_radix("1101010101010101", 2),
            Ok(0xD555.into())
        );
        assert_eq!(
            INT::from_str_radix("11101010101010101", 2),
            Err(make_overflow_err())
        );
    }

    test16_bit::<u16>();
    test16_bit::<Bn<u16, 1>>();
    test16_bit::<Bn<u8, 2>>();

    fn test32_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u32>,
    >() {
        assert_eq!(INT::from_str_radix("08", 16), Ok(8.into()));
        assert_eq!(INT::from_str_radix("1234cbaf", 16), Ok(0x1234cbaf.into()));
        assert_eq!(INT::from_str_radix("cbaf1234", 16), Ok(0xcbaf1234.into()));
        assert_eq!(
            INT::from_str_radix("1cbaf1234", 16),
            Err(make_overflow_err())
        );
        assert_eq!(
            INT::from_str_radix("3210012332210112", 4),
            Ok(3827034390.into())
        );
    }

    test32_bit::<u32>();
    test32_bit::<Bn<u8, 4>>();
    test32_bit::<Bn<u16, 2>>();
    test32_bit::<Bn<u32, 1>>();
}

#[test]
fn fmt_to_hex() {
    fn b2str(data: &[u8]) -> &str {
        let nul_range_end = data.iter().position(|&c| c == b'\0').unwrap_or(data.len());
        let strslice: &str = core::str::from_utf8(&data[..nul_range_end]).unwrap();
        strslice
    }
    fn test8_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u8>
            + core::fmt::UpperHex
            + core::fmt::LowerHex,
    >() {
        let val: INT = 42.into();

        let mut buffer = [0u8; 20];
        assert_eq!(write!(WriteWrapper::new(&mut buffer), "{:X}", val), Ok(()));
        assert_eq!(b2str(&buffer), "2A");

        let mut buffer = [0u8; 20];
        assert_eq!(write!(WriteWrapper::new(&mut buffer), "{:X}", 0), Ok(()));
        assert_eq!(b2str(&buffer), "0");

        assert_eq!(write!(WriteWrapper::new(&mut buffer), "{:x}", val), Ok(()));
        assert_eq!(b2str(&buffer), "2a");

        let mut buffer = [0u8; 1];
        assert_eq!(
            write!(WriteWrapper::new(&mut buffer), "{:X}", val),
            Err(core::fmt::Error {})
        );
    }
    test8_bit::<u8>();
    test8_bit::<Bn<u8, 1>>();

    fn test_16_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u16>
            + core::fmt::UpperHex
            + core::fmt::LowerHex,
    >() {
        let val: INT = 42.into();
        let mut buffer = [0u8; 20];
        write!(WriteWrapper::new(&mut buffer), "{:X}", val).unwrap();
        assert_eq!(b2str(&buffer), "2A");

        let mut buffer = [0u8; 20];
        assert_eq!(write!(WriteWrapper::new(&mut buffer), "{:X}", 0), Ok(()));
        assert_eq!(b2str(&buffer), "0");

        let mut buffer = [0u8; 20];
        write!(WriteWrapper::new(&mut buffer), "{:X}", 0xDEAD).unwrap();
        assert_eq!(b2str(&buffer), "DEAD");

        let mut buffer = [0u8; 20];
        write!(WriteWrapper::new(&mut buffer), "{:X}", 0xD0AD).unwrap();
        assert_eq!(b2str(&buffer), "D0AD");

        let mut buffer = [0u8; 20];
        write!(WriteWrapper::new(&mut buffer), "{:X}", 0xD00D).unwrap();
        assert_eq!(b2str(&buffer), "D00D");

        let mut buffer = [0u8; 20];
        write!(WriteWrapper::new(&mut buffer), "{:X}", 0x000D).unwrap();
        assert_eq!(b2str(&buffer), "D");

        let mut buffer = [0u8; 20];
        write!(WriteWrapper::new(&mut buffer), "{:X}", 0x0E0D).unwrap();
        assert_eq!(b2str(&buffer), "E0D");

        let mut buffer = [0u8; 20];
        write!(WriteWrapper::new(&mut buffer), "{:X}", 0x0).unwrap();
        assert_eq!(b2str(&buffer), "0");
    }
    test_16_bit::<u16>();
    test_16_bit::<Bn<u8, 2>>();
    test_16_bit::<Bn<u16, 1>>();
}
