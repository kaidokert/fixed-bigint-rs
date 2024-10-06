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
fn test_to_radix_str() {
    let mut buf = [0u8; 20];

    let n1 = Bn::<u8, 8>::zero();
    let slice = n1.to_radix_str(&mut buf, 2);
    assert_eq!(Ok("0"), slice);

    let n1 = Bn::<u8, 8>::one();
    assert_eq!(n1.to_u8().unwrap(), 1);
    let slice = n1.to_radix_str(&mut buf, 2);
    assert_eq!(Ok("1"), slice);

    let n1 = Bn::<u32, 2>::from_u64(0b110110110101).unwrap();
    let slice = n1.to_radix_str(&mut buf, 2);
    assert_eq!(Ok("110110110101"), slice);

    let n1 = Bn::<u32, 2>::from_u64(0o1234567).unwrap();
    let slice = n1.to_radix_str(&mut buf, 8);
    assert_eq!(Ok("1234567"), slice);

    let n1 = Bn::<u16, 4>::from_u64(0o7654321).unwrap();
    let slice = n1.to_radix_str(&mut buf, 8);
    assert_eq!(Ok("7654321"), slice);

    let n1 = Bn::<u32, 2>::from_u64(987654321).unwrap();
    let slice = n1.to_radix_str(&mut buf, 10);
    assert_eq!(Ok("987654321"), slice);

    let n1 = Bn::<u16, 4>::from_u64(123456789).unwrap();
    let slice = n1.to_radix_str(&mut buf, 10);
    assert_eq!(Ok("123456789"), slice);

    let n1 = Bn::<u32, 2>::from_u64(0x9a802e1c01b2a3f4).unwrap();
    let slice = n1.to_radix_str(&mut buf, 16);
    assert_eq!(Ok("9a802e1c01b2a3f4"), slice);

    let n1 = Bn::<u16, 4>::from_u64(0x01b2a3f4).unwrap();
    let slice = n1.to_radix_str(&mut buf, 16);
    assert_eq!(Ok("1b2a3f4"), slice);

    let n1 = Bn::<u32, 2>::from_u64(123456).unwrap();
    let slice = n1.to_radix_str(&mut buf, 7);
    assert_eq!(Ok("1022634"), slice);

    let n1 = Bn::<u16, 4>::from_u64(7654321).unwrap();
    let slice = n1.to_radix_str(&mut buf, 7);
    assert_eq!(Ok("122026543"), slice);

    let n1 = Bn::<u32, 2>::from_u64(123456789).unwrap();
    let slice = n1.to_radix_str(&mut buf, 13);
    assert_eq!(Ok("1c767471"), slice);

    let n1 = Bn::<u16, 4>::from_u64(987654321).unwrap();
    let slice = n1.to_radix_str(&mut buf, 13);
    assert_eq!(Ok("129806a54"), slice);

    let mut buf_small = [0u8; 5];
    let slice = Bn::<u32, 2>::from_u64(123456)
        .unwrap()
        .to_radix_str(&mut buf_small, 10);
    assert!(slice.is_err());
}

#[test]
fn from_str_radix() {
    fn test_radices<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u64>,
    >() {
        let radices = [2, 3, 4, 7, 10, 13, 16];
        let max_value: u64 = INT::max_value().to_u64().unwrap();

        for &radix in &radices {
            assert_eq!(INT::from_str_radix("", radix), Err(make_empty_error()));

            assert_eq!(INT::from_str_radix("0", radix), Ok(0.into()));
            assert_eq!(INT::from_str_radix("1", radix), Ok(1.into()));

            match radix {
                2 => {
                    assert_eq!(INT::from_str_radix("10", 2), Ok(2.into()));
                    assert_eq!(INT::from_str_radix("10001", 2), Ok(17.into()));
                    assert_eq!(INT::from_str_radix("11001", 2), Ok(25.into()));
                    if max_value < 255 {
                        assert_eq!(
                            INT::from_str_radix("100000000", 2),
                            Err(make_overflow_err())
                        );
                    }
                }
                3 => {
                    assert_eq!(INT::from_str_radix("21", 3), Ok(7.into()));
                    assert_eq!(INT::from_str_radix("222", 3), Ok(26.into()));
                }
                4 => {
                    assert_eq!(INT::from_str_radix("33", 4), Ok(15.into()));
                    assert_eq!(INT::from_str_radix("123", 4), Ok(27.into()));
                }
                7 => {
                    if max_value >= 123456 {
                        assert_eq!(INT::from_str_radix("1022634", 7), Ok(123456.into()));
                    }
                }
                10 => {
                    if max_value >= 123456 {
                        assert_eq!(INT::from_str_radix("12345", 10), Ok(12345.into()));
                    }
                    if max_value >= 100000 {
                        assert_eq!(INT::from_str_radix("100000", 10), Ok(100000.into()));
                    }
                    if max_value >= 987654321 {
                        assert_eq!(INT::from_str_radix("987654321", 10), Ok(987654321.into()));
                    }
                }
                13 => {
                    assert_eq!(INT::from_str_radix("123", 13), Ok(198.into()));
                    if max_value >= 1298065482 {
                        assert_eq!(INT::from_str_radix("178c0B5ac", 13), Ok(1298065482.into()));
                    }
                }
                16 => {
                    assert_eq!(INT::from_str_radix("08", 16), Ok(8.into()));
                    if max_value >= 0x1234cbaf {
                        assert_eq!(INT::from_str_radix("1234cbaf", 16), Ok(0x1234cbaf.into()));
                    }
                    if max_value >= 0xcbaf1234 {
                        assert_eq!(INT::from_str_radix("cbaf1234", 16), Ok(0xcbaf1234.into()));
                    }
                }
                _ => {}
            }
        }
    }

    fn test8_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u64>,
    >() {
        test_radices::<INT>();
    }

    fn test16_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u64>,
    >() {
        test_radices::<INT>();
    }

    fn test32_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u64>,
    >() {
        test_radices::<INT>();
    }

    // First check the test cases are correct
    test32_bit::<u64>();
    test8_bit::<Bn<u8, 1>>();
    test8_bit::<Bn<u8, 2>>();

    test16_bit::<Bn<u16, 1>>();
    test16_bit::<Bn<u8, 2>>();

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
