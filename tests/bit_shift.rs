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

#[test]
fn test_not() {
    fn _test_not_8_bit<INT: num_traits::PrimInt + core::fmt::Debug + core::convert::From<u8>>() {
        assert_eq!(Into::<INT>::into(255).not(), 0.into());
        assert_eq!(Into::<INT>::into(254).not(), 1.into());
        assert_eq!(Into::<INT>::into(0).not(), 255.into());
    }
    _test_not_8_bit::<u8>();
    _test_not_8_bit::<Bn<u8, 1>>();

    fn _test_not_16_bit<INT: num_traits::PrimInt + core::fmt::Debug + core::convert::From<u16>>() {
        assert_eq!(Into::<INT>::into(65535).not(), 0.into());
        assert_eq!(Into::<INT>::into(65534).not(), 1.into());
        assert_eq!(Into::<INT>::into(1).not(), 65534.into());
        assert_eq!(Into::<INT>::into(0).not(), 65535.into());
    }
    _test_not_16_bit::<u16>();
    _test_not_16_bit::<Bn<u16, 1>>();
    _test_not_16_bit::<Bn<u8, 2>>();
}

#[test]
fn test_shl() {
    fn test_shl_1<INT: num_traits::PrimInt>() {
        let h = INT::one();
        let res = h << 8;
        assert_eq!(res.to_u16().unwrap(), 0x100);
        let h = INT::one();
        let res = h << 9;
        assert_eq!(res.to_u16().unwrap(), 0x200);
    }
    test_shl_1::<u16>();
    test_shl_1::<Bn<u8, 8>>();
    test_shl_1::<Bn<u16, 4>>();
    test_shl_1::<Bn<u32, 2>>();
}

#[test]
fn test_shr() {
    fn test_shr_1<INT: num_traits::PrimInt + num_traits::FromPrimitive>() {
        let a = INT::one();
        assert_eq!((a >> 8).to_u16().unwrap(), 0);
        let h = INT::from_u64(0x100).unwrap();
        assert_eq!((h >> 8).to_u16().unwrap(), 1);
        let h = INT::from_u64(0x200).unwrap();
        assert_eq!((h >> 9).to_u16().unwrap(), 1);
        let h = INT::from_u64(0x20200).unwrap();
        assert_eq!((h >> 9).to_u16().unwrap(), 0x101);
    }
    test_shr_1::<Bn<u8, 8>>();
    test_shr_1::<Bn<u16, 4>>();
    test_shr_1::<Bn<u32, 2>>();
}

#[test]
fn test_sh_assign() {
    fn test_sh_8_bit<
        INT: num_traits::PrimInt
            + core::fmt::Debug
            + core::convert::From<u8>
            + std::ops::ShlAssign<usize>
            + std::ops::ShrAssign<usize>,
    >() {
        let mut a: INT = 2u8.into();
        let mut a_r = a;
        a.shl_assign(1);
        a_r <<= 1;
        assert_eq!(a, 4.into());
        assert_eq!(a_r, 4.into());
        a.shl_assign(7);
        a_r <<= 7;
        assert_eq!(a, 0.into());
        assert_eq!(a_r, 0.into());

        let mut a: INT = 128.into();
        let mut a_r = a;
        a.shr_assign(1);
        a_r >>= 1;
        assert_eq!(a, 64.into());
        assert_eq!(a_r, 64.into());
        a.shr_assign(7);
        a_r >>= 7;
        assert_eq!(a, 0.into());
        assert_eq!(a_r, 0.into());
    }
    test_sh_8_bit::<u8>();
    test_sh_8_bit::<Bn<u8, 1>>();

    fn test_shl_16_bit<
        INT: num_traits::PrimInt
            + core::fmt::Debug
            + core::convert::From<u16>
            + std::ops::ShlAssign<usize>
            + std::ops::ShrAssign<usize>,
    >() {
        let mut a: INT = 2u16.into();
        let mut a_r = a;
        a.shl_assign(1);
        a_r <<= 1;
        assert_eq!(a, 4.into());
        assert_eq!(a_r, 4.into());

        a.shl_assign(10);
        a_r <<= 10;
        assert_eq!(a, 4096.into());
        assert_eq!(a_r, 4096.into());

        a.shl_assign(8);
        a_r <<= 8;
        assert_eq!(a, 0.into());
        assert_eq!(a_r, 0.into());
    }
    test_shl_16_bit::<u16>();
    test_shl_16_bit::<Bn<u16, 1>>();
    test_shl_16_bit::<Bn<u8, 2>>();
}
