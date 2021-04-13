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

use fixed_bigint::patch_num_traits::{OverflowingShl, OverflowingShr};
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
        assert_eq!(h.unsigned_shl(8).to_u16().unwrap(), 0x100);

        let h = INT::one();
        let res = h << 9;
        assert_eq!(res.to_u16().unwrap(), 0x200);
        assert_eq!(h.unsigned_shl(9).to_u16().unwrap(), 0x200);
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
        assert_eq!((a.unsigned_shr(8)).to_u16().unwrap(), 0);
        let h = INT::from_u64(0x100).unwrap();
        assert_eq!((h >> 8).to_u16().unwrap(), 1);
        assert_eq!((h.unsigned_shr(8)).to_u16().unwrap(), 1);
        let h = INT::from_u64(0x200).unwrap();
        assert_eq!((h >> 9).to_u16().unwrap(), 1);
        assert_eq!((h.unsigned_shr(9)).to_u16().unwrap(), 1);
        let h = INT::from_u64(0x20200).unwrap();
        assert_eq!((h >> 9).to_u16().unwrap(), 0x101);
        assert_eq!((h.unsigned_shr(9)).to_u16().unwrap(), 0x101);
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

#[test]
fn test_sh_variants() {
    fn test_shifts<
        T: num_traits::PrimInt,
        INT: num_traits::PrimInt
            + core::fmt::Debug
            + core::convert::From<T>
            + OverflowingShl
            + OverflowingShr
            + num_traits::WrappingShl
            + num_traits::WrappingShr
            + num_traits::CheckedShl
            + num_traits::CheckedShr,
    >(
        a_in: T,
        left_vector: &[(u32, T, bool)],
        b_in: T,
        right_vector: &[(u32, T, bool)],
    ) {
        let a: INT = a_in.into();
        for &(shift, res, overflow) in left_vector {
            let r = a.overflowing_shl(shift);
            assert_eq!(r, (res.into(), overflow));
            let r = a.wrapping_shl(shift);
            assert_eq!(r, res.into());
            let r = a.checked_shl(shift);
            if overflow {
                assert_eq!(r, None);
            } else {
                assert_eq!(r, Some(res.into()));
            }
        }
        let a: INT = b_in.into();
        for &(shift, res, overflow) in right_vector {
            let r = a.overflowing_shr(shift);
            assert_eq!(r, (res.into(), overflow));
            let r = a.wrapping_shr(shift);
            assert_eq!(r, res.into());
            let r = a.checked_shr(shift);
            if overflow {
                assert_eq!(r, None);
            } else {
                assert_eq!(r, Some(res.into()));
            }
        }
    }

    let left_ops = [(2, 32, false), (7, 0, false), (8, 8, true), (10, 32, true)];
    let right_ops = [(2, 8, false), (7, 0, false), (8, 32, true), (10, 8, true)];
    test_shifts::<u8, u8>(8, &left_ops, 32, &right_ops);
    test_shifts::<u8, Bn<u8, 1>>(8, &left_ops, 32, &right_ops);

    let left_ops = [
        (2, 32, false),
        (15, 0, false),
        (16, 8, true),
        (18, 32, true),
    ];
    let right_ops = [
        (2, 256, false),
        (15, 0, false),
        (16, 1024, true),
        (18, 256, true),
    ];
    test_shifts::<u16, u16>(8, &left_ops, 1024, &right_ops);
    test_shifts::<u16, Bn<u16, 1>>(8, &left_ops, 1024, &right_ops);
    test_shifts::<u16, Bn<u8, 2>>(8, &left_ops, 1024, &right_ops);

    let left_ops = [
        (2, 32, false),
        (31, 0, false),
        (32, 8, true),
        (34, 32, true),
    ];
    let right_ops = [
        (2, 0x08000000, false),
        (31, 0, false),
        (32, 0x20000000, true),
        (34, 0x08000000, true),
    ];
    test_shifts::<u32, u32>(8, &left_ops, 0x20000000, &right_ops);
    test_shifts::<u32, Bn<u32, 1>>(8, &left_ops, 0x20000000, &right_ops);
    test_shifts::<u32, Bn<u16, 2>>(8, &left_ops, 0x20000000, &right_ops);
    test_shifts::<u32, Bn<u8, 4>>(8, &left_ops, 0x20000000, &right_ops);
}
