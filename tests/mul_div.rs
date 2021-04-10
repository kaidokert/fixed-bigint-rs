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

use num_traits::{FromPrimitive, ToPrimitive};
use std::ops::{Div, Mul};

#[test]
fn test_mul() {
    let a: Bn<u8, 1> = 2u8.into();
    let b: Bn<u8, 1> = 3u8.into();
    assert_eq!(a * b, 6u8.into());
    assert_eq!(a.mul(b), 6u8.into());

    let a = Bn::<u8, 2>::from_u64(3).unwrap();
    let b = Bn::<u8, 2>::from_u64(4).unwrap();
    let r = a * b;
    assert_eq!(r.to_u16().unwrap(), 12);

    let a = Bn::<u8, 2>::from_u64(300).unwrap();
    let b = Bn::<u8, 2>::from_u64(4).unwrap();
    let r = a * b;
    assert_eq!(r.to_u64().unwrap(), 1200);

    let tests = [
        (0x010203u64, 0x1020u64, 0x10407060u64),
        (42, 0, 0),
        (42, 1, 42),
        (42, 2, 84),
        (42, 10, 420),
        (42, 100, 4200),
        (420, 1000, 420000),
        (200, 8, 1600),
        (2, 256, 512),
        (500, 2, 1000),
        (500000, 2, 1000000),
        (500, 500, 250000),
        (1000000000, 2, 2000000000),
        (2, 1000000000, 2000000000),
        (1000000000, 4, 4000000000),
    ];
    for (a, b, res) in &tests {
        let b_a = Bn::<u8, 8>::from_u64(*a).unwrap();
        let b_b = Bn::<u8, 8>::from_u64(*b).unwrap();
        let b_res = b_a * b_b;
        assert_eq!(b_res.to_u64().unwrap(), *res);
    }
    for (a, b, res) in &tests {
        let b_a = Bn::<u32, 2>::from_u64(*a).unwrap();
        let b_b = Bn::<u32, 2>::from_u64(*b).unwrap();
        let b_res = b_a * b_b;
        assert_eq!(b_res.to_u64().unwrap(), *res);
    }
}

#[test]
fn test_div() {
    let a: Bn<u8, 1> = 6u8.into();
    let b: Bn<u8, 1> = 3u8.into();
    assert_eq!(a / b, 2u8.into());
    assert_eq!(a.div(b), 2u8.into());

    fn test_div_1<BN: num_traits::PrimInt>()
    where
        BN::FromStrRadixErr: core::fmt::Debug,
    {
        let tests = [
            ("00000010", "00000002", 0x8),
            ("0000001b", "00000003", 0x9),
            ("0000012C", "00000064", 3),
            ("00015F90", "0000012C", 0x12C),
        ];
        for (a, b, res) in &tests {
            let f = BN::from_str_radix(a, 16).unwrap();
            let g = BN::from_str_radix(b, 16).unwrap();
            let e = f / g;
            assert_eq!(e.to_u64().unwrap(), *res);
        }
    }
    test_div_1::<Bn<u8, 8>>();
    test_div_1::<Bn<u16, 4>>();
    test_div_1::<Bn<u32, 2>>();
}
#[test]
fn test_rem() {
    fn test_rem_1<BN: num_traits::PrimInt + num_traits::FromPrimitive>() {
        let tests = [
            (10u64, 3u64, 1u64),
            (256, 256, 0),
            (256, 1, 0),
            (256, 255, 1),
            (255, 256, 255),
            (4_294_967_295, 65536, 65535),
        ];
        for (a, b, res) in &tests {
            let cmp = a % b;
            assert_eq!(*res, cmp);

            let f = BN::from_u64(*a).unwrap();
            let g = BN::from_u64(*b).unwrap();
            let e = f % g;
            assert_eq!(*res, e.to_u64().unwrap());
        }
    }
    test_rem_1::<Bn<u8, 8>>();
    test_rem_1::<Bn<u16, 4>>();
    test_rem_1::<Bn<u32, 2>>();
}

#[test]
fn test_overflowing_mul() {
    fn test_8_bit<
        INT: num_traits::PrimInt
            + num_traits::ops::overflowing::OverflowingMul
            + core::fmt::Debug
            + core::convert::From<u8>,
    >() {
        let a: INT = 2.into();
        let b: INT = 3.into();
        let c: INT = 130.into();
        assert_eq!(a.overflowing_mul(&b), (6.into(), false));
        assert_eq!(a.overflowing_mul(&c), (4.into(), true));
        assert_eq!(Into::<INT>::into(128).overflowing_mul(&a), (0.into(), true));
        assert_eq!(
            Into::<INT>::into(127).overflowing_mul(&a),
            (254.into(), false)
        );
    }

    test_8_bit::<u8>();
    test_8_bit::<Bn<u8, 1>>();

    fn test_16_bit<
        INT: num_traits::PrimInt
            + num_traits::ops::overflowing::OverflowingMul
            + num_traits::WrappingMul
            + num_traits::SaturatingMul
            + core::fmt::Debug
            + core::convert::From<u16>,
    >() {
        let a: INT = 2.into();
        let b: INT = 3.into();
        let c: INT = 32770.into();

        assert_eq!(a.overflowing_mul(&b), (6.into(), false));
        assert_eq!(a.overflowing_mul(&c), (4.into(), true));
        assert_eq!(c.overflowing_mul(&a), (4.into(), true));
        assert_eq!(
            Into::<INT>::into(32768).overflowing_mul(&a),
            (0.into(), true)
        );
        assert_eq!(
            Into::<INT>::into(32767).overflowing_mul(&a),
            (65534.into(), false)
        );

        let tests = [
            (0u16, 0u16, 0u16, false),
            (2, 3, 6, false),
            (2, 32767, 65534, false),
            (2, 32768, 0, true),
            (2, 32770, 4, true),
            (255, 255, 65025, false),
            (255, 256, 65280, false),
            (256, 256, 0, true),
            (256, 257, 256, true),
            (257, 257, 513, true),
        ];
        for (a, b, res, overflow) in &tests {
            let ac: INT = (*a).into();
            let bc: INT = (*b).into();
            assert_eq!(ac.overflowing_mul(&bc), ((*res).into(), *overflow));
            assert_eq!(bc.overflowing_mul(&ac), ((*res).into(), *overflow));
            assert_eq!(ac.wrapping_mul(&bc), (*res).into());
            let checked = ac.checked_mul(&bc);
            let saturating = ac.saturating_mul(&bc);
            if *overflow {
                assert_eq!(checked, None);
                assert_eq!(saturating, INT::max_value());
            } else {
                assert_eq!(checked, Some((*res).into()));
                assert_eq!(saturating, (*res).into())
            }
        }
    }

    test_16_bit::<u16>();
    test_16_bit::<Bn<u8, 2>>();
    test_16_bit::<Bn<u16, 1>>();

    fn test_32_bit<
        INT: num_traits::PrimInt
            + num_traits::ops::overflowing::OverflowingMul
            + num_traits::WrappingMul
            + num_traits::SaturatingMul
            + core::fmt::Debug
            + core::convert::From<u32>,
    >() {
        let a: INT = 2.into();
        let b: INT = 3.into();
        let c: INT = 2147483650.into();

        assert_eq!(a.overflowing_mul(&b), (6.into(), false));
        assert_eq!(a.overflowing_mul(&c), (4.into(), true));
        assert_eq!(c.overflowing_mul(&a), (4.into(), true));
        let tests = [
            (0u32, 0u32, 0u32, false),
            (2, 3, 6, false),
            (2, 2_147_483_647, 4_294_967_294, false),
            (2, 2_147_483_648, 0, true),
            (2, 2_147_483_650, 4, true),
            (65535, 65535, 4_294_836_225, false),
            (65535, 65536, 4_294_901_760, false),
            (65536, 65536, 0, true),
            (65536, 65537, 65536, true),
            (65537, 65537, 131073, true),
        ];
        for (a, b, res, overflow) in &tests {
            let ac: INT = (*a).into();
            let bc: INT = (*b).into();
            assert_eq!(ac.overflowing_mul(&bc), ((*res).into(), *overflow));
            assert_eq!(ac.wrapping_mul(&bc), (*res).into());
            let checked = ac.checked_mul(&bc);
            let saturating = ac.saturating_mul(&bc);
            if *overflow {
                assert_eq!(checked, None);
                assert_eq!(saturating, INT::max_value());
            } else {
                assert_eq!(checked, Some((*res).into()));
                assert_eq!(saturating, (*res).into())
            }
        }
    }
    test_32_bit::<u32>();
    test_32_bit::<Bn<u16, 2>>();
    test_32_bit::<Bn<u8, 4>>();
}

#[test]
#[ignore]
fn test_full_range_mul() {
    fn test_ref<
        REF: num_traits::PrimInt + num_traits::ops::overflowing::OverflowingMul,
        INT: num_traits::PrimInt + num_traits::ops::overflowing::OverflowingMul + core::fmt::Debug,
    >()
    where
        INT: core::convert::From<REF>,
        core::ops::Range<REF>: Iterator<Item = REF>,
    {
        for i in REF::zero()..REF::max_value() {
            for j in REF::zero()..REF::max_value() {
                let ref_val = i.overflowing_mul(&j);
                let lhs: INT = i.into();
                let rhs: INT = j.into();
                let int_val = lhs.overflowing_mul(&rhs);
                assert_eq!(int_val, (ref_val.0.into(), ref_val.1));
            }
        }
    }
    test_ref::<u8, Bn<u8, 1>>();
    test_ref::<u16, Bn<u16, 1>>();
    test_ref::<u16, Bn<u8, 2>>();
    //  this would never finish, single-threaded
    //  test_ref::<Bn<u8, 4>, u32>();
    //  test_ref::<Bn<u16, 2>, u32>();
    //  test_ref::<Bn<u32, 1>, u32>();
}
