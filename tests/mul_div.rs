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

#[test]
fn test_mul() {
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
