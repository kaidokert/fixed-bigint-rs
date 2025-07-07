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
use fixed_bigint::FixedUInt;
use num_integer::Integer;

#[test]
fn test_evenodd() {
    fn even_odd<T: num_integer::Integer + From<u8>>() {
        let tests = [(0u8, true), (1u8, false), (2u8, true), (255u8, false)];
        for &(num, even) in &tests {
            let f: T = num.into();
            assert_eq!(f.is_even(), even);
            assert_eq!(f.is_odd(), !even);
        }
    }
    even_odd::<u8>();
    even_odd::<FixedUInt<u8, 1>>();
    even_odd::<FixedUInt<u8, 2>>();
    even_odd::<FixedUInt<u16, 1>>();
}

#[test]
fn test_divides() {
    fn divides<T: num_integer::Integer + From<u8>>() {
        let tests = [(6u8, 3u8, true), (8, 2, true), (8, 1, true), (17, 2, false)];
        for &(multiple, multiplier, expected) in &tests {
            assert_eq!(
                num_integer::Integer::is_multiple_of(&multiple, &multiplier),
                expected
            );
            assert_eq!(multiple.divides(&multiplier), expected);
        }
        let divrem = [
            (6u8, 3u8, 2u8, 0u8),
            (8, 2, 4, 0),
            (7, 2, 3, 1),
            (89, 13, 6, 11),
        ];
        for &(multiple, divider, div, rem) in &divrem {
            let (divres, remres) = multiple.div_rem(&divider);
            assert_eq!(divres, div);
            assert_eq!(remres, rem);

            assert_eq!(multiple.div_floor(&divider), divres);
            assert_eq!(multiple.mod_floor(&divider), remres);
        }
    }
    divides::<u8>();
    divides::<FixedUInt<u8, 1>>();
    divides::<FixedUInt<u8, 2>>();
    divides::<FixedUInt<u16, 1>>();
}

// TODO: Test GCD / LCM
#[test]
fn test_gcd_lcm() {
    fn gcd_lcm<T: num_integer::Integer + From<u8>>() {
        let gcd_tests = [
            (8u8, 12u8, 4u8),
            (1, 1, 1),
            (100, 100, 100),
            (99, 98, 1),
            (99, 90, 9),
        ];
        for &(a, b, expected) in &gcd_tests {
            assert_eq!(a.gcd(&b), expected);
        }
        let lcm_tests = [
            (10u8, 2u8, 10u8),
            (1, 1, 1),
            (4, 6, 12),
            (7, 12, 84),
            (14, 12, 84),
            (255, 255, 255),
        ];
        for &(a, b, expected) in &lcm_tests {
            assert_eq!(a.lcm(&b), expected);
        }
    }
    gcd_lcm::<u8>();
    gcd_lcm::<FixedUInt<u8, 1>>();
    gcd_lcm::<FixedUInt<u8, 2>>();
    gcd_lcm::<FixedUInt<u16, 1>>();
}
