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
            assert_eq!(multiple.is_multiple_of(&multiplier), expected);
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
    //todo!()
}
