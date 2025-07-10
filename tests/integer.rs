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
            assert_eq!(
                num_integer::Integer::is_multiple_of(&multiple, &multiplier),
                expected
            );
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

            assert_eq!(num_integer::Integer::div_floor(&multiple, &divider), divres);
            assert_eq!(num_integer::Integer::mod_floor(&multiple, &divider), remres);
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

#[test]
fn test_gcd_edge_cases() {
    fn gcd_edge_cases<T: num_integer::Integer + From<u8> + std::fmt::Debug>() {
        let zero = T::from(0u8);
        let _one = T::from(1u8);
        let five = T::from(5u8);
        let ten = T::from(10u8);

        // Test zero cases - should return the other value
        assert_eq!(zero.gcd(&five), five);
        assert_eq!(five.gcd(&zero), five);
        assert_eq!(zero.gcd(&zero), zero);

        // Test equal values
        assert_eq!(five.gcd(&five), five);
        assert_eq!(ten.gcd(&ten), ten);

        // Test cases where one number is larger
        assert_eq!(ten.gcd(&five), five);
        assert_eq!(five.gcd(&ten), five);
    }
    gcd_edge_cases::<FixedUInt<u8, 1>>();
    gcd_edge_cases::<FixedUInt<u8, 2>>();
    gcd_edge_cases::<FixedUInt<u16, 1>>();
}

#[test]
fn test_lcm_edge_cases() {
    fn lcm_edge_cases<T: num_integer::Integer + From<u8> + std::fmt::Debug>() {
        let zero = T::from(0u8);
        let one = T::from(1u8);
        let five = T::from(5u8);
        let ten = T::from(10u8);

        // Test zero cases - should return zero
        assert_eq!(zero.lcm(&five), zero);
        assert_eq!(five.lcm(&zero), zero);
        assert_eq!(zero.lcm(&zero), zero);

        // Test with one
        assert_eq!(one.lcm(&five), five);
        assert_eq!(five.lcm(&one), five);

        // Test equal values
        assert_eq!(five.lcm(&five), five);
        assert_eq!(ten.lcm(&ten), ten);
    }
    lcm_edge_cases::<FixedUInt<u8, 1>>();
    lcm_edge_cases::<FixedUInt<u8, 2>>();
    lcm_edge_cases::<FixedUInt<u16, 1>>();
}

#[test]
fn test_div_floor_mod_floor() {
    fn div_floor_mod_floor<T: num_integer::Integer + From<u8> + std::fmt::Debug>() {
        let tests = [
            (8u8, 3u8, 2u8, 2u8),
            (10, 5, 2, 0),
            (7, 3, 2, 1),
            (15, 4, 3, 3),
            (100, 7, 14, 2),
        ];

        for &(dividend, divisor, expected_div, expected_mod) in &tests {
            let a = T::from(dividend);
            let b = T::from(divisor);
            assert_eq!(
                num_integer::Integer::div_floor(&a, &b),
                T::from(expected_div)
            );
            assert_eq!(
                num_integer::Integer::mod_floor(&a, &b),
                T::from(expected_mod)
            );
        }
    }
    div_floor_mod_floor::<FixedUInt<u8, 1>>();
    div_floor_mod_floor::<FixedUInt<u8, 2>>();
    div_floor_mod_floor::<FixedUInt<u16, 1>>();
}

#[test]
fn test_divides_comprehensive() {
    fn divides_comprehensive<T: num_integer::Integer + From<u8> + std::fmt::Debug>() {
        let tests = [
            (12u8, 3u8, true),
            (12, 4, true),
            (12, 5, false),
            (15, 3, true),
            (15, 4, false),
            (100, 10, true),
            (100, 11, false),
        ];

        for &(multiple, divisor, expected) in &tests {
            let a = T::from(multiple);
            let b = T::from(divisor);
            assert_eq!(num_integer::Integer::is_multiple_of(&a, &b), expected);
            assert_eq!(num_integer::Integer::is_multiple_of(&a, &b), expected);
        }
    }
    divides_comprehensive::<FixedUInt<u8, 1>>();
    divides_comprehensive::<FixedUInt<u8, 2>>();
    divides_comprehensive::<FixedUInt<u16, 1>>();
}

#[test]
fn test_integer_div_rem() {
    fn integer_div_rem<T: num_integer::Integer + From<u8> + std::fmt::Debug>() {
        let tests = [
            (15u8, 4u8, 3u8, 3u8),
            (20, 6, 3, 2),
            (100, 7, 14, 2),
            (25, 5, 5, 0),
        ];

        for &(dividend, divisor, expected_div, expected_rem) in &tests {
            let a = T::from(dividend);
            let b = T::from(divisor);
            let (div, rem) = a.div_rem(&b);
            assert_eq!(div, T::from(expected_div));
            assert_eq!(rem, T::from(expected_rem));
        }
    }
    integer_div_rem::<FixedUInt<u8, 1>>();
    integer_div_rem::<FixedUInt<u8, 2>>();
    integer_div_rem::<FixedUInt<u16, 1>>();
}
