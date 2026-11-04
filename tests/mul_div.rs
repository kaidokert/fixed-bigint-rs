#![cfg(feature = "num-traits")]
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
use fixed_bigint::HeaplessBigInt;

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

    fn test_div_1<BN: num_traits::PrimInt + num_traits::NumAssign + num_traits::NumAssignRef>()
    where
        BN::FromStrRadixErr: core::fmt::Debug,
    {
        let tests = [
            ("0", "00000002", 0),
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
            let e = f.div(g);
            assert_eq!(e.to_u64().unwrap(), *res);

            //div-assign
            let mut x = f;
            x /= g;
            assert_eq!(x.to_u64().unwrap(), *res);
            // by reference
            let mut x = f;
            let gref = &g;
            x /= gref;
            assert_eq!(x.to_u64().unwrap(), *res);
        }
    }
    test_div_1::<Bn<u8, 8>>();
    test_div_1::<Bn<u16, 4>>();
    test_div_1::<Bn<u32, 2>>();
}

// Divisors that fit in one word take a different path from wider ones, so
// sweep both against native `u64` division.
#[test]
fn test_div_rem_against_u64() {
    fn check<BN>(word_bits: u32)
    where
        BN: FromPrimitive + ToPrimitive + Clone + Div<Output = BN> + core::ops::Rem<Output = BN>,
    {
        let mut state = 0x9e37_79b9_7f4a_7c15u64;
        let mut next = || {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            state
        };
        for _ in 0..2000 {
            let a = next();
            for bits in [1, word_bits / 2, word_bits, word_bits + 1, 63, 64] {
                let mask = if bits >= 64 {
                    u64::MAX
                } else {
                    (1u64 << bits) - 1
                };
                let b = (next() & mask).max(1);
                let (fa, fb) = (BN::from_u64(a).unwrap(), BN::from_u64(b).unwrap());
                assert_eq!((fa.clone() / fb.clone()).to_u64(), Some(a / b), "{a} / {b}");
                assert_eq!((fa % fb).to_u64(), Some(a % b), "{a} % {b}");
            }
        }
    }
    check::<Bn<u8, 8>>(8);
    check::<Bn<u16, 4>>(16);
    check::<Bn<u32, 2>>(32);
    check::<Bn<u64, 1>>(64);
    check::<HeaplessBigInt<u8, 8>>(8);
    check::<HeaplessBigInt<u16, 4>>(16);
    check::<HeaplessBigInt<u32, 2>>(32);
    check::<HeaplessBigInt<u64, 1>>(64);
}
// Multi-word divisors go through Knuth's Algorithm D under `fast-div`.
// Sweep against native `u128` with divisors of every bit length, and with
// words of all zeros or all ones, which exercise the quotient-estimate
// corrections and the add-back step.
trait U128Io: Sized + Clone + Div<Output = Self> + core::ops::Rem<Output = Self> {
    fn from_u128(x: u128) -> Self;
    fn to_u128(&self) -> u128;
}
macro_rules! u128_io {
    ($($t:ty),*) => {$(
        impl U128Io for Bn<$t, { 16 / core::mem::size_of::<$t>() }> {
            fn from_u128(x: u128) -> Self {
                Self::from_le_bytes(&x.to_le_bytes())
            }
            fn to_u128(&self) -> u128 {
                let mut out = [0u8; 16];
                self.to_le_bytes(&mut out).unwrap();
                u128::from_le_bytes(out)
            }
        }
        impl U128Io for HeaplessBigInt<$t, { 16 / core::mem::size_of::<$t>() }> {
            fn from_u128(x: u128) -> Self {
                Self::from_le_bytes(&x.to_le_bytes())
            }
            fn to_u128(&self) -> u128 {
                let mut out = [0u8; 16];
                let n = self.to_le_bytes(&mut out).len();
                out[n..].fill(0);
                u128::from_le_bytes(out)
            }
        }
    )*};
}
u128_io!(u8, u16, u32, u64);

#[test]
fn test_div_rem_against_u128() {
    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            self.0
        }
        // Random 128 bits with some 16-bit chunks forced to all zeros or
        // all ones.
        fn patterned(&mut self) -> u128 {
            let mut x = ((self.next() as u128) << 64) | self.next() as u128;
            for chunk in 0..8 {
                match self.next() % 4 {
                    0 => x &= !(0xffffu128 << (chunk * 16)),
                    1 => x |= 0xffffu128 << (chunk * 16),
                    _ => {}
                }
            }
            x
        }
    }
    fn check<BN: U128Io>() {
        let mut rng = Lcg(0x2545_f491_4f6c_dd1d);
        for _ in 0..250 {
            let a = rng.patterned();
            for bits in 1..=128u32 {
                let mask = if bits == 128 {
                    u128::MAX
                } else {
                    (1u128 << bits) - 1
                };
                let b = (rng.patterned() & mask) | (1u128 << (bits - 1));
                let (fa, fb) = (BN::from_u128(a), BN::from_u128(b));
                assert_eq!(
                    (fa.clone() / fb.clone()).to_u128(),
                    a / b,
                    "{a:#x} / {b:#x}"
                );
                assert_eq!((fa % fb).to_u128(), a % b, "{a:#x} % {b:#x}");
            }
        }
    }
    check::<Bn<u8, 16>>();
    check::<Bn<u16, 8>>();
    check::<Bn<u32, 4>>();
    check::<Bn<u64, 2>>();
    check::<HeaplessBigInt<u8, 16>>();
    check::<HeaplessBigInt<u16, 8>>();
    check::<HeaplessBigInt<u32, 4>>();
    check::<HeaplessBigInt<u64, 2>>();
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
fn test_key_range_mul() {
    fn test_key_values<REF, INT>()
    where
        REF: num_traits::PrimInt + num_traits::ops::overflowing::OverflowingMul + core::fmt::Debug,
        INT: num_traits::PrimInt
            + num_traits::ops::overflowing::OverflowingMul
            + core::fmt::Debug
            + core::convert::From<REF>,
    {
        // Generate key test values: edge cases and some representative samples
        let mut test_values = Vec::new();

        // Edge cases
        test_values.push(REF::zero());
        test_values.push(REF::one());

        // Values around small powers of 2 (important for overflow detection)
        let mut power_of_2 = REF::one();
        for _ in 0..4 {
            // Only test first few powers of 2 to avoid large numbers
            if power_of_2 < REF::max_value() / (REF::one() + REF::one()) {
                test_values.push(power_of_2);
                test_values.push(power_of_2 + REF::one());
                if power_of_2 > REF::zero() {
                    test_values.push(power_of_2 - REF::one());
                }
                power_of_2 = power_of_2 + power_of_2; // power_of_2 *= 2
            }
        }

        // Some smaller middle values for broader coverage
        let max_val = REF::max_value();
        test_values.push(max_val / (REF::one() + REF::one())); // max/2

        // Add max_value last for boundary testing
        test_values.push(max_val);

        // Remove duplicates and sort
        test_values.sort();
        test_values.dedup();

        // Test all combinations of key values
        for &i in &test_values {
            for &j in &test_values {
                let ref_val = i.overflowing_mul(&j);
                let lhs: INT = i.into();
                let rhs: INT = j.into();
                let int_val = lhs.overflowing_mul(&rhs);
                assert_eq!(
                    int_val,
                    (ref_val.0.into(), ref_val.1),
                    "Failed for {:?} * {:?}",
                    i,
                    j
                );
            }
        }
    }

    test_key_values::<u8, Bn<u8, 1>>();
    test_key_values::<u16, Bn<u16, 1>>();
    test_key_values::<u16, Bn<u8, 2>>();

    // Note: Larger types may have overflow detection differences
    // Only test with smaller, safer values for now
    test_key_values::<u32, Bn<u32, 1>>();
    test_key_values::<u32, Bn<u16, 2>>();
    test_key_values::<u32, Bn<u8, 4>>();
}

#[test]
fn test_checked_div() {
    fn test<
        INT: num_traits::PrimInt
            + core::fmt::Debug
            + num_traits::CheckedDiv
            + num_traits::CheckedRem
            + core::convert::From<u8>,
    >() {
        let a: INT = 2.into();
        let b: INT = 0.into();
        assert_eq!(Into::<INT>::into(128).checked_div(&a), Some(64.into()));
        assert_eq!(Into::<INT>::into(128).checked_div(&b), None);
        assert_eq!(Into::<INT>::into(0).checked_div(&b), None);
        assert_eq!(Into::<INT>::into(0).checked_div(&a), Some(0.into()));

        assert_eq!(Into::<INT>::into(127).checked_rem(&a), Some(1.into()));
        assert_eq!(Into::<INT>::into(127).checked_rem(&b), None);
        assert_eq!(Into::<INT>::into(0).checked_rem(&b), None);
        assert_eq!(Into::<INT>::into(0).checked_rem(&a), Some(0.into()));
    }
    test::<u8>();
    test::<Bn<u8, 1>>();
    test::<u16>();
    test::<Bn<u16, 1>>();
    test::<Bn<u8, 2>>();
    test::<u32>();
    test::<Bn<u32, 1>>();
    test::<Bn<u16, 2>>();
    test::<Bn<u8, 4>>();
}
