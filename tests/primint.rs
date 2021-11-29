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
fn test_bitcount() {
    fn test_8_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u8>,
    >() {
        assert_eq!(Into::<INT>::into(0b0).count_ones(), 0);
        assert_eq!(Into::<INT>::into(0b010).count_ones(), 1);
        assert_eq!(Into::<INT>::into(0b110).count_ones(), 2);
        assert_eq!(Into::<INT>::into(0xFF).count_ones(), 8);

        assert_eq!(Into::<INT>::into(0b0).count_zeros(), 8);
        assert_eq!(Into::<INT>::into(0b010).count_zeros(), 7);
        assert_eq!(Into::<INT>::into(0b110).count_zeros(), 6);
        assert_eq!(Into::<INT>::into(0xFF).count_zeros(), 0);
    }
    test_8_bit::<u8>();
    test_8_bit::<Bn<u8, 1>>();

    fn test_16_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u16>,
    >() {
        assert_eq!(Into::<INT>::into(0b0).count_ones(), 0);
        assert_eq!(Into::<INT>::into(0b010).count_ones(), 1);
        assert_eq!(Into::<INT>::into(0b110).count_ones(), 2);
        assert_eq!(Into::<INT>::into(0xFFFF).count_ones(), 16);

        assert_eq!(Into::<INT>::into(0b0).count_zeros(), 16);
        assert_eq!(Into::<INT>::into(0b010).count_zeros(), 15);
        assert_eq!(Into::<INT>::into(0b110).count_zeros(), 14);
        assert_eq!(Into::<INT>::into(0xFFFF).count_zeros(), 0);
    }

    test_16_bit::<u16>();
    test_16_bit::<Bn<u8, 2>>();
    test_16_bit::<Bn<u16, 1>>();

    fn test_32_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u32>,
    >() {
        assert_eq!(Into::<INT>::into(0b0).count_ones(), 0);
        assert_eq!(Into::<INT>::into(0b110).count_ones(), 2);
        assert_eq!(Into::<INT>::into(0xFFFFFFFF).count_ones(), 32);

        assert_eq!(Into::<INT>::into(0b0).count_zeros(), 32);
        assert_eq!(Into::<INT>::into(0b110000).count_zeros(), 30);
        assert_eq!(Into::<INT>::into(0xFFFFFFFF).count_zeros(), 0);
    }
    test_32_bit::<u32>();
    test_32_bit::<Bn<u8, 4>>();
    test_32_bit::<Bn<u16, 2>>();
    test_32_bit::<Bn<u32, 1>>();
}

#[test]
fn test_leading_trailing_bits() {
    fn test_8_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u8>,
    >() {
        assert_eq!(Into::<INT>::into(0b0).leading_zeros(), 8);
        assert_eq!(Into::<INT>::into(0b1).leading_zeros(), 7);
        assert_eq!(Into::<INT>::into(0x80).leading_zeros(), 0);
        assert_eq!(Into::<INT>::into(0xFF).leading_zeros(), 0);

        assert_eq!(Into::<INT>::into(0b0).trailing_zeros(), 8);
        assert_eq!(Into::<INT>::into(0x80).trailing_zeros(), 7);
        assert_eq!(Into::<INT>::into(0b1).trailing_zeros(), 0);
    }
    test_8_bit::<u8>();
    test_8_bit::<Bn<u8, 1>>();

    fn test_16_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u16>,
    >() {
        assert_eq!(Into::<INT>::into(0b0).leading_zeros(), 16);
        assert_eq!(Into::<INT>::into(0b1).leading_zeros(), 15);
        assert_eq!(Into::<INT>::into(0x8000).leading_zeros(), 0);
        assert_eq!(Into::<INT>::into(0xFFFF).leading_zeros(), 0);

        assert_eq!(Into::<INT>::into(0b0).trailing_zeros(), 16);
        assert_eq!(Into::<INT>::into(0x8000).trailing_zeros(), 15);
        assert_eq!(Into::<INT>::into(0b1).trailing_zeros(), 0);
    }
    test_16_bit::<u16>();
    test_16_bit::<Bn<u8, 2>>();
    test_16_bit::<Bn<u16, 1>>();

    fn test_32_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u32>,
    >() {
        assert_eq!(Into::<INT>::into(0b0).leading_zeros(), 32);
        assert_eq!(Into::<INT>::into(0b1).leading_zeros(), 31);
        assert_eq!(Into::<INT>::into(0x80000000).leading_zeros(), 0);
        assert_eq!(Into::<INT>::into(0xFFFFFFFF).leading_zeros(), 0);

        assert_eq!(Into::<INT>::into(0b0).trailing_zeros(), 32);
        assert_eq!(Into::<INT>::into(0x80000000).trailing_zeros(), 31);
        assert_eq!(Into::<INT>::into(0b1).trailing_zeros(), 0);
    }
    test_32_bit::<u32>();
    test_32_bit::<Bn<u8, 4>>();
    test_32_bit::<Bn<u16, 2>>();
    test_32_bit::<Bn<u32, 1>>();
}

#[test]
fn test_swap_bytes() {
    fn test_8_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u8>,
    >() {
        let tests = [(0x01, 0x01)];

        for (a, res) in &tests {
            let b_a = Into::<INT>::into(*a);

            let b_res = b_a.swap_bytes();
            assert_eq!(b_res.to_u64().unwrap(), *res);
        }
    }

    test_8_bit::<u8>();
    test_8_bit::<Bn<u8, 1>>();

    // 16 bit
    fn test_16_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u16>,
    >() {
        let tests = [(0x0102, 0x0201)];

        for (a, res) in &tests {
            let b_a = Into::<INT>::into(*a);

            let b_res = b_a.swap_bytes();
            assert_eq!(b_res.to_u64().unwrap(), *res);
        }
    }

    test_16_bit::<u16>();
    test_16_bit::<Bn<u8, 2>>();
    test_16_bit::<Bn<u16, 1>>();

    //32 bit
    fn test_32_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u32>,
    >() {
        let tests = [(0x01020304, 0x04030201)];

        for (a, res) in &tests {
            let b_a = Into::<INT>::into(*a);

            let b_res = b_a.swap_bytes();
            assert_eq!(b_res.to_u64().unwrap(), *res);
        }
    }

    test_32_bit::<u32>();
    test_32_bit::<Bn<u8, 4>>();
    test_32_bit::<Bn<u16, 2>>();
    test_32_bit::<Bn<u32, 1>>();
}

#[test]
fn test_to_be() {
    fn test_8_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u8>,
    >() {
        let tests = [(0x01, 0x01)];

        for (a, res) in &tests {
            let b_a = Into::<INT>::into(*a);

            let b_res = b_a.to_be();
            assert_eq!(b_res.to_u64().unwrap(), *res);
        }
    }

    test_8_bit::<u8>();
    test_8_bit::<Bn<u8, 1>>();

    // 16 bit
    fn test_16_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u16>,
    >() {
        let tests = [(0x0102, 0x0201)];

        for (a, res) in &tests {
            let b_a = Into::<INT>::into(*a);

            let b_res = b_a.to_be();
            assert_eq!(b_res.to_u64().unwrap(), *res);
        }
    }

    test_16_bit::<u16>();
    test_16_bit::<Bn<u8, 2>>();
    test_16_bit::<Bn<u16, 1>>();

    //32 bit
    fn test_32_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u32>,
    >() {
        let tests = [(0x01020304, 0x04030201)];

        for (a, res) in &tests {
            let b_a = Into::<INT>::into(*a);

            let b_res = b_a.to_be();
            assert_eq!(b_res.to_u64().unwrap(), *res);
        }
    }

    test_32_bit::<u32>();
    test_32_bit::<Bn<u8, 4>>();
    test_32_bit::<Bn<u16, 2>>();
    test_32_bit::<Bn<u32, 1>>();
}

#[test]
fn test_to_le() {
    fn test_8_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u8>,
    >() {
        let tests = [(0x01, 0x01)];

        for (a, res) in &tests {
            let b_a = Into::<INT>::into(*a);

            let b_res = b_a.to_le();
            assert_eq!(b_res.to_u64().unwrap(), *res);
        }
    }

    test_8_bit::<u8>();
    test_8_bit::<Bn<u8, 1>>();

    // 16 bit
    fn test_16_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u16>,
    >() {
        let tests = [(0x0102, 0x0102)];

        for (a, res) in &tests {
            let b_a = Into::<INT>::into(*a);

            let b_res = b_a.to_le();
            assert_eq!(b_res.to_u64().unwrap(), *res);
        }
    }

    test_16_bit::<u16>();
    test_16_bit::<Bn<u8, 2>>();
    test_16_bit::<Bn<u16, 1>>();

    //32 bit
    fn test_32_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u32>,
    >() {
        let tests = [(0x01020304, 0x01020304)];

        for (a, res) in &tests {
            let b_a = Into::<INT>::into(*a);

            let b_res = b_a.to_le();
            assert_eq!(b_res.to_u64().unwrap(), *res);
        }
    }

    test_32_bit::<u32>();
    test_32_bit::<Bn<u8, 4>>();
    test_32_bit::<Bn<u16, 2>>();
    test_32_bit::<Bn<u32, 1>>();
}

