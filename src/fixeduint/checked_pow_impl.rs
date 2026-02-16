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

//! Checked power implementation for FixedUInt.

use super::{FixedUInt, MachineWord};
use crate::const_numtrait::{ConstCheckedMul, ConstCheckedPow, ConstOne};
use crate::machineword::ConstMachineWord;

c0nst::c0nst! {
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstCheckedPow for FixedUInt<T, N> {
        fn checked_pow(self, exp: u32) -> Option<Self> {
            if exp == 0 {
                return Some(Self::one());
            }
            // Exponentiation by squaring with overflow checking
            let mut result = Self::one();
            let mut base = self;
            let mut e = exp;
            while e > 0 {
                if (e & 1) == 1 {
                    result = match ConstCheckedMul::checked_mul(&result, &base) {
                        Some(v) => v,
                        None => return None,
                    };
                }
                e >>= 1;
                if e > 0 {
                    base = match ConstCheckedMul::checked_mul(&base, &base) {
                        Some(v) => v,
                        None => return None,
                    };
                }
            }
            Some(result)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_checked_pow() {
        type U16 = FixedUInt<u8, 2>;

        // Basic cases
        assert_eq!(
            ConstCheckedPow::checked_pow(U16::from(2u8), 0),
            Some(U16::from(1u8))
        );
        assert_eq!(
            ConstCheckedPow::checked_pow(U16::from(2u8), 1),
            Some(U16::from(2u8))
        );
        assert_eq!(
            ConstCheckedPow::checked_pow(U16::from(2u8), 2),
            Some(U16::from(4u8))
        );
        assert_eq!(
            ConstCheckedPow::checked_pow(U16::from(2u8), 8),
            Some(U16::from(256u16))
        );
        assert_eq!(
            ConstCheckedPow::checked_pow(U16::from(3u8), 3),
            Some(U16::from(27u8))
        );

        // Edge cases
        assert_eq!(
            ConstCheckedPow::checked_pow(U16::from(0u8), 0),
            Some(U16::from(1u8))
        );
        assert_eq!(
            ConstCheckedPow::checked_pow(U16::from(0u8), 5),
            Some(U16::from(0u8))
        );
        assert_eq!(
            ConstCheckedPow::checked_pow(U16::from(1u8), 100),
            Some(U16::from(1u8))
        );

        // Overflow cases
        assert_eq!(ConstCheckedPow::checked_pow(U16::from(2u8), 16), None); // 2^16 = 65536 > 65535
        assert_eq!(ConstCheckedPow::checked_pow(U16::from(256u16), 2), None); // 256^2 = 65536 > 65535

        // Just fits
        assert_eq!(
            ConstCheckedPow::checked_pow(U16::from(2u8), 15),
            Some(U16::from(32768u16))
        );
    }

    c0nst::c0nst! {
        pub c0nst fn const_checked_pow<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            base: FixedUInt<T, N>,
            exp: u32,
        ) -> Option<FixedUInt<T, N>> {
            ConstCheckedPow::checked_pow(base, exp)
        }
    }

    #[test]
    fn test_const_checked_pow() {
        type U16 = FixedUInt<u8, 2>;

        assert_eq!(
            const_checked_pow(U16::from(2u8), 8),
            Some(U16::from(256u16))
        );

        #[cfg(feature = "nightly")]
        {
            const BASE: U16 = FixedUInt { array: [2, 0] };
            const POW_RESULT: Option<U16> = const_checked_pow(BASE, 8);
            assert_eq!(POW_RESULT, Some(FixedUInt { array: [0, 1] })); // 256 = [0, 1] in little-endian
        }
    }
}
