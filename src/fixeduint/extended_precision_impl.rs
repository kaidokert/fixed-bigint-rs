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

//! Extended precision arithmetic operations for FixedUInt.
//!
//! These operations expose carry/borrow inputs and outputs, and widening
//! multiplication, useful for implementing arbitrary-precision arithmetic.

use super::{FixedUInt, MachineWord};
use crate::const_numtrait::{
    ConstBorrowingSub, ConstCarryingAdd, ConstCarryingMul, ConstWideningMul,
};
use crate::machineword::ConstMachineWord;

c0nst::c0nst! {
    /// Add with carry input, returns sum and carry output.
    c0nst fn add_with_carry<T: [c0nst] ConstMachineWord, const N: usize>(
        a: &[T; N],
        b: &[T; N],
        carry_in: bool,
    ) -> ([T; N], bool) {
        let mut result = [T::zero(); N];
        let mut carry = if carry_in { T::one() } else { T::zero() };
        let mut i = 0usize;
        while i < N {
            let (sum1, c1) = a[i].overflowing_add(&b[i]);
            let (sum2, c2) = sum1.overflowing_add(&carry);
            result[i] = sum2;
            carry = if c1 || c2 { T::one() } else { T::zero() };
            i += 1;
        }
        (result, !carry.is_zero())
    }

    /// Subtract with borrow input, returns difference and borrow output.
    c0nst fn sub_with_borrow<T: [c0nst] ConstMachineWord, const N: usize>(
        a: &[T; N],
        b: &[T; N],
        borrow_in: bool,
    ) -> ([T; N], bool) {
        let mut result = [T::zero(); N];
        let mut borrow = if borrow_in { T::one() } else { T::zero() };
        let mut i = 0usize;
        while i < N {
            let (diff1, b1) = a[i].overflowing_sub(&b[i]);
            let (diff2, b2) = diff1.overflowing_sub(&borrow);
            result[i] = diff2;
            borrow = if b1 || b2 { T::one() } else { T::zero() };
            i += 1;
        }
        (result, !borrow.is_zero())
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstCarryingAdd for FixedUInt<T, N> {
        fn carrying_add(self, rhs: Self, carry: bool) -> (Self, bool) {
            let (array, carry_out) = add_with_carry(&self.array, &rhs.array, carry);
            (Self { array }, carry_out)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstBorrowingSub for FixedUInt<T, N> {
        fn borrowing_sub(self, rhs: Self, borrow: bool) -> (Self, bool) {
            let (array, borrow_out) = sub_with_borrow(&self.array, &rhs.array, borrow);
            (Self { array }, borrow_out)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstWideningMul for FixedUInt<T, N> {
        fn widening_mul(self, rhs: Self) -> (Self, Self) {
            // Perform full multiplication into a double-width buffer
            // Result is 2*N words, split into low N words and high N words
            let mut result_low = [T::zero(); N];
            let mut result_high = [T::zero(); N];

            // Schoolbook multiplication: for each word pair, accumulate into result
            let mut i = 0usize;
            while i < N {
                let mut j = 0usize;
                while j < N {
                    let pos = i + j;
                    // Multiply words and get double-width result
                    let (prod_lo, prod_hi) = self.array[i].widening_mul(&rhs.array[j]);

                    // Add prod_lo to result at position pos
                    let mut carry = prod_lo;
                    let mut k = pos;
                    while !carry.is_zero() && k < 2 * N {
                        if k < N {
                            let (sum, c) = result_low[k].overflowing_add(&carry);
                            result_low[k] = sum;
                            carry = if c { T::one() } else { T::zero() };
                        } else {
                            let (sum, c) = result_high[k - N].overflowing_add(&carry);
                            result_high[k - N] = sum;
                            carry = if c { T::one() } else { T::zero() };
                        }
                        k += 1;
                    }

                    // Add prod_hi to result at position pos+1
                    carry = prod_hi;
                    k = pos + 1;
                    while !carry.is_zero() && k < 2 * N {
                        if k < N {
                            let (sum, c) = result_low[k].overflowing_add(&carry);
                            result_low[k] = sum;
                            carry = if c { T::one() } else { T::zero() };
                        } else {
                            let (sum, c) = result_high[k - N].overflowing_add(&carry);
                            result_high[k - N] = sum;
                            carry = if c { T::one() } else { T::zero() };
                        }
                        k += 1;
                    }

                    j += 1;
                }
                i += 1;
            }

            (Self { array: result_low }, Self { array: result_high })
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> c0nst ConstCarryingMul for FixedUInt<T, N> {
        fn carrying_mul(self, rhs: Self, carry: Self) -> (Self, Self) {
            // widening_mul + add carry to result
            let (lo, hi) = ConstWideningMul::widening_mul(self, rhs);

            // Add carry to lo, propagate to hi
            let (lo2, c) = add_with_carry(&lo.array, &carry.array, false);
            let carry_array = if c {
                let mut arr = [T::zero(); N];
                arr[0] = T::one();
                arr
            } else {
                [T::zero(); N]
            };
            let (hi2, _) = add_with_carry(&hi.array, &carry_array, false);

            (Self { array: lo2 }, Self { array: hi2 })
        }

        fn carrying_mul_add(self, rhs: Self, addend: Self, carry: Self) -> (Self, Self) {
            // widening_mul + add addend + add carry
            let (lo, hi) = ConstWideningMul::widening_mul(self, rhs);

            // Add carry to lo, propagate to hi
            let (lo2, c1) = add_with_carry(&lo.array, &carry.array, false);
            let carry_array1 = if c1 {
                let mut arr = [T::zero(); N];
                arr[0] = T::one();
                arr
            } else {
                [T::zero(); N]
            };

            // Add addend to lo2, propagate to hi
            let (lo3, c2) = add_with_carry(&lo2, &addend.array, false);
            let carry_array2 = if c2 {
                let mut arr = [T::zero(); N];
                arr[0] = T::one();
                arr
            } else {
                [T::zero(); N]
            };

            // Add both carries to hi
            let (hi2, _) = add_with_carry(&hi.array, &carry_array1, false);
            let (hi3, _) = add_with_carry(&hi2, &carry_array2, false);

            (Self { array: lo3 }, Self { array: hi3 })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type U16 = FixedUInt<u8, 2>;
    type U32 = FixedUInt<u8, 4>;

    c0nst::c0nst! {
        pub c0nst fn const_carrying_add<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            a: FixedUInt<T, N>,
            b: FixedUInt<T, N>,
            carry: bool,
        ) -> (FixedUInt<T, N>, bool) {
            ConstCarryingAdd::carrying_add(a, b, carry)
        }

        pub c0nst fn const_borrowing_sub<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            a: FixedUInt<T, N>,
            b: FixedUInt<T, N>,
            borrow: bool,
        ) -> (FixedUInt<T, N>, bool) {
            ConstBorrowingSub::borrowing_sub(a, b, borrow)
        }

        pub c0nst fn const_widening_mul<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            a: FixedUInt<T, N>,
            b: FixedUInt<T, N>,
        ) -> (FixedUInt<T, N>, FixedUInt<T, N>) {
            ConstWideningMul::widening_mul(a, b)
        }

        pub c0nst fn const_carrying_mul<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            a: FixedUInt<T, N>,
            b: FixedUInt<T, N>,
            carry: FixedUInt<T, N>,
        ) -> (FixedUInt<T, N>, FixedUInt<T, N>) {
            ConstCarryingMul::carrying_mul(a, b, carry)
        }

        pub c0nst fn const_carrying_mul_add<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
            a: FixedUInt<T, N>,
            b: FixedUInt<T, N>,
            addend: FixedUInt<T, N>,
            carry: FixedUInt<T, N>,
        ) -> (FixedUInt<T, N>, FixedUInt<T, N>) {
            ConstCarryingMul::carrying_mul_add(a, b, addend, carry)
        }
    }

    #[test]
    fn test_carrying_add_no_carry() {
        let a = U16::from(100u8);
        let b = U16::from(50u8);

        // Without carry in
        let (sum, carry_out) = const_carrying_add(a, b, false);
        assert_eq!(sum, U16::from(150u8));
        assert!(!carry_out);

        // With carry in
        let (sum, carry_out) = const_carrying_add(a, b, true);
        assert_eq!(sum, U16::from(151u8));
        assert!(!carry_out);
    }

    #[test]
    fn test_carrying_add_with_overflow() {
        let max = U16::from(0xFFFFu16);
        let one = U16::from(1u8);

        // max + 0 with carry = max + 1 = 0 with carry out
        let (sum, carry_out) = const_carrying_add(max, U16::from(0u8), true);
        assert_eq!(sum, U16::from(0u8));
        assert!(carry_out);

        // max + 1 = 0 with carry out
        let (sum, carry_out) = const_carrying_add(max, one, false);
        assert_eq!(sum, U16::from(0u8));
        assert!(carry_out);

        // max + max = 0xFFFE with carry out
        let (sum, carry_out) = const_carrying_add(max, max, false);
        assert_eq!(sum, U16::from(0xFFFEu16));
        assert!(carry_out);
    }

    #[test]
    fn test_borrowing_sub_no_borrow() {
        let a = U16::from(150u8);
        let b = U16::from(50u8);

        // Without borrow in
        let (diff, borrow_out) = const_borrowing_sub(a, b, false);
        assert_eq!(diff, U16::from(100u8));
        assert!(!borrow_out);

        // With borrow in
        let (diff, borrow_out) = const_borrowing_sub(a, b, true);
        assert_eq!(diff, U16::from(99u8));
        assert!(!borrow_out);
    }

    #[test]
    fn test_borrowing_sub_with_underflow() {
        let zero = U16::from(0u8);
        let one = U16::from(1u8);

        // 0 - 1 = 0xFFFF with borrow out
        let (diff, borrow_out) = const_borrowing_sub(zero, one, false);
        assert_eq!(diff, U16::from(0xFFFFu16));
        assert!(borrow_out);

        // 0 - 0 with borrow = 0xFFFF with borrow out
        let (diff, borrow_out) = const_borrowing_sub(zero, zero, true);
        assert_eq!(diff, U16::from(0xFFFFu16));
        assert!(borrow_out);

        // 1 - 1 with borrow = 0xFFFF with borrow out
        let (diff, borrow_out) = const_borrowing_sub(one, one, true);
        assert_eq!(diff, U16::from(0xFFFFu16));
        assert!(borrow_out);
    }

    #[test]
    fn test_widening_mul() {
        // 100 * 100 = 10000 (fits in 16 bits, high = 0)
        let a = U16::from(100u8);
        let (lo, hi) = const_widening_mul(a, a);
        assert_eq!(lo, U16::from(10000u16));
        assert_eq!(hi, U16::from(0u8));

        // 256 * 256 = 65536 = 0x10000 (low = 0, high = 1)
        let b = U16::from(256u16);
        let (lo, hi) = const_widening_mul(b, b);
        assert_eq!(lo, U16::from(0u8));
        assert_eq!(hi, U16::from(1u8));

        // 0xFFFF * 0xFFFF = 0xFFFE0001
        let max = U16::from(0xFFFFu16);
        let (lo, hi) = const_widening_mul(max, max);
        assert_eq!(lo, U16::from(0x0001u16)); // low 16 bits of 0xFFFE0001
        assert_eq!(hi, U16::from(0xFFFEu16)); // high 16 bits of 0xFFFE0001
    }

    #[test]
    fn test_widening_mul_larger() {
        // Test with 32-bit type (U32 = FixedUInt<u8, 4>)
        let a = U32::from(0x10000u32); // 2^16
        let b = U32::from(0x10000u32); // 2^16
        let (lo, hi) = const_widening_mul(a, b);
        // 2^16 * 2^16 = 2^32 = 0x100000000
        // low 32 bits = 0, high 32 bits = 1
        assert_eq!(lo, U32::from(0u8));
        assert_eq!(hi, U32::from(1u8));
    }

    #[test]
    fn test_carrying_mul() {
        let a = U16::from(100u8);
        let b = U16::from(100u8);
        let carry = U16::from(5u8);

        // 100 * 100 + 5 = 10005
        let (lo, hi) = const_carrying_mul(a, b, carry);
        assert_eq!(lo, U16::from(10005u16));
        assert_eq!(hi, U16::from(0u8));

        // With larger carry that causes overflow in low part
        let max = U16::from(0xFFFFu16);
        let one = U16::from(1u8);
        // 1 * 1 + 0xFFFF = 0x10000 = (0, 1)
        let (lo, hi) = const_carrying_mul(one, one, max);
        assert_eq!(lo, U16::from(0u8));
        assert_eq!(hi, U16::from(1u8));
    }

    #[test]
    fn test_carrying_mul_add() {
        let a = U16::from(100u8);
        let b = U16::from(100u8);
        let addend = U16::from(10u8);
        let carry = U16::from(5u8);

        // 100 * 100 + 10 + 5 = 10015
        let (lo, hi) = const_carrying_mul_add(a, b, addend, carry);
        assert_eq!(lo, U16::from(10015u16));
        assert_eq!(hi, U16::from(0u8));
    }

    #[test]
    fn test_const_context() {
        #[cfg(feature = "nightly")]
        {
            const A: U16 = FixedUInt { array: [100, 0] };
            const B: U16 = FixedUInt { array: [50, 0] };

            // Test carrying_add in const context
            const ADD_RESULT: (U16, bool) = const_carrying_add(A, B, false);
            assert_eq!(ADD_RESULT.0, U16::from(150u8));
            assert!(!ADD_RESULT.1);

            const ADD_WITH_CARRY: (U16, bool) = const_carrying_add(A, B, true);
            assert_eq!(ADD_WITH_CARRY.0, U16::from(151u8));

            // Test borrowing_sub in const context
            const SUB_RESULT: (U16, bool) = const_borrowing_sub(A, B, false);
            assert_eq!(SUB_RESULT.0, U16::from(50u8));
            assert!(!SUB_RESULT.1);

            // Test widening_mul in const context
            const C: U16 = FixedUInt { array: [0, 1] }; // 256
            const MUL_RESULT: (U16, U16) = const_widening_mul(C, C);
            assert_eq!(MUL_RESULT.0, U16::from(0u8)); // 256*256 = 65536, low = 0
            assert_eq!(MUL_RESULT.1, U16::from(1u8)); // high = 1
        }
    }
}
