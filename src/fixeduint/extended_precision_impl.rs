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
    ConstBorrowingSub, ConstCarryingAdd, ConstCarryingMul, ConstWideningMul, ConstZero,
};
use crate::machineword::ConstMachineWord;

c0nst::c0nst! {
    /// Add with carry input, returns sum and carry output.
    /// Uses ConstCarryingAdd on limb types for consistency.
    c0nst fn add_with_carry<T: [c0nst] ConstMachineWord + [c0nst] ConstCarryingAdd, const N: usize>(
        a: &[T; N],
        b: &[T; N],
        carry_in: bool,
    ) -> ([T; N], bool) {
        let mut result = [T::zero(); N];
        let mut carry = carry_in;
        let mut i = 0usize;
        while i < N {
            let (sum, c) = ConstCarryingAdd::carrying_add(a[i], b[i], carry);
            result[i] = sum;
            carry = c;
            i += 1;
        }
        (result, carry)
    }

    /// Subtract with borrow input, returns difference and borrow output.
    /// Uses ConstBorrowingSub on limb types for consistency.
    c0nst fn sub_with_borrow<T: [c0nst] ConstMachineWord + [c0nst] ConstBorrowingSub, const N: usize>(
        a: &[T; N],
        b: &[T; N],
        borrow_in: bool,
    ) -> ([T; N], bool) {
        let mut result = [T::zero(); N];
        let mut borrow = borrow_in;
        let mut i = 0usize;
        while i < N {
            let (diff, b) = ConstBorrowingSub::borrowing_sub(a[i], b[i], borrow);
            result[i] = diff;
            borrow = b;
            i += 1;
        }
        (result, borrow)
    }

    /// Add a single word to an array at a given position, propagating carry.
    /// Returns the final carry out.
    c0nst fn add_word_at<T: [c0nst] ConstMachineWord + [c0nst] ConstCarryingAdd, const N: usize>(
        arr: &mut [T; N],
        word: T,
        pos: usize,
    ) -> bool {
        if pos >= N || word.is_zero() {
            return false;
        }
        let (sum, mut carry) = ConstCarryingAdd::carrying_add(arr[pos], word, false);
        arr[pos] = sum;
        let mut k = pos + 1;
        while carry && k < N {
            let (s, c) = ConstCarryingAdd::carrying_add(arr[k], T::zero(), true);
            arr[k] = s;
            carry = c;
            k += 1;
        }
        carry
    }

    impl<T: [c0nst] ConstMachineWord + [c0nst] ConstCarryingAdd + [c0nst] ConstBorrowingSub + MachineWord, const N: usize> c0nst ConstCarryingAdd for FixedUInt<T, N> {
        fn carrying_add(self, rhs: Self, carry: bool) -> (Self, bool) {
            let (array, carry_out) = add_with_carry(&self.array, &rhs.array, carry);
            (Self { array }, carry_out)
        }
    }

    impl<T: [c0nst] ConstMachineWord + [c0nst] ConstCarryingAdd + [c0nst] ConstBorrowingSub + MachineWord, const N: usize> c0nst ConstBorrowingSub for FixedUInt<T, N> {
        fn borrowing_sub(self, rhs: Self, borrow: bool) -> (Self, bool) {
            let (array, borrow_out) = sub_with_borrow(&self.array, &rhs.array, borrow);
            (Self { array }, borrow_out)
        }
    }

    impl<T: [c0nst] ConstMachineWord + [c0nst] ConstCarryingAdd + [c0nst] ConstBorrowingSub + MachineWord, const N: usize> c0nst ConstWideningMul for FixedUInt<T, N> {
        fn widening_mul(self, rhs: Self) -> (Self, Self) {
            // Use double-word accumulator approach like const_mul to achieve O(N²) complexity.
            // Instead of propagating carries per partial product (O(N³)), we accumulate
            // into ConstDoubleWord and extract single words once per position.
            let mut result_low = [T::zero(); N];
            let mut result_high = [T::zero(); N];

            let t_max = T::to_double(T::max_value());
            let dw_zero = <<T as ConstMachineWord>::ConstDoubleWord as ConstZero>::zero();
            let word_bits = core::mem::size_of::<T>() * 8;

            let mut i = 0usize;
            while i < N {
                let mut carry = dw_zero;
                let mut j = 0usize;
                while j < N {
                    let pos = i + j;
                    let op1_dw = T::to_double(self.array[i]);
                    let op2_dw = T::to_double(rhs.array[j]);
                    let mul_res = op1_dw * op2_dw;

                    // Get current accumulator value from appropriate half
                    let current = if pos < N {
                        T::to_double(result_low[pos])
                    } else if pos < 2 * N {
                        T::to_double(result_high[pos - N])
                    } else {
                        dw_zero
                    };

                    let mut accumulator = current + mul_res + carry;

                    // Extract carry for next position
                    if accumulator > t_max {
                        carry = accumulator >> word_bits;
                        accumulator &= t_max;
                    } else {
                        carry = dw_zero;
                    }

                    // Store back
                    if pos < N {
                        result_low[pos] = T::from_double(accumulator);
                    } else if pos < 2 * N {
                        result_high[pos - N] = T::from_double(accumulator);
                    }

                    j += 1;
                }

                // Propagate final carry from this row
                let mut pos = i + N;
                while carry != dw_zero && pos < 2 * N {
                    let current = T::to_double(result_high[pos - N]);
                    let mut accumulator = current + carry;
                    if accumulator > t_max {
                        carry = accumulator >> word_bits;
                        accumulator &= t_max;
                    } else {
                        carry = dw_zero;
                    }
                    result_high[pos - N] = T::from_double(accumulator);
                    pos += 1;
                }

                i += 1;
            }

            (Self { array: result_low }, Self { array: result_high })
        }
    }

    impl<T: [c0nst] ConstMachineWord + [c0nst] ConstCarryingAdd + [c0nst] ConstBorrowingSub + MachineWord, const N: usize> c0nst ConstCarryingMul for FixedUInt<T, N> {
        fn carrying_mul(self, rhs: Self, carry: Self) -> (Self, Self) {
            // widening_mul + add carry to result
            let (lo, hi) = ConstWideningMul::widening_mul(self, rhs);

            // Add carry to lo, propagate overflow to hi using carry bit directly
            let (lo2, c) = add_with_carry(&lo.array, &carry.array, false);

            // Pass the carry bit directly instead of constructing a temporary array
            let zeros = [T::zero(); N];
            let (hi2, _) = add_with_carry(&hi.array, &zeros, c);

            (Self { array: lo2 }, Self { array: hi2 })
        }

        fn carrying_mul_add(self, rhs: Self, addend: Self, carry: Self) -> (Self, Self) {
            // widening_mul + add addend + add carry
            let (lo, hi) = ConstWideningMul::widening_mul(self, rhs);

            // Add carry to lo
            let (lo2, c1) = add_with_carry(&lo.array, &carry.array, false);

            // Add addend to lo2
            let (lo3, c2) = add_with_carry(&lo2, &addend.array, false);

            // Add both carry bits to hi (c1 and c2 can both be true)
            let zeros = [T::zero(); N];
            let (hi2, extra_carry) = add_with_carry(&hi.array, &zeros, c1);
            let (hi3, _) = add_with_carry(&hi2, &zeros, c2 || extra_carry);

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
        pub c0nst fn const_carrying_add<T: [c0nst] ConstMachineWord + [c0nst] ConstCarryingAdd + [c0nst] ConstBorrowingSub + MachineWord, const N: usize>(
            a: FixedUInt<T, N>,
            b: FixedUInt<T, N>,
            carry: bool,
        ) -> (FixedUInt<T, N>, bool) {
            ConstCarryingAdd::carrying_add(a, b, carry)
        }

        pub c0nst fn const_borrowing_sub<T: [c0nst] ConstMachineWord + [c0nst] ConstCarryingAdd + [c0nst] ConstBorrowingSub + MachineWord, const N: usize>(
            a: FixedUInt<T, N>,
            b: FixedUInt<T, N>,
            borrow: bool,
        ) -> (FixedUInt<T, N>, bool) {
            ConstBorrowingSub::borrowing_sub(a, b, borrow)
        }

        pub c0nst fn const_widening_mul<T: [c0nst] ConstMachineWord + [c0nst] ConstCarryingAdd + [c0nst] ConstBorrowingSub + MachineWord, const N: usize>(
            a: FixedUInt<T, N>,
            b: FixedUInt<T, N>,
        ) -> (FixedUInt<T, N>, FixedUInt<T, N>) {
            ConstWideningMul::widening_mul(a, b)
        }

        pub c0nst fn const_carrying_mul<T: [c0nst] ConstMachineWord + [c0nst] ConstCarryingAdd + [c0nst] ConstBorrowingSub + MachineWord, const N: usize>(
            a: FixedUInt<T, N>,
            b: FixedUInt<T, N>,
            carry: FixedUInt<T, N>,
        ) -> (FixedUInt<T, N>, FixedUInt<T, N>) {
            ConstCarryingMul::carrying_mul(a, b, carry)
        }

        pub c0nst fn const_carrying_mul_add<T: [c0nst] ConstMachineWord + [c0nst] ConstCarryingAdd + [c0nst] ConstBorrowingSub + MachineWord, const N: usize>(
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
    fn test_carrying_mul_add_double_overflow() {
        // Test case where both addend and carry cause overflow
        let max = U16::from(0xFFFFu16);
        let one = U16::from(1u8);

        // 1 * 1 + 0xFFFF + 0xFFFF = 1 + 0x1FFFE = 0x1FFFF = (0xFFFF, 1)
        let (lo, hi) = const_carrying_mul_add(one, one, max, max);
        assert_eq!(lo, U16::from(0xFFFFu16));
        assert_eq!(hi, U16::from(1u8));
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
