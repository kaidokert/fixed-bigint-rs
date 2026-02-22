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
use crate::const_numtraits::{
    ConstBorrowingSub, ConstCarryingAdd, ConstCarryingMul, ConstWideningMul,
};
use crate::machineword::ConstMachineWord;
use crate::patch_num_traits::{CarryingMul, WideningMul};

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

    impl<T: [c0nst] ConstMachineWord + [c0nst] ConstCarryingAdd + MachineWord, const N: usize> c0nst ConstCarryingAdd for FixedUInt<T, N> {
        fn carrying_add(self, rhs: Self, carry: bool) -> (Self, bool) {
            let (array, carry_out) = add_with_carry(&self.array, &rhs.array, carry);
            (Self { array }, carry_out)
        }
    }

    impl<T: [c0nst] ConstMachineWord + [c0nst] ConstBorrowingSub + MachineWord, const N: usize> c0nst ConstBorrowingSub for FixedUInt<T, N> {
        fn borrowing_sub(self, rhs: Self, borrow: bool) -> (Self, bool) {
            let (array, borrow_out) = sub_with_borrow(&self.array, &rhs.array, borrow);
            (Self { array }, borrow_out)
        }
    }

    /// Helper: get value at position in 2N-word result (split into low/high).
    c0nst fn get_at<T: [c0nst] ConstMachineWord, const N: usize>(
        lo: &[T; N], hi: &[T; N], pos: usize
    ) -> T {
        if pos < N { lo[pos] } else if pos < 2 * N { hi[pos - N] } else { T::zero() }
    }

    /// Helper: set value at position in 2N-word result (split into low/high).
    c0nst fn set_at<T: [c0nst] ConstMachineWord, const N: usize>(
        lo: &mut [T; N], hi: &mut [T; N], pos: usize, val: T
    ) {
        if pos < N { lo[pos] = val; } else if pos < 2 * N { hi[pos - N] = val; }
    }

    impl<T: [c0nst] ConstMachineWord + [c0nst] ConstCarryingAdd + [c0nst] ConstBorrowingSub + MachineWord, const N: usize> c0nst ConstWideningMul for FixedUInt<T, N> {
        fn widening_mul(self, rhs: Self) -> (Self, Self) {
            // Schoolbook multiplication: for each (i,j), add the 2-word product a[i]*b[j]
            // to result[i+j : i+j+2], propagating any carry upward.
            let mut result_low = [T::zero(); N];
            let mut result_high = [T::zero(); N];

            let mut i = 0usize;
            while i < N {
                let mut j = 0usize;
                while j < N {
                    let pos = i + j;
                    let (mul_lo, mul_hi) = ConstWideningMul::widening_mul(self.array[i], rhs.array[j]);

                    // Add the 2-word product (mul_hi, mul_lo) at position pos.
                    // Step 1: add mul_lo at pos
                    let cur0 = get_at(&result_low, &result_high, pos);
                    let (sum0, c0) = ConstCarryingAdd::carrying_add(cur0, mul_lo, false);
                    set_at(&mut result_low, &mut result_high, pos, sum0);

                    // Step 2: add mul_hi + carry at pos+1
                    let cur1 = get_at(&result_low, &result_high, pos + 1);
                    let (sum1, c1) = ConstCarryingAdd::carrying_add(cur1, mul_hi, c0);
                    set_at(&mut result_low, &mut result_high, pos + 1, sum1);

                    // Step 3: propagate any remaining carry
                    let mut carry = c1;
                    let mut p = pos + 2;
                    while carry && p < 2 * N {
                        let cur = get_at(&result_low, &result_high, p);
                        let (sum, c) = ConstCarryingAdd::carrying_add(cur, T::zero(), true);
                        set_at(&mut result_low, &mut result_high, p, sum);
                        carry = c;
                        p += 1;
                    }

                    j += 1;
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

            // Add carry bits to hi separately (both c1 and c2 can be true = need to add 2)
            let zeros = [T::zero(); N];
            let (hi2, _) = add_with_carry(&hi.array, &zeros, c1);
            let (hi3, _) = add_with_carry(&hi2, &zeros, c2);

            (Self { array: lo3 }, Self { array: hi3 })
        }
    }
}

/// Non-const widening multiplication that delegates to ConstWideningMul.
impl<T: ConstMachineWord + ConstCarryingAdd + ConstBorrowingSub + MachineWord, const N: usize>
    WideningMul for FixedUInt<T, N>
{
    type Output = Self;
    fn widening_mul(self, rhs: Self) -> (Self, Self) {
        <Self as ConstWideningMul>::widening_mul(self, rhs)
    }
}

/// Ref-based widening multiplication — avoids copying large FixedUInt on stack.
impl<T: ConstMachineWord + ConstCarryingAdd + ConstBorrowingSub + MachineWord, const N: usize>
    WideningMul for &FixedUInt<T, N>
{
    type Output = FixedUInt<T, N>;
    fn widening_mul(self, rhs: Self) -> (FixedUInt<T, N>, FixedUInt<T, N>) {
        <FixedUInt<T, N> as ConstWideningMul>::widening_mul(*self, *rhs)
    }
}

/// Non-const carrying multiplication that delegates to ConstCarryingMul.
impl<T: ConstMachineWord + ConstCarryingAdd + ConstBorrowingSub + MachineWord, const N: usize>
    CarryingMul for FixedUInt<T, N>
{
    type Output = Self;
    fn carrying_mul(self, rhs: Self, carry: Self) -> (Self, Self) {
        <Self as ConstCarryingMul>::carrying_mul(self, rhs, carry)
    }

    fn carrying_mul_add(self, rhs: Self, addend: Self, carry: Self) -> (Self, Self) {
        <Self as ConstCarryingMul>::carrying_mul_add(self, rhs, addend, carry)
    }
}

/// Ref-based carrying multiplication — avoids copying large FixedUInt on stack.
impl<T: ConstMachineWord + ConstCarryingAdd + ConstBorrowingSub + MachineWord, const N: usize>
    CarryingMul for &FixedUInt<T, N>
{
    type Output = FixedUInt<T, N>;
    fn carrying_mul(self, rhs: Self, carry: Self) -> (FixedUInt<T, N>, FixedUInt<T, N>) {
        <FixedUInt<T, N> as ConstCarryingMul>::carrying_mul(*self, *rhs, *carry)
    }

    fn carrying_mul_add(
        self,
        rhs: Self,
        addend: Self,
        carry: Self,
    ) -> (FixedUInt<T, N>, FixedUInt<T, N>) {
        <FixedUInt<T, N> as ConstCarryingMul>::carrying_mul_add(*self, *rhs, *addend, *carry)
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

    /// Polymorphic test: verify widening_mul produces identical results across
    /// different word layouts for the same values.
    #[test]
    fn test_widening_mul_polymorphic() {
        // Generic test function following crate pattern
        fn test_widening<T>(a: T, b: T, expected_lo: T, expected_hi: T)
        where
            T: ConstWideningMul
                + ConstCarryingAdd
                + ConstBorrowingSub
                + Eq
                + core::fmt::Debug
                + Copy,
        {
            let (lo, hi) = ConstWideningMul::widening_mul(a, b);
            assert_eq!(lo, expected_lo, "lo mismatch");
            assert_eq!(hi, expected_hi, "hi mismatch");
        }

        // Test 1: 256 * 256 = 65536
        // As u16 (FixedUInt<u8, 2>): 16-bit overflow, 256*256 = 0x10000 = (lo=0, hi=1)
        test_widening(
            U16::from(256u16),
            U16::from(256u16),
            U16::from(0u16),
            U16::from(1u16),
        );

        // As u32 (FixedUInt<u8, 4>): fits in 32 bits, so lo=65536, hi=0
        test_widening(
            U32::from(256u32),
            U32::from(256u32),
            U32::from(65536u32),
            U32::from(0u32),
        );

        // Test 2: 0xFFFF * 0xFFFF = 0xFFFE0001
        test_widening(
            U16::from(0xFFFFu16),
            U16::from(0xFFFFu16),
            U16::from(0x0001u16),
            U16::from(0xFFFEu16),
        );

        // Test 3: 0xFFFFFFFF * 2 = 0x1_FFFFFFFE (tests carry across word boundary)
        test_widening(
            U32::from(0xFFFFFFFFu32),
            U32::from(2u32),
            U32::from(0xFFFFFFFEu32),
            U32::from(1u32),
        );
    }

    /// Polymorphic test for carrying_mul_add with edge cases.
    #[test]
    fn test_carrying_mul_add_polymorphic() {
        fn test_cma<T>(a: T, b: T, addend: T, carry: T, expected_lo: T, expected_hi: T)
        where
            T: ConstCarryingMul + Eq + core::fmt::Debug + Copy,
        {
            let (lo, hi) = ConstCarryingMul::carrying_mul_add(a, b, addend, carry);
            assert_eq!(lo, expected_lo, "lo mismatch");
            assert_eq!(hi, expected_hi, "hi mismatch");
        }

        // Test: max * max + max + max = 0xFFFF * 0xFFFF + 0xFFFF + 0xFFFF
        //     = 0xFFFE0001 + 0x1FFFE = 0xFFFFFFFF
        // lo = 0xFFFF, hi = 0xFFFF
        let max16 = U16::from(0xFFFFu16);
        test_cma(
            max16,
            max16,
            max16,
            max16,
            U16::from(0xFFFFu16),
            U16::from(0xFFFFu16),
        );

        // Same test with different layout (U32 = FixedUInt<u8, 4>)
        let max32 = U32::from(0xFFFFFFFFu32);
        let zero32 = U32::from(0u32);
        // max * 1 + 0 + max = max + max = 2*max = 0x1_FFFFFFFE
        test_cma(
            max32,
            U32::from(1u32),
            zero32,
            max32,
            U32::from(0xFFFFFFFEu32),
            U32::from(1u32),
        );
    }

    /// Test the non-const WideningMul trait for primitives and FixedUInt.
    #[test]
    fn test_widening_mul_trait() {
        // Test primitive types via WideningMul trait
        assert_eq!(WideningMul::widening_mul(255u8, 255u8), (1, 254)); // 0xFE01
        assert_eq!(
            WideningMul::widening_mul(0xFFFFu16, 0xFFFFu16),
            (0x0001, 0xFFFE)
        );
        assert_eq!(
            WideningMul::widening_mul(0xFFFF_FFFFu32, 2u32),
            (0xFFFF_FFFE, 1)
        );
        assert_eq!(
            WideningMul::widening_mul(0xFFFF_FFFF_FFFF_FFFFu64, 2u64),
            (0xFFFF_FFFF_FFFF_FFFE, 1)
        );

        // Test FixedUInt via WideningMul trait
        let a = U16::from(0xFFFFu16);
        let (lo, hi) = WideningMul::widening_mul(a, a);
        assert_eq!(lo, U16::from(0x0001u16));
        assert_eq!(hi, U16::from(0xFFFEu16));

        // Verify WideningMul produces same result as ConstWideningMul
        let b = U32::from(0x1234_5678u32);
        let c = U32::from(0x9ABC_DEF0u32);
        let (lo_trait, hi_trait) = WideningMul::widening_mul(b, c);
        let (lo_const, hi_const) = ConstWideningMul::widening_mul(b, c);
        assert_eq!(lo_trait, lo_const);
        assert_eq!(hi_trait, hi_const);
    }

    /// Test the non-const CarryingMul trait for primitives and FixedUInt.
    #[test]
    fn test_carrying_mul_trait() {
        // Test primitive types via CarryingMul trait
        // 10 * 10 + 5 = 105
        assert_eq!(CarryingMul::carrying_mul(10u8, 10u8, 5u8), (105, 0));
        // 255 * 255 + 255 = 65280 = 0xFF00
        assert_eq!(CarryingMul::carrying_mul(255u8, 255u8, 255u8), (0, 255));

        // Test carrying_mul_add: 10 * 10 + 3 + 2 = 105
        assert_eq!(
            CarryingMul::carrying_mul_add(10u8, 10u8, 3u8, 2u8),
            (105, 0)
        );
        // 255 * 255 + 255 + 255 = 65535 = 0xFFFF
        assert_eq!(
            CarryingMul::carrying_mul_add(255u8, 255u8, 255u8, 255u8),
            (255, 255)
        );

        // Test FixedUInt via CarryingMul trait
        let a = U16::from(100u8);
        let b = U16::from(100u8);
        let carry = U16::from(5u8);
        let (lo, hi) = CarryingMul::carrying_mul(a, b, carry);
        assert_eq!(lo, U16::from(10005u16)); // 100 * 100 + 5 = 10005
        assert_eq!(hi, U16::from(0u8));

        // Verify CarryingMul produces same result as ConstCarryingMul
        let x = U32::from(0x1234u32);
        let y = U32::from(0x5678u32);
        let c = U32::from(0xABCDu32);
        let (lo_trait, hi_trait) = CarryingMul::carrying_mul(x, y, c);
        let (lo_const, hi_const) = ConstCarryingMul::carrying_mul(x, y, c);
        assert_eq!(lo_trait, lo_const);
        assert_eq!(hi_trait, hi_const);

        // Test carrying_mul_add for FixedUInt
        let addend = U32::from(0x9999u32);
        let (lo_trait, hi_trait) = CarryingMul::carrying_mul_add(x, y, addend, c);
        let (lo_const, hi_const) = ConstCarryingMul::carrying_mul_add(x, y, addend, c);
        assert_eq!(lo_trait, lo_const);
        assert_eq!(hi_trait, hi_const);
    }

    /// Test ref-based WideningMul and CarryingMul impls.
    #[test]
    fn test_ref_based_mul_traits() {
        // Primitives: ref should match value
        assert_eq!(
            WideningMul::widening_mul(&0xFFFFu16, &0xFFFFu16),
            WideningMul::widening_mul(0xFFFFu16, 0xFFFFu16),
        );
        assert_eq!(
            CarryingMul::carrying_mul(&255u8, &255u8, &255u8),
            CarryingMul::carrying_mul(255u8, 255u8, 255u8),
        );
        assert_eq!(
            CarryingMul::carrying_mul_add(&10u8, &10u8, &3u8, &2u8),
            CarryingMul::carrying_mul_add(10u8, 10u8, 3u8, 2u8),
        );

        // FixedUInt: ref should match value
        let a = U32::from(0x1234_5678u32);
        let b = U32::from(0x9ABC_DEF0u32);
        assert_eq!(
            WideningMul::widening_mul(&a, &b),
            WideningMul::widening_mul(a, b),
        );

        let carry = U16::from(5u8);
        let x = U16::from(100u8);
        assert_eq!(
            CarryingMul::carrying_mul(&x, &x, &carry),
            CarryingMul::carrying_mul(x, x, carry),
        );
        let addend = U16::from(10u8);
        assert_eq!(
            CarryingMul::carrying_mul_add(&x, &x, &addend, &carry),
            CarryingMul::carrying_mul_add(x, x, addend, carry),
        );
    }
}
