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

use super::{FixedUInt, MachineWord, add_with_carry, sub_with_borrow};
use crate::const_numtraits::{
    BorrowingSub, Bounded, CarryingAdd, CarryingMul, One, WideningMul, Zero,
};
use crate::machineword::ConstMachineWord;
use const_num_traits::{Personality, PersonalityTag};

c0nst::c0nst! {
    c0nst impl<T: [c0nst] ConstMachineWord + [c0nst] CarryingAdd + MachineWord, const N: usize, P: Personality> CarryingAdd for FixedUInt<T, N, P> {
        fn carrying_add(self, rhs: Self, carry: bool) -> (Self, bool) {
            let (array, carry_out) = add_with_carry(&self.array, &rhs.array, carry);
            (Self::from_array(array), carry_out)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + [c0nst] BorrowingSub + MachineWord, const N: usize, P: Personality> BorrowingSub for FixedUInt<T, N, P> {
        fn borrowing_sub(self, rhs: Self, borrow: bool) -> (Self, bool) {
            let (array, borrow_out) = sub_with_borrow(&self.array, &rhs.array, borrow);
            (Self::from_array(array), borrow_out)
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

    // `WideningMul` for FixedUInt is intentionally NOT implemented. Per
    // MIGRATION.md §2.4, `WideningMul::Wide` is a single double-width
    // primitive (`Wide = u16` for `u8` etc.). Arbitrary-precision /
    // fixed-width-generic types like `FixedUInt<N>` have no
    // `FixedUInt<2N>` to be `Wide` without `generic_const_exprs`. The
    // schoolbook full product is exposed through `CarryingMul` below,
    // which returns `(low, high)` natively — exactly the shape needed.

    /// Schoolbook full product `self * rhs` returning the 2N-word result
    /// split into two N-word halves `(low, high)`. Private helper shared
    /// between `CarryingMul::carrying_mul` and `carrying_mul_add`.
    c0nst fn schoolbook_mul<
        T: [c0nst] ConstMachineWord + [c0nst] CarryingAdd + MachineWord,
        const N: usize, P: Personality,
    >(
        a: FixedUInt<T, N, P>, b: FixedUInt<T, N, P>,
    ) -> (FixedUInt<T, N, P>, FixedUInt<T, N, P>)
    where
        <T as ConstMachineWord>::ConstDoubleWord:
            [c0nst] core::ops::Mul<Output = <T as ConstMachineWord>::ConstDoubleWord>
            + [c0nst] core::ops::BitAnd<Output = <T as ConstMachineWord>::ConstDoubleWord>
            + [c0nst] core::ops::Shr<usize, Output = <T as ConstMachineWord>::ConstDoubleWord>,
    {
        // External `WideningMul` on T returns a single wide-int
        // (`<u8 as WideningMul>::Wide = u16`), not a `(lo, hi)` tuple.
        // We compute the per-limb wide product via the
        // `ConstMachineWord` double-word path and split into two T
        // halves with a mask + shift.
        let word_bits = core::mem::size_of::<T>() * 8;
        let t_max_dw = <T as ConstMachineWord>::to_double(<T as Bounded>::max_value());
        let mut result_low = [<T as Zero>::zero(); N];
        let mut result_high = [<T as Zero>::zero(); N];

        let mut i = 0usize;
        while i < N {
            let mut j = 0usize;
            while j < N {
                let pos = i + j;
                let op1_dw = <T as ConstMachineWord>::to_double(a.array[i]);
                let op2_dw = <T as ConstMachineWord>::to_double(b.array[j]);
                let prod_dw = op1_dw * op2_dw;
                let mul_lo = <T as ConstMachineWord>::from_double(prod_dw & t_max_dw);
                let mul_hi = <T as ConstMachineWord>::from_double(prod_dw >> word_bits);

                // Add the 2-word product (mul_hi, mul_lo) at position pos.
                let cur0 = get_at(&result_low, &result_high, pos);
                let (sum0, c0) = CarryingAdd::carrying_add(cur0, mul_lo, false);
                set_at(&mut result_low, &mut result_high, pos, sum0);

                let cur1 = get_at(&result_low, &result_high, pos + 1);
                let (sum1, c1) = CarryingAdd::carrying_add(cur1, mul_hi, c0);
                set_at(&mut result_low, &mut result_high, pos + 1, sum1);

                // Propagate any remaining carry. Personality-dispatched:
                // Nct keeps the fast early-exit (the tail is the
                // inner-inner Montgomery loop and matters for verify-side
                // throughput); Ct iterates the full tail unconditionally
                // so loop length depends only on the public counters.
                let mut carry = c1;
                let mut p = pos + 2;
                match P::TAG {
                    PersonalityTag::Nct => {
                        while carry && p < 2 * N {
                            let cur = get_at(&result_low, &result_high, p);
                            let (sum, c) = CarryingAdd::carrying_add(cur, T::zero(), true);
                            set_at(&mut result_low, &mut result_high, p, sum);
                            carry = c;
                            p += 1;
                        }
                    }
                    PersonalityTag::Ct => {
                        while p < 2 * N {
                            let cur = get_at(&result_low, &result_high, p);
                            let (sum, c) = CarryingAdd::carrying_add(cur, T::zero(), carry);
                            set_at(&mut result_low, &mut result_high, p, sum);
                            carry = c;
                            p += 1;
                        }
                    }
                }

                j += 1;
            }
            i += 1;
        }

        (FixedUInt::from_array(result_low), FixedUInt::from_array(result_high))
    }

    c0nst impl<T: [c0nst] ConstMachineWord + [c0nst] CarryingAdd + [c0nst] BorrowingSub + MachineWord, const N: usize, P: Personality> CarryingMul for FixedUInt<T, N, P>
    where
        <T as ConstMachineWord>::ConstDoubleWord:
            [c0nst] core::ops::Mul<Output = <T as ConstMachineWord>::ConstDoubleWord>
            + [c0nst] core::ops::BitAnd<Output = <T as ConstMachineWord>::ConstDoubleWord>
            + [c0nst] core::ops::Shr<usize, Output = <T as ConstMachineWord>::ConstDoubleWord>,
    {
        type Unsigned = Self;
        fn carrying_mul(self, rhs: Self, carry: Self) -> (Self, Self) {
            // Full product + add carry to low half, propagate to high.
            let (lo, hi) = schoolbook_mul(self, rhs);

            let (lo2, c) = add_with_carry(&lo.array, &carry.array, false);
            let zeros = [T::zero(); N];
            let (hi2, _) = add_with_carry(&hi.array, &zeros, c);

            (Self::from_array(lo2), Self::from_array(hi2))
        }

        fn carrying_mul_add(self, rhs: Self, addend: Self, carry: Self) -> (Self, Self) {
            // Full product + add addend + add carry.
            let (lo, hi) = schoolbook_mul(self, rhs);

            let (lo2, c1) = add_with_carry(&lo.array, &carry.array, false);
            let (lo3, c2) = add_with_carry(&lo2, &addend.array, false);

            // Both c1 and c2 can be true; add each carry to hi separately.
            let zeros = [T::zero(); N];
            let (hi2, _) = add_with_carry(&hi.array, &zeros, c1);
            let (hi3, _) = add_with_carry(&hi2, &zeros, c2);

            (Self::from_array(lo3), Self::from_array(hi3))
        }
    }

    // --- Reference-receiver bigint-helper impls -----------------------------

    c0nst impl<T: [c0nst] ConstMachineWord + [c0nst] CarryingAdd + MachineWord, const N: usize, P: Personality> CarryingAdd for &FixedUInt<T, N, P> {
        fn carrying_add(self, rhs: Self, carry: bool) -> (FixedUInt<T, N, P>, bool) {
            <FixedUInt<T, N, P> as CarryingAdd>::carrying_add(*self, *rhs, carry)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + [c0nst] BorrowingSub + MachineWord, const N: usize, P: Personality> BorrowingSub for &FixedUInt<T, N, P> {
        fn borrowing_sub(self, rhs: Self, borrow: bool) -> (FixedUInt<T, N, P>, bool) {
            <FixedUInt<T, N, P> as BorrowingSub>::borrowing_sub(*self, *rhs, borrow)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + [c0nst] CarryingAdd + [c0nst] BorrowingSub + MachineWord, const N: usize, P: Personality> CarryingMul for &FixedUInt<T, N, P>
    where
        <T as ConstMachineWord>::ConstDoubleWord:
            [c0nst] core::ops::Mul<Output = <T as ConstMachineWord>::ConstDoubleWord>
            + [c0nst] core::ops::BitAnd<Output = <T as ConstMachineWord>::ConstDoubleWord>
            + [c0nst] core::ops::Shr<usize, Output = <T as ConstMachineWord>::ConstDoubleWord>,
    {
        type Unsigned = FixedUInt<T, N, P>;
        fn carrying_mul(self, rhs: Self, carry: Self) -> (FixedUInt<T, N, P>, FixedUInt<T, N, P>) {
            <FixedUInt<T, N, P> as CarryingMul>::carrying_mul(*self, *rhs, *carry)
        }
        fn carrying_mul_add(self, rhs: Self, addend: Self, carry: Self) -> (FixedUInt<T, N, P>, FixedUInt<T, N, P>) {
            <FixedUInt<T, N, P> as CarryingMul>::carrying_mul_add(*self, *rhs, *addend, *carry)
        }
    }
}

// (Legacy non-const WideningMul / CarryingMul shim impls retired —
// the `c0nst WideningMul` / `c0nst CarryingMul` impls above are now
// the impls of the external traits.)

#[cfg(test)]
mod tests {
    use super::*;

    type U16 = FixedUInt<u8, 2>;
    type U32 = FixedUInt<u8, 4>;

    c0nst::c0nst! {
        pub c0nst fn const_carrying_add<T: [c0nst] ConstMachineWord + [c0nst] CarryingAdd + [c0nst] BorrowingSub + MachineWord, const N: usize, P: Personality>(
            a: FixedUInt<T, N, P>,
            b: FixedUInt<T, N, P>,
            carry: bool,
        ) -> (FixedUInt<T, N, P>, bool) {
            CarryingAdd::carrying_add(a, b, carry)
        }

        pub c0nst fn const_borrowing_sub<T: [c0nst] ConstMachineWord + [c0nst] CarryingAdd + [c0nst] BorrowingSub + MachineWord, const N: usize, P: Personality>(
            a: FixedUInt<T, N, P>,
            b: FixedUInt<T, N, P>,
            borrow: bool,
        ) -> (FixedUInt<T, N, P>, bool) {
            BorrowingSub::borrowing_sub(a, b, borrow)
        }

        /// Backwards-compatible test shim: returns the full `(low, high)`
        /// product. `FixedUInt` no longer implements `WideningMul` (per
        /// MIGRATION.md §2.4); this routes through `CarryingMul` with a
        /// zero carry, which produces the same value.
        pub c0nst fn const_widening_mul<T: [c0nst] ConstMachineWord + [c0nst] CarryingAdd + [c0nst] BorrowingSub + MachineWord, const N: usize, P: Personality>(
            a: FixedUInt<T, N, P>,
            b: FixedUInt<T, N, P>,
        ) -> (FixedUInt<T, N, P>, FixedUInt<T, N, P>)
        where
            <T as ConstMachineWord>::ConstDoubleWord:
                [c0nst] core::ops::Mul<Output = <T as ConstMachineWord>::ConstDoubleWord>
                + [c0nst] core::ops::BitAnd<Output = <T as ConstMachineWord>::ConstDoubleWord>
                + [c0nst] core::ops::Shr<usize, Output = <T as ConstMachineWord>::ConstDoubleWord>,
        {
            CarryingMul::carrying_mul(a, b, <FixedUInt<T, N, P> as Zero>::zero())
        }

        pub c0nst fn const_carrying_mul<T: [c0nst] ConstMachineWord + [c0nst] CarryingAdd + [c0nst] BorrowingSub + MachineWord, const N: usize, P: Personality>(
            a: FixedUInt<T, N, P>,
            b: FixedUInt<T, N, P>,
            carry: FixedUInt<T, N, P>,
        ) -> (FixedUInt<T, N, P>, FixedUInt<T, N, P>)
        where
            <T as ConstMachineWord>::ConstDoubleWord:
                [c0nst] core::ops::Mul<Output = <T as ConstMachineWord>::ConstDoubleWord>
                + [c0nst] core::ops::BitAnd<Output = <T as ConstMachineWord>::ConstDoubleWord>
                + [c0nst] core::ops::Shr<usize, Output = <T as ConstMachineWord>::ConstDoubleWord>,
        {
            CarryingMul::carrying_mul(a, b, carry)
        }

        pub c0nst fn const_carrying_mul_add<T: [c0nst] ConstMachineWord + [c0nst] CarryingAdd + [c0nst] BorrowingSub + MachineWord, const N: usize, P: Personality>(
            a: FixedUInt<T, N, P>,
            b: FixedUInt<T, N, P>,
            addend: FixedUInt<T, N, P>,
            carry: FixedUInt<T, N, P>,
        ) -> (FixedUInt<T, N, P>, FixedUInt<T, N, P>)
        where
            <T as ConstMachineWord>::ConstDoubleWord:
                [c0nst] core::ops::Mul<Output = <T as ConstMachineWord>::ConstDoubleWord>
                + [c0nst] core::ops::BitAnd<Output = <T as ConstMachineWord>::ConstDoubleWord>
                + [c0nst] core::ops::Shr<usize, Output = <T as ConstMachineWord>::ConstDoubleWord>,
        {
            CarryingMul::carrying_mul_add(a, b, addend, carry)
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
            const A: U16 = FixedUInt::from_array([100, 0]);
            const B: U16 = FixedUInt::from_array([50, 0]);

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
            const C: U16 = FixedUInt::from_array([0, 1]); // 256
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
            T: CarryingMul<Unsigned = T>
                + core::ops::Mul<T, Output = T>
                + CarryingAdd
                + BorrowingSub
                + Eq
                + core::fmt::Debug
                + Copy
                + Zero,
        {
            let (lo, hi) = CarryingMul::carrying_mul(a, b, <T as Zero>::zero());
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
            T: CarryingMul<Unsigned = T>
                + core::ops::Mul<T, Output = T>
                + Eq
                + core::fmt::Debug
                + Copy,
        {
            let (lo, hi) = CarryingMul::carrying_mul_add(a, b, addend, carry);
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
        assert_eq!(CarryingMul::carrying_mul(255u8, 255u8, 0u8), (1, 254)); // 0xFE01
        assert_eq!(
            CarryingMul::carrying_mul(0xFFFFu16, 0xFFFFu16, 0u16),
            (0x0001, 0xFFFE)
        );
        assert_eq!(
            CarryingMul::carrying_mul(0xFFFF_FFFFu32, 2u32, 0u32),
            (0xFFFF_FFFE, 1)
        );
        assert_eq!(
            CarryingMul::carrying_mul(0xFFFF_FFFF_FFFF_FFFFu64, 2u64, 0u64),
            (0xFFFF_FFFF_FFFF_FFFE, 1)
        );

        // Test FixedUInt via WideningMul trait
        let a = U16::from(0xFFFFu16);
        let (lo, hi) = CarryingMul::carrying_mul(a, a, <U16 as Zero>::zero());
        assert_eq!(lo, U16::from(0x0001u16));
        assert_eq!(hi, U16::from(0xFFFEu16));

        // Sanity: CarryingMul on FixedUInt produces deterministic results.
        // (The original `WideningMul`-vs-`WideningMul` self-check is
        // retired now that `FixedUInt` no longer implements `WideningMul`
        // per MIGRATION.md §2.4.)
        let b = U32::from(0x1234_5678u32);
        let c = U32::from(0x9ABC_DEF0u32);
        let zero32 = <U32 as Zero>::zero();
        let (lo_a, hi_a) = CarryingMul::carrying_mul(b, c, zero32);
        let (lo_b, hi_b) = CarryingMul::carrying_mul(b, c, zero32);
        assert_eq!(lo_a, lo_b);
        assert_eq!(hi_a, hi_b);
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

        // Verify CarryingMul produces same result as CarryingMul
        let x = U32::from(0x1234u32);
        let y = U32::from(0x5678u32);
        let c = U32::from(0xABCDu32);
        let (lo_trait, hi_trait) = CarryingMul::carrying_mul(x, y, c);
        let (lo_const, hi_const) = CarryingMul::carrying_mul(x, y, c);
        assert_eq!(lo_trait, lo_const);
        assert_eq!(hi_trait, hi_const);

        // Test carrying_mul_add for FixedUInt
        let addend = U32::from(0x9999u32);
        let (lo_trait, hi_trait) = CarryingMul::carrying_mul_add(x, y, addend, c);
        let (lo_const, hi_const) = CarryingMul::carrying_mul_add(x, y, addend, c);
        assert_eq!(lo_trait, lo_const);
        assert_eq!(hi_trait, hi_const);
    }

    /// Sanity check: CarryingMul is deterministic on primitives + FixedUInt.
    ///
    /// (Originally a "ref-based vs value-based" check that became
    /// redundant once MIGRATION.md §2.1 unified everything to by-value,
    /// and lost its FixedUInt half once §2.4 ruled out
    /// `impl WideningMul for FixedUInt`.)
    #[test]
    fn test_ref_based_mul_traits() {
        assert_eq!(
            CarryingMul::carrying_mul(0xFFFFu16, 0xFFFFu16, 0u16),
            CarryingMul::carrying_mul(0xFFFFu16, 0xFFFFu16, 0u16),
        );
        assert_eq!(
            CarryingMul::carrying_mul(255u8, 255u8, 255u8),
            CarryingMul::carrying_mul(255u8, 255u8, 255u8),
        );
        assert_eq!(
            CarryingMul::carrying_mul_add(10u8, 10u8, 3u8, 2u8),
            CarryingMul::carrying_mul_add(10u8, 10u8, 3u8, 2u8),
        );

        let a = U32::from(0x1234_5678u32);
        let b = U32::from(0x9ABC_DEF0u32);
        let zero32 = <U32 as Zero>::zero();
        assert_eq!(
            CarryingMul::carrying_mul(a, b, zero32),
            CarryingMul::carrying_mul(a, b, zero32),
        );

        let carry = U16::from(5u8);
        let x = U16::from(100u8);
        assert_eq!(
            CarryingMul::carrying_mul(x, x, carry),
            CarryingMul::carrying_mul(x, x, carry),
        );
        let addend = U16::from(10u8);
        assert_eq!(
            CarryingMul::carrying_mul_add(x, x, addend, carry),
            CarryingMul::carrying_mul_add(x, x, addend, carry),
        );
    }
}
