//! `modmath_cios::CiosRowOps` impl for `HeaplessBigInt`.
//!
//! CIOS Montgomery multiplication drives multi-limb integer operands
//! through two row-op kernels: a plain multiply-accumulate and a
//! multiply-accumulate-with-shift. Together with `word_count()` and a
//! `cios_accumulator()` sized to match the operand width, they let the
//! CIOS driver be generic over the carrier type.
//!
//! `cios_accumulator(&self)` is overridden so runtime-width operands
//! hand back a zero-value carrier whose `len` matches `self.len`; the
//! trait's `Default` body returns the mathematical zero at `len == 0`,
//! which would give the driver `word_count(acc) == 0` and break the
//! invariant.
//!
//! The row-op bodies mirror the `mul_slice` shape in `arith.rs`
//! (`carrying_mul` + `carrying_add`), reusing the max-value analysis
//! that shows carry propagation stays inside a single `T`.

use super::{HeaplessBigInt, zero};
use crate::MachineWord;
use const_num_traits::{CarryingAdd, CarryingMul, ConstOne, Personality};

impl<T, const CAP: usize, P: Personality> modmath_cios::CiosRowOps for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type Word = T;

    fn word_count(&self) -> usize {
        self.len as usize
    }

    fn cios_accumulator(&self) -> Self {
        Self::new_zero_with_len(self.len)
    }

    fn word(&self, i: usize) -> T {
        self.limbs[i]
    }

    fn mul_acc_row(scalar: T, multiplicand: &Self, acc: &mut Self, carry_in: T) -> T {
        // acc += scalar * multiplicand + carry_in. Each iteration adds
        // one limb's worth. carry propagates through the loop; the
        // final carry-out is returned.
        let n = multiplicand.len as usize;
        let mut carry = carry_in;
        let mut i = 0;
        while i < n {
            let (t_lo, t_hi) =
                <T as CarryingMul>::carrying_mul(scalar, multiplicand.limbs[i], carry);
            let (sum, c) = <T as CarryingAdd>::carrying_add(acc.limbs[i], t_lo, false);
            acc.limbs[i] = sum;
            // t_hi + c never overflows T: when t_hi is maximal (2^b - 1)
            // the corresponding t_lo is zero, so acc[i] + t_lo does not
            // overflow and c == 0.
            let (new_carry, _) = <T as CarryingAdd>::carrying_add(t_hi, zero(), c);
            carry = new_carry;
            i += 1;
        }
        carry
    }

    fn mul_acc_shift_row(scalar: T, multiplicand: &Self, acc: &mut Self, acc_hi: T) -> T {
        let n = multiplicand.len as usize;
        // Phase 1: acc += scalar * multiplicand, running carry.
        let mut carry = zero::<T>();
        let mut i = 0;
        while i < n {
            let (t_lo, t_hi) =
                <T as CarryingMul>::carrying_mul(scalar, multiplicand.limbs[i], carry);
            let (sum, c) = <T as CarryingAdd>::carrying_add(acc.limbs[i], t_lo, false);
            acc.limbs[i] = sum;
            let (new_carry, _) = <T as CarryingAdd>::carrying_add(t_hi, zero(), c);
            carry = new_carry;
            i += 1;
        }
        // Combine phase-1 carry with the incoming acc_hi at position W.
        let (top_low, top_hi_bit) = <T as CarryingAdd>::carrying_add(carry, acc_hi, false);
        // Shift right by one limb: drop acc[0] (which the CIOS
        // invariant makes zero), shuffle limbs down, place top_low at
        // the highest slot.
        let mut i = 0;
        while i + 1 < n {
            acc.limbs[i] = acc.limbs[i + 1];
            i += 1;
        }
        if n > 0 {
            acc.limbs[n - 1] = top_low;
        }
        if top_hi_bit {
            <T as ConstOne>::ONE
        } else {
            zero()
        }
    }
}
