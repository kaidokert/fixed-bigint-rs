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
use const_num_traits::{CarryingAdd, CarryingMul, Personality};

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
        // acc += scalar * multiplicand + carry_in; returns the carry-out.
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
        // Shift right by one limb: drop acc[0] (zero by the CIOS
        // invariant) and place top_low at the highest slot.
        let mut i = 0;
        while i + 1 < n {
            acc.limbs[i] = acc.limbs[i + 1];
            i += 1;
        }
        if n > 0 {
            acc.limbs[n - 1] = top_low;
        }
        // Convert the carry bool to a T-word branchlessly, matching
        // `FixedUInt::mul_acc_shift_row`. An `if top_hi_bit { … }` would
        // branch on a secret-derived carry bit under a `Ct` carrier; there is
        // no generic `bool as T`, so fold it through `carrying_add`.
        <T as CarryingAdd>::carrying_add(zero(), zero(), top_hi_bit).0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use const_num_traits::{Ct, Nct};
    use modmath_cios::CiosRowOps;

    /// The final carry word is produced by a branchless `carrying_add`
    /// fold (not an `if`); it must still be exactly 0 or 1. Covers both the
    /// no-overflow and the overflow (former `if top_hi_bit`) paths.
    #[test]
    fn mul_acc_shift_row_carry_bit_is_0_or_1() {
        type H = HeaplessBigInt<u8, 2, Ct>;
        // Tiny product, small acc_hi → no top overflow → 0.
        let mult = H::from_limbs([1, 0], 2);
        let mut acc = H::from_limbs([2, 0], 2);
        assert_eq!(
            <H as CiosRowOps>::mul_acc_shift_row(1, &mult, &mut acc, 3),
            0
        );
        // Maximal product carry + maximal acc_hi → top overflows a byte → 1.
        let mult = H::from_limbs([0xFF, 0xFF], 2);
        let mut acc = H::from_limbs([0, 0], 2);
        assert_eq!(
            <H as CiosRowOps>::mul_acc_shift_row(0xFF, &mult, &mut acc, 0xFF),
            1
        );
    }

    /// Both personalities run the same body and must agree bit-for-bit,
    /// including the branchless carry fold.
    #[test]
    fn row_ops_ct_matches_nct() {
        type HN = HeaplessBigInt<u8, 4, Nct>;
        type HC = HeaplessBigInt<u8, 4, Ct>;
        let m = [0xAB, 0xCD, 0x12, 0x34];
        let a = [0x10, 0x20, 0x30, 0x40];

        let mut acc_n = HN::from_limbs(a, 4);
        let cn = <HN as CiosRowOps>::mul_acc_row(0x7, &HN::from_limbs(m, 4), &mut acc_n, 0x11);
        let mut acc_c = HC::from_limbs(a, 4);
        let cc = <HC as CiosRowOps>::mul_acc_row(0x7, &HC::from_limbs(m, 4), &mut acc_c, 0x11);
        assert_eq!(acc_n.all_limbs(), acc_c.all_limbs());
        assert_eq!(cn, cc);

        let mut sacc_n = HN::from_limbs(a, 4);
        let sn =
            <HN as CiosRowOps>::mul_acc_shift_row(0x9, &HN::from_limbs(m, 4), &mut sacc_n, 0xEE);
        let mut sacc_c = HC::from_limbs(a, 4);
        let sc =
            <HC as CiosRowOps>::mul_acc_shift_row(0x9, &HC::from_limbs(m, 4), &mut sacc_c, 0xEE);
        assert_eq!(sacc_n.all_limbs(), sacc_c.all_limbs());
        assert_eq!(sn, sc);
    }
}
