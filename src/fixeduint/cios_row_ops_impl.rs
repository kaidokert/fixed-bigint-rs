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

//! `modmath_cios::CiosRowOps` implementation for `FixedUInt`. Gated
//! behind the `cios` cargo feature.
//!
//! One impl block covers both personalities: `word(&self, i)`'s trait
//! contract guarantees `i` is public and in-range, so infallible
//! indexing doesn't leak — no `Nct`/`Ct` split needed on the accessor.

#![cfg(feature = "cios")]

use super::{FixedUInt, MachineWord};
use const_num_traits::Personality;
use const_num_traits::{CarryingAdd, CarryingMul, ConstZero};

impl<T, const N: usize, P: Personality> modmath_cios::CiosRowOps for FixedUInt<T, N, P>
where
    T: MachineWord + CarryingMul<Unsigned = T> + CarryingAdd,
{
    type Word = T;

    #[inline]
    fn word_count(&self) -> usize {
        N
    }

    /// `get().unwrap_or(ZERO)` rather than `array[i]` so no
    /// `panic_bounds_check` reaches the linked binary. Fallback is
    /// unreachable per the trait's public-`i < N` precondition.
    ///
    /// CT invariant: `i` is a public shape parameter of the caller
    /// (`0..word_count()`), never derived from a secret value. Under
    /// that contract the safe-slice check is CT-uniform.
    #[inline]
    fn word(&self, i: usize) -> T {
        self.array.get(i).copied().unwrap_or(<T as ConstZero>::ZERO)
    }

    /// `acc += scalar * multiplicand`. Returns the carry-out word.
    fn mul_acc_row(scalar: T, multiplicand: &Self, acc: &mut Self, carry_in: T) -> T {
        let mut carry = carry_in;
        let mut j = 0;
        while j < N {
            let (lo, hi) =
                CarryingMul::carrying_mul_add(scalar, multiplicand.array[j], acc.array[j], carry);
            acc.array[j] = lo;
            carry = hi;
            j += 1;
        }
        carry
    }

    /// `[acc, acc_hi] = ([acc, acc_hi] + scalar * multiplicand) >>
    /// word_bits`. Returns the carry word (0 or 1) from the fold.
    fn mul_acc_shift_row(scalar: T, multiplicand: &Self, acc: &mut Self, acc_hi: T) -> T {
        // First word: discarded (zero by CIOS construction).
        // (N > 0 is a trait-contract precondition; the array indexing
        // below would panic on N=0 regardless.)
        let (_, mut carry) = CarryingMul::carrying_mul_add(
            scalar,
            multiplicand.array[0],
            acc.array[0],
            <T as ConstZero>::ZERO,
        );

        // Remaining words: shift down by one position.
        let mut j = 1;
        while j < N {
            let (lo, hi) =
                CarryingMul::carrying_mul_add(scalar, multiplicand.array[j], acc.array[j], carry);
            acc.array[j - 1] = lo;
            carry = hi;
            j += 1;
        }

        // Fold acc_hi + carry into acc[N-1].
        let (sum, overflow) = <T as CarryingAdd>::carrying_add(acc_hi, carry, false);
        acc.array[N - 1] = sum;

        // No `bool as T` cast is generically available; convert the
        // overflow bool to a T-word via `carrying_add(0, 0, overflow)`.
        <T as CarryingAdd>::carrying_add(<T as ConstZero>::ZERO, <T as ConstZero>::ZERO, overflow).0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use const_num_traits::{Ct, Nct};
    use modmath_cios::CiosRowOps;

    type U16Nct = FixedUInt<u8, 2, Nct>;
    type U16Ct = FixedUInt<u8, 2, Ct>;

    /// Tripwire: the impl is generic on the `Personality` parameter, so
    /// every test that constructs through `CiosRowOps::word_count` /
    /// `::word` should work for both `Ct` and `Nct` without separate
    /// bodies. If someone later splits the impl by personality
    /// (`Nct`-only `CiosRowOps`, etc.), this fails to compile — exactly
    /// the regression we want to catch.
    fn word_count_and_lookup<P: Personality>(v: FixedUInt<u8, 2, P>) -> (usize, u8, u8) {
        let count = CiosRowOps::word_count(&v);
        let lo = CiosRowOps::word(&v, 0);
        let hi = CiosRowOps::word(&v, 1);
        (count, lo, hi)
    }

    #[test]
    fn word_count_is_instance_method() {
        let nct = U16Nct::from(0x1234u16);
        let ct = U16Ct::from(0x1234u16);
        assert_eq!(word_count_and_lookup(nct), (2, 0x34, 0x12));
        assert_eq!(word_count_and_lookup(ct), (2, 0x34, 0x12));
    }

    #[test]
    fn word_returns_zero_on_out_of_bounds() {
        // Trait contract forbids `i >= word_count()`; the safe-slice
        // fallback keeps `panic_bounds_check` out of the binary.
        let v = U16Nct::from(0x1234u16);
        assert_eq!(CiosRowOps::word(&v, 2), 0);
        assert_eq!(CiosRowOps::word(&v, 999), 0);
    }

    #[test]
    fn mul_acc_row_zero_input_is_identity_on_acc() {
        // scalar = 0 ⇒ acc unchanged, carry = 0.
        let mult = U16Nct::from(0xFFFFu16);
        let mut acc = U16Nct::from(0x1234u16);
        let carry = <U16Nct as CiosRowOps>::mul_acc_row(0, &mult, &mut acc, 0);
        assert_eq!(acc, U16Nct::from(0x1234u16));
        assert_eq!(carry, 0);
    }

    #[test]
    fn mul_acc_row_smoke() {
        // acc + scalar * mult, hand-checked:
        //   1 * 2 + 3 = 5, fits one limb, carry 0.
        let mult = U16Nct::from(2u16);
        let mut acc = U16Nct::from(3u16);
        let carry = <U16Nct as CiosRowOps>::mul_acc_row(1, &mult, &mut acc, 0);
        assert_eq!(acc, U16Nct::from(5u16));
        assert_eq!(carry, 0);
    }

    #[test]
    fn mul_acc_shift_row_hand_checked() {
        // (scalar * mult + [acc, acc_hi * B^N]) shifted right by one word.
        // scalar=1, mult=1, acc=2, acc_hi=3 → the low byte (=3) is
        // discarded by the shift, acc becomes [0, acc_hi + carry] with
        // carry = 0 from the tiny product.
        let mult = U16Nct::from(1u8);
        let mut acc = U16Nct::from(2u8);
        let overflow = <U16Nct as CiosRowOps>::mul_acc_shift_row(1, &mult, &mut acc, 3);
        assert_eq!(acc.array, [0, 3]);
        assert_eq!(overflow, 0);
    }

    #[test]
    fn mul_acc_shift_row_ct_matches_nct() {
        let mult_n = U16Nct::from(0xABCDu16);
        let mut acc_n = U16Nct::from(0x1234u16);
        let ov_n = <U16Nct as CiosRowOps>::mul_acc_shift_row(0x7, &mult_n, &mut acc_n, 0x11);

        let mult_c = U16Ct::from(0xABCDu16);
        let mut acc_c = U16Ct::from(0x1234u16);
        let ov_c = <U16Ct as CiosRowOps>::mul_acc_shift_row(0x7, &mult_c, &mut acc_c, 0x11);

        assert_eq!(acc_n.array, acc_c.array);
        assert_eq!(ov_n, ov_c);
    }

    #[test]
    fn ct_personality_uses_same_body() {
        // Both personalities must produce identical numeric results —
        // the impl is uniform and this pins that invariant.
        let mult_n = U16Nct::from(0x10u16);
        let mut acc_n = U16Nct::from(0x20u16);
        let c_n = <U16Nct as CiosRowOps>::mul_acc_row(0x3, &mult_n, &mut acc_n, 0);

        let mult_c = U16Ct::from(0x10u16);
        let mut acc_c = U16Ct::from(0x20u16);
        let c_c = <U16Ct as CiosRowOps>::mul_acc_row(0x3, &mult_c, &mut acc_c, 0);

        assert_eq!(acc_n.array, acc_c.array);
        assert_eq!(c_n, c_c);
    }
}
