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

//! `modmath_cios::CiosRowOps` implementation for `FixedUInt`.
//!
//! Gated behind the `cios` cargo feature so a default build of
//! `fixed-bigint` does not pull `modmath-cios` in. Enabled by downstream
//! crates that want to drive CIOS-style Montgomery multiplication
//! through `modmath`'s algorithm body (which deps `modmath-cios` and
//! is generic over `CiosRowOps`).
//!
//! ## Why the trait lives in `modmath-cios` (a leaf crate)
//!
//! An earlier iteration (commit `af832a9`) put `CiosRowOps` in
//! `modmath` itself with `modmath` dev-deping `fixed-bigint` to test
//! the `FixedUInt` impl. That doesn't work: `cargo test` compiles
//! `modmath` twice — once normally (the library `fixed-bigint` links
//! against through its `modmath` dep) and once with `--test` (the
//! `modmath` test binary). Same source, two distinct metadata hashes,
//! two distinct `CiosRowOps` identities. The impl satisfies one;
//! `modmath`'s own tests reference the other. The bound never
//! resolves. Cargo-level dedup ≠ rustc-level dedup. See
//! `CIOS_TRAIT_MOVED.md`.
//!
//! Moving the trait to its own leaf crate (`modmath-cios`, no deps,
//! `#![no_std]`) closes the duplication: both `modmath` (in both
//! normal and `--test` mode) and `fixed-bigint` see exactly one
//! `modmath_cios::CiosRowOps`.
//!
//! `modmath` does not re-export `CiosRowOps`. Consumers import from
//! `modmath_cios` directly (per the maintainer's "API moved, path
//! moves with it" policy — no compatibility shim).
//!
//! ## One impl, both personalities
//!
//! `CiosRowOps`'s trait contract documents that the `word(&self, i)`
//! accessor is only ever called with a public `i < self.word_count()`.
//! Under that precondition, infallible direct indexing is CT-safe — `i`
//! is never operand-dependent, so the bounds check doesn't leak. There
//! is no `Nct`/`Ct` discriminant on this trait (unlike the retired
//! `MulAccOps`, whose `GetWordOutput = Option<T>` / `CtOption<T>` split
//! was the personality marker). So one impl block covers both.
//!
//! ## Replaces `MulAccOps`
//!
//! `fixed_bigint::MulAccOps` and its impls are deleted in the same
//! commit. The two row kernels are byte-identical (same loop, same
//! `CarryingMul::carrying_mul_add` calls, same overflow handling); only
//! the trait shape changed. The two callsite-visible breaks vs
//! `MulAccOps`:
//!
//! - `fn word_count() -> usize` → `fn word_count(&self) -> usize`.
//!   Instance method now, admits heap bigint backends.
//! - `fn get_word(&self, i) -> Self::GetWordOutput` → `fn word(&self, i)
//!   -> Self::Word`. Infallible; the personality-discriminant
//!   associated type is gone.

#![cfg(feature = "cios")]

use super::{FixedUInt, MachineWord};
use crate::const_numtraits::{CarryingAdd, CarryingMul, ConstZero};
use const_num_traits::Personality;

impl<T, const N: usize, P: Personality> modmath_cios::CiosRowOps for FixedUInt<T, N, P>
where
    T: MachineWord
        + CarryingMul<Unsigned = T>
        + CarryingAdd
        + core::ops::Mul<T, Output = T>,
{
    type Word = T;

    #[inline]
    fn word_count(&self) -> usize {
        N
    }

    /// Panic-free, CT-safe under the trait precondition (`i` is public,
    /// `i < N`). `array.get(i).copied().unwrap_or(ZERO)` instead of
    /// `array[i]` — the `unwrap_or` fallback is dead code at the
    /// algorithm level (the trait contract forbids an out-of-bounds
    /// `i`), but the safe-slice form keeps `panic_bounds_check` out of
    /// the linked binary. Same body for both personalities: `i` is
    /// public, the bounds check is value-independent.
    #[inline]
    fn word(&self, i: usize) -> T {
        self.array
            .get(i)
            .copied()
            .unwrap_or(<T as ConstZero>::ZERO)
    }

    /// Phase 1 row: `acc += scalar * multiplicand`. Returns the
    /// carry-out word.
    ///
    /// Byte-identical body to the retired `MulAccOps::mul_acc_row`.
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

    /// Phase 2 row: `[acc, acc_hi] = ([acc, acc_hi] + scalar *
    /// multiplicand) >> word_bits`. Returns the carry word (0 or 1)
    /// from the fold.
    ///
    /// Byte-identical body to the retired `MulAccOps::mul_acc_shift_row`.
    fn mul_acc_shift_row(scalar: T, multiplicand: &Self, acc: &mut Self, acc_hi: T) -> T {
        debug_assert!(N > 0, "CiosRowOps requires at least one word");
        // First word: discarded (zero by CIOS construction).
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

        // Branchless: convert overflow bool to word via carrying_add(0, 0, overflow).
        let (overflow_word, _) = <T as CarryingAdd>::carrying_add(
            <T as ConstZero>::ZERO,
            <T as ConstZero>::ZERO,
            overflow,
        );
        overflow_word
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
        // Documented dead-code branch: the trait contract forbids
        // `i >= word_count()`, but the body avoids panic_bounds_check
        // by returning ZERO instead. Exercising it just confirms the
        // safe-slice path is wired correctly.
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
    fn ct_personality_uses_same_body() {
        // Same numeric result regardless of personality (the trait body
        // is uniform). If a future change accidentally introduces a
        // `match P::TAG` split that diverges, this catches it.
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
